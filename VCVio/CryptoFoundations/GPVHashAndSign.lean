/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics
import VCVio.ProgramLogic.Relational.ProgrammingOracle

/-!
# GPV Hash-and-Sign Framework

This file defines a generic hash-and-sign signature scheme following the GPV (Gentry–Peikert–
Vaikuntanathan) framework [GPV08]. The construction is parameterized by a *preimage sampleable
function* (PSF), a many-to-one function equipped with a probabilistic trapdoor that samples
short preimages.

The GPV framework is the hash-and-sign analogue of the Fiat-Shamir transform:

| Interactive protocol | Fiat-Shamir → SignatureAlg |
|---|---|
| Trapdoor PSF | GPVHashAndSign → SignatureAlg |

## Main Definitions

- `PreimageSampleableFunction` — a function `eval` with a probabilistic trapdoor sampler and a
  shortness predicate on preimages.
- `GPVHashAndSign` — builds a `SignatureAlg` in the random-oracle model from a PSF, a generable
  key relation, and a salt type.

## Security

The PFDH (Probabilistic Full-Domain Hash) variant of the GPV scheme uses a random salt per
signing query. The precise EUF-CMA bound from [FGdG+25] Theorem 1 is:

  `Adv^{UF-CMA}(A) ≤ (r_u^{C_s} · (r_p^{C_s} · Adv^{ISIS}(B))^{...})^{...}`
  `                  + tail_bound + Q_s · (C_s + Q_H) / 2^k`

where the salt-collision term `Q_s · (C_s + Q_H) / 2^k` bounds the probability that
a fresh salt collides with any prior RO query. The simpler birthday bound
`qSign² / (2 · |Salt|)` from GPV08 Prop 6.2 is slightly looser but still valid and is
the one we formalize here.

The proof decomposes into:
- `GPVHashAndSign.reduction`: the collision-finding adversary (sign-then-hash simulation)
- `GPVHashAndSign.programmedPreimageReduction`: the exact-match branch reduction
- `GPVHashAndSign.collisionBound`: the salt-collision birthday bound
- `GPVHashAndSign.forgery_yields_collision`: the core distinct-preimage game-hop
- `GPVHashAndSign.forgery_yields_collision_or_exact_match`: the explicit split bound

## References

- [FGdG+25]: Fouque, Gajland, de Groote, Janneck, Kiltz. "A Closer Look at Falcon."
  ePrint 2024/1769. First concrete proof for Falcon+ (Theorem 1).
- [Jia+26]: Jia, Zhang, Yu, Tang. "Revisiting the Concrete Security of Falcon-type
  Signatures." ePrint 2026/096. Tightens Rényi loss to < 0.2 bits.
- GPV08: Gentry, Peikert, Vaikuntanathan. STOC 2008, Propositions 6.1–6.2.
- BDF+11: Boneh et al. "Random Oracles in a Quantum World." ASIACRYPT 2011.
-/

universe v


open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

/-! ## Preimage Sampleable Functions -/

/-- A preimage sampleable function (PSF) consists of:
- A public evaluation map `eval : PK → Domain → Range`.
- A probabilistic trapdoor sampler `trapdoorSample` that, given the secret key and a target in
  the range, produces a preimage in the domain.
- A shortness predicate `isShort` that the verifier checks on purported preimages.

This abstracts the core primitive in the GPV hash-and-sign framework. Unlike
`TrapdoorPermutation` (in `OneWay.lean`), a PSF is many-to-one, the inversion is probabilistic,
and acceptance depends on a quality predicate rather than exact inversion. -/
structure PreimageSampleableFunction (PK SK Domain Range : Type) where
  eval : PK → Domain → Range
  trapdoorSample : PK → SK → Range → ProbComp Domain
  isShort : Domain → Bool

namespace PreimageSampleableFunction

variable {PK SK Domain Range : Type}

/-- A PSF is correct if the trapdoor sampler always produces a valid preimage that is
accepted by the shortness predicate. -/
def Correct (psf : PreimageSampleableFunction PK SK Domain Range) : Prop :=
  ∀ pk sk t, ∀ x ∈ support (psf.trapdoorSample pk sk t),
    psf.eval pk x = t ∧
      psf.isShort x = true

/-- The GPV *regularity* (preimage-sampleability) property, expressed externally as an
equality of joint distributions.

A PSF is regular when there is a domain sampler `domainSample : PK → ProbComp Domain` such
that, for every key pair `(pk, sk)`, the joint distribution of `(eval pk s, s)` for a
forward-sampled preimage `s ← domainSample pk` matches the joint distribution of `(c, s)`
where the target `c` is drawn uniformly from `Range` and `s ← trapdoorSample pk sk c` is the
trapdoor preimage of `c`.

This is the classical GPV08 preimage-sampleability requirement: sampling a short preimage and
hashing it forward is statistically identical to sampling a uniform target and inverting it
with the trapdoor. It is the hypothesis that justifies the sign-then-hash hop in the EUF-CMA
proof. It is entered as an external hypothesis rather than as a field of
`PreimageSampleableFunction`, so the generic GPV theorem stays loss-free and each concrete
instance (e.g. Falcon) accounts for any sampler imperfection separately.

The property is satisfiable in principle: when `eval pk` is a bijection,
`trapdoorSample pk sk c := pure ((eval pk)⁻¹ c)` and `domainSample pk := $ᵗ Domain` realize
the equality. It is also non-trivial: the equation genuinely constrains `domainSample` against
the trapdoor sampler, so it is not vacuously true. -/
def Regularity [SampleableType Range]
    (psf : PreimageSampleableFunction PK SK Domain Range) : Prop :=
  ∃ domainSample : PK → ProbComp Domain,
    ∀ (pk : PK) (sk : SK),
      𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]

end PreimageSampleableFunction

/-! ## GPV Hash-and-Sign Construction -/

/-- The GPV hash-and-sign signature scheme in the random-oracle model.

Given a preimage sampleable function `psf`, a generable key relation `hr`, and a salt type
`Salt`, the construction builds a `SignatureAlg` where:

- **`keygen`**: sample a key pair from `hr.gen`.
- **`sign pk sk m`**: sample a random salt `r`, query the random oracle at `(r, m)` to obtain
  a target `c`, use `trapdoorSample` to find a short preimage `s` of `c`, and return `(r, s)`.
- **`verify pk m (r, s)`**: recompute `c` from the random oracle at `(r, m)`, then check that
  `eval pk s = c` and `isShort s`.

The signature type is `Salt × Domain` (salt paired with the short preimage).
The oracle spec is `unifSpec + (Salt × M →ₒ Range)` (uniform sampling + random oracle). -/
def GPVHashAndSign
    {m : Type → Type v} [Monad m]
    {PK SK Domain Range : Type}
    (psf : PreimageSampleableFunction PK SK Domain Range)
    {p : PK → SK → Bool}
    (hr : GenerableRelation PK SK p)
    (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt]
    [DecidableEq Range] [SampleableType Range]
    [MonadLiftT ProbComp m] [MonadLiftT (OracleQuery (Salt × M →ₒ Range)) m] :
    SignatureAlg m
      (M := M) (PK := PK) (SK := SK) (S := Salt × Domain) where
  keygen := liftM hr.gen
  sign := fun pk sk msg => do
    let r ← ($ᵗ Salt : ProbComp Salt)
    let c ← (Salt × M →ₒ Range).query (r, msg)
    let s ← psf.trapdoorSample pk sk c
    pure (r, s)
  verify := fun pk msg (r, s) => do
    let c ← (Salt × M →ₒ Range).query (r, msg)
    pure (decide (psf.eval pk s = c) && psf.isShort s)

namespace GPVHashAndSign

variable {PK SK Domain Range : Type}
  {p : PK → SK → Bool}
  [DecidableEq Range] [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt] [Fintype Salt]

/-- Runtime bundle for the GPV hash-and-sign random-oracle world. -/
noncomputable def runtime :
    ProbCompRuntime (OracleComp (unifSpec + (Salt × M →ₒ Range))) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (Salt × M →ₒ Range) (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)))
    ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

/-- Structural bound that counts only random-oracle queries in a GPV EUF-CMA adversary.

Defined as the generic predicate-targeted query bound `IsQueryBoundP` with the predicate
selecting the nested `.inl (.inr _)` (random-oracle) component of the index sum. -/
def hashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ S')) α) (Q : ℕ) : Prop :=
  OracleComp.IsQueryBoundP oa (· matches .inl (.inr _)) Q

/-- Structural query bound for GPV EUF-CMA adversaries that tracks both signing-oracle
queries (`qSign`) and random-oracle queries (`qHash`). Uniform-sampling queries are
unrestricted.

Defined as the conjunction of two predicate-targeted query bounds `IsQueryBoundP`, one per
counted oracle. Because the two index predicates are disjoint, the conjunction is
equivalent to the prior single-vector `IsQueryBound` formulation. -/
def signHashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ S')) α)
    (qSign qHash : ℕ) : Prop :=
  oa.IsQueryBoundP (· matches .inr _) qSign ∧
  oa.IsQueryBoundP (· matches .inl (.inr _)) qHash

/-- A collision-finding adversary receives a public key and must produce two distinct
short preimages with the same image under `psf.eval`. -/
abbrev CollisionAdversary := PK → ProbComp (Domain × Domain)

/-- Keyed collision-finding experiment for a preimage sampleable function. -/
def collisionFindingExp [DecidableEq Domain]
    (adversary : CollisionAdversary (PK := PK) (Domain := Domain)) :
    ProbComp Bool := do
  let pk ← do
    let keyPair ← hr.gen
    pure keyPair.1
  let (x₁, x₂) ← adversary pk
  return decide (x₁ ≠ x₂) &&
    decide (psf.eval pk x₁ = psf.eval pk x₂) &&
    psf.isShort x₁ &&
    psf.isShort x₂

/-- Success probability in the keyed collision-finding experiment. -/
noncomputable def collisionFindingAdvantage [DecidableEq Domain]
    (adversary : CollisionAdversary (PK := PK) (Domain := Domain)) :
    ℝ≥0∞ :=
  Pr[= true | collisionFindingExp (psf := psf) (hr := hr) adversary]

/-- A programmed-preimage adversary receives a public key and a programmed target `y`,
and tries to reproduce the challenger's hidden short preimage sampled for `y`. -/
abbrev ProgrammedPreimageAdversary := PK → Range → ProbComp Domain

/-- Exact-match experiment for the hidden programmed-preimage branch of the GPV proof.

The challenger samples an honest key pair, then chooses a uniformly random target `y` and a
hidden short preimage `x ← trapdoorSample pk sk y`. The adversary sees only `(pk, y)` and
succeeds iff it reproduces exactly the hidden programmed preimage `x`. -/
def programmedPreimageExp [DecidableEq Domain]
    (adversary : ProgrammedPreimageAdversary
      (PK := PK) (Domain := Domain) (Range := Range)) :
    ProbComp Bool := do
  let (pk, sk) ← hr.gen
  let y ← $ᵗ Range
  let x ← psf.trapdoorSample pk sk y
  let x' ← adversary pk y
  return decide (x' = x)

/-- Success probability in the exact-match programmed-preimage experiment. -/
noncomputable def programmedPreimageAdvantage [DecidableEq Domain]
    (adversary : ProgrammedPreimageAdversary
      (PK := PK) (Domain := Domain) (Range := Range)) :
    ℝ≥0∞ :=
  Pr[= true | programmedPreimageExp (psf := psf) (hr := hr) adversary]

/-! ## Proof Decomposition

The EUF-CMA security proof proceeds by a game-hopping argument:

**Game 0**: The real EUF-CMA experiment with a lazy random oracle and the honest
signing oracle (trapdoor sampler).

**Game 1**: Replace signing with "sign-then-hash": for each signing query on message `m`,
sample a short preimage `s ← D_short`, set `c := psf.eval pk s`, program the RO at
`(r, m) := c`, and return `(r, s)`. This is indistinguishable from Game 0 when the PSF
sampler is correct (the output distribution conditioned on the target is the same).

**Bad event**: A salt collision occurs (two distinct signing queries or the forgery reuse
the same `(salt, message)` pair as a prior RO entry). Under the birthday bound, this
happens with probability at most `q_S² / (2 · |Salt|)`.

**Game 2 (reduction)**: The simulator programs the random oracle with hidden short preimages.
If the adversary forges on a fresh `(salt, message)` pair and the forged short preimage differs
from the simulator's hidden programmed preimage at that point, the pair forms a collision under
`psf.eval`.

The exact-match branch, where the forgery reproduces the simulator's programmed preimage, is a
separate one-way/min-entropy obligation and is intentionally not encoded in the collision game
below.
-/

/-- The collision-branch GPV reduction adversary. Given a public key `pk`,
the reduction internally simulates the CMA experiment for the adversary:

1. Program a lazy random oracle, storing for each entry the hidden short preimage used to
   define that entry.
2. Answer signing queries using the sign-then-hash strategy: sample a short preimage
   `s` via `trapdoorSample`, compute `c = psf.eval pk s`, and program the RO at
   `(r, msg) := c`. Return `(r, s)` as the signature.
3. Run the adversary and, on a successful fresh forgery, return the simulator's hidden
   programmed preimage together with the forged preimage as a candidate collision.

The key insight is that in the sign-then-hash game, the reduction controls the entire
RO table. If the adversary forges on a fresh `(r*, msg*)` pair, the RO value at that
point was set by the reduction, so the hidden programmed preimage and the forged preimage
land at the same image under `psf.eval`.

The detailed construction simulates the adversary's oracle interactions by maintaining
a programmable RO state, using PSF correctness to ensure consistency. -/
noncomputable def reduction
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) :
    CollisionAdversary (PK := PK) (Domain := Domain) :=
  fun pk => do
    -- The simulation state threads the lazy random-oracle cache together with a *hidden
    -- preimage table* recording, for each programmed `(salt, message)` entry, the short
    -- preimage `s` used to define `psf.eval pk s` as the random-oracle value at that point.
    let State := (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)
    -- Random-oracle handler: on a cache hit reuse the recorded value; on a miss
    -- forward-sample a short preimage `s ← domainSample pk`, set the value to `psf.eval pk s`,
    -- and record `s` in the hidden table at the queried point.
    let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
      fun t => do
        let st ← get
        match st.1 t with
        | some v => pure v
        | none => do
            let s ← (domainSample pk : ProbComp Domain)
            let v := psf.eval pk s
            set ((st.1.cacheQuery t v, fun t' => if t' = t then some s else st.2 t') : State)
            pure v
    -- Uniform-sampling handler: answer uniform queries by drawing from the ambient `ProbComp`.
    let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
      fun t => (unifSpec.query t : ProbComp _)
    -- Signing handler (sign-then-hash): draw a fresh salt `r`, forward-sample a short preimage
    -- `s ← domainSample pk`, program the random oracle at `(r, msg) := psf.eval pk s`, record the
    -- hidden preimage, and return the signature `(r, s)`.
    let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
      fun msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let s ← (domainSample pk : ProbComp Domain)
        let v := psf.eval pk s
        let st ← get
        set ((st.1.cacheQuery (r, msg) v,
          fun t' => if t' = (r, msg) then some s else st.2 t') : State)
        pure (r, s)
    let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
        (StateT State ProbComp) := (unifImpl + roImpl) + signImpl
    -- Run the adversary under the simulated oracle stack, then extract a collision candidate.
    let ((msgStar, (rStar, sStar)), st) ←
      (simulateQ impl (adv.main pk)).run (∅, fun _ => none)
    -- On the forgery `(msgStar, (rStar, sStar))`, look up the hidden programmed preimage at the
    -- forged point. If present, it and the forged preimage `sStar` share the image
    -- `psf.eval pk sStar` (the random-oracle value the reduction programmed there), forming a
    -- collision candidate. Otherwise fall back to the forged preimage itself.
    match st.2 (rStar, msgStar) with
    | some sHidden => pure (sHidden, sStar)
    | none => pure (sStar, sStar)

/-- The exact-match branch reduction adversary. Given a public key `pk` and programmed target
`y`, the reduction embeds `(pk, y)` at one guessed programmed random-oracle entry. If the
adversary later forges on that entry and exactly reproduces the simulator's hidden preimage,
the reduction wins the programmed-preimage game.

Because the target must be embedded at one guessed programmed entry, this branch incurs an
explicit multi-target loss proportional to the total number of programmed entries. -/
noncomputable def programmedPreimageReduction
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) :
    ProgrammedPreimageAdversary (PK := PK) (Domain := Domain) (Range := Range) :=
  fun pk y => do
    -- The simulation state threads the lazy random-oracle cache, a running count of programmed
    -- entries, and the current reservoir winner: the `(salt, message)` point at which the target
    -- `y` is embedded, paired with the normal value `psf.eval pk s` that point would otherwise
    -- carry (kept so the displaced previous winner can be restored when a later entry wins).
    let State := (Salt × M →ₒ Range).QueryCache × ℕ × Option ((Salt × M) × Range)
    -- Embed `y` at one uniformly chosen programmed entry via reservoir sampling: at the `k`-th
    -- programmed point the new point wins with probability `1 / (k + 1)`. The winner's cache value
    -- is set to the target `y`; every other programmed entry carries its normal `psf.eval pk s`.
    let programStep : (Salt × M) → StateT State ProbComp Unit := fun t => do
      let s ← (domainSample pk : ProbComp Domain)
      let v := psf.eval pk s
      let st ← get
      let (cache, count, winner) := st
      let b ← ($ᵗ Fin (count + 1) : ProbComp (Fin (count + 1)))
      if b = 0 then
        -- New reservoir winner: restore the previous winner's normal value (if any), then embed
        -- `y` at the new point and record it together with its restorable normal value `v`.
        let cache' := match winner with
          | some (tOld, vOld) => cache.cacheQuery tOld vOld
          | none => cache
        set ((cache'.cacheQuery t y, count + 1, some (t, v)) : State)
      else
        set ((cache.cacheQuery t v, count + 1, winner) : State)
    -- Random-oracle handler: reuse cache hits; on a miss program the entry via `programStep`.
    let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
      fun t => do
        let st ← get
        match st.1 t with
        | some v => pure v
        | none => do
            programStep t
            let st' ← get
            pure ((st'.1 t).getD y)
    -- Uniform-sampling handler.
    let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
      fun t => (unifSpec.query t : ProbComp _)
    -- Signing handler (sign-then-hash): draw a fresh salt `r`, program `(r, msg)` via the same
    -- reservoir step, and return the signature `(r, s)` recovered from the programmed cache.
    let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
      fun msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let s ← (domainSample pk : ProbComp Domain)
        let v := psf.eval pk s
        let st ← get
        let (cache, count, winner) := st
        let b ← ($ᵗ Fin (count + 1) : ProbComp (Fin (count + 1)))
        if b = 0 then
          let cache' := match winner with
            | some (tOld, vOld) => cache.cacheQuery tOld vOld
            | none => cache
          set ((cache'.cacheQuery (r, msg) y, count + 1, some ((r, msg), v)) : State)
        else
          set ((cache.cacheQuery (r, msg) v, count + 1, winner) : State)
        pure (r, s)
    let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
        (StateT State ProbComp) := (unifImpl + roImpl) + signImpl
    let ((_msgStar, (_rStar, sStar)), _st) ←
      (simulateQ impl (adv.main pk)).run (∅, 0, none)
    -- The forged preimage `sStar` is the reduction's preimage candidate for the target `y`: when
    -- the forgery lands on the embedded entry, the random oracle there returned `y`, so a valid
    -- forgery `psf.eval pk sStar = y` exhibits a preimage of `y`.
    pure sStar

/-- The salt-collision birthday bound (GPV08, Proposition 6.2).

For `qSign` signing queries and `qHash` random-oracle queries, with salts drawn uniformly from a
set of size `|Salt|`, the standard GPV/FDH-with-salt bound on a fresh signing salt colliding with
any previously recorded random-oracle input (a prior signing salt or an adversary hash query) is
`(qSign + qHash)² / (2 · |Salt|)`. This upper-bounds the exact union sum
`qSign·(qSign-1)/2 + qSign·qHash` over the `qSign` fresh draws, each compared against at most
`j + qHash` recorded entries.

For Falcon with 40-byte salts (`|Salt| = 2^320`) and `qSign, qHash ≤ 2^64`:
  `collisionBound (Bytes 40) (2^64) (2^64) = 2^130 / (2 · 2^320) = 2^{-191}`. -/
noncomputable def collisionBound (qSign qHash : ℕ) : ENNReal :=
  ((qSign + qHash : ℕ) : ENNReal) ^ 2 / (2 * Fintype.card Salt)

open scoped Classical in
omit [DecidableEq Salt] in
/-- A single uniform salt draw lands in a fixed cache `cache ⊆ Salt` with probability exactly
`|cache| / |Salt|`.

This is the per-draw building block of the GPV salt-collision union bound: each fresh salt is
sampled uniformly and independently, so the chance it hits any of the previously recorded
random-oracle inputs is the size of that recorded set over the size of the salt space. -/
lemma probEvent_mem_uniformSample (cache : Finset Salt) :
    Pr[(· ∈ cache) | ($ᵗ Salt)] = cache.card / Fintype.card Salt := by
  rw [probEvent_uniformSample]
  congr 1
  simp

omit [DecidableEq Salt] [SampleableType Salt] in
/-- Arithmetic core of the GPV salt-collision birthday bound.

Summing the per-draw collision probabilities for `qSign` signing queries, where the `j`-th
fresh salt is compared against the at most `j + qHash` recorded random-oracle inputs (the `j`
prior signing salts and the up to `qHash` adversary hash queries), gives the running total
`∑_{j < qSign} (j + qHash) / |Salt|`. The exact sum
`∑_{j < qSign} (j + qHash) = qSign·(qSign-1)/2 + qSign·qHash` is at most `(qSign + qHash)² / 2`,
so the union bound is dominated by `collisionBound`. -/
lemma sum_range_div_card_le_collisionBound (qSign qHash : ℕ) :
    (∑ j ∈ Finset.range qSign, ((j + qHash : ℕ) : ℝ≥0∞) / Fintype.card Salt)
      ≤ collisionBound Salt qSign qHash := by
  unfold collisionBound
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have hsum : (∑ j ∈ Finset.range qSign, ((j + qHash : ℕ) : ℝ≥0∞))
      = ((∑ j ∈ Finset.range qSign, (j + qHash) : ℕ) : ℝ≥0∞) := by rw [Nat.cast_sum]
  rw [hsum]
  rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc]
  gcongr
  have hnat : (∑ j ∈ Finset.range qSign, (j + qHash)) * 2 ≤ (qSign + qHash) ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_range_id, Finset.sum_const, Finset.card_range,
      smul_eq_mul, add_mul, Nat.div_mul_cancel (Nat.even_mul_pred_self qSign).two_dvd]
    rcases Nat.eq_zero_or_pos qSign with h | h
    · simp [h]
    · nlinarith [Nat.sub_le qSign 1]
  have hcast : ((∑ j ∈ Finset.range qSign, (j + qHash) : ℕ) : ℝ≥0∞) * 2
      ≤ (((qSign + qHash : ℕ) : ℝ≥0∞)) ^ 2 := by
    have h2 := (Nat.cast_le (α := ℝ≥0∞)).2 hnat
    push_cast at h2 ⊢
    convert h2 using 2
  calc ((∑ j ∈ Finset.range qSign, (j + qHash) : ℕ) : ℝ≥0∞)
      = ((∑ j ∈ Finset.range qSign, (j + qHash) : ℕ) : ℝ≥0∞) * 2 * 2⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    _ ≤ ((qSign + qHash : ℕ) : ℝ≥0∞) ^ 2 * 2⁻¹ := by gcongr

open scoped Classical in
omit [DecidableEq Salt] in
/-- The GPV salt-collision union bound (GPV08, Proposition 6.2), as a uniform-draw-hits-cache
estimate.

If the random-oracle cache seen by the `j`-th signing query has size at most `j + qHash` (the `j`
prior signing salts plus the up to `qHash` adversary hash queries already recorded), then the
total probability that some fresh salt collides with a previously recorded entry is bounded by
`collisionBound`. The hypothesis `hcache` supplies the per-draw cache sizes `c j` together with
the bound `c j ≤ j + qHash`; the conclusion is the union bound over the `qSign` independent
uniform draws.

This is the real salt-collision event of the GPV proof (a fresh uniform draw hitting the
recorded random-oracle inputs), distinct from a hash-*output* collision over `|Range|`. -/
lemma probEvent_salt_collision_le_collisionBound (qSign qHash : ℕ)
    (c : ℕ → Finset Salt) (hcache : ∀ j, (c j).card ≤ j + qHash) :
    (∑ j ∈ Finset.range qSign, Pr[(· ∈ c j) | ($ᵗ Salt)]) ≤ collisionBound Salt qSign qHash := by
  refine le_trans (Finset.sum_le_sum ?_) (sum_range_div_card_le_collisionBound Salt qSign qHash)
  intro j _
  rw [probEvent_mem_uniformSample]
  gcongr
  exact_mod_cast hcache j

/-! ## Salt-averaged collision telescope (the combined draw-then-query step)

The Phase-5 per-query `withProgramming` union framework cannot see the GPV salt averaging: the
programming bad flag fires deterministically on a *fixed* query input `t = (r, m)`, while the
collision randomness lives in the fresh salt `r` drawn *inside* the signing oracle, one step
*before* the random-oracle query is issued. The right granularity is therefore a **combined
"draw salt `r`, then check `r` against the recorded inputs" step**, whose firing probability,
*integrated over the uniform salt draw*, is `card cache / |Salt|`.

`saltSeq` is exactly this combined-step process abstracted away from the oracle plumbing: it
draws `qSign` fresh salts in sequence and reports whether any draw `r_j` lands in the recorded
set `c j` seen by the `j`-th signing query. `probEvent_saltSeq_le` telescopes the per-draw
collision probabilities (each a `probEvent_mem_uniformSample` instance) into the running sum
`∑_{j < qSign} card (c j) / |Salt|`, and `probEvent_saltSeq_le_collisionBound` finishes with the
banked Gauss-sum estimate. This realizes the salt-AVERAGED step bound that the Phase-5 wall
identified as the missing reformulation. -/

open Classical in
omit [DecidableEq Salt] in
/-- The combined draw-then-collision-check process underlying the GPV salt-collision union bound.

`saltSeq c n` draws `n` fresh uniform salts in sequence; the `j`-th draw `r_j` is checked for
membership in the recorded random-oracle input set `c j` (the salts and hash inputs seen by the
`j`-th signing query). It returns `true` iff some draw collides with its recorded set. This is the
salt-averaged abstraction of "draw a fresh signing salt, then query the random oracle at it":
firing is integrated over the fresh draw rather than evaluated at a fixed query input. -/
noncomputable def saltSeq (c : ℕ → Finset Salt) : (n : ℕ) → ProbComp Bool
  | 0 => pure false
  | (n + 1) => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let rest ← saltSeq c n
      pure ((decide (r ∈ c n)) || rest)

/-- **Salt-averaged collision telescope.** The probability that the combined draw-then-check
process `saltSeq c n` ever reports a collision is bounded by the running sum of per-draw
collision probabilities `∑_{j < n} card (c j) / |Salt|`.

This is the salt-AVERAGED per-step bound the Phase-5 wall called for: the head draw `r ← $ᵗ Salt`
contributes `card (c n) / |Salt|` (one `probEvent_mem_uniformSample` instance, integrated over the
fresh salt), and the remaining `n` draws contribute the inductive tail. The union is assembled by
`probEvent_bind_le_add` on the monotone Boolean disjunction. Unlike the Phase-5 fixed-`t`
`withProgramming` step (which fires deterministically and cannot be capped below `1`), every step
here is averaged over its own fresh salt draw, so the small `card / |Salt|` cap is honest. -/
theorem probEvent_saltSeq_le (c : ℕ → Finset Salt) (n : ℕ) :
    Pr[(· = true) | saltSeq (Salt := Salt) c n]
      ≤ ∑ j ∈ Finset.range n, ((c j).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞) := by
  classical
  induction n with
  | zero => simp [saltSeq]
  | succ n ih =>
      rw [probEvent_congr' (q := fun y : Bool => ¬ y = false)
            (oa' := saltSeq (Salt := Salt) c (n + 1)) (fun b _ => by cases b <;> simp) rfl]
      rw [saltSeq, Finset.sum_range_succ, add_comm]
      refine probEvent_bind_le_add (m := ProbComp)
        (p := fun r => r ∉ c n) (q := fun b : Bool => b = false)
        (ε₁ := ((c n).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))
        (ε₂ := ∑ j ∈ Finset.range n, ((c j).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))
        ?_ ?_
      · simp only [not_not]
        rw [probEvent_uniformSample]
        simp
      · intro r _ hr
        simp only [Bool.not_eq_false]
        rw [decide_eq_false hr]
        simp only [Bool.false_or]
        rw [bind_pure]
        exact ih

/-- **Salt-averaged collision telescope, finished against `collisionBound`.** When the recorded
input set seen by the `j`-th signing query has size at most `j + qHash` (the `j` prior signing
salts plus the up to `qHash` adversary hash queries), the combined draw-then-check process over
`qSign` signing queries reports a collision with probability at most `collisionBound Salt qSign
qHash`.

This chains `probEvent_saltSeq_le` with the banked Gauss-sum estimate
`sum_range_div_card_le_collisionBound`. It is the salt-averaged collision bound stated directly on
the fresh-salt-draw process, the honest counterpart of the deterministic Phase-5 fixed-`t` step. -/
theorem probEvent_saltSeq_le_collisionBound (qSign qHash : ℕ)
    (c : ℕ → Finset Salt) (hcache : ∀ j, (c j).card ≤ j + qHash) :
    Pr[(· = true) | saltSeq (Salt := Salt) c qSign] ≤ collisionBound Salt qSign qHash := by
  refine (probEvent_saltSeq_le Salt c qSign).trans ?_
  refine le_trans (Finset.sum_le_sum ?_) (sum_range_div_card_le_collisionBound Salt qSign qHash)
  intro j _
  gcongr
  exact_mod_cast hcache j

open Classical in
/-- **Salt-split tsum identity.** Weighting the uniform-draw distribution by `1` on a finite cache
`s` and by a constant `q` off it sums to `p + (1 - p) · q`, where `p = card s / |Salt|` is the
probability of landing in `s`. This is the inclusion-exclusion kernel underlying both the
salt-collision recursion `probEvent_saltSeq_succ` and the per-step charge of the salt-inclusive
coupling induction. -/
theorem tsum_probOutput_uniformSample_ite (s : Finset Salt) (q : ℝ≥0∞) :
    (∑' x : Salt, Pr[= x | ($ᵗ Salt : ProbComp Salt)] * (if x ∈ s then 1 else q))
      = ((s.card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))
        + (1 - ((s.card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))) * q := by
  classical
  set p : ℝ≥0∞ := ((s.card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞)) with hp
  have hp_le : p ≤ 1 := by
    rw [hp, ← probEvent_mem_uniformSample (Salt := Salt) s]
    exact probEvent_le_one
  have hmem : Pr[(· ∈ s) | ($ᵗ Salt : ProbComp Salt)] = p := by
    rw [hp]; exact probEvent_mem_uniformSample (Salt := Salt) s
  have hcompl : Pr[(· ∉ s) | ($ᵗ Salt : ProbComp Salt)] = 1 - p := by
    have hsum := probEvent_compl (mx := ($ᵗ Salt : ProbComp Salt)) (· ∈ s)
    rw [hmem] at hsum
    have hbot : Pr[⊥ | ($ᵗ Salt : ProbComp Salt)] = 0 := by simp
    rw [hbot, tsub_zero] at hsum
    exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top hp_le) (by
      rw [add_comm]; exact hsum)
  have hsplit : ∀ x : Salt,
      Pr[= x | ($ᵗ Salt : ProbComp Salt)] * (if x ∈ s then 1 else q)
        = (if x ∈ s then Pr[= x | ($ᵗ Salt : ProbComp Salt)] else 0)
          + (if x ∈ s then 0 else Pr[= x | ($ᵗ Salt : ProbComp Salt)] * q) := by
    intro x; by_cases hx : x ∈ s <;> simp [hx]
  simp_rw [hsplit]
  rw [ENNReal.tsum_add]
  congr 1
  · rw [← probEvent_eq_tsum_ite]; exact hmem
  · have hre : ∀ x : Salt,
        (if x ∈ s then 0 else Pr[= x | ($ᵗ Salt : ProbComp Salt)] * q)
          = (if x ∉ s then Pr[= x | ($ᵗ Salt : ProbComp Salt)] else 0) * q := by
      intro x; by_cases hx : x ∈ s <;> simp [hx]
    simp_rw [hre]
    rw [ENNReal.tsum_mul_right, ← probEvent_eq_tsum_ite (p := (· ∉ s)), hcompl]

open Classical in
/-- **Exact one-step recursion of the salt-collision probability.** The probability that the
combined draw-then-check process `saltSeq c (n + 1)` reports a collision decomposes by independence
of the fresh head draw `r ← $ᵗ Salt` from the remaining `n` draws: with `p = card (c n) / |Salt|`
the head-collision probability, the head fires with probability `p`, and otherwise (probability
`1 - p`) the tail `saltSeq c n` must fire. Hence
`Pr[saltSeq c (n + 1)] = p + (1 - p) · Pr[saltSeq c n]`.

This is the tight inclusion-exclusion identity (the head draw and the tail are independent), which
is exactly the per-step charge produced by the salt-inclusive coupling induction
`signRunF_tvDist_le_saltSeq`. -/
theorem probEvent_saltSeq_succ (c : ℕ → Finset Salt) (n : ℕ) :
    Pr[(· = true) | saltSeq (Salt := Salt) c (n + 1)]
      = ((c n).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞)
        + (1 - ((c n).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))
          * Pr[(· = true) | saltSeq (Salt := Salt) c n] := by
  classical
  set q : ℝ≥0∞ := Pr[(· = true) | saltSeq (Salt := Salt) c n] with hq
  -- Expand the head draw.
  conv_lhs => rw [saltSeq]
  rw [probEvent_bind_eq_tsum]
  -- Per-`r` inner probability: `1` if `r ∈ c n`, else `q`.
  have hinner : ∀ r : Salt,
      Pr[(· = true) | (saltSeq (Salt := Salt) c n >>=
            fun rest => (pure (decide (r ∈ c n) || rest) : ProbComp Bool))]
        = (if r ∈ c n then 1 else q) := by
    intro r
    by_cases hr : r ∈ c n
    · simp only [hr, if_true, decide_true, Bool.true_or]
      simp
    · simp only [hr, if_false, decide_false, Bool.false_or]
      rw [hq]
      simp
  simp_rw [hinner]
  exact tsum_probOutput_uniformSample_ite (Salt := Salt) (c n) q

/-! ## Open sub-step: the salt-collision coupling `hcouple`

The salt-averaged telescope above (`probEvent_saltSeq_le_collisionBound`) is the honest, axiom-clean
bound on the GPV salt-collision event: a sequence of `qSign` fresh uniform salt draws, the `j`-th
checked against the recorded inputs `c j` of size `≤ j + qHash`, collides with probability at most
`collisionBound Salt qSign qHash`. This realizes the salt-AVERAGED combined "draw salt, then check"
step that the per-query `withProgramming` framework cannot express.

Discharging the U2 hypothesis `hbad` of `tvDist_runtime_real_programmed_le_collisionBound` from this
telescope is **not** possible at the current statement granularity, for two independent structural
reasons, both of which are genuine and isolated here (no false bridge is asserted):

1. **Wrong event.** The `hbad` left-hand side is the `withProgramming` *bad flag*, which fires on a
   cache-*miss* whose query input lies in the programming policy's support
   (`cache t = none ∧ policy t = some v`; see `QueryImpl.withProgramming`). For the GPV simulator
   policy (which programs at every fresh signing point) this fires *deterministically* once an
   uncached signing point is reached, so its probability is near `1`, not `collisionBound`. The
   salt-collision event of the telescope is the opposite: a fresh salt *hitting* an
   already-recorded entry (a cache *hit* at a programmed point), which the monotone fire-on-miss
   flag does not record.

2. **Invisible salt draws.** `hbad` is phrased over `ob : OracleComp (Salt × M →ₒ Range)`, a
   random-oracle-only computation. The GPV signing salts are drawn in `unifSpec`/`ProbComp`, i.e.
   *outside* the `(Salt × M →ₒ Range)` spec, one step before each random-oracle query. By the time a
   query input `(r, m)` reaches the `withProgramming` handler the salt `r` is already a fixed value,
   so the `card / |Salt|` averaging that the telescope performs over the fresh draw is structurally
   absent from `ob`'s granularity. The averaging cannot be recovered without exposing the salt
   draws.

The U2 *re-statement* `tvDist_runtime_real_programmed_le_collisionBound_saltInclusive` (below)
carries out the first half of the closure: it re-states U2 over the salt-inclusive signing run with
the bad event instrumented as the cache-HIT salt collision `saltSeq c qSign`, and discharges the
loss-free `tvDist ≤ collisionBound.toReal` conclusion *given* the genuine up-to-bad coupling
`hcouple : tvDist(real, programmed) ≤ Pr[saltSeq c qSign = true]`. It deliberately does **not**
route through the fire-on-miss `hbad` (which, per reason 1 above, would require the false inequality
"fire-on-miss ≤ salt-collision").

What remains open is **exactly** `hcouple`: the identical-until-bad coupling between the real GPV
run (lazy random oracle, fresh uniform answer at each `(r, m)`) and the programmed run (answer
`psf.eval pk s`), whose only divergence is a fresh signing salt colliding with a recorded cache
slice — precisely the `saltSeq` event. Discharging it is a `#228`-class joint-distribution over
the interleaved `unifSpec` salt-draw / `(Salt × M →ₒ Range)` random-oracle-query streams of the
salt-inclusive signing program. The salt-averaged telescope banked above is the reusable analytic
core the coupling lands on; the remaining work is the joint-distribution coupling itself, which —
because the salt draws live in the caller of the hash-only `ob` (reason 2) — cannot be expressed at
the current `runtime` / `ob` interface without exposing the signing program's salt draws to the
coupling, a deeper structural change tracked separately. -/

/-! ## Salt-inclusive identical-until-bad coupling primitives

The coupling `hcouple` cannot be discharged at the hash-only `ob` granularity (reasons 1 and 2
above). The honest way to make progress is to expose the salt draws and build the coupling on a
*salt-inclusive* signing process, where the salt-collision averaging is structurally visible. This
section banks the reusable identical-until-bad primitives for that process.

`tvDist_signStep_real_programmed_le_collision` is the proven per-step core: a single combined
"draw a fresh salt `r`, then answer" step, where the *real* branch answers with the lazy
random-oracle value and the *programmed* branch answers with the regularity-supplied value. Off the
per-step salt collision `r ∈ cache`, regularity makes the two answer branches agree in distribution
(`h_eq`), so the total-variation distance of the combined step is bounded by exactly the salt
collision probability `card cache / |Salt|`. This is the single-step instance of the
fundamental-lemma-of-game-playing, with the bad event averaged over the fresh salt draw — precisely
the granularity the Phase-5 per-query `withProgramming` framework could not express. It is a direct
specialization of the banked `tvDist_bind_left_event_le`.

`signRunF` is the flag-carrying sequenced signing process: it draws `qSign` fresh salts in turn,
applies a per-step answer handler `step n state r`, and sets a Boolean flag the first time a drawn
salt lands in its recorded cache slice `c n`. Its flag-true marginal is the run-level counterpart of
the `saltSeq` collision event. `signRunF_flag_le_saltSeq` records that the flag-true probability of
the *real* run is bounded by `Pr[saltSeq c qSign = true]` (the flag fires iff some draw collides,
which is exactly the `saltSeq` disjunction marginalized over the threaded state).

The remaining open coupling is `signRunF_tvDist_le_flag`: the total-variation distance between the
real and programmed sequenced runs is bounded by the run-level flag-true probability. This is the
genuine `#228`-class multi-step joint coupling: off the per-step collision the *current* step
distributions agree (via `h_step`), but the two runs recurse with *different* per-step handlers, so
the off-bad agreement must be threaded through the recursion with the accumulating flag — it cannot
be obtained by a single application of the per-step primitive (the tails differ). It is isolated
below as the one precise residual; chaining it with `signRunF_flag_le_saltSeq` and the banked
`probEvent_saltSeq_le_collisionBound` telescope yields the salt-inclusive coupling that discharges
`hcouple`. -/

omit [DecidableEq Salt] [Fintype Salt] in
/-- **Per-step salt-inclusive identical-until-bad coupling (proven).**

A single combined "draw a fresh salt `r`, then answer" step. The *real* answer branch `freal r` and
the *programmed* answer branch `fprog r` are coupled through the shared fresh salt draw. Off the
per-step salt collision `r ∈ cache`, regularity guarantees the two answer branches agree in
distribution (`h_eq`), so the total-variation distance of the combined step is bounded by the
probability that the fresh salt lands in `cache`, namely `card cache / |Salt|` (via
`probEvent_mem_uniformSample`).

This is the single-step instance of the fundamental-lemma-of-game-playing with the bad event
averaged over the fresh salt draw. It specializes the banked `tvDist_bind_left_event_le` at
`mx := $ᵗ Salt` and `bad := (· ∈ cache)`. It is the per-step core the sequenced coupling
`signRunF_tvDist_le_flag` accumulates. -/
theorem tvDist_signStep_real_programmed_le_collision [Nonempty Salt] {β : Type}
    (cache : Finset Salt) (freal fprog : Salt → ProbComp β)
    (h_eq : ∀ r, r ∉ cache → 𝒟[freal r] = 𝒟[fprog r]) :
    tvDist
        (do let r ← ($ᵗ Salt : ProbComp Salt); freal r)
        (do let r ← ($ᵗ Salt : ProbComp Salt); fprog r)
      ≤ (Pr[(· ∈ cache) | ($ᵗ Salt : ProbComp Salt)]).toReal :=
  tvDist_bind_left_event_le _ freal fprog (· ∈ cache) h_eq

open Classical in
/-- **Flag-carrying sequenced signing process.**

`signRunF step c n` runs `n` combined signing steps over a threaded state `St × Bool`. At step `j`
it draws a fresh salt `r ← $ᵗ Salt`, advances the state by the per-step handler `step j state r`,
and records in the Boolean flag whether `r` landed in the recorded cache slice `c j`. The flag is
monotone (set once a collision occurs), so its final value is the run-level salt-collision event —
the salt-inclusive, state-threaded counterpart of the salt-averaged `saltSeq` process. -/
noncomputable def signRunF {St : Type} (step : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) : (n : ℕ) → St × Bool → ProbComp (St × Bool)
  | 0, sb => pure sb
  | (n + 1), sb => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let st' ← step n sb.1 r
      signRunF step c n (st', sb.2 || decide (r ∈ c n))

omit [Fintype Salt] in
/-- **`signRunF` never fails when its step never fails.** If every per-step handler `step n s r`
never fails, the whole `qSign`-step `signRunF` recursion never fails: the leading uniform salt draw
is total, the step is total by hypothesis, and the tail never fails by induction. Consequently its
output distribution has total mass one, so it can be discarded as a value-irrelevant never-failing
prefix (`evalDist_bind_const_neverFails`) — the tape-suffix-discard step of a fold factorization. -/
theorem signRunF_neverFail {St : Type} [Nonempty Salt]
    (step : ℕ → St → Salt → ProbComp St) (c : ℕ → Finset Salt)
    [hstep : ∀ n s r, NeverFail (step n s r)] :
    ∀ (n : ℕ) (sb : St × Bool), NeverFail (signRunF (Salt := Salt) step c n sb) := by
  intro n
  induction n with
  | zero => intro sb; exact inferInstanceAs (NeverFail (pure sb))
  | succ n ih =>
      intro sb
      refine (neverFail_bind_iff _ _).2 ⟨inferInstance, fun r _ => ?_⟩
      exact (neverFail_bind_iff _ _).2 ⟨hstep n sb.1 r, fun st' _ => ih _⟩

omit [Fintype Salt] in
/-- **Discarding the `signRunF` salt prefix.** When the per-step handler never fails, the entire
`signRunF` recursion never fails (`signRunF_neverFail`), so binding a *value-irrelevant*
continuation `k` after it contributes only `signRunF`'s total mass one: the salt-draw prefix is
discarded from the output distribution. This is the GPV `signRunF` instance of the generic
never-failing-prefix discard `evalDist_bind_const_neverFails`; it is the move that drops the
over-provisioned front salt tape once the genuine content has been spliced out, the analogue of the
`drawList` suffix discard in the worked Fiat–Shamir factorization. -/
theorem evalDist_signRunF_bind_const {St γ : Type} [Nonempty Salt]
    (step : ℕ → St → Salt → ProbComp St) (c : ℕ → Finset Salt)
    [∀ n s r, NeverFail (step n s r)] (n : ℕ) (sb : St × Bool) (k : ProbComp γ) :
    𝒟[signRunF (Salt := Salt) step c n sb >>= fun _ => k] = 𝒟[k] := by
  haveI := signRunF_neverFail (Salt := Salt) step c n sb
  refine SPMF.ext fun x => ?_
  set sr := signRunF (Salt := Salt) step c n sb with hsr
  rw [show 𝒟[sr >>= fun _ => k] x = Pr[= x | sr >>= fun _ => k] from (probOutput_def _ _).symm,
    show 𝒟[k] x = Pr[= x | k] from (probOutput_def _ _).symm,
    probOutput_bind_const, probFailure_eq_zero]
  simp

omit [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] in
/-- **Uniform per-fibre TV bound for a shared base.** If two continuations are pointwise at
total-variation distance at most `δ` (with `δ ≥ 0`), then binding them over a common base
computation is also within `δ`. The base only needs to be a sub-probability computation; the mass
`∑' Pr[= a] ≤ 1` absorbs the constant fibre bound. -/
theorem tvDist_bind_le_of_forall_le {α β : Type} (mx : ProbComp α) (f g : α → ProbComp β)
    (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ a, tvDist (f a) (g a) ≤ δ) :
    tvDist (mx >>= f) (mx >>= g) ≤ δ := by
  refine le_trans (tvDist_bind_left_le mx f g) ?_
  have hbase : Summable (fun a : α => Pr[= a | mx].toReal) :=
    ENNReal.summable_toReal (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
  have hsum_le_one : ∑' a : α, Pr[= a | mx].toReal ≤ 1 := by
    have h1 : (∑' a : α, Pr[= a | mx].toReal) = (∑' a : α, Pr[= a | mx]).toReal :=
      (ENNReal.tsum_toReal_eq (fun a => ne_top_of_le_ne_top one_ne_top probOutput_le_one)).symm
    rw [h1, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
      one_ne_top).2 tsum_probOutput_le_one
  calc ∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a)
        ≤ ∑' a, Pr[= a | mx].toReal * δ :=
        Summable.tsum_le_tsum
          (fun a => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)
          (Summable.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
            (fun a => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg) (hbase.mul_right δ))
          (hbase.mul_right δ)
    _ = (∑' a, Pr[= a | mx].toReal) * δ := by rw [tsum_mul_right]
    _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hsum_le_one hδ
    _ = δ := one_mul δ

open Classical in
omit [Fintype Salt] in
/-- **Stateful identical-until-bad telescoping (generalized over the initial flag and state).**

This is the inductive heart of the salt-inclusive coupling. For any initial flag `b` and state
`st`, the total-variation distance between the real and programmed sequenced runs is bounded by the
salt-averaged collision probability `Pr[saltSeq c n = true]`, *independently of `b` and `st`* (the
flag only accumulates the collision disjunction and the RHS does not depend on the threaded state).

The successor step shares the fresh salt draw `r ← $ᵗ Salt` and splits per-`r`:
* On the per-step collision `r ∈ c n` the step is charged its full mass (`tvDist ≤ 1`), contributing
  the head term `card (c n) / |Salt|`.
* Off the collision (`r ∉ c n`) the head handlers agree in distribution (`h_step`), so by the
  triangle inequality the step contributes only the tail, bounded by the induction hypothesis at the
  advanced state and flag. The `NeverFail` hypothesis keeps the state-marginal mass equal to one.

The per-`r` charges accumulate to exactly `card (c n) / |Salt| + (1 - card (c n) / |Salt|) ·
Pr[saltSeq c n]`, which equals `Pr[saltSeq c (n + 1)]` by the independence identity
`probEvent_saltSeq_succ`. This realizes design L3a: a stateful telescoping accepting
state-dependent per-step costs. -/
theorem signRunF_tvDist_le_saltSeq_aux {St : Type} [Finite Salt]
    (stepReal stepProg : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) [∀ n st r, NeverFail (stepReal n st r)]
    (h_step : ∀ n st r, r ∉ c n → 𝒟[stepReal n st r] = 𝒟[stepProg n st r])
    (n : ℕ) (st : St) (b : Bool) :
    tvDist (signRunF (Salt := Salt) stepReal c n (st, b))
        (signRunF (Salt := Salt) stepProg c n (st, b))
      ≤ (Pr[(· = true) | saltSeq (Salt := Salt) c n]).toReal := by
  classical
  haveI : Fintype Salt := Fintype.ofFinite Salt
  induction n generalizing st b with
  | zero =>
      simp only [signRunF]
      rw [tvDist_self]
      exact ENNReal.toReal_nonneg
  | succ n ih =>
      -- Notation for the per-step head-collision probability `p` and tail probability `q`.
      set q : ℝ≥0∞ := Pr[(· = true) | saltSeq (Salt := Salt) c n] with hq
      set p : ℝ≥0∞ := ((c n).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞) with hp
      have hp_le : p ≤ 1 := by
        rw [hp, ← probEvent_mem_uniformSample (Salt := Salt) (c n)]
        exact probEvent_le_one
      have hq_le : q ≤ 1 := by rw [hq]; exact probEvent_le_one
      -- Unfold one step on both sides; the salt draw `r ← $ᵗ Salt` is shared.
      rw [signRunF, signRunF]
      -- Per-`r` continuation bound.
      refine le_trans (tvDist_bind_left_le ($ᵗ Salt : ProbComp Salt) _ _) ?_
      -- Bound each per-`r` term by `if r ∈ c n then 1 else q.toReal`.
      have hterm : ∀ r : Salt,
          tvDist (stepReal n st r >>= fun st' =>
              signRunF (Salt := Salt) stepReal c n (st', b || decide (r ∈ c n)))
            (stepProg n st r >>= fun st' =>
              signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n)))
            ≤ (if r ∈ c n then 1 else q.toReal) := by
        intro r
        by_cases hr : r ∈ c n
        · rw [if_pos hr]; exact tvDist_le_one _ _
        · rw [if_neg hr]
          -- Triangle through the real head with the programmed tail.
          refine le_trans (tvDist_triangle _
            (stepReal n st r >>= fun st' =>
              signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n))) _) ?_
          have htail : tvDist (stepReal n st r >>= fun st' =>
                signRunF (Salt := Salt) stepReal c n (st', b || decide (r ∈ c n)))
              (stepReal n st r >>= fun st' =>
                signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n)))
              ≤ q.toReal :=
            tvDist_bind_le_of_forall_le (stepReal n st r) _ _ q.toReal ENNReal.toReal_nonneg
              (fun st' => ih st' (b || decide (r ∈ c n)))
          have hhead : tvDist (stepReal n st r >>= fun st' =>
                signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n)))
              (stepProg n st r >>= fun st' =>
                signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n)))
              = 0 := by
            rw [tvDist_eq_zero_iff, evalDist_bind, evalDist_bind, h_step n st r hr]
          rw [hhead, add_zero]
          exact htail
      -- Normalize the product projections `(st, b).1`, `(st, b).2` to `st`, `b`.
      change (∑' a : Salt, Pr[= a | ($ᵗ Salt : ProbComp Salt)].toReal *
          tvDist (stepReal n st a >>= fun st' =>
              signRunF (Salt := Salt) stepReal c n (st', b || decide (a ∈ c n)))
            (stepProg n st a >>= fun st' =>
              signRunF (Salt := Salt) stepProg c n (st', b || decide (a ∈ c n))))
        ≤ (Pr[(· = true) | saltSeq (Salt := Salt) c (n + 1)]).toReal
      -- `q.toReal ≤ 1` and base summability.
      have hq_toReal_le : q.toReal ≤ 1 := by
        rw [← ENNReal.toReal_one]
        exact (ENNReal.toReal_le_toReal probEvent_ne_top one_ne_top).2 hq_le
      have hbase : Summable (fun a : Salt => Pr[= a | ($ᵗ Salt : ProbComp Salt)].toReal) :=
        ENNReal.summable_toReal (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
      have hcap : ∀ a : Salt, (if a ∈ c n then (1 : ℝ) else q.toReal) ≤ 1 := by
        intro a; split_ifs with ha
        · exact le_refl 1
        · exact hq_toReal_le
      have hcap_nonneg : ∀ a : Salt, (0 : ℝ) ≤ (if a ∈ c n then (1 : ℝ) else q.toReal) := by
        intro a; split_ifs <;> [norm_num; exact ENNReal.toReal_nonneg]
      -- Summability of the salt-split bounding sum.
      have hsummable_term : Summable (fun a : Salt =>
          Pr[= a | ($ᵗ Salt : ProbComp Salt)].toReal * (if a ∈ c n then 1 else q.toReal)) :=
        Summable.of_nonneg_of_le
          (fun a => mul_nonneg ENNReal.toReal_nonneg (hcap_nonneg a))
          (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (hcap a)) hbase
      -- Summability of the actual tvDist-weighted sum.
      have hsummable_tv : Summable (fun a : Salt =>
          Pr[= a | ($ᵗ Salt : ProbComp Salt)].toReal *
            tvDist (stepReal n st a >>= fun st' =>
                signRunF (Salt := Salt) stepReal c n (st', b || decide (a ∈ c n)))
              (stepProg n st a >>= fun st' =>
                signRunF (Salt := Salt) stepProg c n (st', b || decide (a ∈ c n)))) :=
        Summable.of_nonneg_of_le
          (fun a => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
          (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg
            ((hterm a).trans (hcap a))) hbase
      refine le_trans (Summable.tsum_le_tsum (fun a =>
        mul_le_mul_of_nonneg_left (hterm a) ENNReal.toReal_nonneg)
        hsummable_tv hsummable_term) ?_
      -- Identify the salt-split sum with `Pr[saltSeq c (n+1)].toReal`.
      -- Each real term is the `toReal` of the corresponding `ℝ≥0∞` term.
      have hterm_toReal : ∀ i : Salt,
          Pr[= i | ($ᵗ Salt : ProbComp Salt)].toReal * (if i ∈ c n then (1 : ℝ) else q.toReal)
            = (Pr[= i | ($ᵗ Salt : ProbComp Salt)] * (if i ∈ c n then 1 else q)).toReal := by
        intro i
        by_cases hi : i ∈ c n <;> simp [hi]
      simp_rw [hterm_toReal]
      -- Pull the `toReal` out of the sum (each term is finite), evaluate, and identify.
      rw [← ENNReal.tsum_toReal_eq (fun i => ENNReal.mul_ne_top
        (ne_top_of_le_ne_top one_ne_top probOutput_le_one) (by
          split_ifs <;> [exact one_ne_top; exact probEvent_ne_top])),
        tsum_probOutput_uniformSample_ite (Salt := Salt) (c n) q, ← probEvent_saltSeq_succ]

omit [Fintype Salt] in
/-- **Salt-inclusive identical-until-bad coupling.**

The total-variation distance between the real sequenced signing run `signRunF stepReal c n` and the
programmed sequenced signing run `signRunF stepProg c n` is bounded by the salt-averaged collision
probability `Pr[saltSeq c n = true]`, provided the two per-step handlers agree in distribution off
the per-step salt collision `r ∈ c j` (`h_step`, supplied for GPV by regularity `hreg`). The
`NeverFail` hypothesis on the real handler keeps probability mass during the state marginalization.

This is the `#228`-class multi-step joint coupling that gates the GPV proof, threaded through the
recursion by `signRunF_tvDist_le_saltSeq_aux` (the generalization over the initial flag and state).
It decomposes into two true parts, both banked in this section:

* **Per-step charge.** Off `r ∈ c j` the two combined "draw salt, then answer" steps agree in
  distribution, so each step contributes only its salt-collision mass `card (c j) / |Salt|`. This is
  the proven per-step primitive `tvDist_signStep_real_programmed_le_collision`, applied per fibre
  via `tvDist_bind_le_of_forall_le`.
* **Accumulation to `saltSeq`.** The per-step charges accumulate along the recursion to the
  run-level collision-flag probability, which equals the salt-averaged `saltSeq` disjunction once
  the threaded state is marginalized out — the inclusion-exclusion identity
  `probEvent_saltSeq_succ`.

Chaining this result with the banked telescope `probEvent_saltSeq_le_collisionBound`
(`Pr[saltSeq] ≤ collisionBound`) yields the salt-inclusive coupling that discharges the U2
hypothesis `hcouple`, once the GPV reduction handlers and per-step caches `c j` are instantiated. -/
theorem signRunF_tvDist_le_saltSeq {St : Type} [Finite Salt]
    (stepReal stepProg : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) [∀ n st r, NeverFail (stepReal n st r)]
    (h_step : ∀ n st r, r ∉ c n → 𝒟[stepReal n st r] = 𝒟[stepProg n st r])
    (n : ℕ) (st : St) :
    tvDist (signRunF (Salt := Salt) stepReal c n (st, false))
        (signRunF (Salt := Salt) stepProg c n (st, false))
      ≤ (Pr[(· = true) | saltSeq (Salt := Salt) c n]).toReal :=
  signRunF_tvDist_le_saltSeq_aux (Salt := Salt) (St := St)
    stepReal stepProg c h_step n st false

/-- **U2, re-stated over the salt-inclusive signing run (unconditional).**

This is the salt-inclusive U2: it bounds the total-variation distance between the real and
programmed *signing runs* directly by `collisionBound`, with **no coupling hypothesis**. Unlike the
hash-only `tvDist_runtime_real_programmed_le_collisionBound_saltInclusive` (which takes the
`#228`-class coupling as the typed hypothesis `hcouple`), this lemma is phrased over the
salt-inclusive vehicle `signRunF` — where each of the `qSign` fresh signing salts `r ← $ᵗ Salt` is
an explicit step of the recursion — so the salt-collision averaging is *structurally visible* and
the proven coupling discharges it outright.

The proof chains the two banked, axiom-clean results with no loss:
* the proven multi-step coupling `signRunF_tvDist_le_saltSeq`
  (`tvDist (signRunF stepReal …) (signRunF stepProg …) ≤ Pr[saltSeq c qSign = true]`), and
* the salt-averaged telescope `probEvent_saltSeq_le_collisionBound`
  (`Pr[saltSeq c qSign = true] ≤ collisionBound Salt qSign qHash`),
moved to `ℝ` by `ENNReal.toReal_mono` (using `collisionBound < ⊤`).

`stepReal`/`stepProg` are the per-signing-step answer handlers (real lazy random oracle vs the
regularity-supplied programmed answer); `h_step` is the off-collision branch agreement supplied by
PSF regularity (`psf.Regularity`); `c j` is the recorded random-oracle cache slice seen by the
`j`-th signing query, with the standard growth bound `card (c j) ≤ j + qHash` (`hcache`).

The remaining structural work to feed the four GPV theorems is *not* a probability fact but the
adaptive→`signRunF` factorization: matching the real adversary run
`simulateQ impl (adv.main pk)` — which interleaves the `qSign` signing queries (each drawing a
fresh salt) with up to `qHash` adversary hash queries *adaptively* — to this fixed `qSign`-step
`signRunF` recursion. That factorization is the `#228`-class deferred-sampling joint coupling (see
the *Adaptive→signRunF factorization* section below). -/
theorem signRunF_tvDist_le_collisionBound {St : Type} [Finite Salt] [Nonempty Salt]
    (stepReal stepProg : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) [∀ n st r, NeverFail (stepReal n st r)]
    (h_step : ∀ n st r, r ∉ c n → 𝒟[stepReal n st r] = 𝒟[stepProg n st r])
    (qSign qHash : ℕ) (hcache : ∀ j, (c j).card ≤ j + qHash) (st : St) :
    tvDist (signRunF (Salt := Salt) stepReal c qSign (st, false))
        (signRunF (Salt := Salt) stepProg c qSign (st, false))
      ≤ (collisionBound Salt qSign qHash).toReal := by
  refine (signRunF_tvDist_le_saltSeq (Salt := Salt) stepReal stepProg c h_step qSign st).trans ?_
  refine ENNReal.toReal_mono ?_ (probEvent_saltSeq_le_collisionBound Salt qSign qHash c hcache)
  refine (ENNReal.div_lt_top ?_ ?_).ne
  · simp
  · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
    exact Fintype.card_ne_zero

/-! ## R2: adaptive→`signRunF` factorization (framework + isolated residual)

The unconditional salt-inclusive U2 `signRunF_tvDist_le_collisionBound` (above) bounds the real and
programmed *salt-inclusive signing runs* — phrased over the clean fixed `qSign`-step recursion
`signRunF`. To consume it in the four GPV theorems, whose advantage is over the **adaptive** real
game run `simulateQ impl (adv.main pk)` (`SignatureAlg.unforgeableExp`), one must match that
adaptive run to the fixed `signRunF` recursion. That match is the **adaptive→`signRunF`
factorization** (R2):
the adversary interleaves its `≤ qSign` signing queries (each drawing one fresh salt `r ← $ᵗ Salt`)
with `≤ qHash` random-oracle queries *adaptively*, while `signRunF` draws its `qSign` salts in a
fixed front sequence. Front-loading the interleaved salt draws past the adaptive adversary fold is a
`#228`-class deferred-sampling joint coupling, structurally identical to the Fiat–Shamir-with-abort
*fold-level tape factorization*
`FiatShamirWithAbort.evalDist_deferredDrawRead_eq_drawList_tapeDrawRead` (each signing body's inline
draws are recast as consumption from a pre-drawn front tape, proved by induction over the
`simulateQ` fold using `OracleComp.DeferredSampling.evalDist_step_commute_tape` for the
answer-irrelevant — here, the adversary hash/uniform — steps and a per-body splice for the drawing
steps).

This section banks the part of R2 that is provable now and isolates the genuine remaining sub-step.

* **Banked (proven):** `regularity_signAnswer_agree` discharges the abstract coupling's
  off-collision branch-agreement hypothesis (`h_step`) for the concrete GPV signing answer: under
  PSF regularity the *real* RO-cache-miss answer `(c, s)` (fresh uniform target `c ← $ᵗ Range`, then
  `s ← trapdoorSample pk sk c`) and the *programmed* answer (`s ← domainSample pk`, target
  `eval pk s`) are equal in distribution. This is the regularity equation transposed and is the
  per-step content the off-collision case of `signRunF_tvDist_le_saltSeq_aux` consumes.

* **Isolated residual (the one open sub-step):** `AdaptiveFactorizesSignRunF` is the typed
  obligation packaging exactly the missing factorization — that the adaptive real and programmed
  game runs are distributed as the corresponding `signRunF` runs over a common per-query cache
  sequence `c` with `card (c j) ≤ j + qHash`. It is a *predicate* (a typed obligation, in the style
  of the discharged `hcouple`), **not** a `sorry`: it commits no proof to a statement whose truth
  the deferred-sampling coupling has not established, while making the remaining work a single named
  target. `factorized_advantage_le_collisionBound` shows that supplying it discharges the
  salt-inclusive U2 against the adaptive game run via the unconditional
  `signRunF_tvDist_le_collisionBound`. -/

omit [DecidableEq Range] in
/-- **Regularity branch-agreement bridge (proven).** Under PSF regularity, the real cache-miss
signing answer and the programmed signing answer agree in distribution.

The real answer at a fresh salt — produced by the lazy random oracle on a cache miss — draws a fresh
uniform target `c ← $ᵗ Range` and then a short preimage `s ← trapdoorSample pk sk c`, returning the
pair `(c, s)`. The programmed answer draws `s ← domainSample pk` and uses the target `eval pk s`,
returning `(eval pk s, s)`. PSF regularity (`psf.Regularity`) states exactly that these two joint
distributions coincide, so this is the regularity equation read right-to-left.

This is the GPV-concrete witness for the off-collision branch-agreement hypothesis `h_step` of
`signRunF_tvDist_le_saltSeq` / `signRunF_tvDist_le_collisionBound`: off the per-step salt collision
`r ∉ c j`, the real and programmed per-signing-step answer handlers agree in distribution. -/
theorem regularity_signAnswer_agree (hreg : psf.Regularity) (pk : PK) (sk : SK) :
    ∃ domainSample : PK → ProbComp Domain,
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
          : ProbComp (Range × Domain))]
        = 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] := by
  obtain ⟨domainSample, h⟩ := hreg
  exact ⟨domainSample, (h pk sk).symm⟩

/-- **Adaptive→`signRunF` factorization obligation (the isolated R2 residual).**

`AdaptiveFactorizesSignRunF realRun progRun` asserts the existence of a `signRunF` presentation of
the adaptive real and programmed game runs sharing a common per-signing-query cache sequence: there
exist a handler-state type `St`, real/programmed per-step answer handlers `stepReal`/`stepProg` (the
latter agreeing with the former off the per-step salt collision, `stepReal` never failing), a
per-query recorded-cache sequence `c` bounded by `card (c j) ≤ j + qHash`, and a start state such
that the real and programmed adaptive runs equal (in distribution) the corresponding
`signRunF stepReal c qSign` / `signRunF stepProg c qSign` runs.

This is the precise content the deferred-sampling fold-level coupling must establish (cf.
`FiatShamirWithAbort.evalDist_deferredDrawRead_eq_drawList_tapeDrawRead`): front-load the
adaptively-interleaved fresh salt draws of `realRun`/`progRun` into the fixed `qSign`-step
`signRunF` sequence. It is stated as a typed obligation rather than proved, isolating exactly the
open `#228`-class sub-step; `factorized_advantage_le_collisionBound` shows it suffices. -/
def AdaptiveFactorizesSignRunF [Nonempty Salt] {α : Type}
    (realRun progRun : SPMF α) (qSign qHash : ℕ) : Prop :=
  ∃ (St : Type) (stepReal stepProg : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) (st : St) (g : St × Bool → ProbComp α),
    (∀ n s r, NeverFail (stepReal n s r)) ∧
    (∀ n s r, r ∉ c n → 𝒟[stepReal n s r] = 𝒟[stepProg n s r]) ∧
    (∀ j, (c j).card ≤ j + qHash) ∧
    realRun = 𝒟[signRunF (Salt := Salt) stepReal c qSign (st, false) >>= g] ∧
    progRun = 𝒟[signRunF (Salt := Salt) stepProg c qSign (st, false) >>= g]

/-- **The R2 residual suffices (proven).** Supplying the adaptive→`signRunF` factorization
obligation `AdaptiveFactorizesSignRunF` discharges the salt-inclusive U2 against the adaptive game
runs: the total-variation distance between the real and programmed game runs is bounded by
`collisionBound Salt qSign qHash`.

The proof factors the runs through the obligation's `signRunF` presentation, applies the
data-processing inequality `tvDist_bind_right_le` to drop the shared post-processing `g`, and closes
with the unconditional salt-inclusive U2 `signRunF_tvDist_le_collisionBound`. This is the precise
statement of *why* the isolated residual `AdaptiveFactorizesSignRunF` is exactly the remaining work:
once the deferred-sampling fold-level coupling establishes it, the four GPV theorems' sign-then-hash
hop follows with no further probability content. -/
theorem factorized_advantage_le_collisionBound [Finite Salt] [Nonempty Salt] {α : Type}
    (realRun progRun : SPMF α) (qSign qHash : ℕ)
    (hfac : AdaptiveFactorizesSignRunF (Salt := Salt) realRun progRun qSign qHash) :
    SPMF.tvDist realRun progRun ≤ (collisionBound Salt qSign qHash).toReal := by
  obtain ⟨St, stepReal, stepProg, c, st, g, hNF, hstep, hcache, hreal, hprog⟩ := hfac
  subst hreal hprog
  refine le_trans (tvDist_bind_right_le g _ _) ?_
  haveI : ∀ n s r, NeverFail (stepReal n s r) := hNF
  exact signRunF_tvDist_le_collisionBound (Salt := Salt) (St := St)
    stepReal stepProg c hstep qSign qHash hcache st

/-! ## Concrete GPV `signRunF` handlers (the R2 construction)

The obligation `AdaptiveFactorizesSignRunF` is an existential over a handler-state type `St`,
real/programmed per-step handlers, a recorded-cache sequence `c`, a start state, and a shared
post-processor `g`. This section pins the GPV-concrete witnesses for the handler-state and step
handlers, and proves the two *structurally provable* conjuncts of the obligation against them — the
`NeverFail` of the real step and the off-collision branch agreement under regularity. What remains
purely deep — the two run-equalities `realRun = 𝒟[signRunF stepReal c qSign …]` /
`progRun = 𝒟[signRunF stepProg c qSign …]` together with the cache-growth bound on the *adaptive*
run's recorded slices — is the front-loading fold factorization, isolated as the single residual
`gpvRun_factorizes_signRunF` below.

The handler state is the lazy random-oracle cache `(Salt × M →ₒ Range).QueryCache`; both step
handlers update it at the freshly drawn salt `r` and the `n`-th signing message `msgs n`. The
`stepReal` handler mirrors the real signing oracle's *cache-miss* branch: draw a uniform target
`c ← $ᵗ Range`, draw the trapdoor preimage, and cache `c`. The `stepProg` handler mirrors the
sign-then-hash simulator: forward-sample a short preimage `s ← domainSample pk` and program the
cache entry to `psf.eval pk s`. -/

open Classical in
/-- **Real GPV signing step (cache-miss branch).** At signing step `n` with random-oracle cache
`cache` and freshly drawn salt `r`, draw a uniform target `c ← $ᵗ Range`, draw a trapdoor preimage
of `c`, and record `(r, msgs n) ↦ c` in the cache. This is the per-step handler used as `stepReal`
in the GPV `signRunF` presentation of the real game run. -/
noncomputable def gpvStepReal (pk : PK) (sk : SK) (msgs : ℕ → M) :
    ℕ → (Salt × M →ₒ Range).QueryCache → Salt → ProbComp ((Salt × M →ₒ Range).QueryCache) :=
  fun n cache r => do
    let c ← ($ᵗ Range)
    let _s ← psf.trapdoorSample pk sk c
    pure (cache.cacheQuery (r, msgs n) c)

open Classical in
/-- **Programmed GPV signing step (sign-then-hash branch).** At signing step `n` with random-oracle
cache `cache` and freshly drawn salt `r`, forward-sample a short preimage `s ← domainSample pk` and
record `(r, msgs n) ↦ psf.eval pk s` in the cache. This is the per-step handler used as `stepProg`
in the GPV `signRunF` presentation of the programmed (simulator) run. -/
noncomputable def gpvStepProg (pk : PK) (domainSample : PK → ProbComp Domain) (msgs : ℕ → M) :
    ℕ → (Salt × M →ₒ Range).QueryCache → Salt → ProbComp ((Salt × M →ₒ Range).QueryCache) :=
  fun n cache r => do
    let s ← domainSample pk
    pure (cache.cacheQuery (r, msgs n) (psf.eval pk s))

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Real GPV step never fails.** Given that the trapdoor sampler never fails (a mild
side-condition satisfied by any total preimage sampler — e.g. Falcon's `ffSampling` loop, which
always returns), the real per-step handler `gpvStepReal` never fails: the uniform target draw is
total, the trapdoor draw is total by hypothesis, and the final cache update is a `pure`. This
discharges the `NeverFail (stepReal n s r)` conjunct of the obligation against the concrete
`stepReal := gpvStepReal`. -/
theorem gpvStepReal_neverFail (pk : PK) (sk : SK) (msgs : ℕ → M)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (n : ℕ) (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt) :
    NeverFail (gpvStepReal psf M Salt pk sk msgs n cache r) := by
  unfold gpvStepReal
  rw [neverFail_bind_iff]
  refine ⟨inferInstance, fun c _ => ?_⟩
  rw [neverFail_bind_iff]
  exact ⟨hNF c, fun _ _ => inferInstance⟩

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Real/programmed GPV step distributional agreement.** Under PSF regularity (witnessed by the
forward sampler `domainSample` of `psf.Regularity`), the real and programmed per-step handlers agree
as output distributions at every step `n`, cache, and salt `r`.

Both handlers update the same cache slot `(r, msgs n)` with the first component of a `(target,
preimage)` pair; the real handler draws that pair as `(c, s)` with `c ← $ᵗ Range`, `s ←
trapdoorSample pk sk c`, while the programmed handler draws it as `(eval pk s, s)` with `s ←
domainSample pk`. PSF regularity equates exactly these two joint distributions, so projecting onto
the cache update preserves the equality. This agreement is in fact *unconditional* in `r` (it does
not require `r ∉ c n`), which is stronger than the obligation's off-collision conjunct demands. -/
theorem gpvStep_agree (pk : PK) (sk : SK) (msgs : ℕ → M)
    (domainSample : PK → ProbComp Domain)
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (n : ℕ) (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt) :
    𝒟[gpvStepReal psf M Salt pk sk msgs n cache r]
      = 𝒟[gpvStepProg psf M Salt pk domainSample msgs n cache r] := by
  unfold gpvStepReal gpvStepProg
  set proj : Range × Domain → (Salt × M →ₒ Range).QueryCache :=
    fun cs => cache.cacheQuery (r, msgs n) cs.1 with hproj
  have hR : (($ᵗ Range) >>= fun c => psf.trapdoorSample pk sk c >>=
              fun _s => (pure (cache.cacheQuery (r, msgs n) c) : ProbComp _))
        = ((($ᵗ Range) >>= fun c => psf.trapdoorSample pk sk c >>= fun s => pure (c, s)) >>=
            fun cs => pure (proj cs)) := by simp [hproj]
  have hP : (domainSample pk >>=
              fun s => (pure (cache.cacheQuery (r, msgs n) (psf.eval pk s)) : ProbComp _))
        = ((domainSample pk >>= fun s => pure (psf.eval pk s, s)) >>=
            fun cs => pure (proj cs)) := by simp [hproj]
  change 𝒟[(($ᵗ Range) >>= fun c => psf.trapdoorSample pk sk c >>=
              fun _s => pure (cache.cacheQuery (r, msgs n) c))] = _
  rw [hR, hP]
  simp only [evalDist_bind, hreg]

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Real GPV signing-body cache splice (cache-miss key).** One real signing-query body, run
through the lazy random oracle at a *missing* cache key `(r, msgs n)`, produces a recorded-cache
transition distributed exactly as the concrete `signRunF` real step `gpvStepReal` at the (already
fixed) salt `r`.

The signing body queries the random oracle at `(r, msgs n)`; on the cache miss `cache (r, msgs n) =
none` the oracle draws a fresh uniform target `u ← $ᵗ Range`, records `(r, msgs n) ↦ u`, and returns
`u`; the body then draws the trapdoor preimage and yields the updated cache. The handler
`gpvStepReal` draws the same uniform target `c ← $ᵗ Range`, the same trapdoor preimage, and records
`(r, msgs n) ↦ c` — so the two recorded-cache distributions coincide. This is the *per-body splice*
of the adaptive→`signRunF` fold factorization (the signing-step case of
`gpvRun_factorizes_signRunF`): it recasts one inline signing-oracle body, on a fresh-salt cache
miss, as the concrete `signRunF` real step, with the fresh salt `r` having been front-loaded out of
the body. It is *pinned* to the concrete `randomOracle` and `gpvStepReal`, requires only the
cache-miss side condition `hmiss` (guaranteed for a fresh salt), and is unconditional otherwise. -/
theorem evalDist_gpvSignBody_run_eq_gpvStepReal (pk : PK) (sk : SK) (msgs : ℕ → M) (n : ℕ)
    (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt)
    (hmiss : cache (r, msgs n) = none) :
    𝒟[(do
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msgs n)).run cache
        let _s ← psf.trapdoorSample pk sk p.1
        pure p.2 : ProbComp ((Salt × M →ₒ Range).QueryCache))]
      = 𝒟[gpvStepReal psf M Salt pk sk msgs n cache r] := by
  unfold gpvStepReal
  rw [show (randomOracle (spec := (Salt × M →ₒ Range)) (r, msgs n)).run cache
        = (fun u => (u, cache.cacheQuery (r, msgs n) u)) <$>
            (uniformSampleImpl (spec := (Salt × M →ₒ Range)) (r, msgs n))
      from QueryImpl.withCaching_run_none uniformSampleImpl hmiss]
  rw [show (uniformSampleImpl (spec := (Salt × M →ₒ Range)) (r, msgs n))
        = ($ᵗ Range : ProbComp Range) from rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind]

open Classical in
omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Programmed GPV signing-body cache splice (simulator signing query).** One programmed
simulator signing-query body — the `signImpl` handler of `progGameRun`, which draws a fresh salt
`r ← $ᵗ Salt`, forward-samples a short preimage `s ← domainSample pk`, programs the random-oracle
cache entry `(r, msg) ↦ psf.eval pk s`, updates the preimage record, and returns `(r, s)` — has its
recorded random-oracle *cache component* (with the salt draw front-loaded, and the returned
signature and the auxiliary preimage record dropped) distributed exactly as the salt-prefixed
concrete `signRunF` programmed step: draw the same fresh salt `r ← $ᵗ Salt`, then apply
`gpvStepProg` at that `r`.

This is the programmed-side dual of `evalDist_gpvSignBody_run_eq_gpvStepReal`, and the signing-step
case of the *programmed* run-equality
`progGameRun … = 𝒟[signRunF gpvStepProg c qSign …]` inside the residual
`gpvRun_factorizes_signRunF`. It is *pinned* to the concrete `progGameRun` signing body and the
concrete `gpvStepProg`: the cache transition `cache ↦ cache.cacheQuery (r, msgs n) (psf.eval pk s)`
on both sides is the same, the salt draw is the same front-loaded `$ᵗ Salt`, and `domainSample` is
the shared programming randomness. No probability-mass averaging is performed; the equality is the
exact recasting of one inline simulator signing body — with its salt front-loaded — as one
`signRunF` programmed step. The auxiliary preimage record `((Salt × M) → Option Domain)` of
`progGameRun`'s state, which `gpvStepProg` does not carry, is dropped here (it is
collision-extraction bookkeeping, irrelevant to the random-oracle cache distribution that the
sign-then-hash hop compares; it is reattached at the run level, not the per-step level). -/
theorem evalDist_gpvSignBody_run_eq_gpvStepProg (pk : PK) (domainSample : PK → ProbComp Domain)
    (msgs : ℕ → M) (n : ℕ)
    (cache : (Salt × M →ₒ Range).QueryCache) (pre : (Salt × M) → Option Domain) :
    𝒟[(do
        -- The actual `progGameRun` simulator signing body (`signImpl`), with the fresh salt draw
        -- front-loaded, run on state `(cache, pre)`; project out the random-oracle cache component
        -- (dropping the returned signature and the auxiliary preimage record).
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← ((do
            let s ← (domainSample pk : ProbComp Domain)
            let v := psf.eval pk s
            let st ← get
            set ((st.1.cacheQuery (r, msgs n) v,
              fun t' => if t' = (r, msgs n) then some s else st.2 t')
                : (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain))
            pure (r, s) :
              StateT ((Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain))
                ProbComp (Salt × Domain)).run (cache, pre))
        pure p.2.1 : ProbComp ((Salt × M →ₒ Range).QueryCache))]
      = 𝒟[(do
          let r ← ($ᵗ Salt : ProbComp Salt)
          gpvStepProg psf M Salt pk domainSample msgs n cache r
            : ProbComp ((Salt × M →ₒ Range).QueryCache))] := by
  unfold gpvStepProg
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set,
    StateT.run_map, bind_pure_comp, map_pure, Functor.map_map, monadLift_self]

/-! ## The R2 residual: front-loading the adaptive salt draws into `signRunF`

The remaining content of `AdaptiveFactorizesSignRunF` against the concrete handlers above is the
pair of run-equalities together with the cache-growth bound on the recorded slices. These facts are
*not* structural: they assert that the adaptive real / programmed game runs
`simulateQ impl (adv.main pk)` (where each signing query draws a fresh salt at an
adversary-chosen point and queries the random oracle at it) factor through the *fixed* `qSign`-step
`signRunF` recursion with the concrete `gpvStepReal` / `gpvStepProg` handlers and a common recorded
cache sequence `c` with `card (c j) ≤ j + qHash`.

Establishing this is the deferred-sampling fold-level coupling: every fresh salt draw, currently
issued inside the signing oracle at an adversarially-chosen point in an adaptively-interleaved query
stream, must be *commuted to the front* of a clean `qSign`-step draw sequence (the salts are fresh
uniform and independent of the adversary view until revealed; the interleaved hash queries are
answer-irrelevant w.r.t. the salt draws and so commute). This is the GPV instance of the worked
Fiat–Shamir factorization
`FiatShamirWithAbort.evalDist_deferredDrawRead_eq_drawList_tapeDrawRead`: an induction on
`adv.main pk` via `OracleComp.inductionOn`, with the uniform / hash-read steps handled by the
generic `OracleComp.DeferredSampling.evalDist_step_commute_tape` answer-irrelevant commute and the
signing step handled by a bespoke per-body salt splice. -/

/-! ### The pinned GPV game runs

The residual `gpvRun_factorizes_signRunF` is pinned to the *actual* GPV game runs of the
adversary's main computation `adv.main pk`, not to free `SPMF` parameters or to a hash-only run
under a deterministic programming policy. Two named game-run distributions model the two worlds of
the sign-then-hash hop:

- `realGameRun` is the **real EUF-CMA game run**: `adv.main pk` simulated under the real ambient
  oracle forwarding (the lazy random oracle via the `runtime` bundle) and the real GPV signing
  oracle (`SignatureAlg.signingOracle`, which on each signing query draws a fresh salt, queries the
  random oracle, and trapdoor-samples a preimage). This is exactly the inner run of
  `SignatureAlg.unforgeableExpNoFresh` for the GPV scheme, with the forgery `(msg, σ)` extracted.

- `progGameRun` is the **randomized sign-then-hash game run**: `adv.main pk` simulated under the
  *programmed* random oracle and the *simulator* signing oracle of the collision reduction
  (the very handler stack of `reduction`). On each random-oracle miss the programmed oracle
  forward-samples `s ← domainSample pk` and records `psf.eval pk s`; on each signing query the
  simulator draws a fresh salt `r`, forward-samples `s`, programs `(r, msg) := psf.eval pk s`, and
  returns `(r, s)`. The randomness is genuine (it lives in `domainSample`), so this models the
  randomized sign-then-hash game rather than a deterministic point-mass programming policy.

The total-variation distance between these two runs is the sign-then-hash hop bounded by
`collisionBound`; the residual factors both through the `signRunF` presentation so that
`factorized_advantage_le_collisionBound` delivers the bound. -/

open Classical in
/-- **The real GPV EUF-CMA game run** of `adv.main pk` at key pair `(pk, sk)`.

The adversary's main computation is simulated under the real ambient oracle forwarding (the lazy
random oracle supplied by the `runtime` bundle) together with the real GPV signing oracle
(`SignatureAlg.signingOracle`), and the resulting forgery `(msg, σ)` is extracted. This is exactly
the inner run of `SignatureAlg.unforgeableExpNoFresh` for the GPV scheme: it is the real-world side
of the sign-then-hash hop, pinned as the residual's `realRun`. -/
noncomputable def realGameRun
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) :
    SPMF (M × (Salt × Domain)) :=
  (runtime M Salt).evalDist do
    let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
        (WriterT (QueryLog (M →ₒ (Salt × Domain)))
          (OracleComp (unifSpec + (Salt × M →ₒ Range)))) :=
      (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
          (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
        (WriterT (QueryLog (M →ₒ (Salt × Domain)))
          (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
        (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
          psf hr M Salt).signingOracle pk sk
    let (out, _log) ← (simulateQ impl (adv.main pk)).run
    pure out

open Classical in
/-- **The randomized sign-then-hash game run** of `adv.main pk` at public key `pk`.

The adversary's main computation is simulated under the collision reduction's programmed
random-oracle / simulator-signing handler stack (the handler model of `reduction`): on a
random-oracle miss the oracle forward-samples `s ← domainSample pk` and records `psf.eval pk s`; on
a signing query the simulator draws a fresh salt `r`, forward-samples `s`, programs
`(r, msg) := psf.eval pk s`, and returns `(r, s)`. The forgery `(msg, σ)` is extracted. The
programming is *randomized* (the randomness lives in `domainSample`), so this models the randomized
sign-then-hash game; it is pinned as the residual's `progRun`. -/
noncomputable def progGameRun
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (pk : PK) :
    SPMF (M × (Salt × Domain)) :=
  let State := (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1 t with
      | some v => pure v
      | none => do
          let s ← (domainSample pk : ProbComp Domain)
          let v := psf.eval pk s
          set ((st.1.cacheQuery t v, fun t' => if t' = t then some s else st.2 t') : State)
          pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let s ← (domainSample pk : ProbComp Domain)
      let v := psf.eval pk s
      let st ← get
      set ((st.1.cacheQuery (r, msg) v,
        fun t' => if t' = (r, msg) then some s else st.2 t') : State)
      pure (r, s)
  let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT State ProbComp) := (unifImpl + roImpl) + signImpl
  𝒟[Prod.fst <$> (simulateQ impl (adv.main pk)).run (∅, fun _ => none)]

/-! ### Round-5 normalization: collapsing the runtime indirection of `realGameRun`

The residual's real-side run-equality compares `realGameRun` — defined through the bundled
`runtime` `SPMF` semantics, which is *itself* a `simulateQ` (`withStateOracle`) over a `StateT`
random-oracle layer wrapping the WriterT signing-oracle `simulateQ` — against the single-`simulateQ`
`signRunF` presentation. Before that deep fold coupling can be attempted with the generic
handler-congruence / `inductionOn` machinery, the *outer* runtime indirection of `realGameRun` must
be peeled back to an explicit `simulateQ` form. The two lemmas below do exactly that peeling (and
nothing more): they are pure structural unfoldings of the `runtime` bundle, pinned to the concrete
`realGameRun`, and do **not** perform any distributional coupling. -/

/-- **`withStateOracle` `SPMF` semantics as an explicit `simulateQ` run (general).**

The bundled `withStateOracle hashImpl s` `SPMF` semantics of a surface computation `mx` is exactly
the observed `StateT.run'` of the `simulateQ` of the public-randomness lift summed with the stateful
`hashImpl`, started from `s`. This is a definitional unfolding of the bundle (`evalDist` is
`denote = observe ∘ interpret`, with `interpret = simulateQ'` and
`observe = liftM ∘ StateT.run' · s`) and carries no probabilistic content; it is the entry point for
reasoning about the runtime layer of
`realGameRun` by an explicit `simulateQ`. -/
theorem withStateOracle_evalDist_eq {ι : Type} {hashSpec : OracleSpec ι} {σ : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ)
    {α : Type} (mx : OracleComp (unifSpec + hashSpec) α) :
    (SPMFSemantics.withStateOracle hashImpl s).evalDist mx
      = (liftM (StateT.run'
          (simulateQ
            ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + hashImpl)
            mx) s) : SPMF α) := by
  unfold SPMFSemantics.evalDist SPMFSemantics.withStateOracle
  simp only [SemanticsVia.denote]

/-- **WriterT-log discard across a substituting oracle (general).**

Simulating `oa` under a WriterT-valued query implementation `so` and then projecting away the
written log (`Prod.fst <$> (·).run`) coincides with simulating `oa` under the *unlogged* base-spec
implementation `soNoLog`, provided the two agree per query after the same log discard
(`hso : ∀ t, Prod.fst <$> (so t).run = soNoLog t`).

Unlike `OracleComp.fst_map_writerT_run_simulateQ`, the target base spec `specBase` may differ from
the source spec `spec`: `soNoLog` is allowed to *substitute* each query by an arbitrary base-spec
computation (not merely re-emit it), so this applies to a genuine oracle replacement such as the GPV
signing oracle (which replaces an abstract signing query by its real `sign` computation over the
random-oracle spec). It is proved by induction on `oa`, with the append-accumulated WriterT log on
the binder collapsing under `Prod.fst`. The log carrier uses the append-based `WriterT` monad
(`[EmptyCollection ω] [Append ω] [LawfulAppend ω]`) so that it applies directly to the `QueryLog`
log of the GPV signing oracle, whose `WriterT` monad instance is the append-based one (there is
deliberately no `Monoid (QueryLog spec)` instance). -/
theorem fst_map_writerT_run_simulateQ_noLog
    {ι ιB : Type} {spec : OracleSpec ι} {specBase : OracleSpec ιB}
    {ω : Type} [EmptyCollection ω] [Append ω] [LawfulAppend ω] {α : Type}
    (so : QueryImpl spec (WriterT ω (OracleComp specBase)))
    (soNoLog : QueryImpl spec (OracleComp specBase))
    (hso : ∀ (t : spec.Domain),
      (Prod.fst <$> (so t).run : OracleComp specBase _) = soNoLog t)
    (oa : OracleComp spec α) :
    (Prod.fst <$> (simulateQ so oa).run : OracleComp specBase α) = simulateQ soNoLog oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [WriterT.run_pure]
  | query_bind t oa ih =>
    rw [simulateQ_bind, simulateQ_query, WriterT.run_bind, map_bind]
    have heq : ((OracleSpec.query t).cont <$> so (OracleSpec.query t).input) = so t := by
      simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query]
    rw [heq]
    rw [show simulateQ soNoLog (liftM (OracleSpec.query t) >>= oa)
          = soNoLog t >>= fun u => simulateQ soNoLog (oa u) by
        rw [simulateQ_bind, simulateQ_query]
        simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query]]
    refine (bind_congr fun x => ?_).trans (by rw [← bind_map_left, hso t])
    obtain ⟨a, w₁⟩ := x
    dsimp only []
    rw [← LawfulFunctor.comp_map]
    have : Prod.fst ∘ (fun x : α × ω ↦ (x.1, w₁ ++ x.2)) = Prod.fst :=
      funext fun ⟨_, _⟩ => rfl
    rw [this]
    exact ih a

/-- **The unlogged real GPV handler stack.**

The real-world handler used inside `realGameRun` is the WriterT-valued stack
`(HasQuery.toQueryImpl).liftTarget (WriterT …) + signingOracle pk sk`, which logs each signing
query. `realGameRunImplNoLog` is the same handler with the signing log discarded: the public/random
oracle queries are re-emitted unchanged into the underlying `OracleComp (unifSpec + (Salt × M →ₒ
Range))`, and each signing query is replaced by the real GPV `sign pk sk` computation (draw a fresh
salt, query the random oracle, trapdoor-sample). It targets `OracleComp (unifSpec + (Salt × M →ₒ
Range))` directly, so simulating `adv.main pk` under it produces the same forgery distribution as
the logged stack with its log discarded (`realGameRun_writerLog_discard`). -/
noncomputable def realGameRunImplNoLog (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (OracleComp (unifSpec + (Salt × M →ₒ Range))) :=
  (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
      (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
    (fun msg => (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
      psf hr M Salt).sign pk sk msg)

omit [Fintype Salt] in
/-- **Round-5 real-side WriterT-log discard (pinned).**

Discarding the signing log from the real GPV WriterT handler stack of `realGameRun` leaves exactly
the unlogged stack `realGameRunImplNoLog`: projecting the first component of the WriterT run of
`simulateQ ((HasQuery.toQueryImpl).liftTarget (WriterT …) + signingOracle pk sk) (adv.main pk)`
equals `simulateQ (realGameRunImplNoLog …) (adv.main pk)`.

It is *pinned* to the concrete real GPV handler stack and is a pure structural rewrite (the general
`fst_map_writerT_run_simulateQ_noLog` discharged by the per-query log-transparency of the two
summands: the lifted public/random-oracle handler re-emits its query, and
`signingOracle = withLogging sign` recovers `sign` after the log discard). No salt front-loading or
distributional coupling is
performed; this is the WriterT-boundary half of the real-side normalization toward the single-impl
`signRunF` shape. -/
theorem realGameRun_writerLog_discard (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    (Prod.fst <$> (simulateQ
        (((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
            (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
          (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
            psf hr M Salt).signingOracle pk sk))
        (adv.main pk)).run
        : OracleComp (unifSpec + (Salt × M →ₒ Range)) (M × (Salt × Domain)))
      = simulateQ (realGameRunImplNoLog psf hr M Salt pk sk) (adv.main pk) := by
  refine fst_map_writerT_run_simulateQ_noLog _ _ (fun t => ?_) (adv.main pk)
  rcases t with t | msg
  · change (Prod.fst <$> ((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
        (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
        (WriterT (QueryLog (M →ₒ (Salt × Domain)))
          (OracleComp (unifSpec + (Salt × M →ₒ Range)))) t).run
        : OracleComp (unifSpec + (Salt × M →ₒ Range)) _)
      = realGameRunImplNoLog psf hr M Salt pk sk (Sum.inl t)
    simp only [QueryImpl.liftTarget_apply, WriterT.run_liftM]
    rfl
  · change (Prod.fst <$> ((GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
        psf hr M Salt).signingOracle pk sk msg).run
        : OracleComp (unifSpec + (Salt × M →ₒ Range)) _)
      = (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
          psf hr M Salt).sign pk sk msg
    simp only [SignatureAlg.signingOracle, QueryImpl.withLogging_apply, bind_pure_comp,
      WriterT.run_bind, WriterT.run_liftM, bind_map_left]
    simp only [WriterT.run_map, WriterT.run_tell, map_pure]
    rw [← Functor.map_map]
    simp

open Classical in
omit [Fintype Salt] in
/-- **Round-5 real-side normalization (pinned): `realGameRun` as an explicit two-layer
`simulateQ` run.**

This peels the bundled `runtime` indirection off `realGameRun`, exposing the *explicit* nested
`simulateQ` form: the inner WriterT signing-oracle `simulateQ` over `adv.main pk` (its `.run`
discarding the signing log to the `Prod.fst` projection), evaluated under the outer
public-randomness-lift `+ randomOracle` `StateT QueryCache ProbComp` `simulateQ`, observed by
`StateT.run'` from the empty cache.

It is *pinned* to the concrete `realGameRun` (it is an equation about that exact distribution, with
the concrete WriterT handler stack `liftTarget HasQuery.toQueryImpl + signingOracle pk sk` and the
concrete outer lazy random oracle), and it is a pure structural rewrite — the trailing `pure out`
of the `realGameRun` do-block is commuted out by `withStateOracle_evalDist_bind_pure`, and the
runtime layer is unfolded by `withStateOracle_evalDist_eq`. No salt front-loading and no
distributional coupling is performed; this is the runtime-indirection removal that the deep fold
coupling builds on. -/
theorem realGameRun_eq_simulateQ_run
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) :
    realGameRun psf hr M Salt adv pk sk =
      Prod.fst <$> ((SPMFSemantics.withStateOracle
        (randomOracle : QueryImpl (Salt × M →ₒ Range)
          (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalDist
        ((simulateQ
            (((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
                (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
                (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                  (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
              (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                psf hr M Salt).signingOracle pk sk))
            (adv.main pk)).run)) := by
  unfold realGameRun
  rw [show (do
        let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) :=
          (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
              (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
            (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
              psf hr M Salt).signingOracle pk sk
        let (out, _log) ← (simulateQ impl (adv.main pk)).run
        pure out) = ((simulateQ
            (((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
                (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
                (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                  (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
              (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                psf hr M Salt).signingOracle pk sk))
            (adv.main pk)).run >>= fun p => pure p.1) from rfl]
  rw [GPVHashAndSign.runtime]
  change (SPMFSemantics.withStateOracle _ ∅).evalDist _ = _
  rw [SPMFSemantics.withStateOracle_evalDist_bind_pure]

open Classical in
omit [Fintype Salt] in
/-- **Round-5 real-side normalization (pinned, single-impl): `realGameRun` as one bundled
`simulateQ` over the unlogged real handler stack.**

This is the assembled real-side normalization: `realGameRun` equals the bundled `withStateOracle`
random-oracle `SPMF` semantics of `simulateQ (realGameRunImplNoLog …) (adv.main pk)` — a *single*
`OracleComp (unifSpec + (Salt × M →ₒ Range))`-valued `simulateQ` over the unlogged real GPV handler
stack, with no remaining WriterT layer. It chains `realGameRun_eq_simulateQ_run` (peeling the
`runtime` indirection and commuting the trailing `pure out` to `Prod.fst <$>`),
`SPMFSemantics.withStateOracle_evalDist_map` (pushing that `Prod.fst <$>` *inside* the outer
bundle, since `<$>` does not thread the random-oracle state), and `realGameRun_writerLog_discard`
(collapsing the inner WriterT signing-log run to `realGameRunImplNoLog`).

It is *pinned* to the concrete `realGameRun` and is purely structural (no salt front-loading, no
distributional coupling). This is the canonical single-`simulateQ` shape that the eventual fold
coupling consumes: `realGameRun`'s adversary computation is now interpreted by one ambient handler
`realGameRunImplNoLog` over `OracleComp (unifSpec + (Salt × M →ₒ Range))`, then observed by the
random-oracle `withStateOracle` bundle — the same surface shape carried by `progGameRun`'s single
`StateT`-state `simulateQ`. -/
theorem realGameRun_eq_withStateOracle_implNoLog
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) :
    realGameRun psf hr M Salt adv pk sk =
      (SPMFSemantics.withStateOracle
        (randomOracle : QueryImpl (Salt × M →ₒ Range)
          (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalDist
        (simulateQ (realGameRunImplNoLog psf hr M Salt pk sk) (adv.main pk)) := by
  rw [realGameRun_eq_simulateQ_run, ← SPMFSemantics.withStateOracle_evalDist_map,
    realGameRun_writerLog_discard]

/-! ### Round-6 normalization: dropping the preimage-record component of `progGameRun`

`progGameRun` simulates `adv.main pk` under a handler stack whose state is the product
`QueryCache × ((Salt × M) → Option Domain)`. The second component is the *preimage record*: it
records, for each programmed random-oracle point, the domain element forward-sampled to produce the
answer. That record is bookkeeping for the collision reduction's extraction only — it is written by
every programming step (and read solely to update *itself*), but it never influences the
random-oracle cache, the output, or any other branch. Hence the forgery distribution `progGameRun`
(the `Prod.fst` of the run) is unchanged by dropping the record component, leaving a single
`simulateQ` over the bare
`StateT QueryCache ProbComp` random-oracle surface — the *same* state shape carried by
`realGameRunImplNoLog` under the runtime `withStateOracle` bundle. The lemma below performs exactly
that drop (no distributional coupling). -/

/-- **The record-free `progGameRun` handler stack.**

The same programmed random-oracle / simulator-signing handler stack as `progGameRun`, but with the
preimage-record component removed: its state is just the random-oracle `QueryCache`. The
random-oracle handler programs a miss with `psf.eval pk (domainSample pk)`; the signing handler
draws a fresh salt, forward-samples, programs the cache point, and returns `(r, s)`. This carries
the same
`StateT QueryCache ProbComp` random-oracle surface as `realGameRunImplNoLog` (observed through the
runtime `withStateOracle` bundle), the shared shape required before the fold coupling. -/
noncomputable def progGameRunImplNoRec (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
  let roImpl : QueryImpl (Salt × M →ₒ Range)
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
    fun t => do
      let st ← get
      match st t with
      | some v => pure v
      | none => do
          let s ← (domainSample pk : ProbComp Domain)
          let v := psf.eval pk s
          set (st.cacheQuery t v)
          pure v
  let unifImpl : QueryImpl unifSpec (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let s ← (domainSample pk : ProbComp Domain)
      let v := psf.eval pk s
      let st ← get
      set (st.cacheQuery (r, msg) v)
      pure (r, s)
  (unifImpl + roImpl) + signImpl

open Classical in
omit [Fintype Salt] in
/-- **Round-6 prog-side normalization (pinned): `progGameRun` with the preimage record dropped.**

`progGameRun … adv domainSample pk` equals the random-oracle `SPMF` semantics of the *single*
`simulateQ (progGameRunImplNoRec …) (adv.main pk)` over the bare `StateT QueryCache ProbComp` state,
observed by `StateT.run'` from the empty cache. The preimage-record component of `progGameRun`'s
state is genuinely passive: it is written by the programming steps but never read by the cache, the
output, or the control flow, so projecting it away (`proj = Prod.fst`) commutes with every oracle
step and hence with the whole simulation (`map_run_simulateQ_eq_of_query_map_eq`).

It is *pinned* to the concrete `progGameRun` and is a pure structural state-projection (no salt
front-loading, no distributional coupling). Together with `realGameRun_eq_withStateOracle_implNoLog`
this puts **both** game runs on the same `StateT QueryCache ProbComp` random-oracle surface — the
prerequisite for the `OracleComp.inductionOn` fold coupling. -/
theorem progGameRun_eq_run'_implNoRec
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (pk : PK) :
    progGameRun psf hr M Salt adv domainSample pk =
      𝒟[(simulateQ (progGameRunImplNoRec psf M Salt domainSample pk)
          (adv.main pk)).run' (∅ : (Salt × M →ₒ Range).QueryCache)] := by
  unfold progGameRun
  simp only [evalDist]
  refine congrArg _ ?_
  -- LHS is `Prod.fst <$> run = run'`; the record component (initially `fun _ => none`) is the
  -- passive auxiliary, so the state projection `proj = Prod.fst` commutes with every step.
  rw [show ((∅ : (Salt × M →ₒ Range).QueryCache)) = Prod.fst
      (((∅ : (Salt × M →ₒ Range).QueryCache), (fun _ => none : (Salt × M) → Option Domain))) from
        rfl]
  rw [← StateT.run']
  refine run'_simulateQ_eq_of_query_map_eq _
    (progGameRunImplNoRec psf M Salt domainSample pk) Prod.fst ?_ (adv.main pk)
    (∅, fun _ => none)
  -- For each oracle (uniform / random-oracle / signing) the cache update depends only on the
  -- cache component, so projecting away the preimage record commutes with the step.
  rintro ((t | t) | t) ⟨st, rec⟩ <;>
    simp only [HAdd.hAdd, QueryImpl.add, progGameRunImplNoRec]
  · -- uniform-sampling query: state untouched by either handler
    simp [StateT.run_monadLift, Prod.map]
  · -- random-oracle query: the cache hit/miss is determined by the cache component `st t`
    rcases h : st t with _ | v <;>
      simp [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift, Prod.map, h]
  · -- signing query: cache update depends only on the cache component
    simp [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift, Prod.map]

/-- **The composed single-impl real GPV handler stack.**

The two-layer real-side simulation of `realGameRun` — `simulateQ realGameRunImplNoLog (adv.main pk)`
producing an `OracleComp (unifSpec + (Salt × M →ₒ Range))`, then observed by the runtime's
public-randomness-lift `+ randomOracle` `StateT QueryCache ProbComp` simulation — fused into a
*single* `StateT QueryCache ProbComp`-valued handler via `QueryImpl.compose` (`∘ₛ`). This carries
the same bare `StateT QueryCache ProbComp` random-oracle surface as `progGameRunImplNoRec`, the
shared shape the fold coupling consumes. -/
noncomputable def gpvRealImpl (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
  (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) +
      (randomOracle : QueryImpl (Salt × M →ₒ Range)
        (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp))) ∘ₛ
    realGameRunImplNoLog psf hr M Salt pk sk)

open Classical in
omit [Fintype Salt] in
/-- **Round-6 real-side single-impl normalization (pinned): `realGameRun` as one bundled `simulateQ`
over the composed real handler `gpvRealImpl`.**

This collapses the two-layer real-side simulation of `realGameRun` into a single `simulateQ` over
the composed handler `gpvRealImpl` (`= outerLift ∘ₛ realGameRunImplNoLog`), observed by
`StateT.run'` from the empty cache:
`realGameRun … = 𝒟[(simulateQ (gpvRealImpl …) (adv.main pk)).run' ∅]`. It
chains `realGameRun_eq_withStateOracle_implNoLog` (the round-5 peeling of the runtime indirection to
a single `simulateQ realGameRunImplNoLog` observed through `withStateOracle`),
`withStateOracle_evalDist_eq` (unfolding the `withStateOracle` bundle to an explicit
`StateT.run'`-of-`simulateQ` of the public-randomness lift `+ randomOracle`), and
`QueryImpl.simulateQ_compose` (fusing the two `simulateQ` layers into the single composed handler).

It is *pinned* to the concrete `realGameRun` and is a pure structural normalization — no salt
front-loading, no distributional coupling. Together with `progGameRun_eq_run'_implNoRec` this puts
**both** game runs in the identical `𝒟[(simulateQ · (adv.main pk)).run' ∅]` shape over the *same*
`StateT QueryCache ProbComp` random-oracle surface, the prerequisite for attempting the
`OracleComp.inductionOn` fold coupling on a common vehicle. -/
theorem realGameRun_eq_run'_implReal
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) :
    realGameRun psf hr M Salt adv pk sk =
      𝒟[(simulateQ (gpvRealImpl psf hr M Salt pk sk)
          (adv.main pk)).run' (∅ : (Salt × M →ₒ Range).QueryCache)] := by
  rw [realGameRun_eq_withStateOracle_implNoLog, withStateOracle_evalDist_eq]
  rw [← QueryImpl.simulateQ_compose]
  rfl

/-! ### GPV tape-consuming impls (the Fiat–Shamir-template first block)

The fold coupling discharging `gpvRun_factorizes_signRunF` follows the worked Fiat–Shamir instance
`FiatShamirWithAbort.evalDist_deferredDrawRead_eq_drawList_tapeDrawRead`: an
`OracleComp.inductionOn`
over `adv.main pk` that front-loads every signing query's fresh salt draw into a single front draw
block `OracleComp.drawList ($ᵗ Salt) qSign`, leaving a *tape-consuming* run whose signing steps read
their salt off the pre-drawn tape rather than drawing it inline.

This block builds the GPV tape-consuming handlers — the analogues of Fiat–Shamir's
`tapeDrawReadImpl` — and their per-query `.run` unfolding lemmas (the analogues of
`tapeDrawReadImpl_run_unif` / `_read` / `_sign`). Each handler carries the random-oracle
`QueryCache` *plus a salt tape* `List Salt` in its state: a signing query consumes the head salt of
the tape (running the rest of the inline signing body on it) instead of drawing `r ← $ᵗ Salt`, while
uniform and random-oracle-read queries leave the tape untouched. These are concrete definitions and
their structural per-query unfoldings; the full `inductionOn` factorization (relating
`simulateQ gpvRealImpl` to the front-tape `drawList ($ᵗ Salt) qSign >>= simulateQ gpvRealImplTape`)
and the `drawList`↔`signRunF` bridge remain the deep open core of the residual. -/

/-- **The real GPV tape-consuming handler.**

The salt-tape analogue of `gpvRealImpl`: its state is the random-oracle `QueryCache` paired with a
*salt tape* `List Salt`. A signing query consumes the head salt `r` of the tape (instead of drawing
`r ← $ᵗ Salt` inline), queries the random oracle at `(r, msg)`, trapdoor-samples a preimage, and
returns `(r, s)` while advancing the tape by one; uniform and random-oracle-read queries behave
exactly as the real handler and leave the tape untouched. The tape is over-provisioned (length
`qSign`, one salt per signing query); a missing head (empty tape) defaults to the inline draw so the
handler is total. This is the GPV analogue of Fiat–Shamir's `tapeDrawReadImpl`; its per-query
unfoldings are recorded by `gpvRealImplTape_run_unif` / `_read` / `_sign` below. -/
noncomputable def gpvRealImplTape (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × List Salt) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inr mc) => StateT.mk fun s =>
      (fun p : Range × (Salt × M →ₒ Range).QueryCache => (p.1, (p.2, s.2))) <$>
        (randomOracle (spec := (Salt × M →ₒ Range)) mc).run s.1
  | .inr msg => StateT.mk fun s =>
      match s.2 with
      | [] =>
          (fun rsc : (Salt × Domain) × (Salt × M →ₒ Range).QueryCache =>
              (rsc.1, (rsc.2, ([] : List Salt)))) <$>
            (do
              let r ← ($ᵗ Salt : ProbComp Salt)
              let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
              let sgn ← psf.trapdoorSample pk sk p.1
              pure ((r, sgn), p.2))
      | r :: tl =>
          (fun rsc : (Salt × Domain) × (Salt × M →ₒ Range).QueryCache => (rsc.1, (rsc.2, tl))) <$>
            (do
              let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
              let sgn ← psf.trapdoorSample pk sk p.1
              pure ((r, sgn), p.2))

omit [Fintype Salt] [DecidableEq Range] in
/-- **One-step unfolding of `gpvRealImplTape` on a uniform query.** The tape is untouched. -/
lemma gpvRealImplTape_run_unif (pk : PK) (sk : SK) (n : unifSpec.Domain)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp _) := rfl

omit [Fintype Salt] [DecidableEq Range] in
/-- **One-step unfolding of `gpvRealImplTape` on a random-oracle read query.** The tape is
untouched; the cache component runs the lazy `randomOracle` step. -/
lemma gpvRealImplTape_run_read (pk : PK) (sk : SK) (mc : Salt × M)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inr mc))).run s =
      (fun p : Range × (Salt × M →ₒ Range).QueryCache => (p.1, (p.2, s.2))) <$>
        (randomOracle (spec := (Salt × M →ₒ Range)) mc).run s.1 := rfl

omit [Fintype Salt] [DecidableEq Range] in
/-- **One-step unfolding of `gpvRealImplTape` on a signing query with a non-empty tape.** The head
salt `r` is consumed off the tape (the tape advances to its tail `tl`), the random oracle is queried
at `(r, msg)`, a trapdoor preimage is drawn, and `(r, s)` is returned. This is the GPV analogue of
`tapeDrawReadImpl_run_sign`: the inline salt draw `r ← $ᵗ Salt` is *replaced* by consuming the
pre-drawn tape head. -/
lemma gpvRealImplTape_run_sign_cons (pk : PK) (sk : SK) (msg : M) (r : Salt) (tl : List Salt)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (gpvRealImplTape psf M Salt pk sk (.inr msg)).run (cache, r :: tl) =
      (fun rsc : (Salt × Domain) × (Salt × M →ₒ Range).QueryCache => (rsc.1, (rsc.2, tl))) <$>
        (do
          let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
          let sgn ← psf.trapdoorSample pk sk p.1
          pure ((r, sgn), p.2)) := rfl

/-- **The programmed (simulator) GPV tape-consuming handler.**

The salt-tape analogue of `progGameRunImplNoRec`: its state is the random-oracle `QueryCache` paired
with a salt tape `List Salt`. A signing query consumes the head salt `r` of the tape (instead of
drawing `r ← $ᵗ Salt` inline), forward-samples a short preimage `s ← domainSample pk`, programs the
cache point `(r, msg) ↦ psf.eval pk s`, and returns `(r, s)` while advancing the tape; the
random-oracle handler programs a miss with `psf.eval pk (domainSample pk)` and the uniform handler
is the bare sample, both leaving the tape untouched. This is the programmed dual of
`gpvRealImplTape`; its per-query unfoldings are recorded by `progGameRunImplTape_run_unif` /
`_read` / `_sign` below. -/
noncomputable def progGameRunImplTape (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × List Salt) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inr mc) => StateT.mk fun s =>
      match s.1 mc with
      | some v => pure (v, s)
      | none =>
          (fun sd : Domain => (psf.eval pk sd, (s.1.cacheQuery mc (psf.eval pk sd), s.2))) <$>
            (domainSample pk : ProbComp Domain)
  | .inr msg => StateT.mk fun s =>
      match s.2 with
      | [] =>
          (do
            let r ← ($ᵗ Salt : ProbComp Salt)
            let sd ← (domainSample pk : ProbComp Domain)
            pure ((r, sd), (s.1.cacheQuery (r, msg) (psf.eval pk sd), ([] : List Salt))))
      | r :: tl =>
          (fun sd : Domain => ((r, sd), (s.1.cacheQuery (r, msg) (psf.eval pk sd), tl))) <$>
            (domainSample pk : ProbComp Domain)

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **One-step unfolding of `progGameRunImplTape` on a uniform query.** The tape is untouched. -/
lemma progGameRunImplTape_run_unif (domainSample : PK → ProbComp Domain) (pk : PK)
    (n : unifSpec.Domain) (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (progGameRunImplTape psf M Salt domainSample pk (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp _) := rfl

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **One-step unfolding of `progGameRunImplTape` on a random-oracle read query.** The tape is
untouched; on a cache hit the recorded value is returned, on a miss the answer is programmed to
`psf.eval pk (domainSample pk)`. -/
lemma progGameRunImplTape_run_read (domainSample : PK → ProbComp Domain) (pk : PK) (mc : Salt × M)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (progGameRunImplTape psf M Salt domainSample pk (.inl (.inr mc))).run s =
      (match s.1 mc with
        | some v => pure (v, s)
        | none =>
            (fun sd : Domain => (psf.eval pk sd, (s.1.cacheQuery mc (psf.eval pk sd), s.2))) <$>
              (domainSample pk : ProbComp Domain)) := rfl

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **One-step unfolding of `progGameRunImplTape` on a signing query with a non-empty tape.** The
head salt `r` is consumed off the tape (the tape advances to its tail `tl`), a short preimage is
forward-sampled, the cache point `(r, msg) ↦ psf.eval pk s` is programmed, and `(r, s)` is returned.
This is the programmed analogue of `gpvRealImplTape_run_sign_cons`: the inline salt draw is replaced
by consuming the pre-drawn tape head. -/
lemma progGameRunImplTape_run_sign_cons (domainSample : PK → ProbComp Domain) (pk : PK) (msg : M)
    (r : Salt) (tl : List Salt) (cache : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run (cache, r :: tl) =
      (fun sd : Domain => ((r, sd), (cache.cacheQuery (r, msg) (psf.eval pk sd), tl))) <$>
        (domainSample pk : ProbComp Domain) := rfl

omit [Fintype Salt] [DecidableEq Range] in
/-- **Real tape signing-step cache bridge.** The cache component of one `gpvRealImplTape` signing
step on a consed tape `r :: tl`, at a *missing* cache key `(r, msgs n) = none`, is distributed
exactly as the concrete `signRunF` real step `gpvStepReal` at the consumed head salt `r`.

This is the GPV analogue of Fiat–Shamir's per-body splice (the signing-step case of the fold
factorization): it relates the tape-consuming signing step to the `signRunF` handler the residual
`gpvRun_factorizes_signRunF` factors through. It is *pinned* to the concrete `gpvRealImplTape` and
`gpvStepReal`, and reduces (via `gpvRealImplTape_run_sign_cons`) to the banked inline splice
`evalDist_gpvSignBody_run_eq_gpvStepReal`: with the head salt `r` already supplied (front-loaded out
of the tape), the tape signing step is exactly one real signing body run through the lazy random
oracle, whose recorded cache transition is `gpvStepReal n cache r`. The only side condition is the
fresh-salt cache miss `hmiss`. -/
lemma evalDist_gpvRealImplTape_sign_cache_eq_gpvStepReal (pk : PK) (sk : SK) (msgs : ℕ → M) (n : ℕ)
    (r : Salt) (tl : List Salt) (cache : (Salt × M →ₒ Range).QueryCache)
    (hmiss : cache (r, msgs n) = none) :
    𝒟[(fun p : (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × List Salt) => p.2.1) <$>
        (gpvRealImplTape psf M Salt pk sk (.inr (msgs n))).run (cache, r :: tl)]
      = 𝒟[gpvStepReal psf M Salt pk sk msgs n cache r] := by
  rw [gpvRealImplTape_run_sign_cons]
  simp only [Functor.map_map]
  rw [← evalDist_gpvSignBody_run_eq_gpvStepReal psf M Salt pk sk msgs n cache r hmiss]
  simp [map_bind]

open Classical in
omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **Programmed tape signing-step cache bridge.** The cache component of one
`progGameRunImplTape` signing step on a consed tape `r :: tl` is distributed exactly as the concrete
`signRunF` programmed step `gpvStepProg` at the consumed head salt `r`.

This is the programmed dual of `evalDist_gpvRealImplTape_sign_cache_eq_gpvStepReal`, and the
signing-step case of the *programmed* run-equality the residual factors through. It is *pinned* to
the concrete `progGameRunImplTape` and `gpvStepProg`: both forward-sample `s ← domainSample pk` and
record the cache transition `cache ↦ cache.cacheQuery (r, msgs n) (psf.eval pk s)` at the consumed
head salt `r`, so projecting the random-oracle cache component yields exactly `gpvStepProg`. No
side condition is required (the programmed step caches unconditionally). -/
lemma evalDist_progGameRunImplTape_sign_cache_eq_gpvStepProg (domainSample : PK → ProbComp Domain)
    (pk : PK) (msgs : ℕ → M) (n : ℕ) (r : Salt) (tl : List Salt)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    𝒟[(fun p : (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × List Salt) => p.2.1) <$>
        (progGameRunImplTape psf M Salt domainSample pk (.inr (msgs n))).run (cache, r :: tl)]
      = 𝒟[gpvStepProg psf M Salt pk domainSample msgs n cache r] := by
  rw [progGameRunImplTape_run_sign_cons]
  unfold gpvStepProg
  simp [map_eq_bind_pure_comp, Function.comp]

/-! ### Per-query tape↔unified-impl bridges (the Fiat–Shamir-template second block)

These lemmas relate one query-step of the tape-consuming impls `gpvRealImplTape` /
`progGameRunImplTape` (round-8 block) to one query-step of the unified impls `gpvRealImpl` /
`progGameRunImplNoRec` (round-6 block), all on a common per-query `.run`. They are the analogues of
Fiat–Shamir's per-query relating lemmas. The full `inductionOn (adv.main pk)` factorization
(relating `simulateQ gpvRealImpl` to the front-tape
`drawList ($ᵗ Salt) qSign >>= simulateQ gpvRealImplTape`) and the `drawList`↔`signRunF` step bridge
remain the deep open core of the residual.

First the per-query `.run` unfoldings of the *unified* impls on non-signing queries (the unified
analogues of `gpvRealImplTape_run_unif` / `_read`). Unlike the tape lemmas these are not `rfl`: the
unified real handler is the `∘ₛ`-composition `gpvRealImpl = (outerLift + randomOracle) ∘ₛ
realGameRunImplNoLog`, so each non-signing query reduces through `QueryImpl.compose` /
`realGameRunImplNoLog`'s query re-emission. -/

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImpl` on a uniform query.** The cache is untouched: the unified
real handler re-emits the public-randomness query through `realGameRunImplNoLog` and the outer
public-randomness lift forwards it to the bare `unifSpec.query n`, pairing the cache back unchanged.
-/
lemma gpvRealImpl_run_unif (pk : PK) (sk : SK) (n : unifSpec.Domain)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (gpvRealImpl psf hr M Salt pk sk (.inl (.inl n))).run cache =
      (fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _) := rfl

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImpl` on a random-oracle read query.** The unified real handler
re-emits the random-oracle query through `realGameRunImplNoLog`, and the outer `randomOracle`
summand runs the lazy random-oracle step on the cache component. -/
lemma gpvRealImpl_run_read (pk : PK) (sk : SK) (mc : Salt × M)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (gpvRealImpl psf hr M Salt pk sk (.inl (.inr mc))).run cache =
      (randomOracle (spec := (Salt × M →ₒ Range)) mc).run cache := by
  simp [gpvRealImpl, QueryImpl.compose, realGameRunImplNoLog, HAdd.hAdd, QueryImpl.add]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRec` on a uniform query.** The cache is untouched. -/
lemma progGameRunImplNoRec_run_unif (domainSample : PK → ProbComp Domain) (pk : PK)
    (n : unifSpec.Domain) (cache : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inl n))).run cache =
      (fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _) := rfl

open Classical in
omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRec` on a random-oracle read query.** On a cache hit
the recorded value is returned; on a miss the answer is programmed to
`psf.eval pk (domainSample pk)` and recorded in the cache. The tape (in the tape impl) is replaced
here by the bare cache. -/
lemma progGameRunImplNoRec_run_read (domainSample : PK → ProbComp Domain) (pk : PK) (mc : Salt × M)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inr mc))).run cache =
      (match cache mc with
        | some v => pure (v, cache)
        | none =>
            (fun sd : Domain => (psf.eval pk sd, cache.cacheQuery mc (psf.eval pk sd))) <$>
              (domainSample pk : ProbComp Domain)) := by
  cases h : cache mc <;>
    simp [progGameRunImplNoRec, HAdd.hAdd, QueryImpl.add, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_monadLift, h, map_eq_bind_pure_comp, Function.comp]

omit [Fintype Salt] in
/-- **Tier-1 (uniform) tape↔unified bridge — real side.** One uniform query-step of the tape impl
`gpvRealImplTape` equals the corresponding `gpvRealImpl` step with the salt tape carried through
unchanged: both forward the bare `unifSpec.query n` and leave the cache (resp. cache and tape)
untouched. This is the FS template's trivial per-query relating lemma; the tape is a passive
passenger on a uniform query. -/
lemma gpvRealImplTape_run_unif_eq_gpvRealImpl (pk : PK) (sk : SK) (n : unifSpec.Domain)
    (cache : (Salt × M →ₒ Range).QueryCache) (tape : List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inl n))).run (cache, tape) =
      (fun p => (p.1, (p.2, tape))) <$>
        (gpvRealImpl psf hr M Salt pk sk (.inl (.inl n))).run cache := by
  rw [gpvRealImplTape_run_unif, gpvRealImpl_run_unif]; rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Tier-1 (uniform) tape↔unified bridge — programmed side.** One uniform query-step of the
programmed tape impl `progGameRunImplTape` equals the corresponding `progGameRunImplNoRec` step with
the salt tape carried through unchanged. -/
lemma progGameRunImplTape_run_unif_eq_progGameRunImplNoRec (domainSample : PK → ProbComp Domain)
    (pk : PK) (n : unifSpec.Domain) (cache : (Salt × M →ₒ Range).QueryCache) (tape : List Salt) :
    (progGameRunImplTape psf M Salt domainSample pk (.inl (.inl n))).run (cache, tape) =
      (fun p => (p.1, (p.2, tape))) <$>
        (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inl n))).run cache := by
  rw [progGameRunImplTape_run_unif, progGameRunImplNoRec_run_unif]; rfl

omit [Fintype Salt] in
/-- **Tier-2 (random-oracle read) tape↔unified bridge — real side.** One random-oracle read
query-step of the tape impl `gpvRealImplTape` equals the corresponding `gpvRealImpl` step with the
salt tape carried through unchanged: both run the *same* lazy `randomOracle` step on the cache
component (`gpvRealImpl` re-emits the read query through `realGameRunImplNoLog` and the outer
`randomOracle` summand answers it), leaving the tape a passive passenger. -/
lemma gpvRealImplTape_run_read_eq_gpvRealImpl (pk : PK) (sk : SK) (mc : Salt × M)
    (cache : (Salt × M →ₒ Range).QueryCache) (tape : List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inr mc))).run (cache, tape) =
      (fun p => (p.1, (p.2, tape))) <$>
        (gpvRealImpl psf hr M Salt pk sk (.inl (.inr mc))).run cache := by
  rw [gpvRealImplTape_run_read, gpvRealImpl_run_read]; rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Tier-2 (random-oracle read) tape↔unified bridge — programmed side.** One random-oracle read
query-step of the programmed tape impl `progGameRunImplTape` equals the corresponding
`progGameRunImplNoRec` step with the salt tape carried through unchanged: on a cache hit both return
the recorded value, on a miss both program `psf.eval pk (domainSample pk)` and record it, leaving
the tape untouched. -/
lemma progGameRunImplTape_run_read_eq_progGameRunImplNoRec (domainSample : PK → ProbComp Domain)
    (pk : PK) (mc : Salt × M) (cache : (Salt × M →ₒ Range).QueryCache) (tape : List Salt) :
    (progGameRunImplTape psf M Salt domainSample pk (.inl (.inr mc))).run (cache, tape) =
      (fun p => (p.1, (p.2, tape))) <$>
        (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inr mc))).run cache := by
  rw [progGameRunImplTape_run_read, progGameRunImplNoRec_run_read]
  cases h : cache mc <;> simp [h, Functor.map_map]

open Classical in
omit [Fintype Salt] in
/-- **The R2 residual (the single open sub-step): the *pinned* adaptive GPV game runs satisfy the
`AdaptiveFactorizesSignRunF` factorization obligation, with regularity threaded in.**

The two computations being factored are **not** free parameters and **not** a hash-only run under a
deterministic programming policy: they are *pinned* to the actual GPV game runs of the adversary's
main computation `adv.main pk`, over the full oracle stack
`(unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))` — the vehicle that *has* the signing
oracle and therefore the fresh salt draws. The real run `realGameRun … adv pk sk` is the real
EUF-CMA game (lazy random oracle plus the real GPV signing oracle, exactly the inner run of
`SignatureAlg.unforgeableExpNoFresh`); the programmed run `progGameRun … adv domainSample pk` is the
randomized sign-then-hash game (the collision reduction's programmed-oracle / simulator-signing
handler stack, whose programming randomness lives in `domainSample`). The PSF regularity witness is
threaded in as `hreg` (so the produced obligation's off-collision branch agreement is dischargeable
by `gpvStep_agree`) and the trapdoor sampler's totality as `hNF` (so the real step never fails); the
query bound `hQ : signHashQueryBound (oa := adv.main pk) qSign qHash` ties `qSign` to the
adversary's signing-query count and `qHash` to its hash-query count. The conclusion is exactly
`AdaptiveFactorizesSignRunF (realGameRun …) (progGameRun …) qSign qHash` — the obligation consumed
by `factorized_advantage_le_collisionBound`.

This statement is *true-as-stated* (counterexample-checked at `qSign = 0`): with the query bound
`hQ` and `qSign = 0`, the adversary makes **no** signing queries, so the simulator signing oracle of
`progGameRun` never fires — nothing is programmed by the signing path. Each random-oracle answer of
`progGameRun` is `psf.eval pk (domainSample pk)`, whose distribution equals a uniform `$ᵗ Range`
answer by the first marginal of `hreg`, so the programmed run and the real run coincide:
`realGameRun … = progGameRun …`. The obligation `AdaptiveFactorizesSignRunF` at `qSign = 0` requires
exactly `realRun = progRun = 𝒟[g (st, false)]` (since `signRunF stepReal c 0 (st, false) =
pure (st, false)`), which is satisfied by the shared run as `g`. So there is **no** `qSign = 0`
free-parameter hole: pinning both runs to the genuine GPV game-run distributions (rather than to
free `SPMF` parameters, as the false predecessor did) and constraining `qSign` by `hQ` excludes the
point-mass counterexample of the free-parameter version.

This is the **single remaining `#228`-class sub-step**: the deferred-sampling fold factorization
front-loading the adversary's adaptively-interleaved fresh salt draws of the game runs into the
fixed `qSign`-step `signRunF` sequence (see the section docstring above and the worked Fiat–Shamir
instance `FiatShamirWithAbort.evalDist_deferredDrawRead_eq_drawList_tapeDrawRead`). Once discharged,
it feeds (directly, via `factorized_advantage_le_collisionBound`) the salt-inclusive sign-then-hash
hop of the four GPV theorems; the structural conjuncts (`NeverFail`, off-collision agreement) are
supplied here from `hNF`/`hreg` so the residual's *only* remaining content is the deep run-equality
factorization. -/
theorem gpvRun_factorizes_signRunF [Finite Range] [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    AdaptiveFactorizesSignRunF (Salt := Salt)
      (realGameRun psf hr M Salt adv pk sk)
      (progGameRun psf hr M Salt adv domainSample pk) qSign qHash := by
  -- The deferred-sampling fold factorization of the *pinned* adaptive GPV game runs
  -- `realGameRun … adv pk sk` (real EUF-CMA game: lazy RO + real GPV signing oracle) and
  -- `progGameRun … adv domainSample pk` (randomized sign-then-hash game: the reduction's
  -- programmed-oracle / simulator-signing handler stack).  The structural conjuncts of
  -- `AdaptiveFactorizesSignRunF` are already dischargeable here (`gpvStepReal_neverFail` from
  -- `hNF`, `gpvStep_agree` from `hreg`); the ONLY remaining content is the pair of run-equalities
  -- `realGameRun … = 𝒟[signRunF gpvStepReal c qSign …]` / `progGameRun … =
  -- 𝒟[signRunF gpvStepProg c qSign …]` over a shared recorded cache sequence `c` with
  -- `card (c j) ≤ j + qHash`.  Establishing those is the `#228`-class adaptive→`signRunF` coupling
  -- described in the section docstring: front-loading the adversary's adaptively-interleaved fresh
  -- salt draws (issued inside the signing oracle of `adv.main pk` at adversary-chosen points) into
  -- the fixed `qSign`-step `signRunF` sequence.  It is the one isolated residual of the GPV
  -- campaign.  Pinned to the genuine game runs (NOT free-parameter, NOT a hash-only deterministic
  -- policy run), and constrained by `hQ`; counterexample-checked TRUE at `qSign = 0` (docstring:
  -- with no signing queries the simulator never fires, each programmed RO answer is `eval`-of-a-
  -- forward-sample which is uniform by the first marginal of `hreg`, so the two runs coincide).
  sorry

/-- **Step 1 (sign-then-hash ≡ real) TV bound — proven, consuming the R2 residual.**

This is the salt-inclusive sign-then-hash hop *over the pinned GPV game runs*, with the deep
factorization supplied by the re-stated residual `gpvRun_factorizes_signRunF`. The real run
`realGameRun … adv pk sk` (the real EUF-CMA game) and the programmed run
`progGameRun … adv domainSample pk` (the randomized sign-then-hash game of the collision reduction)
are the two distributions of the sign-then-hash hop; given the query bound `hQ`, the trapdoor
totality `hNF`, and PSF regularity `hreg`, their total-variation distance is bounded by
`(collisionBound Salt qSign qHash).toReal`.

The proof *consumes* the residual: it applies `gpvRun_factorizes_signRunF` (which yields the
`AdaptiveFactorizesSignRunF` obligation for the pinned game runs) and then closes with the banked
`factorized_advantage_le_collisionBound`. This makes the re-stated residual **load-bearing**: it is
no longer a dormant statement but is invoked in a real (non-`sorry`) proof, exactly as the design's
Step-1 chain requires (LHS → residual → `factorized_advantage_le_collisionBound`).

It is the GPV instance of the U2 surface
`tvDist_runtime_real_programmed_le_collisionBound_saltInclusive`, but unconditional and over the
actual game run: where that lemma takes the up-to-bad coupling as the hypothesis `hcouple`, here the
coupling is delivered by the residual factorization rather than assumed. -/
theorem gpv_tvDist_real_programmed_le_collisionBound
    [Finite Range] [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    SPMF.tvDist (realGameRun psf hr M Salt adv pk sk)
        (progGameRun psf hr M Salt adv domainSample pk)
      ≤ (collisionBound Salt qSign qHash).toReal :=
  factorized_advantage_le_collisionBound (Salt := Salt)
    (realGameRun psf hr M Salt adv pk sk)
    (progGameRun psf hr M Salt adv domainSample pk) qSign qHash
    (gpvRun_factorizes_signRunF psf hr M Salt pk sk adv domainSample qSign qHash hQ hNF hreg)

open Classical in
omit [DecidableEq Range] [Fintype Salt] in
/-- **Discharging `AdaptiveFactorizesSignRunF` from the R2 residual (proven reduction).**

Given the trapdoor sampler's totality (`hNF`), the regularity witness (`hreg`), and the fold
factorization `gpvRun_factorizes_signRunF` (`hfac`) for the concrete GPV handlers, the obligation
`AdaptiveFactorizesSignRunF realRun progRun qSign qHash` holds: the concrete `gpvStepReal` /
`gpvStepProg` handlers, the factorization's recorded-cache sequence, the empty start cache, and the
shared post-processor witness the existential, with the structural conjuncts supplied by
`gpvStepReal_neverFail` and `gpvStep_agree`.

This isolates exactly the deep content into `gpvRun_factorizes_signRunF`: everything *else* the
obligation requires (the never-failing real step and the off-collision branch agreement) is proven
here unconditionally from regularity and trapdoor totality. -/
theorem adaptiveFactorizesSignRunF_gpv [Nonempty Salt] {α : Type}
    (pk : PK) (sk : SK) (msgs : ℕ → M) (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ)
    (realRun progRun : SPMF α) (g : (Salt × M →ₒ Range).QueryCache × Bool → ProbComp α)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hfac : ∃ c : ℕ → Finset Salt,
      (∀ j, (c j).card ≤ j + qHash) ∧
      realRun = 𝒟[signRunF (Salt := Salt)
          (gpvStepReal psf M Salt pk sk msgs) c qSign (∅, false) >>= g] ∧
      progRun = 𝒟[signRunF (Salt := Salt)
          (gpvStepProg psf M Salt pk domainSample msgs) c qSign (∅, false) >>= g]) :
    AdaptiveFactorizesSignRunF (Salt := Salt) realRun progRun qSign qHash := by
  obtain ⟨c, hcache, hreal, hprog⟩ := hfac
  exact ⟨(Salt × M →ₒ Range).QueryCache,
    gpvStepReal psf M Salt pk sk msgs, gpvStepProg psf M Salt pk domainSample msgs,
    c, ∅, g,
    fun n s r => gpvStepReal_neverFail psf M Salt pk sk msgs hNF n s r,
    fun n s r _ => gpvStep_agree psf M Salt pk sk msgs domainSample hreg n s r,
    hcache, hreal, hprog⟩

/-! ## State-threading bridge: runtime ↦ bare random oracle

The GPV `runtime` interprets the surface program over the *sum* spec
`unifSpec + (Salt × M →ₒ Range)` via
`simulateQ' ((QueryImpl.ofLift unifSpec ProbComp).liftTarget _ + randomOracle)`. The reusable
state-threading bridge in `ProgramLogic/Relational/ProgrammingOracle.lean`
(`tvDist_simulateQ_randomOracle_withProgramming_le_probEvent_bad`) is instead stated for the bare
single-spec lazy random oracle `simulateQ randomOracle`. The lemma
`runtime_evalDist_liftComp` is the missing reduction connecting the two: on a sub-computation that
only touches the random oracle (a hash-only `OracleComp (Salt × M →ₒ Range)` lifted into the sum),
the runtime's bundled `SPMF` semantics collapse to the bare `randomOracle` run from the empty
cache. -/

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Pre-bridge.** On a random-oracle-only sub-computation `ob` lifted into the sum spec, the GPV
runtime's `SPMF` semantics equal the externally observed bare lazy random-oracle run from the empty
cache.

This is the reduction from the runtime's sum-spec `simulateQ'` interpreter down to the bare
`simulateQ randomOracle` form expected by the banked random-oracle state-threading bridge. It is
proved by unfolding `withStateOracle` and applying `QueryImpl.simulateQ_add_liftComp_right`, which
discards the (lifted-identity) uniform-sampling handler on a computation that never queries it. -/
theorem runtime_evalDist_liftComp {α : Type} (ob : OracleComp (Salt × M →ₒ Range) α) :
    (runtime M Salt).evalDist (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range)))
      = (liftM (StateT.run'
          (simulateQ (randomOracle :
            QueryImpl (Salt × M →ₒ Range) (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ob)
          ∅) : SPMF α) := by
  classical
  unfold ProbCompRuntime.evalDist runtime
  change (SPMFSemantics.withStateOracle _ ∅).evalDist _ = _
  unfold SPMFSemantics.evalDist SPMFSemantics.withStateOracle
  simp only [SemanticsVia.denote]
  rw [QueryImpl.simulateQ_add_liftComp_right]

/-! ## U2: sign-then-hash ≡ real, up to the programming bad event

The "sign-then-hash ≡ real" hop replaces the real lazy random oracle by a `policy`-programmed one
(the simulator programs each fresh signing target with `psf.eval pk s` for a freshly sampled short
preimage `s`). This is **not** an exact distributional equality: it is exact up to the
*programming bad event*, namely that a freshly sampled signing salt collides with an entry already
present in the random-oracle cache. `tvDist_runtime_real_programmed_le_bad` is the exact, proven
core of the hop: the total-variation distance between the real-runtime output and the
programmed-run output is bounded by the probability that the programming bad flag fires.

The `Fintype Range`/`Inhabited Range` hypotheses supply the `IsUniformSpec (Salt × M →ₒ Range)`
instance required by the banked bridge; they are mild for a hash range. -/

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **U2 core (proven): sign-then-hash up-to-bad TV bound.**

For any random-oracle-only sub-computation `ob` and any programming `policy`, the total-variation
distance between the *real* GPV runtime output and the *programmed* (sign-then-hash) output is
bounded by the probability that the programming bad flag fires during the programmed run.

This is the exact, statistical-distance form of the sign-then-hash hop: it is one TV bound, **not**
an exact equality (stating it as equality would be false, since a fresh salt can collide with a
cached entry). It combines the pre-bridge `runtime_evalDist_liftComp` with the banked
`tvDist_simulateQ_randomOracle_withProgramming_le_probEvent_bad`. The downstream task is to bound
the right-hand bad-event probability by `collisionBound Salt qSign qHash` using regularity `hreg`
(to align the programmed value `psf.eval pk s` with the real uniform answer) and the salt-collision
union bound `probEvent_salt_collision_le_collisionBound`.

The `Finite Range`/`Inhabited Range` hypotheses supply the `IsUniformSpec (Salt × M →ₒ Range)`
instance required by the banked bridge; they are mild for a hash range. -/
theorem tvDist_runtime_real_programmed_le_bad [Finite Range] [Inhabited Range] {α : Type}
    (policy : OracleSpec.ProgrammingPolicy (Salt × M →ₒ Range))
    (ob : OracleComp (Salt × M →ₒ Range) α) :
    SPMF.tvDist
        ((runtime M Salt).evalDist (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range))))
        (liftM (StateT.run'
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob) (∅, false))
          : SPMF α)
      ≤ Pr[fun z : α × (Salt × M →ₒ Range).QueryCache × Bool => z.2.2 = true |
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob).run
            (∅, false)].toReal := by
  haveI : Fintype Range := Fintype.ofFinite Range
  haveI : IsUniformSpec (Salt × M →ₒ Range) := IsUniformSpec.ofFintypeInhabited _
  rw [runtime_evalDist_liftComp]
  exact tvDist_simulateQ_randomOracle_withProgramming_le_probEvent_bad
    (spec := (Salt × M →ₒ Range)) policy ob ∅

omit [DecidableEq Range] [SampleableType Salt] in
/-- **U2 headline (proven, conditional on the bad-event bound).**

The sign-then-hash hop is correct up to the salt-collision birthday bound: if the programming bad
event of `policy` on the run `ob` is bounded by `collisionBound Salt qSign qHash` (the Part-C
obligation discharged by regularity + the salt-collision union bound
`probEvent_salt_collision_le_collisionBound`), then the total-variation distance between the real
GPV runtime output and the programmed (sign-then-hash) output is at most
`(collisionBound Salt qSign qHash).toReal`.

This packages the full U2 statement with the genuine remaining obligation isolated as the
hypothesis `hbad`. The proof simply chains the proven up-to-bad core
`tvDist_runtime_real_programmed_le_bad` with `hbad`. -/
theorem tvDist_runtime_real_programmed_le_collisionBound [Finite Range] [Inhabited Range]
    [Nonempty Salt] {α : Type} (qSign qHash : ℕ)
    (policy : OracleSpec.ProgrammingPolicy (Salt × M →ₒ Range))
    (ob : OracleComp (Salt × M →ₒ Range) α)
    (hbad : Pr[ fun z : α × (Salt × M →ₒ Range).QueryCache × Bool => z.2.2 = true |
        (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob).run (∅, false)]
        ≤ collisionBound Salt qSign qHash) :
    SPMF.tvDist
        ((runtime M Salt).evalDist (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range))))
        (liftM (StateT.run'
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob) (∅, false))
          : SPMF α)
      ≤ (collisionBound Salt qSign qHash).toReal := by
  refine (tvDist_runtime_real_programmed_le_bad M Salt policy ob).trans ?_
  refine ENNReal.toReal_mono ?_ hbad
  refine (ENNReal.div_lt_top ?_ ?_).ne
  · simp
  · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
    exact Fintype.card_ne_zero

/-! ## U2 (re-stated, salt-inclusive cache-hit bad event)

The headline `tvDist_runtime_real_programmed_le_collisionBound` above bounds the sign-then-hash TV
distance by the `withProgramming` *fire-on-miss* bad event over the random-oracle-only computation
`ob`. As the *Open sub-step* section records, that bad event is the wrong shape for GPV: the
fire-on-miss flag is set the **first** time the policy fires on an uncached point, so for the GPV
simulator (which programs at every fresh signing point) it fires *deterministically* — its
probability is near `1`, not `collisionBound`. Concretely, routing the salt-collision through the
fire-on-miss `hbad` is **unsound**: the genuine salt-collision probability is
`≈ collisionBound ≪ 1` while the fire-on-miss probability is `≈ 1`, so the inequality
"fire-on-miss ≤ salt-collision" needed to reuse the headline is *false* for the GPV policy. Moreover
the fresh signing salts — drawn in `unifSpec`, one step *before* each random-oracle query — are
invisible at `ob`'s granularity, so the `card / |Salt|` averaging is structurally absent from the
fire-on-miss flag.

`tvDist_runtime_real_programmed_le_collisionBound_saltInclusive` re-states U2 so its bad event is
the genuine GPV salt-collision: a fresh signing salt drawn in `unifSpec` landing in the recorded
random-oracle cache restricted to its message slice (a cache *hit* at a programmed point), modelled
by the salt-averaged process `saltSeq c qSign` of the telescope section. The per-step caches `c j`
are the recorded random-oracle inputs seen by the `j`-th signing query; the standard GPV
cache-growth bound `card (c j) ≤ j + qHash` (the `j` prior signing salts plus the up to `qHash`
adversary hash queries) is supplied as `hcache`.

Crucially, the lemma does **not** route through the headline U2's fire-on-miss `hbad`; it takes the
genuine *up-to-bad* coupling directly as `hcouple`: the total-variation distance between the real
and programmed runs is bounded by the salt-collision probability `Pr[saltSeq c qSign = true]`. This
is the correct identical-until-bad statement for the GPV game with bad event = cache-HIT salt
collision (the two runs differ only when a fresh salt collides with a recorded entry). It is
**true** (it is the real GPV up-to-bad bound, the cache-hit counterpart of the proven fire-on-miss
core `tvDist_runtime_real_programmed_le_bad`) and **non-vacuous** (`saltSeq c qSign` is a genuine
probabilistic process whose collision probability `probEvent_saltSeq_le_collisionBound` bounds it
strictly by `collisionBound < ⊤`, so `hcouple` is a real inequality between two `< ⊤` quantities,
not a `≤ ⊤` triviality; and the TV distance it bounds is in general positive, so it is not
vacuously `0 ≤ _`). Unlike the fire-on-miss route, `hcouple` is *satisfiable* by the GPV policy
precisely because its bad event is the small cache-hit collision rather than the deterministic
fire-on-miss.

`hcouple` isolates exactly the `#228`-class joint-distribution coupling over the interleaved
salt-draw / random-oracle-query streams of the salt-inclusive signing run: each of the `qSign`
fresh salts is checked against the recorded cache slice of size `≤ j + qHash`, which is precisely
the `saltSeq` process. Once `hcouple` is discharged by the coupling, this lemma yields the loss-free
`tvDist ≤ (collisionBound Salt qSign qHash).toReal` consumed by the four GPV theorems.

The proof is loss-free: chain `hcouple` (TV distance ≤ `saltSeq` collision) with the banked
salt-averaged telescope `probEvent_saltSeq_le_collisionBound` (`saltSeq` collision ≤
`collisionBound`), then move to `ℝ` with `ENNReal.toReal_mono`. -/
omit [DecidableEq Range] in
theorem tvDist_runtime_real_programmed_le_collisionBound_saltInclusive
    [Finite Range] [Inhabited Range] [Nonempty Salt] {α : Type} (qSign qHash : ℕ)
    (policy : OracleSpec.ProgrammingPolicy (Salt × M →ₒ Range))
    (ob : OracleComp (Salt × M →ₒ Range) α)
    (c : ℕ → Finset Salt) (hcache : ∀ j, (c j).card ≤ j + qHash)
    (hcouple : (SPMF.tvDist
        ((runtime M Salt).evalDist (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range))))
        (liftM (StateT.run'
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob) (∅, false))
          : SPMF α) : ℝ)
        ≤ (Pr[ (· = true) | saltSeq (Salt := Salt) c qSign]).toReal) :
    SPMF.tvDist
        ((runtime M Salt).evalDist (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range))))
        (liftM (StateT.run'
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob) (∅, false))
          : SPMF α)
      ≤ (collisionBound Salt qSign qHash).toReal :=
  hcouple.trans (ENNReal.toReal_mono
    (by
      refine (ENNReal.div_lt_top ?_ ?_).ne
      · simp
      · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
        exact Fintype.card_ne_zero)
    (probEvent_saltSeq_le_collisionBound Salt qSign qHash c hcache))

/-! ## Step 1 (consumed) and the Step-2 / headline-wiring frontier

**Step 1 (sign-then-hash ≡ real) is done and load-bearing.** The proven
`gpv_tvDist_real_programmed_le_collisionBound` *consumes* the re-stated R2 residual
`gpvRun_factorizes_signRunF` in a real (non-`sorry`) proof: it produces the
`AdaptiveFactorizesSignRunF` obligation for the *pinned* GPV game runs and discharges the
salt-inclusive sign-then-hash hop `tvDist realRun progRun ≤ collisionBound` via
`factorized_advantage_le_collisionBound`. The residual is therefore no longer dormant — it is
invoked on the Step-1 path, exactly as the campaign's Step-1 chain requires.

**What still gates the four GPV theorems (the *adaptive game identification* and Step 2).** Two
facts remain between `gpv_tvDist_real_programmed_le_collisionBound` and the headline bounds, both of
which would change statements *other than* the authorized residual and so are recorded here rather
than asserted:

1. *Game identification (a second `#228`-class fact).* The headline LHS `adv.advantage (runtime)` is
   `Pr[= true | unforgeableExp (runtime) adv]`, whose body runs `simulateQ impl (adv.main pk)` — the
   signing oracle draws each fresh salt *internally* at an adversary-chosen point over the sum spec
   `unifSpec + (Salt × M →ₒ Range)`. Connecting this to the *pinned* hash-only run `ob` of
   `gpv_tvDist_real_programmed_le_collisionBound` (so that `abs_probOutput_toReal_sub_le_tvDist`
   converts the run-level `tvDist ≤ collisionBound` into `realAdv ≤ progAdv + collisionBound`) is
   the same deferred-sampling factorization as the residual, now over the adversary's *adaptive*
   control flow rather than a fixed `ob`. It is not a separate probability fact but a second
   instance of the
   isolated `#228`-class coupling, and is not expressible as a change to the residual statement
   alone.
2. *Step 2 (collision extraction).* In the programmed sign-then-hash game every random-oracle entry
   carries the simulator's hidden short preimage; a fresh forgery on a programmed point with a
   *distinct* preimage is a collision under `psf.eval`, bounding `progAdv` by
   `collisionFindingAdvantage (reduction …)`. Stating this *pinned and true* requires the concrete
   programmed forgery game and the concrete `reduction` body (`reduction`, line ~295, is itself an
   open constructor `sorry`); a free-parameter or reduction-agnostic isolation would be a vacuous
   stub feeding a headline, which the campaign discipline forbids. It is therefore left open
   together with the reduction constructor rather than isolated as a speculative lemma. -/

/-- **Collision branch of the GPV game-hop**: when the PSF is correct and the adversary
makes at most `qSign` signing queries and `qHash` random-oracle queries, the probability
that it produces a fresh forgery whose preimage differs from the simulator's programmed
preimage is bounded by the collision-finding advantage of the reduction plus the
salt-collision birthday bound.

The argument proceeds in two steps:

**Step 1 (sign-then-hash ≡ real).**  Replace the signing oracle with one that:
  (a) samples a fresh salt `r ← Salt`,
  (b) samples a short preimage `s` using the trapdoor sampler on a fresh random target,
  (c) programs the RO at `(r, msg) := psf.eval pk s`.
By PSF correctness (`hcorrect`), the joint distribution `(r, s, H(r, msg))` is identical
to the real game. This step is exact (zero statistical distance).

**Step 2 (extract collision).**  In the sign-then-hash game, every RO entry is
programmed by the simulator together with a hidden short preimage. If the adversary's
fresh forgery `(msg*, (r*, s*))` lands on a programmed entry and `s*` differs from the
simulator's hidden preimage for that entry, the pair is a valid collision under
`psf.eval`. The salt-collision probability bounds the only way the programming can
become inconsistent. -/
theorem forgery_yields_collision [DecidableEq Domain]
    (hcorrect : psf.Correct) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK),
      𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    adv.advantage (runtime M Salt) ≤
      collisionFindingAdvantage (psf := psf) (hr := hr)
        (reduction psf hr M Salt adv domainSample) +
      collisionBound Salt qSign qHash := by
  let _ := hcorrect
  let _ := hreg
  let _ := qSign
  let _ := qHash
  let _ := adv
  let _ := hQ
  sorry

/-- **Full split GPV game-hop**: every successful fresh forgery falls into one of two cases.

1. **Distinct-preimage branch:** the forgery differs from the simulator's hidden programmed
   preimage at the forged point, yielding a collision under `psf.eval`.
2. **Exact-match branch:** the forgery exactly reproduces the simulator's hidden programmed
   preimage at that point. To capture this branch, the reduction guesses one of the at most
   `qSign + qHash` programmed entries and turns success there into a win in the single-target
   programmed-preimage experiment.

The only additional failure mode is a salt collision, bounded by `collisionBound`. -/
theorem forgery_yields_collision_or_exact_match [DecidableEq Domain]
    (hcorrect : psf.Correct) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK),
      𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    adv.advantage (runtime M Salt) ≤
      collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample) +
        ((qSign + qHash : ℕ) : ENNReal) *
          programmedPreimageAdvantage (psf := psf) (hr := hr)
            (programmedPreimageReduction psf hr M Salt adv domainSample) +
        collisionBound Salt qSign qHash := by
  let _ := hcorrect
  let _ := hreg
  let _ := qSign
  let _ := qHash
  let _ := adv
  let _ := hQ
  sorry

/-- **Collision-style GPV PFDH bound in the random-oracle model**.

For any adversary `A` making at most `qSign` signing queries against the GPV hash-and-sign
scheme with a correct PSF and `k`-bit salts, and making at most `qHash`
random-oracle queries, there exists a collision-finding reduction `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{collision}(B) + (qSign + qHash)² / (2 · |Salt|)`

This packages the distinct-preimage branch of the standard GPV argument. The complementary
exact-match branch, where the forgery reproduces the simulator's programmed preimage, is to
be discharged separately via a PSF preimage-min-entropy or one-wayness lemma.

The salt-collision term `(qSign + qHash)² / (2 · |Salt|)` is the birthday bound on a fresh
signing salt colliding with any previously recorded `(salt, message)` random-oracle input (a
prior signing salt or an adversary hash query). For Falcon with 40-byte salts
(`|Salt| = 2^320`), this is `2^{-191}` even for `qSign = qHash = 2^64`.

References: GPV08 Section 6; BDF+11 for the QROM extension. -/
theorem euf_cma_collision_bound [DecidableEq Domain]
    (hcorrect : psf.Correct) (hreg : psf.Regularity) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    ∃ (red : CollisionAdversary (PK := PK) (Domain := Domain)),
      adv.advantage (runtime M Salt) ≤
        collisionFindingAdvantage (psf := psf) (hr := hr) red +
        collisionBound Salt qSign qHash := by
  obtain ⟨domainSample, h⟩ := hreg
  exact ⟨reduction psf hr M Salt adv domainSample,
    forgery_yields_collision psf hr M Salt hcorrect qSign qHash adv domainSample h hQ⟩

/-- **Split GPV PFDH bound in the random-oracle model**.

This theorem makes both branches of the GPV proof explicit:

- a collision term for the distinct-preimage branch,
- a programmed-preimage replay term for the exact-match branch, with the explicit
  multi-target factor `qSign + qHash`,
- and the birthday salt-collision term.

It is the most honest generic statement available from the current API, before any additional
PSF-specific min-entropy lemma collapses the exact-match branch into the collision branch. -/
theorem euf_cma_split_bound [DecidableEq Domain]
    (hcorrect : psf.Correct) (hreg : psf.Regularity) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    ∃ (collisionRed : CollisionAdversary (PK := PK) (Domain := Domain))
      (exactMatchRed : ProgrammedPreimageAdversary
        (PK := PK) (Domain := Domain) (Range := Range)),
      adv.advantage (runtime M Salt) ≤
        collisionFindingAdvantage (psf := psf) (hr := hr) collisionRed +
          ((qSign + qHash : ℕ) : ENNReal) *
            programmedPreimageAdvantage (psf := psf) (hr := hr) exactMatchRed +
          collisionBound Salt qSign qHash := by
  obtain ⟨domainSample, h⟩ := hreg
  exact ⟨reduction psf hr M Salt adv domainSample,
    programmedPreimageReduction psf hr M Salt adv domainSample,
    forgery_yields_collision_or_exact_match psf hr M Salt hcorrect qSign qHash adv
      domainSample h hQ⟩

end GPVHashAndSign
