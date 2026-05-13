/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.AsymmEncAlg.Defs
import VCVio.CryptoFoundations.HardnessAssumptions.OneWay
import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.Append

/-!
# Bellare-Rogaway 1993 Encryption

This file sets up the Bellare-Rogaway 1993 public-key encryption construction from:

- a trapdoor permutation `f(pk, ·)` over a randomness space `Rand`
- a hash/random oracle `H : Rand → M`
- an additive message space `M`

Encryption samples `r ← Rand` and returns `(f(pk, r), H(r) + m)`. Decryption inverts the
trapdoor permutation and unmasks by subtraction.

The security proof follows the standard three-step outline:

1. Real CPA game.
2. Replace the challenge hash query with a fresh uniform mask, up to the bad event that the
   adversary queries the hidden `r`.
3. Replace the masked challenge message with a uniform ciphertext component, yielding success
   probability `1/2`.

The bad event is then reduced to the repo's trapdoor-preimage experiment
(`tdpAdvantage`) by inspecting the adversary's random-oracle queries. The proof
bodies remain `sorry` for now.
-/

open OracleComp OracleSpec ENNReal OneWay

namespace BR93

variable {PK SK Rand M : Type}
variable [Inhabited Rand] [Fintype Rand] [DecidableEq Rand] [SampleableType Rand]
variable [Inhabited M] [Fintype M] [DecidableEq M] [SampleableType M] [AddCommGroup M]

/-- The concrete BR93 scheme instantiated with an explicit hash function `hash : Rand → M`. -/
@[simps!] def br93AsymmEnc (tdp : TrapdoorPermutation PK SK Rand) (hash : Rand → M) :
    AsymmEncAlg ProbComp (M := M) (PK := PK) (SK := SK) (C := Rand × M) where
  keygen := tdp.keygen
  encrypt pk msg := do
    let r ← $ᵗ Rand
    return (tdp.forward pk r, hash r + msg)
  decrypt sk c :=
    return (some (c.2 - hash (tdp.inverse sk c.1)))

namespace br93AsymmEnc

variable {tdp : TrapdoorPermutation PK SK Rand} {hash : Rand → M}

omit [Inhabited Rand] [Fintype Rand] [DecidableEq Rand] [Inhabited M] [Fintype M]
  [SampleableType M] in
/-- Correctness of BR93 follows from correctness of the underlying trapdoor permutation. -/
theorem correct (hcorrect : tdp.Correct) :
    (br93AsymmEnc (M := M) tdp hash).PerfectlyCorrect ProbCompRuntime.probComp := by
  intro msg
  let mx : ProbComp Bool := do
    let x ← tdp.keygen
    let c ← (do let r ← $ᵗ Rand; pure (tdp.forward x.1 r, hash r + msg))
    let msg' ← pure (some (c.2 - hash (tdp.inverse x.2 c.1)))
    pure (decide (msg' = some msg))
  change Pr[= true | ProbCompRuntime.probComp.evalDist mx] = 1
  simp only [mx]
  have huniq : ∀ y ∈ support mx, y = true := by
    intro y hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨⟨pk, sk⟩, hpksk, hy⟩ := hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨c, hc, hy⟩ := hy
    rw [mem_support_bind_iff] at hc
    obtain ⟨r, _, hc⟩ := hc
    simp only [support_pure, Set.mem_singleton_iff] at hc hy
    subst hc; subst hy
    simp [hcorrect pk sk hpksk r]
  change Pr[= true | mx] = 1
  exact probOutput_eq_one_of_support_subset_singleton
    (NeverFail.probFailure_eq_zero (mx := mx)) huniq

/-! ## One-time IND-CPA in the random-oracle model -/

/-- The shared oracle interface for BR93 games: unrestricted uniform sampling plus a
lazy random oracle `Rand → M`. -/
abbrev RO_Spec (Rand M : Type) := unifSpec + (Rand →ₒ M)

/-- A one-time CPA adversary for BR93. Both phases share access to the same random oracle. -/
structure CPA_Adv where
  State : Type
  choose : PK → OracleComp (RO_Spec Rand M) (M × M × State)
  guess : State → Rand × M → OracleComp (RO_Spec Rand M) Bool

/-- Shared implementation of the BR93 random-oracle world: the left component handles uniform
sampling, while the right component is a lazy random oracle on `Rand → M`. -/
private def roQueryImpl :
    QueryImpl (RO_Spec Rand M) (StateT ((Rand →ₒ M).QueryCache) ProbComp) :=
  let ro : QueryImpl (Rand →ₒ M) (StateT ((Rand →ₒ M).QueryCache) ProbComp) := randomOracle
  let idImpl := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT ((Rand →ₒ M).QueryCache) ProbComp)
  idImpl + ro

/-- Lift a `ProbComp` computation into the BR93 random-oracle world. -/
private def liftProbComp {α : Type} (px : ProbComp α) : OracleComp (RO_Spec Rand M) α :=
  px

/-- Real one-time CPA game in the random-oracle model. -/
def cpaGame (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) : ProbComp Bool :=
  (simulateQ roQueryImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
    let b ← liftProbComp ($ᵗ Bool)
    let (pk, _sk) ← liftProbComp tdp.keygen
    let (m₁, m₂, st) ← adv.choose pk
    let r ← liftProbComp ($ᵗ Rand)
    let h : M ← (RO_Spec Rand M).query (Sum.inr r)
    let c : Rand × M := (tdp.forward pk r, h + if b then m₁ else m₂)
    let b' ← adv.guess st c
    return (b == b'))).run' ∅

/-- Game 1: replace the challenge hash value with a fresh uniform mask. The adversary still
interacts with the same lazy random oracle, so this only changes the game if it queries the
hidden challenge randomness `r`. -/
def game1 (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) : ProbComp Bool :=
  (simulateQ roQueryImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
    let b ← liftProbComp ($ᵗ Bool)
    let (pk, _sk) ← liftProbComp tdp.keygen
    let (m₁, m₂, st) ← adv.choose pk
    let r ← liftProbComp ($ᵗ Rand)
    let h ← liftProbComp ($ᵗ M)
    let c : Rand × M := (tdp.forward pk r, h + if b then m₁ else m₂)
    let b' ← adv.guess st c
    return (b == b'))).run' ∅

/-- Game 2: after replacing the challenge hash with a uniform mask, translation by the
challenge message preserves uniformity, so the challenge ciphertext no longer depends on `b`. -/
def game2 (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) : ProbComp Bool :=
  do
    let b ← ($ᵗ Bool)
    let b' ← (simulateQ roQueryImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
      let (pk, _sk) ← liftProbComp tdp.keygen
      let (_m₁, _m₂, st) ← adv.choose pk
      let r ← liftProbComp ($ᵗ Rand)
      let h ← liftProbComp ($ᵗ M)
      let c : Rand × M := (tdp.forward pk r, h)
      adv.guess st c)).run' ∅
    return (b == b')

/-- Bad event for the Game 0 → Game 1 hop: the adversary queries the random oracle at the
hidden challenge randomness `r`. -/
def badEventExp (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) : ProbComp Bool := do
  let loggedRun :
      StateT ((Rand →ₒ M).QueryCache) ProbComp
        (Rand × QueryLog (RO_Spec Rand M)) :=
    (simulateQ roQueryImpl.withLogging <| (show OracleComp (RO_Spec Rand M) Rand from do
      let (pk, _sk) ← liftProbComp tdp.keygen
      let (m₁, m₂, st) ← adv.choose pk
      let b ← liftProbComp ($ᵗ Bool)
      let r ← liftProbComp ($ᵗ Rand)
      let h ← liftProbComp ($ᵗ M)
      let c : Rand × M := (tdp.forward pk r, h + if b then m₁ else m₂)
      let _b' ← adv.guess st c
      return r)).run
  let (r, log) ← loggedRun.run' ∅
  return decide (log.any fun entry => match entry.1 with
    | Sum.inl _ => false
    | Sum.inr r' => r' = r)

/-- Probability of the bad event. -/
noncomputable def badEventProb (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) : ℝ :=
  (Pr[= true | badEventExp tdp adv]).toReal

/-- Inversion reduction: run the BR93 adversary in the idealized challenge game, log its
random-oracle queries, and return the first query whose image under the trapdoor permutation
matches the challenge `y`. -/
def inverter (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) : TDPAdversary PK Rand :=
  fun pk y => do
    let loggedRun :
        StateT ((Rand →ₒ M).QueryCache) ProbComp
          (Unit × QueryLog (RO_Spec Rand M)) :=
      (simulateQ roQueryImpl.withLogging <| (show OracleComp (RO_Spec Rand M) Unit from do
        let (m₁, m₂, st) ← adv.choose pk
        let b ← liftProbComp ($ᵗ Bool)
        let h ← liftProbComp ($ᵗ M)
        let c : Rand × M := (y, h + if b then m₁ else m₂)
        let _b' ← adv.guess st c
        return ())).run
    let (_result, log) ← loggedRun.run' ∅
    match log.find? (fun entry => match entry.1 with
      | Sum.inl _ => false
      | Sum.inr r => tdp.forward pk r = y) with
    | some entry =>
        match entry.1 with
        | Sum.inl _ => return default
        | Sum.inr r => return r
    | none => return default

omit [Fintype Rand] [Fintype M] [DecidableEq M] in
/-- Up-to-bad step: replacing the challenge hash query with a fresh uniform mask changes the
game by at most the bad-event probability.

**Proof outline.** Up-to-bad lemma between `cpaGame` (where the challenge hash is `RO(r)`,
cached) and `game1` (where the challenge hash is fresh uniform, not cached). The two games
diverge only when the adversary subsequently queries the RO at the hidden `r`.

Strategy:
1. Couple the RO state between the two games: identical on all entries except possibly `r`.
2. Show that conditioned on "adversary never queries `r`", the games are perfectly coupled,
   so their indicator functions agree.
3. Bound the failure-of-coupling probability by `Pr[adversary queries r]`, which is
   `badEventProb` (the bad event is defined exactly as "RO log contains an entry at `r`").
4. Standard up-to-bad gives `|Pr[cpa] - Pr[game1]| ≤ Pr[bad]`.

Tools likely needed:
- A coupling/identical-until-bad lemma for `withLogging` / `randomOracle` (may need to add).
- `probEvent_diff_le_probEvent_bad` style lemma at SPMF/ProbComp level. -/
theorem cpaGame_gap_le_badEvent (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    |(Pr[= true | cpaGame tdp adv]).toReal -
      (Pr[= true | game1 tdp adv]).toReal| ≤
      badEventProb tdp adv := by
  sorry

omit [Fintype Rand] [Fintype M] [DecidableEq M] in
/-- Uniform masking step: once the challenge hash output is replaced by a fresh uniform mask,
adding either challenge message yields the same ciphertext distribution.

**Proof outline.** Distribution equality between `game1` and `game2`. Two structural
differences:
- `game1` samples `b ← uniform Bool` *inside* the `simulateQ` block; `game2` samples `b`
  *outside* the simulation.
- `game1` computes `c.2 = h + (if b then m₁ else m₂)`; `game2` computes `c.2 = h`.

Strategy:
1. **Translation invariance of uniform `M`.** Since `M` is `AddCommGroup` and `h ← $ᵗ M`,
   for any fixed `x : M`, `h + x` has the same distribution as `h`. The relevant lemma is
   `evalDist_add_right_uniform` (or its bind form `probOutput_bind_add_right_uniform`).
2. **Commuting `b` out of the simulation.** `b` is independent of the RO state and only
   used to select `if b then m₁ else m₂`. Once the addition is eliminated (step 1), `b`
   no longer enters the inner simulation at all — only into the final `(b == b')` return.
   By independence, we can pull `b ← $ᵗ Bool` to the outermost position.
3. **Match game2's structure.** After steps 1-2, game1's structure becomes:
   `do let b ← $ᵗ Bool; let b' ← (simulation without b); return (b == b')`, which is
   exactly `game2`'s shape.

Tools available in-repo:
- `evalDist_add_right_uniform [AddGroup α] (m : α)` at `SampleableType.lean:174`.
- `probOutput_bind_add_right_uniform` (bind form).
- `simulateQ_bind` for pushing `simulateQ` through `do`-block binds.
- `evalDist_ext` for pointwise equality.

The challenge is that the uniform-`h` sample is *inside* a `simulateQ roQueryImpl` block,
not a raw `ProbComp`. We need a lemma that lets us push `evalDist` through `simulateQ`
and `.run' ∅` to apply the `ProbComp`-level translation lemma. -/
theorem game1_eq_game2 (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    𝒟[game1 tdp adv] = 𝒟[game2 tdp adv] := by
  sorry

omit [Fintype Rand] [Inhabited M] [Fintype M] [DecidableEq M] [AddCommGroup M] in
/-- In the all-random game, the challenge ciphertext is independent of the hidden bit, so the
adversary succeeds with probability exactly `1/2`. -/
theorem game2_eq_half (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    Pr[= true | game2 tdp adv] = 1 / 2 := by
  let f : Bool → ProbComp Bool := fun _ =>
    (simulateQ roQueryImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
      let (pk, _sk) ← liftProbComp tdp.keygen
      let (_m₁, _m₂, st) ← adv.choose pk
      let r ← liftProbComp ($ᵗ Rand)
      let h ← liftProbComp ($ᵗ M)
      let c : Rand × M := (tdp.forward pk r, h)
      adv.guess st c)).run' ∅
  simpa [game2, f] using
    (probOutput_decide_eq_uniformBool_half f (by rfl))

omit [Fintype Rand] [Fintype M] [DecidableEq M] in
/-- The bad event is bounded by the trapdoor-preimage advantage of the inverter
constructed from the adversary's random-oracle transcript.

**Proof outline.** The `inverter` runs the adversary in a game where the challenge ciphertext
uses `y` (the TDP challenge) directly as the first component, then searches the adversary's
RO query log for an `r'` with `tdp.forward pk r' = y`.

Strategy:
1. **Distribution alignment.** In `badEventExp`, `y := tdp.forward pk r` for uniform `r`.
   In `tdpAdvantage`, `y := tdp.forward pk r` for uniform `r` (the TDP challenge sampler).
   By `TrapdoorPermutation` being a bijection on `Rand`, the marginal distribution of `y`
   is the same in both experiments.
2. **Adversary view equivalence.** In `badEventExp`, the adversary sees a ciphertext built
   from `y` (the trapdoor of `r`) and `h + if b then m₁ else m₂` (with `h` uniform).
   In the `inverter`'s simulation, the adversary sees exactly the same data: `(y, h + ...)`
   with `y` from the outside challenge and `h` uniform. So the adversaries' RO query logs
   have identical distributions.
3. **Bad event implies inverter success.** The bad event fires iff the RO log contains an
   entry at `r`. Since `r` is the unique preimage of `y` under `tdp.forward pk`, the
   inverter's `log.find?` returns this `r`, and `tdp.forward pk r = y` (the success
   predicate of the TDP experiment).
4. **Probability comparison.** Therefore
   `Pr[bad event] ≤ Pr[inverter outputs an r with tdp.forward pk r = y] = tdpAdvantage`.

Tools likely needed:
- A `TrapdoorPermutation.bijective` lemma (or `forward_uniform_eq_uniform`).
- `simulateQ_withLogging` interaction lemmas (the log shape factoring out of the simulation).
- `List.find?` reasoning to relate "log contains entry at `r`" to "inverter outputs the
  right preimage". -/
theorem badEventProb_le_tdpAdvantage (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    badEventProb tdp adv ≤
      (tdpAdvantage tdp (inverter tdp adv)).toReal := by
  sorry

omit [Fintype Rand] [Fintype M] [DecidableEq M] in
/-- Main BR93 bound for this file's custom one-time ROM CPA game: the distinguishing
bias is bounded by the trapdoor-preimage advantage via the standard up-to-bad
reduction. -/
theorem indcpa_bound (adv : CPA_Adv (PK := PK) (Rand := Rand) (M := M)) :
    |(Pr[= true | cpaGame tdp adv]).toReal - 1 / 2| ≤
      (tdpAdvantage tdp (inverter tdp adv)).toReal := by
  have hg12 : Pr[= true | game1 tdp adv] = Pr[= true | game2 tdp adv] :=
    congr_fun (congr_arg _ (game1_eq_game2 adv)) true
  calc |(Pr[= true | cpaGame tdp adv]).toReal - 1 / 2|
      = |(Pr[= true | cpaGame tdp adv]).toReal -
          (Pr[= true | game1 tdp adv]).toReal| := by
        congr 1; rw [hg12, game2_eq_half adv]; norm_num
    _ ≤ badEventProb tdp adv := cpaGame_gap_le_badEvent adv
    _ ≤ (tdpAdvantage tdp (inverter tdp adv)).toReal :=
        badEventProb_le_tdpAdvantage adv

end br93AsymmEnc

end BR93
