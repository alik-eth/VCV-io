/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.DirectCoupling.SharpTagSlotPositive

/-!
# PRF Tag/Reader Protocol — Sharp Direct-Coupling Headline

The sharp lazy-form multiple-vs-single ideal-world bound
`multipleIdeal_le_singleIdeal_add_bad_DC_sharp`: the multiple-session ideal world is bounded by
the single-session ideal world plus the multiple-bad collision probability and three slack
terms, for every adversary and with no distinctness hypothesis on its reader nonces. The three
positions of the statement are the *same experiments* as in the sibling
`multipleIdeal_le_singleIdeal_add_bad_DC`; only the slack terms differ:

* fire `qReader · |TagId| / (|Digest| - qReader)` versus the sibling's
  `qReader · |TagId| / |Digest|`;
* tilt `qTag · qReader / (|Nonce| · |Digest|)` versus the sibling's `qReader · qTag / |Nonce|`
  — smaller by the factor `|Digest|`, the payoff of the sharp coupling;
* discard `qReader · |TagId| · sessionsPerTag / (|Digest| - qReader)` versus the sibling's
  `qReader · |TagId| · sessionsPerTag / |Digest|`.

The sharp tilt term is always at most the sibling's tilt term, while the sharp fire and
discard terms exceed the sibling's by the factor `|Digest| / (|Digest| - qReader)` (at most `2`
once `2 · qReader ≤ |Digest|`). Neither theorem derives the other in degenerate regimes — at
`qReader ≥ |Digest|` the sharp denominators vanish while the sibling bound stays finite, and
for `qReader ≪ |Digest| ≪ |Nonce|`-style parameters the sharp tilt is strictly smaller — so
both statements are kept as canonical.

The proof instantiates the sharp coupling induction `sharpCoupling_aux` at the initial
knowledge state `ProbeState.init` (every cell `excluded ∅`, all six invariant conjuncts
trivial) and the full reader budget `qRInit = qR = qReader`, and identifies the initial
consistent-table distribution with the uniform table draw (`evalDist_genTable_init`); the
remaining moves are the eagerization bridges shared with the sibling headline.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section SharpCompose

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

namespace UnlinkReduction

/-! ### The initial knowledge state

At `ProbeState.init` every cell is `excluded ∅`, so the six conjuncts of the sharp coupling
invariant hold trivially and the consistent-table distribution is the uniform table draw. -/

omit [DecidableEq TagId] [Fintype TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest] in
/-- Every cell of the initial knowledge state is undetermined. -/
private lemma slotPosExcluded_init :
    slotPosExcluded (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest) :=
  fun _ _ _ _ => ⟨∅, rfl⟩

omit [DecidableEq TagId] [Fintype TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest] in
/-- Every cell of the initial knowledge state is fresh. -/
private lemma liveSlotsFresh_init :
    liveSlotsFresh (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest)
      (UnlinkState.init (TagId := TagId)) :=
  fun _ _ _ _ _ => rfl

omit [DecidableEq TagId] [Fintype TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest] in
/-- The initial knowledge state has no determined cell, so `knownRecorded` holds vacuously. -/
private lemma knownRecorded_init :
    knownRecorded (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest)
      (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) := by
  intro tag n v h
  simp [ProbeState.init] at h

omit [DecidableEq TagId] [Fintype TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest] in
/-- The initial knowledge state carries no exclusions, so every row potential vanishes. -/
private lemma slotZeroRowExcl_init_le [Fintype Nonce] (m : ℕ) (tag : TagId) :
    slotZeroRowExcl (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest) tag
      ≤ m := by
  simp [slotZeroRowExcl, ProbeState.init]

/-! ### From the initial consistent table to the uniform table draw -/

omit [SampleableType Nonce] [NeZero sessionsPerTag] in
/-- Output probabilities of a computation seeded by the initial consistent table coincide with
those of the same computation seeded by a uniform table. -/
private lemma probOutput_genTable_init_bind_liftM [Fintype Nonce] [Fintype Digest]
    {β : Type} (A : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp β) (b : β) :
    Pr[= b | (genTable (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest) >>=
        fun gS => liftM (A gS) : OptionT ProbComp β)]
      = Pr[= b | ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= A] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun gS => ?_
  have h1 : Pr[= gS | (genTable (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce)
        Digest) : OptionT ProbComp _)]
      = Pr[= gS | ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest) : ProbComp _)] := by
    rw [probOutput_def, probOutput_def, evalDist_genTable_init]
  rw [h1, OptionT.probOutput_liftM]

omit [SampleableType Nonce] [NeZero sessionsPerTag] in
/-- Event probabilities of a computation seeded by the initial consistent table coincide with
those of the same computation seeded by a uniform table. -/
private lemma probEvent_genTable_init_bind_liftM [Fintype Nonce] [Fintype Digest]
    {β : Type} (A : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp β)
    (p : β → Prop) :
    Pr[ p | (genTable (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest) >>=
        fun gS => liftM (A gS) : OptionT ProbComp β)]
      = Pr[ p | ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= A] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun gS => ?_
  have h1 : Pr[= gS | (genTable (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce)
        Digest) : OptionT ProbComp _)]
      = Pr[= gS | ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest) : ProbComp _)] := by
    rw [probOutput_def, probOutput_def, evalDist_genTable_init]
  rw [h1, OptionT.probEvent_liftM]

/-! ### The sharp headline -/

/-- **Multi-to-single via the sharp direct coupling.** Bounds the multiple-session ideal world
by the single-session ideal world plus the multiple-bad collision probability and three slack
terms, for every adversary and with no distinctness hypothesis on its reader nonces. The three
probability positions are identical to those of the sibling
`multipleIdeal_le_singleIdeal_add_bad_DC`; the slacks differ:

* fire `qReader · |TagId| / (|Digest| - qReader)` — a reader probe genuinely hits a
  conditioned reference cell (sibling: denominator `|Digest|`);
* tilt `qTag · qReader / (|Nonce| · |Digest|)` — the averaged reveal-tilt of tag reveals at
  reader-probed reference cells (sibling: `qReader · qTag / |Nonce|`, larger by the factor
  `|Digest|`);
* discard `qReader · |TagId| · sessionsPerTag / (|Digest| - qReader)` — the single-session
  reader's slot-positive acceptance branch (sibling: denominator `|Digest|`).

The sharp tilt term never exceeds the sibling's, while the sharp fire and discard terms exceed
the sibling's by `|Digest| / (|Digest| - qReader)`; at `qReader ≥ |Digest|` the sharp bound
degenerates to `∞` while the sibling stays finite. Neither theorem subsumes the other.

Proved by running both worlds against one consistent table drawn from the probe knowledge
state of the reader's Boolean probe history (`sharpCoupling_aux` at `ProbeState.init`), rather
than against a uniform table overlaid with a value cache. -/
theorem multipleIdeal_le_singleIdeal_add_bad_DC_sharp [Fintype Nonce] [Fintype Digest]
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag) :
    Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] ≤
      Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] +
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)] +
      ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) /
        ((Fintype.card Digest - qReader : ℕ) : ℝ≥0∞) +
      ((qTag * qReader : ℕ) : ℝ≥0∞) /
        ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) +
      ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        ((Fintype.card Digest - qReader : ℕ) : ℝ≥0∞) := by
  classical
  -- **Step 1.** Replace the multiple-ideal LHS by the multiple-bad LHS (same `Pr[= true]`).
  rw [← probOutput_multipleBad_run'_eq_multipleIdeal adversary
      (UnlinkState.init, (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache)) UnlinkBadState.init]
  -- **Step 2.** Eagerize the M-side: the lazy `multipleBadQueryImpl` run distribution equals the
  -- `$ᵗ gM`-then-eager-table form, modulo the `(z.1, z.2.2)` map projection.
  have hM := evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending
    (sessionsPerTag := sessionsPerTag) adversary
    UnlinkState.init (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) UnlinkBadState.init
  -- M-side success-term rewrite: factor `run' = (·.1) <$> run` through `(z.1, z.2.2) <$> run`.
  have hMsucc :
      Pr[= true | (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
          ((UnlinkState.init, (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache)),
            UnlinkBadState.init)] =
      Pr[= true | do
          let gM ← $ᵗ (TagId × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending
                (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) gM)) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] := by
    rw [probOutput_def, probOutput_def]
    have hlhs : (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
          ((UnlinkState.init, (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache)),
            UnlinkBadState.init) =
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.1) <$>
          ((fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
              ((UnlinkState.init, (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache)),
                UnlinkBadState.init)) := by
      rw [Functor.map_map]; rfl
    have hrhs : (do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending
              (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) gM)) adversary).run
            (UnlinkState.init, UnlinkBadState.init)) =
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.1) <$>
          (do
            let gM ← $ᵗ (TagId × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending
                  (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) gM)) adversary).run
                (UnlinkState.init, UnlinkBadState.init)) := by
      simp only [map_bind, Functor.map_map]
    rw [hlhs, hrhs, evalDist_map, evalDist_map, ← evalDist_map, hM, evalDist_map]
  -- M-side bad-term rewrite: factor `z.2.2.bad = (z.2.bad) ∘ (z.1, z.2.2)` and apply `hM`.
  have hMbad :
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending
              (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) gM)) adversary).run
            (UnlinkState.init, UnlinkBadState.init)] := by
    have hbadev :
        (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad = true) =
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.2.bad = true) ∘
          (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
            (z.1, z.2.2)) := rfl
    rw [hbadev, ← probEvent_map]
    exact probEvent_congr' (fun _ _ => Iff.rfl) hM
  -- **Step 3.** Eagerize the S-side success term to `$ᵗ gS >>= singleTableHandler gS`.
  rw [hMsucc, hMbad, probOutput_singleIdeal_run'_eq_tableSample adversary]
  -- Collapse `tableExtending ∅ g = g` on both M (over `TagId × Nonce`) and S (over the
  -- `(TagId × Fin sp) × Nonce` domain) sides.
  simp only [OracleComp.tableExtending_empty]
  -- **Step 4.** Bridge `$ᵗ (TagId × Nonce → Digest)` to
  -- `$ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)` via `slotZeroSubTable`. The bridge says:
  -- for any continuation `F`, the distribution of `$ᵗ gM >>= F gM` equals the distribution of
  -- `$ᵗ gS >>= F (slotZeroSubTable gS)`. We package this as a generic helper and apply it twice
  -- (once for the success term, once for the bad term).
  haveI : Nonempty Digest :=
    ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  have hbridge : ∀ {X : Type} (F : (TagId × Nonce → Digest) → ProbComp X),
      𝒟[($ᵗ (TagId × Nonce → Digest)) >>= F] =
      𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
            fun gS => F (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)] := by
    intro X F
    have hSZ :
        𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
              fun gS => pure (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)]
        = 𝒟[($ᵗ (TagId × Nonce → Digest))] :=
      evalDist_slotZeroSubTable_uniformSample
    have hR : (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
            fun gS => F (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS))
        = (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
            fun gS => pure (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) >>= F := by
      simp
    rw [hR, evalDist_bind, evalDist_bind, hSZ]
  -- M-success bridge.
  have hbridge_succ :
      Pr[= true | do
          let gM ← $ᵗ (TagId × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) gM) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] =
      Pr[= true | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] :=
    probOutput_congr rfl (hbridge _)
  -- M-bad bridge.
  have hbridge_bad :
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
          let gM ← $ᵗ (TagId × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) gM) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] :=
    probEvent_congr' (fun _ _ => Iff.rfl) (hbridge _)
  rw [hbridge_succ, hbridge_bad]
  -- **Step 4b.** Fine-shape bridges. The aux's signature carries an outer
  -- `gFine ← $ᵗ ((TagId × Fin sp) × Nonce → Digest)` binder and the Fine handler
  -- `multipleBadTableHandlerFine ... gFine`. Bridge the coarse-shape LHS-success and
  -- RHS-bad terms (the current goal shapes after `rw [hbridge_succ, hbridge_bad]`) to the
  -- Fine-shape via `evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_eq`.
  -- Per-`gS`, the bridge gives `𝒟[(π <$> gFine←$ᵗ; Fine.run p)] = 𝒟[coarse.run p]` where
  -- `π = fun z => (z.1, z.2.1, {z.2.2 with cacheBad := p.2.cacheBad})`. Both `Bool.fst` and the
  -- bad event `z.2.bad` factor through `π` (they ignore `cacheBad`).
  have hFineEq : ∀ (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest),
      𝒟[(fun z => (z.1, z.2.1, {z.2.2 with cacheBad :=
              (UnlinkBadState.init : UnlinkBadState TagId Nonce Digest).cacheBad})) <$>
            (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                    (UnlinkState.init, UnlinkBadState.init))]
        = 𝒟[(simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] := fun gS =>
    evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_eq
      (sessionsPerTag := sessionsPerTag)
      (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) adversary
      ((UnlinkState.init, UnlinkBadState.init) :
        UnlinkState TagId × UnlinkBadState TagId Nonce Digest)
  -- Apply the Fine bridge to the success term (event factors through π since π preserves `z.1`).
  have hsucc_fine :
      Pr[= true | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] =
      Pr[= true | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] := by
    -- `Pr[= true | oa] = probOutput oa true`. We convert to `probEvent (· = true)` via
    -- `probEvent_eq_eq_probOutput`, then use `probEvent_bind_congr'`.
    rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
    refine probEvent_bind_congr' _ _ ?_
    intro gS
    -- Per-gS: Pr[(b = true) | (z.1) <$> coarse.run] = Pr[(b = true) | gFine←$ᵗ; (z.1) <$> Fine.run]
    -- Push (z.1) into the inner gFine bind on the Fine side, then apply `probEvent_map` on
    -- both sides to expose `(z.1 = true)` as a precomposition.
    rw [probEvent_map]
    have hrhs :
        (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                  (UnlinkState.init, UnlinkBadState.init))
        = (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                  (UnlinkState.init, UnlinkBadState.init)) := by rw [map_bind]
    rw [hrhs, probEvent_map]
    -- Bridge via hFineEq: replace `coarse.run` with `π <$> (gFine←$ᵗ; Fine.run)`.
    have hbridge :
        Pr[(fun b : Bool => b = true) ∘
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) |
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] =
        Pr[(fun b : Bool => b = true) ∘
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) |
            (fun z => (z.1, z.2.1, {z.2.2 with cacheBad :=
                (UnlinkBadState.init : UnlinkBadState TagId Nonce Digest).cacheBad})) <$>
              (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                      (UnlinkState.init, UnlinkBadState.init))] := by
      rw [probEvent_def, probEvent_def, ← hFineEq gS]
    rw [hbridge, probEvent_map]
    -- Goal: Pr[(b=true) ∘ z.1 ∘ π | gFine←$ᵗ; Fine] = Pr[(b=true) ∘ z.1 | gFine←$ᵗ; Fine].
    -- (b=true) ∘ z.1 ∘ π = (b=true) ∘ z.1 pointwise (π preserves .1).
    exact probEvent_congr' (fun _ _ => Iff.rfl) rfl
  -- Apply the Fine bridge to the bad term. The bad event factors through π (cacheBad ≠ bad).
  -- Strategy: use `probEvent_bind_congr'` to reduce to a per-gS equality, then push the
  -- `(z.1, z.2.2)` map through `probEvent_map` to expose the `z.2.2.bad` predicate, then
  -- apply `hFineEq` after observing that the bad predicate is π-invariant.
  have hbad_fine :
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] := by
    refine probEvent_bind_congr' _ _ ?_
    intro gS
    -- Per-gS goal:
    --   Pr[bad | (z.1, z.2.2) <$> coarse.run]
    --   = Pr[bad | gFine←$ᵗ; (z.1, z.2.2) <$> Fine.run]
    -- Push the (z.1, z.2.2) map through `probEvent_map`:
    rw [probEvent_map]
    -- LHS now: Pr[bad ∘ (z.1, z.2.2) | coarse.run] = Pr[z.2.2.bad | coarse.run].
    -- For the RHS, push the (z.1, z.2.2) map into the inner bind:
    have hrhs :
        (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                  (UnlinkState.init, UnlinkBadState.init))
        = (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                  (UnlinkState.init, UnlinkBadState.init)) := by rw [map_bind]
    rw [hrhs, probEvent_map]
    -- Goal:
    --   Pr[bad ∘ (z.1, z.2.2) | coarse.run] = Pr[bad ∘ (z.1, z.2.2) | gFine←$ᵗ; Fine.run]
    -- which is Pr[z.2.2.bad | coarse.run] = Pr[z.2.2.bad | gFine←$ᵗ; Fine.run]. Express this
    -- via hFineEq: 𝒟[π <$> (gFine←$ᵗ; Fine.run)] = 𝒟[coarse.run]; the bad predicate is
    -- π-invariant.
    have hLHS_via_bridge :
        Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true) ∘
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) |
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] =
        Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true) ∘
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) |
            (fun z => (z.1, z.2.1, {z.2.2 with cacheBad :=
                (UnlinkBadState.init : UnlinkBadState TagId Nonce Digest).cacheBad})) <$>
              (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                      (UnlinkState.init, UnlinkBadState.init))] := by
      rw [probEvent_def, probEvent_def, ← hFineEq gS]
    rw [hLHS_via_bridge, probEvent_map]
    -- Goal: Pr[(bad ∘ (z.1, z.2.2)) ∘ π | gFine←$ᵗ; Fine] = Pr[bad ∘ (z.1, z.2.2) | gFine←$ᵗ; Fine]
    -- Both events agree pointwise (π only changes cacheBad; the event reads only `.2.bad`).
    exact probEvent_congr' (fun _ _ => Iff.rfl) rfl
  rw [hsucc_fine, hbad_fine]
  -- **Step 5.** Identify the three positions with the sharp experiments at the initial
  -- knowledge state and apply the sharp coupling induction.
  have hb1 : Pr[= true | sharpM adversary UnlinkState.init UnlinkBadState.init
      (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest)]
      = Pr[= true | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] := by
    have h := probOutput_genTable_init_bind_liftM (fun gS => ((do
      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
          (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
            (UnlinkState.init, UnlinkBadState.init)) : ProbComp Bool)) true
    exact h
  have hb2 : Pr[= true | sharpS adversary UnlinkState.init
      (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest)]
      = Pr[= true | ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gS =>
          (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS) adversary).run'
            UnlinkState.init] := by
    have h := probOutput_genTable_init_bind_liftM (fun gS =>
      (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS) adversary).run'
        UnlinkState.init) true
    exact h
  have hb3 : Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
      sharpBad adversary UnlinkState.init UnlinkBadState.init
        (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest)]
      = Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] := by
    have h := probEvent_genTable_init_bind_liftM (fun gS => ((do
      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          (z.1, z.2.2)) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
          (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
            (UnlinkState.init, UnlinkBadState.init)) :
        ProbComp (Bool × UnlinkBadState TagId Nonce Digest)))
      (fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad)
    exact h
  rw [← hb1, ← hb2, ← hb3]
  exact sharpCoupling_aux adversary qReader qReader qTag UnlinkState.init UnlinkBadState.init
    (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest) hqReader hqTag le_rfl
    slotPosExcluded_init liveSlotsFresh_init knownRecorded_init
    (ProbeState.exclLe_init.mono (Nat.zero_le _)) (slotZeroRowExcl_init_le _)
    ProbeState.feasible_init

/-- The sharp headline with the tilt term relaxed to `qTag / |Nonce|`: as soon as the reader
budget does not exceed the digest space, the averaged tilt `qTag · qReader / (|Nonce| · |Digest|)`
collapses to a per-tag-query charge independent of the reader budget. -/
theorem multipleIdeal_le_singleIdeal_add_bad_DC_sharp' [Fintype Nonce] [Fintype Digest]
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag)
    (hqD : qReader ≤ Fintype.card Digest) :
    Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] ≤
      Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] +
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)] +
      ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) /
        ((Fintype.card Digest - qReader : ℕ) : ℝ≥0∞) +
      (qTag : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        ((Fintype.card Digest - qReader : ℕ) : ℝ≥0∞) := by
  refine le_trans (multipleIdeal_le_singleIdeal_add_bad_DC_sharp adversary qReader qTag
    hqReader hqTag) ?_
  refine add_le_add (add_le_add (add_le_add (add_le_add le_rfl le_rfl) le_rfl) ?_) le_rfl
  calc ((qTag * qReader : ℕ) : ℝ≥0∞) /
        ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))
      = ((qTag : ℝ≥0∞) * (Fintype.card Nonce : ℝ≥0∞)⁻¹) *
        ((qReader : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹) := by
        rw [Nat.cast_mul, div_eq_mul_inv,
          ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
            (Or.inl (ENNReal.natCast_ne_top _))]
        ring
    _ ≤ ((qTag : ℝ≥0∞) * (Fintype.card Nonce : ℝ≥0∞)⁻¹) * 1 := by
        refine mul_le_mul' le_rfl ?_
        refine le_trans (mul_le_mul' (Nat.cast_le.mpr hqD) le_rfl) ?_
        exact ENNReal.mul_inv_le_one _
    _ = (qTag : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
        rw [mul_one, div_eq_mul_inv]

end UnlinkReduction

end SharpCompose

end PRFTagReader
