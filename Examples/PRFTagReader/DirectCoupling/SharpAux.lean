/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.DirectCoupling
import Examples.PRFTagReader.DirectCoupling.StepLemmas
import Examples.PRFTagReader.MultipleToHybrid.EagerSetup
import VCVio.EvalDist.Monad.BindCongr
import VCVio.EvalDist.Monad.Disagreement
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeColumn

/-!
# PRF Tag/Reader Protocol — Sharp Direct Coupling Over The Consistent-Table Distribution

The sharp form of the direct M_ideal/S_ideal coupling: both worlds read one shared table drawn
from the consistent-table distribution `genTable K` of a probe knowledge state `K` on the
single-session cell domain, instead of a uniformly drawn table overlaid with a value cache. The
knowledge state records, per cell, either a determined value (written by a tag step) or a finite
set of values excluded by reader probe misses — so a reader query conditions the table at the
*Boolean* level only, and the per-step coupling charges shrink accordingly.

## The experiments

`sharpM`, `sharpS`, and `sharpBad` are the three positions of the coupling at knowledge state
`K`: the instrumented multiple-session run projected to its output bit, the single-session run,
and the instrumented run projected to the output bit and bad state.

## The invariant

The induction threads six facts about `(K, s, sB)`, with all reader budgets accounted by
`qRInit`:

* `slotPosExcluded K` — slot-positive cells are never determined;
* `liveSlotsFresh K s` — slot-positive cells of not-yet-consumed sessions are untouched, so the
  single-session world's next reveal at any tag is a full uniform;
* `knownRecorded K sB` — every determined reference-slot cell has a recorded tag response, so a
  determined cell met by a tag step fires the `bad` flag;
* `ProbeState.ExclLe K (qRInit - qR)` — per-cell exclusion budget;
* `slotZeroRowExcl K tag ≤ qRInit - qR` — per-row exclusion potential, paying the averaged
  reveal tilt at tag steps;
* `K.Feasible` — every cell still admits a value.

## The bound

The assembled induction `sharpCoupling_aux` (in `DirectCoupling/SharpTagSlotPositive.lean`)
bounds the M-side success probability by the S-side success probability, the bad-flag
probability, and three slack terms:

* fire `qR · |TagId| / (|Digest| - qRInit)` — reader probes that genuinely hit;
* tilt `qT · qRInit / (|Nonce| · |Digest|)` — the averaged reveal-tilt of tag reveals at
  reader-probed columns;
* discard `qR · |TagId| · sessionsPerTag / (|Digest| - qRInit)` — the single-session reader's
  slot-positive acceptance branch.

The induction case proved here is the slot-zero tag case `sharpAux_tag_slotZero` — at a fresh
tag both worlds reveal the *same* reference cell of the shared table, so the step couples
exactly and charges nothing. The slot-positive tag case lives in
`DirectCoupling/SharpTagSlotPositive.lean`; the reader case `sharpAux_reader_step` is stated
with its final signature and proved separately.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

namespace UnlinkReduction

section SharpInvariant

variable {TagId Nonce Digest : Type} {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- Slot-positive cells of the knowledge state are never determined: reader probes touch only
reference-slot cells, and tag reveals at positive slots are normalized back to the reference
slot, parking only exclusion sets on the positive side. -/
def slotPosExcluded (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest) : Prop :=
  ∀ (tag : TagId) (sid : Fin sessionsPerTag), sid ≠ 0 → ∀ n : Nonce,
    ∃ S, K ((tag, sid), n) = CellKnowledge.excluded S

/-- Slot-positive cells of sessions not yet consumed are untouched: the single-session world's
next tag reveal draws from the full value range. -/
def liveSlotsFresh (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest)
    (s : UnlinkState TagId) : Prop :=
  ∀ (tag : TagId) (sid : Fin sessionsPerTag), sid ≠ 0 → s.sessionsUsed tag ≤ sid.val →
    ∀ n : Nonce, K ((tag, sid), n) = CellKnowledge.excluded ∅

/-- Every determined reference-slot cell has a recorded tag response: determined cells are
tag-written, never reader-written, so a tag step meeting one fires the `bad` flag. -/
def knownRecorded (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest)
    (sB : UnlinkBadState TagId Nonce Digest) : Prop :=
  ∀ (tag : TagId) (n : Nonce) (v : Digest),
    K ((tag, (0 : Fin sessionsPerTag)), n) = CellKnowledge.known v →
    sB.responses (tag, n) ≠ none

/-- The number of excluded values recorded at a cell: zero at a determined cell. -/
def cellExclCard {R : Type} : CellKnowledge R → ℕ
  | .known _ => 0
  | .excluded S => S.card

@[simp] lemma cellExclCard_known {R : Type} (v : R) :
    cellExclCard (CellKnowledge.known v) = 0 := rfl

@[simp] lemma cellExclCard_excluded {R : Type} (S : Finset R) :
    cellExclCard (CellKnowledge.excluded S : CellKnowledge R) = S.card := rfl

/-- The total number of excluded values along a tag's reference-slot row: the per-row potential
paying the averaged reveal tilt of a tag step over the fresh nonce draw. -/
def slotZeroRowExcl [Fintype Nonce]
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest) (tag : TagId) : ℕ :=
  ∑ n : Nonce, cellExclCard (K ((tag, (0 : Fin sessionsPerTag)), n))

end SharpInvariant

section SharpExperiments

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- The M-side experiment of the sharp coupling: draw a table consistent with `K`, run the
instrumented multiple-session handler on its reference-slot sub-table, and return the output
bit. -/
noncomputable def sharpM [Fintype Nonce] [Fintype Digest]
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) (s : UnlinkState TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest) : OptionT ProbComp Bool :=
  genTable K >>= fun gS => liftM (do
    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) oa).run (s, sB))

/-- The S-side experiment of the sharp coupling: draw a table consistent with `K` and run the
single-session handler on it. -/
noncomputable def sharpS [Fintype Nonce] [Fintype Digest]
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) (s : UnlinkState TagId)
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest) : OptionT ProbComp Bool :=
  genTable K >>= fun gS =>
    liftM ((simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) gS) oa).run' s)

/-- The bad-event experiment of the sharp coupling: as `sharpM`, returning the output bit
together with the final bad state. -/
noncomputable def sharpBad [Fintype Nonce] [Fintype Digest]
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) (s : UnlinkState TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest) :
    OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest) :=
  genTable K >>= fun gS => liftM (do
    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
        (z.1, z.2.2)) <$>
      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) oa).run (s, sB))

end SharpExperiments

section SharpHelpers

/-- Transport of a distribution identity of `ProbComp` programs through the `OptionT` lift. -/
private lemma evalDist_liftM_congr {γ : Type} {A B : ProbComp γ} (h : 𝒟[A] = 𝒟[B]) :
    𝒟[(liftM A : OptionT ProbComp γ)] = 𝒟[(liftM B : OptionT ProbComp γ)] :=
  evalDist_ext fun x => by
    rw [OptionT.probOutput_liftM, OptionT.probOutput_liftM,
      probOutput_eq_of_evalDist_eq h x]

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

omit [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Pull a shared nonce draw of the lifted continuation out past the table draw: the lifted
program is decomposed along the bind and the two independent draws are commuted. -/
lemma evalDist_genTable_bind_liftM_comm {γ : Type} [Fintype Nonce] [Fintype Digest]
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest)
    (A : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp γ)
    (Θ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → Nonce → ProbComp γ)
    (hA : ∀ gS, 𝒟[A gS] = 𝒟[($ᵗ Nonce : ProbComp Nonce) >>= fun n => Θ gS n]) :
    𝒟[(genTable K >>= fun gS => liftM (A gS) : OptionT ProbComp γ)] =
      𝒟[((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= fun n =>
        genTable K >>= fun gS => liftM (Θ gS n) : OptionT ProbComp γ)] := by
  have h1 : 𝒟[(genTable K >>= fun gS => liftM (A gS) : OptionT ProbComp γ)]
      = 𝒟[(genTable K >>= fun gS =>
          liftM (($ᵗ Nonce : ProbComp Nonce) >>= fun n => Θ gS n) : OptionT ProbComp γ)] :=
    evalDist_bind_congr fun gS _ => evalDist_liftM_congr (hA gS)
  have h2 : (genTable K >>= fun gS =>
        liftM (($ᵗ Nonce : ProbComp Nonce) >>= fun n => Θ gS n) : OptionT ProbComp γ)
      = genTable K >>= fun gS =>
        (liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= fun n => liftM (Θ gS n) :=
    bind_congr fun gS => liftM_bind _ _
  rw [h1, h2]
  exact evalDist_bind_bind_comm _ _ _

end SharpHelpers

section SharpPreservation

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId]
  [DecidableEq Nonce]
  [DecidableEq Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

omit [DecidableEq Digest] in
/-- Updating a reference-slot cell preserves the slot-positive shape. -/
lemma slotPosExcluded_update_slotZero
    {K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest}
    (hK : slotPosExcluded K) (tag : TagId) (n : Nonce) (c' : CellKnowledge Digest) :
    slotPosExcluded (Function.update K ((tag, (0 : Fin sessionsPerTag)), n) c') := by
  intro tag' sid hsid n'
  rw [Function.update_of_ne (fun h => hsid (congrArg (fun p => p.1.2) h))]
  exact hK tag' sid hsid n'

omit [DecidableEq Digest] in
/-- Updating a reference-slot cell preserves the freshness of live slots. -/
lemma liveSlotsFresh_update_slotZero
    {K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest} {s : UnlinkState TagId}
    (hK : liveSlotsFresh K s) (tag : TagId) (n : Nonce) (c' : CellKnowledge Digest) :
    liveSlotsFresh (Function.update K ((tag, (0 : Fin sessionsPerTag)), n) c') s := by
  intro tag' sid hsid hlive n'
  rw [Function.update_of_ne (fun h => hsid (congrArg (fun p => p.1.2) h))]
  exact hK tag' sid hsid hlive n'

omit [DecidableEq Nonce] [DecidableEq Digest] in
/-- Consuming a session shrinks the live-slot set, so freshness of live slots is preserved. -/
lemma liveSlotsFresh_advance
    {K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest} {s : UnlinkState TagId}
    (hK : liveSlotsFresh K s) (tag : TagId) :
    liveSlotsFresh K
      { s with sessionsUsed :=
          Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } := by
  intro tag' sid hsid hlive n'
  refine hK tag' sid hsid ?_ n'
  have hlive' : Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) tag' ≤ sid.val :=
    hlive
  rcases eq_or_ne tag' tag with rfl | hne
  · rw [Function.update_self] at hlive'
    omega
  · rwa [Function.update_of_ne hne] at hlive'

omit [DecidableEq Digest] in
/-- A recorded tag response survives a tag-step advance of the bad state. -/
lemma multipleBadAdvance_responses_ne_none
    {sB : UnlinkBadState TagId Nonce Digest} {tag : TagId}
    {t : TagTranscript Nonce Digest} {p : TagId × Nonce}
    (h : sB.responses p ≠ none) :
    (multipleBadAdvance tag sB (some t)).responses p ≠ none := by
  change (sB.responses.cacheQuery (tag, t.nonce) _) p ≠ none
  rcases eq_or_ne p (tag, t.nonce) with rfl | hne
  · rw [OracleSpec.QueryCache.cacheQuery_self]
    exact Option.some_ne_none _
  · rwa [OracleSpec.QueryCache.cacheQuery_of_ne _ _ hne]

omit [DecidableEq Digest] in
/-- A tag-step advance records the response of the step's own transcript. -/
lemma multipleBadAdvance_responses_self
    (sB : UnlinkBadState TagId Nonce Digest) (tag : TagId)
    (t : TagTranscript Nonce Digest) :
    (multipleBadAdvance tag sB (some t)).responses (tag, t.nonce) ≠ none := by
  change (sB.responses.cacheQuery (tag, t.nonce) _) (tag, t.nonce) ≠ none
  rw [OracleSpec.QueryCache.cacheQuery_self]
  exact Option.some_ne_none _

omit [DecidableEq Digest] in
/-- A tag step preserves `knownRecorded` at an unchanged knowledge state: the response table
only grows. -/
lemma knownRecorded_badAdvance
    {K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest}
    {sB : UnlinkBadState TagId Nonce Digest} (hK : knownRecorded K sB) (tag : TagId)
    (t : TagTranscript Nonce Digest) :
    knownRecorded K (multipleBadAdvance tag sB (some t)) := fun tag' n' v h =>
  multipleBadAdvance_responses_ne_none (hK tag' n' v h)

omit [DecidableEq Digest] in
/-- A tag step that determines its own reference cell re-establishes `knownRecorded`: the newly
determined cell is the one whose response the advance records. -/
lemma knownRecorded_badAdvance_update
    {K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest}
    {sB : UnlinkBadState TagId Nonce Digest} (hK : knownRecorded K sB) (tag : TagId)
    (n : Nonce) (u : Digest) :
    knownRecorded
      (Function.update K ((tag, (0 : Fin sessionsPerTag)), n) (CellKnowledge.known u))
      (multipleBadAdvance tag sB (some ⟨n, u⟩)) := by
  intro tag' n' v h
  rcases eq_or_ne ((tag', (0 : Fin sessionsPerTag)), n')
      ((tag, (0 : Fin sessionsPerTag)), n) with heq | hne
  · have htag : tag' = tag := congrArg (fun p => p.1.1) heq
    have hn : n' = n := congrArg (fun p => p.2) heq
    subst htag; subst hn
    exact multipleBadAdvance_responses_self sB tag' ⟨n', u⟩
  · rw [Function.update_of_ne hne] at h
    exact multipleBadAdvance_responses_ne_none (hK tag' n' v h)

omit [DecidableEq Digest] in
/-- Determining a cell only removes recorded exclusions, so every row potential is monotone
under a `known` update. -/
lemma slotZeroRowExcl_update_known_le [Fintype Nonce]
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest)
    (d : (TagId × Fin sessionsPerTag) × Nonce) (u : Digest) (tag' : TagId) :
    slotZeroRowExcl (Function.update K d (CellKnowledge.known u)) tag' ≤
      slotZeroRowExcl K tag' := by
  refine Finset.sum_le_sum fun n' _ => ?_
  rcases eq_or_ne ((tag', (0 : Fin sessionsPerTag)), n') d with heq | hne
  · rw [heq, Function.update_self]
    exact Nat.zero_le _
  · rw [Function.update_of_ne hne]

/-- Off-fire shape facts of a reference-slot column probe, packaged for the reader step:
slot-positive cells and live-slot freshness are untouched, no new determined cells appear, and
feasibility is preserved. -/
lemma sharpInv_probeColumnSplit
    {s : UnlinkState TagId} {sB : UnlinkBadState TagId Nonce Digest}
    [Fintype Digest] (a₀ : Digest) (cells : List ((TagId × Fin sessionsPerTag) × Nonce))
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest) (hnd : cells.Nodup)
    (hcells0 : ∀ d ∈ cells, d.1.2 = (0 : Fin sessionsPerTag))
    {z : Bool × Bool × ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest}
    (hz : z ∈ support (probeColumnSplit a₀ cells K)) :
    (slotPosExcluded K → slotPosExcluded z.2.2) ∧
      (liveSlotsFresh K s → liveSlotsFresh z.2.2 s) ∧
      (z.2.1 = false → knownRecorded K sB → knownRecorded z.2.2 sB) ∧
      (K.Feasible → z.2.2.Feasible) := by
  obtain ⟨c1, -, c3, c4, -, -⟩ := probeColumnSplit_support a₀ cells K hnd hz
  have hposcell : ∀ (tag : TagId) (sid : Fin sessionsPerTag), sid ≠ 0 → ∀ n : Nonce,
      z.2.2 ((tag, sid), n) = K ((tag, sid), n) := by
    intro tag sid hsid n
    refine c1 _ fun hmem => hsid ?_
    exact hcells0 _ hmem
  refine ⟨?_, ?_, ?_, c4⟩
  · intro hK tag sid hsid n
    rw [hposcell tag sid hsid n]
    exact hK tag sid hsid n
  · intro hK tag sid hsid hlive n
    rw [hposcell tag sid hsid n]
    exact hK tag sid hsid hlive n
  · intro hfired hK tag n v h
    by_cases hmem : ((tag, (0 : Fin sessionsPerTag)), n) ∈ cells
    · rcases c3 _ hmem with heq | ⟨hf, -⟩ | ⟨S, -, -, hupd⟩
      · exact hK tag n v (heq ▸ h)
      · exact absurd hf (by simp [hfired])
      · rw [hupd] at h
        cases h
    · exact hK tag n v ((c1 _ hmem) ▸ h)

/-- A single-column reference-slot probe grows every row potential by at most one. -/
lemma slotZeroRowExcl_probeColumnSplit_le [Fintype Nonce] [Fintype Digest]
    (a₀ : Digest) (n₀ : Nonce) (cells : List ((TagId × Fin sessionsPerTag) × Nonce))
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest) (hnd : cells.Nodup)
    (hcoln : ∀ d ∈ cells, d.2 = n₀)
    {z : Bool × Bool × ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest}
    (hz : z ∈ support (probeColumnSplit a₀ cells K)) (tag : TagId) :
    slotZeroRowExcl z.2.2 tag ≤ slotZeroRowExcl K tag + 1 := by
  classical
  obtain ⟨c1, -, c3, -, -, -⟩ := probeColumnSplit_support a₀ cells K hnd hz
  have hpoint : ∀ n : Nonce,
      cellExclCard (z.2.2 ((tag, (0 : Fin sessionsPerTag)), n)) ≤
        cellExclCard (K ((tag, (0 : Fin sessionsPerTag)), n)) + (if n = n₀ then 1 else 0) := by
    intro n
    by_cases hmem : ((tag, (0 : Fin sessionsPerTag)), n) ∈ cells
    · have hn : n = n₀ := hcoln _ hmem
      rw [if_pos hn]
      rcases c3 _ hmem with heq | ⟨-, hk⟩ | ⟨S, hKd, -, hupd⟩
      · rw [heq]
        exact Nat.le_succ _
      · rw [hk]
        exact Nat.zero_le _
      · rw [hupd, hKd, cellExclCard_excluded, cellExclCard_excluded]
        exact Finset.card_insert_le a₀ S
    · rw [c1 _ hmem]
      exact Nat.le_add_right _ _
  calc slotZeroRowExcl z.2.2 tag
      ≤ ∑ n : Nonce, (cellExclCard (K ((tag, (0 : Fin sessionsPerTag)), n))
          + if n = n₀ then 1 else 0) := Finset.sum_le_sum fun n _ => hpoint n
    _ = slotZeroRowExcl K tag + 1 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ n₀ (fun _ => 1),
          if_pos (Finset.mem_univ n₀)]
        rfl

end SharpPreservation

section SharpAux

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- The reader (`Sum.inr transcript`) induction step of the sharp coupling aux. The queried
reference-slot column is probed at the Boolean level (`probeColumnSplit`): off the fire event —
some genuine probe hits, with mass at most `|TagId| / (|Digest| - qRInit)` by
`probEvent_probeColumnSplit_fired_le` — the M reader bit is determined by the prior knowledge
alone, a `true` bit is an honest replay also accepted by the S side, and on a `false` bit the
S side's slot-positive acceptance branch is discarded at the mass of the collision indicator
under the residual table. The residual knowledge state records one new exclusion per probed
cell, paid by the `qR`-decrement in the exclusion budgets. The induction hypothesis is supplied
as the explicit premise `ih`. -/
lemma sharpAux_reader_step [Fintype Nonce] [Fintype Digest]
    (qRInit qR qT : ℕ)
    (s : UnlinkState TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest)
    (hqRle : qR ≤ qRInit)
    (hKpos : slotPosExcluded K)
    (hKdead : liveSlotsFresh K s)
    (hKresp : knownRecorded K sB)
    (hKexcl : K.ExclLe (qRInit - qR))
    (hKrow : ∀ tag : TagId, slotZeroRowExcl K tag ≤ qRInit - qR)
    (hKfeas : K.Feasible)
    (transcript : TagTranscript Nonce Digest)
    (k : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inr transcript) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (ih : ∀ (u : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inr transcript))
        (qR qT : ℕ) (s : UnlinkState TagId) (sB : UnlinkBadState TagId Nonce Digest)
        (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest),
        OracleComp.IsQueryBoundP (k u) (·.isRight) qR →
        OracleComp.IsQueryBoundP (k u) (·.isLeft) qT →
        qR ≤ qRInit →
        slotPosExcluded K →
        liveSlotsFresh K s →
        knownRecorded K sB →
        K.ExclLe (qRInit - qR) →
        (∀ tag : TagId, slotZeroRowExcl K tag ≤ qRInit - qR) →
        K.Feasible →
        Pr[= true | sharpM (k u) s sB K] ≤
          Pr[= true | sharpS (k u) s K] +
          Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
            sharpBad (k u) s sB K] +
          ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) /
            ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) +
          ((qT * qRInit : ℕ) : ℝ≥0∞) /
            ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) +
          ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞))
    (hqR : OracleComp.IsQueryBoundP (liftM (OracleSpec.query (Sum.inr transcript)) >>= k)
      (·.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP (liftM (OracleSpec.query (Sum.inr transcript)) >>= k)
      (·.isLeft) qT) :
    Pr[= true | sharpM (liftM (OracleSpec.query (Sum.inr transcript)) >>= k) s sB K] ≤
      Pr[= true | sharpS (liftM (OracleSpec.query (Sum.inr transcript)) >>= k) s K] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        sharpBad (liftM (OracleSpec.query (Sum.inr transcript)) >>= k) s sB K] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) /
        ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) +
      ((qT * qRInit : ℕ) : ℝ≥0∞) /
        ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) := by
  sorry

/-- The slot-zero tag (`Sum.inl tag`, `s.sessionsUsed tag = 0`) induction step of the sharp
coupling aux: both worlds reveal the *same* reference cell `((tag, 0), n)` of the shared table,
so the step couples exactly and charges no slack. At a determined cell the revealed value is
the recorded constant on both sides; at an undetermined cell one shared reveal draw serves both
worlds, and the induction hypothesis applies at the cell determined to the drawn value. The
induction hypothesis is supplied as the explicit premise `ih`. -/
lemma sharpAux_tag_slotZero [Fintype Nonce] [Fintype Digest]
    (qRInit qR qT : ℕ)
    (s : UnlinkState TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest)
    (hqRle : qR ≤ qRInit)
    (hKpos : slotPosExcluded K)
    (hKdead : liveSlotsFresh K s)
    (hKresp : knownRecorded K sB)
    (hKexcl : K.ExclLe (qRInit - qR))
    (hKrow : ∀ tag : TagId, slotZeroRowExcl K tag ≤ qRInit - qR)
    (hKfeas : K.Feasible)
    (tag : TagId)
    (k : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inl tag) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (ih : ∀ (u : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inl tag))
        (qR qT : ℕ) (s : UnlinkState TagId) (sB : UnlinkBadState TagId Nonce Digest)
        (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest),
        OracleComp.IsQueryBoundP (k u) (·.isRight) qR →
        OracleComp.IsQueryBoundP (k u) (·.isLeft) qT →
        qR ≤ qRInit →
        slotPosExcluded K →
        liveSlotsFresh K s →
        knownRecorded K sB →
        K.ExclLe (qRInit - qR) →
        (∀ tag : TagId, slotZeroRowExcl K tag ≤ qRInit - qR) →
        K.Feasible →
        Pr[= true | sharpM (k u) s sB K] ≤
          Pr[= true | sharpS (k u) s K] +
          Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
            sharpBad (k u) s sB K] +
          ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) /
            ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) +
          ((qT * qRInit : ℕ) : ℝ≥0∞) /
            ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) +
          ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞))
    (hqR : OracleComp.IsQueryBoundP (liftM (OracleSpec.query (Sum.inl tag)) >>= k)
      (·.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP (liftM (OracleSpec.query (Sum.inl tag)) >>= k)
      (·.isLeft) qT)
    (hslot : s.sessionsUsed tag < sessionsPerTag)
    (hzero : s.sessionsUsed tag = 0) :
    Pr[= true | sharpM (liftM (OracleSpec.query (Sum.inl tag)) >>= k) s sB K] ≤
      Pr[= true | sharpS (liftM (OracleSpec.query (Sum.inl tag)) >>= k) s K] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        sharpBad (liftM (OracleSpec.query (Sum.inl tag)) >>= k) s sB K] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) /
        ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) +
      ((qT * qRInit : ℕ) : ℝ≥0∞) /
        ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) := by
  classical
  have hqRk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isRight) qR := by
    have := hqR
    rw [OracleComp.isQueryBoundP_query_bind_iff] at this
    simpa using this.2
  have hqTsplit := hqT
  rw [OracleComp.isQueryBoundP_query_bind_iff] at hqTsplit
  have hqTpos : 0 < qT := hqTsplit.1.resolve_left (fun h => absurd rfl h)
  obtain ⟨qT', rfl⟩ : ∃ qT', qT = qT' + 1 := ⟨qT - 1, by omega⟩
  have hqTk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isLeft) qT' := fun u => by
    simpa using hqTsplit.2 u
  set advM : UnlinkState TagId :=
    { s with sessionsUsed :=
        Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } with hadvM
  -- Head-step collapse: under `hzero` both handlers reveal the reference cell `((tag, 0), n)`.
  have hMstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      ∀ gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest,
      multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine (Sum.inl tag) (s, sB)
      = ($ᵗ Nonce) >>= fun n =>
          pure (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
              TagTranscript Nonce Digest),
            advM,
            multipleBadAdvance tag sB
              (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                TagTranscript Nonce Digest))) := by
    intro gS gFine
    change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) (Sum.inl tag)) s
        >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1))
        = _
    rw [multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero
        gS tag s hzero,
      singleTableHandler_tag_run_of_lt gS tag s hslot]
    have hsid : (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) =
        (0 : Fin sessionsPerTag) := Fin.ext hzero
    rw [hsid, ← hadvM]
    exact bind_assoc ..
  have hSstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) gS (Sum.inl tag) s
      = ($ᵗ Nonce) >>= fun n =>
          pure (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
              TagTranscript Nonce Digest),
            advM) := by
    intro gS
    rw [singleTableHandler_tag_run_of_lt gS tag s hslot]
    have hsid : (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) =
        (0 : Fin sessionsPerTag) := Fin.ext hzero
    rw [hsid, ← hadvM]
  -- Rewrite each position to nonce-outermost form via the shared commute helper.
  have hMcommD :
      𝒟[sharpM (liftM (OracleSpec.query (Sum.inl tag)) >>= k) s sB K]
      = 𝒟[((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= fun n =>
          genTable K >>= fun gS => liftM (do
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                z.1) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
                (k (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                  TagTranscript Nonce Digest)))).run
                (advM, multipleBadAdvance tag sB
                  (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest)))) : OptionT ProbComp Bool)] := by
    refine evalDist_genTable_bind_liftM_comm K _ _ fun gS => ?_
    have hprog : (do
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
            (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run (s, sB))
        = (do
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let n ← $ᵗ Nonce
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
              (k (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                TagTranscript Nonce Digest)))).run
              (advM, multipleBadAdvance tag sB
                (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                  TagTranscript Nonce Digest)))) := by
      refine bind_congr fun gFine => ?_
      rw [multipleBadTableFine_run_query_bind', hMstep gS gFine, map_bind]
      exact bind_assoc ..
    rw [hprog]
    exact evalDist_probComp_bind_comm _ ($ᵗ Nonce) _
  have hScommD :
      𝒟[sharpS (liftM (OracleSpec.query (Sum.inl tag)) >>= k) s K]
      = 𝒟[((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= fun n =>
          genTable K >>= fun gS => liftM
            ((simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
              (k (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                TagTranscript Nonce Digest)))).run' advM) : OptionT ProbComp Bool)] := by
    refine evalDist_genTable_bind_liftM_comm K _ _ fun gS => ?_
    have hprog : (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
          (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run' s
        = ($ᵗ Nonce) >>= fun n =>
            (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
              (k (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                TagTranscript Nonce Digest)))).run' advM := by
      rw [singleTable_run'_query_bind', hSstep gS]
      exact bind_assoc ..
    rw [hprog]
  have hBcommD :
      𝒟[sharpBad (liftM (OracleSpec.query (Sum.inl tag)) >>= k) s sB K]
      = 𝒟[((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= fun n =>
          genTable K >>= fun gS => liftM (do
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
                (k (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                  TagTranscript Nonce Digest)))).run
                (advM, multipleBadAdvance tag sB
                  (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest)))) :
          OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))] := by
    refine evalDist_genTable_bind_liftM_comm K _ _ fun gS => ?_
    have hprog : (do
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
            (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run (s, sB))
        = (do
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let n ← $ᵗ Nonce
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
              (k (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                TagTranscript Nonce Digest)))).run
              (advM, multipleBadAdvance tag sB
                (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                  TagTranscript Nonce Digest)))) := by
      refine bind_congr fun gFine => ?_
      rw [multipleBadTableFine_run_query_bind', hMstep gS gFine, map_bind]
      exact bind_assoc ..
    rw [hprog]
    exact evalDist_probComp_bind_comm _ ($ᵗ Nonce) _
  rw [probOutput_eq_of_evalDist_eq hMcommD true,
    probOutput_eq_of_evalDist_eq hScommD true,
    probEvent_eq_of_evalDist_eq hBcommD _]
  simp only [← probEvent_eq_eq_probOutput]
  -- Carve one tilt unit out of the `qT' + 1` budget; the slot-zero step never spends it.
  have hSplit : (((qT' + 1) * qRInit : ℕ) : ℝ≥0∞) /
      ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))
      = ((qRInit : ℕ) : ℝ≥0∞) /
          ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) +
        ((qT' * qRInit : ℕ) : ℝ≥0∞) /
          ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) := by
    rw [show (qT' + 1) * qRInit = qRInit + qT' * qRInit from by ring,
      Nat.cast_add, ENNReal.add_div]
  rw [hSplit]
  rw [show ∀ a b c d e f : ℝ≥0∞,
        a + b + c + (d + e) + f = a + b + d + (c + e + f) from
        fun a b c d e f => by ring]
  refine probEvent_bind_le_add_bad_disagree (D := fun _ : Nonce => False) (by simp) ?_
  intro n _ _
  -- Per-`n`: both worlds reveal the cell `((tag, 0), n)`.
  rcases hcell : K ((tag, (0 : Fin sessionsPerTag)), n) with v | S₀
  · -- Determined cell: the revealed value is the constant `v` on both sides.
    have hMrw :
        𝒟[(genTable K >>= fun gS => liftM (do
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                z.1) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
                (k (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                  TagTranscript Nonce Digest)))).run
                (advM, multipleBadAdvance tag sB
                  (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest)))) : OptionT ProbComp Bool)]
        = 𝒟[sharpM (k (some (⟨n, v⟩ : TagTranscript Nonce Digest))) advM
            (multipleBadAdvance tag sB (some (⟨n, v⟩ : TagTranscript Nonce Digest))) K] := by
      have h := evalDist_genTable_bind_known_comp K hcell fun u gS => liftM (do
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
            (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
            (advM, multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest))))
      exact h
    have hSrw :
        𝒟[(genTable K >>= fun gS => liftM
            ((simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
              (k (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                TagTranscript Nonce Digest)))).run' advM) : OptionT ProbComp Bool)]
        = 𝒟[sharpS (k (some (⟨n, v⟩ : TagTranscript Nonce Digest))) advM K] := by
      have h := evalDist_genTable_bind_known_comp K hcell fun u gS => liftM
        ((simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
          (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' advM)
      exact h
    have hBrw :
        𝒟[(genTable K >>= fun gS => liftM (do
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
                (k (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                  TagTranscript Nonce Digest)))).run
                (advM, multipleBadAdvance tag sB
                  (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest)))) :
            OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))]
        = 𝒟[sharpBad (k (some (⟨n, v⟩ : TagTranscript Nonce Digest))) advM
            (multipleBadAdvance tag sB (some (⟨n, v⟩ : TagTranscript Nonce Digest))) K] := by
      have h := evalDist_genTable_bind_known_comp K hcell fun u gS => liftM (do
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
            (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
            (advM, multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest))))
      exact h
    rw [probEvent_eq_of_evalDist_eq hMrw _, probEvent_eq_of_evalDist_eq hSrw _,
      probEvent_eq_of_evalDist_eq hBrw _]
    have hih := ih (some (⟨n, v⟩ : TagTranscript Nonce Digest)) qR qT' advM
      (multipleBadAdvance tag sB (some (⟨n, v⟩ : TagTranscript Nonce Digest))) K
      (hqRk _) (hqTk _) hqRle hKpos (liveSlotsFresh_advance hKdead tag)
      (knownRecorded_badAdvance hKresp tag _) hKexcl hKrow hKfeas
    rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput,
      ← add_assoc, ← add_assoc]
    exact hih
  · -- Undetermined cell: one shared reveal draw serves both worlds.
    have hMrw :
        𝒟[(genTable K >>= fun gS => liftM (do
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                z.1) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
                (k (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                  TagTranscript Nonce Digest)))).run
                (advM, multipleBadAdvance tag sB
                  (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest)))) : OptionT ProbComp Bool)]
        = 𝒟[(($ (Finset.univ \ S₀)) >>= fun u =>
            sharpM (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
              (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
              (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                (CellKnowledge.known u)) : OptionT ProbComp Bool)] := by
      have h := evalDist_genTable_bind_reveal_comp K hcell fun u gS => liftM (do
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
            (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
            (advM, multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest))))
      exact h
    have hSrw :
        𝒟[(genTable K >>= fun gS => liftM
            ((simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
              (k (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                TagTranscript Nonce Digest)))).run' advM) : OptionT ProbComp Bool)]
        = 𝒟[(($ (Finset.univ \ S₀)) >>= fun u =>
            sharpS (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
              (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                (CellKnowledge.known u)) : OptionT ProbComp Bool)] := by
      have h := evalDist_genTable_bind_reveal_comp K hcell fun u gS => liftM
        ((simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
          (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' advM)
      exact h
    have hBrw :
        𝒟[(genTable K >>= fun gS => liftM (do
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
                (k (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                  TagTranscript Nonce Digest)))).run
                (advM, multipleBadAdvance tag sB
                  (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest)))) :
            OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))]
        = 𝒟[(($ (Finset.univ \ S₀)) >>= fun u =>
            sharpBad (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
              (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
              (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                (CellKnowledge.known u)) :
            OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))] := by
      have h := evalDist_genTable_bind_reveal_comp K hcell fun u gS => liftM (do
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
            (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
            (advM, multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest))))
      exact h
    rw [probEvent_eq_of_evalDist_eq hMrw _, probEvent_eq_of_evalDist_eq hSrw _,
      probEvent_eq_of_evalDist_eq hBrw _]
    rw [show ∀ a b c : ℝ≥0∞, a + b + c = a + b + 0 + c from fun a b c => by ring]
    refine probEvent_bind_le_add_bad_disagree (D := fun _ : Digest => False) (by simp) ?_
    intro u _ _
    have hih := ih (some (⟨n, u⟩ : TagTranscript Nonce Digest)) qR qT' advM
      (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
      (Function.update K ((tag, (0 : Fin sessionsPerTag)), n) (CellKnowledge.known u))
      (hqRk _) (hqTk _) hqRle
      (slotPosExcluded_update_slotZero hKpos tag n _)
      (liveSlotsFresh_advance (liveSlotsFresh_update_slotZero hKdead tag n _) tag)
      (knownRecorded_badAdvance_update hKresp tag n u)
      (hKexcl.update_known _ u)
      (fun tag' => le_trans (slotZeroRowExcl_update_known_le K _ u tag') (hKrow tag'))
      (hKfeas.update _ (Finset.singleton_nonempty u))
    rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput,
      ← add_assoc, ← add_assoc]
    exact hih

end SharpAux

end UnlinkReduction

end PRFTagReader
