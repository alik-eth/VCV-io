/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.DirectCoupling.SharpAux
import Examples.PRFTagReader.DirectCoupling.SharpReaderCase
import Examples.PRFTagReader.DirectCoupling.Swap
import VCVio.OracleComp.QueryTracking.RandomOracle.RevealTilt

/-!
# PRF Tag/Reader Protocol — Sharp Coupling: Slot-Positive Tag Case And Assembly

The slot-positive tag induction step of the sharp direct M_ideal/S_ideal coupling, and the
assembled structural induction `sharpCoupling_aux` over the experiments and six-conjunct
invariant of `DirectCoupling/SharpAux.lean`.

At a tag query with `1 ≤ s.sessionsUsed tag < sessionsPerTag` the two worlds reveal *different*
cells of the shared consistent table: the multiple-session world re-reads the reference cell
`((tag, 0), n)` while the single-session world reads the live cell `((tag, σ), n)`. The step
couples the two reveals through three moves:

* **Bad absorption** (`probOutput_sharpM_le_probEvent_sharpBad_of_bad`): when the reference
  cell is already determined, `knownRecorded` forces a recorded response, so the bad flag fires
  at the step and the whole M-side mass is absorbed by the bad position.
* **Reveal tilt**: when the reference cell carries an exclusion set `S₀`, the M side reveals
  uniformly on `Digest ∖ S₀` while the S side reveals on all of `Digest`; the comparison costs
  `|S₀| / |Digest|` (`probEvent_bind_uniformSelectFinset_sdiff_le`), paid from the per-row
  potential `slotZeroRowExcl` averaged over the fresh nonce.
* **Swap-bridge** (`evalDist_sharpS_swap_bridge`): the S-side knowledge state recording the
  reveal at the live slot is relabeled by the cell swap `((tag, 0), n) ↔ ((tag, σ), n)` into
  the state recording the value at the reference slot with the exclusions parked at the
  now-dead slot, so both worlds continue from one shared knowledge state. The relabeling is a
  `genTable` pushforward along an equivalence (`evalDist_map_comp_equiv_genTable`) composed
  with the pointwise run-invariance `singleTableHandler_simulateQ_swap_invariant`; the M and
  bad positions only read the table through `slotZeroSubTable`, so they cannot distinguish the
  two states (`evalDist_map_comp_genTable_congr`).
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

namespace UnlinkReduction

section SharpSlotPositiveInvariant

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId]
  [DecidableEq Nonce]
  [DecidableEq Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

omit [DecidableEq Digest] in
/-- Recording an exclusion set at any cell preserves the slot-positive shape: no cell becomes
determined. -/
lemma slotPosExcluded_update_excluded
    {K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest}
    (hK : slotPosExcluded K) (d : (TagId × Fin sessionsPerTag) × Nonce) (S : Finset Digest) :
    slotPosExcluded (Function.update K d (CellKnowledge.excluded S)) := by
  intro tag' sid hsid n'
  rcases eq_or_ne ((tag', sid), n') d with rfl | hne
  · exact ⟨S, Function.update_self _ _ _⟩
  · rw [Function.update_of_ne hne]
    exact hK tag' sid hsid n'

omit [DecidableEq Digest] in
/-- Updating a dead slot — one whose session index the state has already consumed — preserves
the freshness of live slots. -/
lemma liveSlotsFresh_update_dead
    {K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest} {st : UnlinkState TagId}
    (hK : liveSlotsFresh K st) {tag : TagId} {σf : Fin sessionsPerTag}
    (hlt : σf.val < st.sessionsUsed tag) (n : Nonce) (c' : CellKnowledge Digest) :
    liveSlotsFresh (Function.update K ((tag, σf), n) c') st := by
  intro tag' sid hsid hlive n'
  have hne : ((tag', sid), n') ≠ ((tag, σf), n) := by
    intro h
    have htag : tag' = tag := congrArg (fun p => p.1.1) h
    have hsidσ : sid = σf := congrArg (fun p => p.1.2) h
    subst htag
    subst hsidσ
    omega
  rw [Function.update_of_ne hne]
  exact hK tag' sid hsid hlive n'

omit [DecidableEq Digest] in
/-- Updating a slot-positive cell preserves `knownRecorded`: only reference-slot cells are
inspected. -/
lemma knownRecorded_update_slotPos
    {K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest}
    {sB : UnlinkBadState TagId Nonce Digest} (hK : knownRecorded K sB)
    {tag : TagId} {σf : Fin sessionsPerTag} (hσ : σf ≠ 0) (n : Nonce)
    (c' : CellKnowledge Digest) :
    knownRecorded (Function.update K ((tag, σf), n) c') sB := by
  intro tag' n' v h
  rw [Function.update_of_ne (fun heq => hσ (congrArg (fun p => p.1.2) heq).symm)] at h
  exact hK tag' n' v h

omit [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Recording an exclusion set within the cardinality budget preserves the per-cell exclusion
bound. -/
lemma exclLe_update_excluded
    {K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest} {m : ℕ}
    (hK : K.ExclLe m) (d : (TagId × Fin sessionsPerTag) × Nonce) {S : Finset Digest}
    (hS : S.card ≤ m) :
    ProbeState.ExclLe (Function.update K d (CellKnowledge.excluded S)) m := by
  intro d' T hT
  rcases eq_or_ne d' d with rfl | hne
  · rw [Function.update_self] at hT
    injection hT with h
    exact h ▸ hS
  · rw [Function.update_of_ne hne] at hT
    exact hK d' T hT

omit [DecidableEq Digest] in
/-- Updating a slot-positive cell leaves every reference-slot row potential unchanged. -/
lemma slotZeroRowExcl_update_slotPos [Fintype Nonce]
    {K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest}
    {tag : TagId} {σf : Fin sessionsPerTag} (hσ : σf ≠ 0) (n : Nonce)
    (c' : CellKnowledge Digest) (tag' : TagId) :
    slotZeroRowExcl (Function.update K ((tag, σf), n) c') tag' = slotZeroRowExcl K tag' := by
  refine Finset.sum_congr rfl fun n' _ => ?_
  rw [Function.update_of_ne (fun h => hσ (congrArg (fun p => p.1.2) h).symm)]

end SharpSlotPositiveInvariant

section SharpSlotPositiveBridge

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

omit [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Reindexing transport for the consistent-table distribution: a consistent table of a
reindexed knowledge state feeding a continuation is distributed as a consistent table of the
original state feeding the continuation through the reindexing. -/
private lemma evalDist_genTable_reindex_bind {D : Type} [Fintype D] [DecidableEq D]
    [Fintype Digest] {β : Type}
    (e : D ≃ D) (K : ProbeState D Digest) (G : (D → Digest) → OptionT ProbComp β) :
    𝒟[genTable (fun d => K (e d)) >>= G] = 𝒟[genTable K >>= fun gS => G (gS ∘ e)] := by
  have h2 : ((fun g : D → Digest => g ∘ e) <$> genTable K) >>= G
      = genTable K >>= fun gS => G (gS ∘ e) := by
    rw [map_eq_bind_pure_comp, bind_assoc]
    exact bind_congr fun gS => by rw [Function.comp_apply, pure_bind]
  rw [← h2, evalDist_bind, evalDist_bind, evalDist_map_comp_equiv_genTable e K]

omit [Fintype TagId] [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] in
/-- The knowledge-state relabeling of the swap-bridge: recording the reveal at the live slot is
the cell swap of recording it at the reference slot and parking the reference slot's exclusion
set at the now-dead slot. -/
private lemma update_known_eq_swap_update (tag : TagId) (σf : Fin sessionsPerTag)
    (hσ : σf ≠ 0) (n : Nonce) (u : Digest) (S₀ : Finset Digest)
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest)
    (hd₀ : K ((tag, (0 : Fin sessionsPerTag)), n) = CellKnowledge.excluded S₀) :
    Function.update K ((tag, σf), n) (CellKnowledge.known u)
      = fun d => (Function.update (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
          (CellKnowledge.known u)) ((tag, σf), n) (CellKnowledge.excluded S₀))
          (Equiv.swap ((tag, (0 : Fin sessionsPerTag)), n) ((tag, σf), n) d) := by
  have hne : ((tag, (0 : Fin sessionsPerTag)), n) ≠ ((tag, σf), n) := by
    intro h
    exact hσ (congrArg (fun p => p.1.2) h).symm
  funext d
  rcases eq_or_ne d ((tag, (0 : Fin sessionsPerTag)), n) with rfl | h0
  · rw [Equiv.swap_apply_left, Function.update_of_ne hne, Function.update_self]
    exact hd₀
  · rcases eq_or_ne d ((tag, σf), n) with rfl | hK
    · rw [Equiv.swap_apply_right, Function.update_self, Function.update_of_ne hne,
        Function.update_self]
    · rw [Equiv.swap_apply_of_ne_of_ne h0 hK, Function.update_of_ne hK,
        Function.update_of_ne hK, Function.update_of_ne h0]

omit [SampleableType Digest] in
/-- **Swap-bridge for the sharp coupling.** The single-session experiment at the knowledge
state recording a live-slot reveal is distributed as the experiment at the state recording the
same value at the reference slot with the reference slot's exclusion set parked at the now-dead
slot. The relabeling is the `genTable` pushforward along the two-cell swap, and the residual
run cannot see the swap: later tag steps of `tag` read slots above `σf`, other cells are fixed,
and the reader existential over a nonce column is permutation-invariant
(`singleTableHandler_simulateQ_swap_invariant`). -/
lemma evalDist_sharpS_swap_bridge [Fintype Nonce] [Fintype Digest]
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (st : UnlinkState TagId) (tag : TagId) (σf : Fin sessionsPerTag) (hσ : σf ≠ 0)
    (hAdv : σf.val < st.sessionsUsed tag)
    (n : Nonce) (u : Digest) (S₀ : Finset Digest)
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest)
    (hd₀ : K ((tag, (0 : Fin sessionsPerTag)), n) = CellKnowledge.excluded S₀) :
    𝒟[sharpS oa st (Function.update K ((tag, σf), n) (CellKnowledge.known u))] =
      𝒟[sharpS oa st (Function.update (Function.update K
        ((tag, (0 : Fin sessionsPerTag)), n) (CellKnowledge.known u))
        ((tag, σf), n) (CellKnowledge.excluded S₀))] := by
  classical
  rw [update_known_eq_swap_update tag σf hσ n u S₀ K hd₀]
  change 𝒟[genTable _ >>= _] = 𝒟[genTable _ >>= _]
  rw [evalDist_genTable_reindex_bind]
  refine evalDist_bind_congr fun gS _ => ?_
  refine congrArg evalDist (congrArg liftM ?_)
  refine singleTableHandler_simulateQ_swap_invariant tag σf hσ n oa st hAdv _ _ ?_ ?_ ?_
  · intro x hx0 hxK
    change gS (Equiv.swap _ _ x) = gS x
    rw [Equiv.swap_apply_of_ne_of_ne hx0 hxK]
  · change gS (Equiv.swap _ _ _) = gS _
    rw [Equiv.swap_apply_left]
  · change gS (Equiv.swap _ _ _) = gS _
    rw [Equiv.swap_apply_right]

omit [SampleableType Digest] in
/-- Marginal congruence through the reference-slot sub-table: two feasible knowledge states
agreeing on every reference-slot cell drive a continuation that reads the table only through
`slotZeroSubTable` to the same distribution. -/
private lemma evalDist_genTable_bind_subTable_congr {β : Type} [Fintype Nonce] [Fintype Digest]
    {K K' : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest}
    (hK : K.Feasible) (hK' : K'.Feasible)
    (hagree : ∀ (tag : TagId) (n : Nonce),
      K ((tag, (0 : Fin sessionsPerTag)), n) = K' ((tag, (0 : Fin sessionsPerTag)), n))
    (F : (TagId × Nonce → Digest) → ProbComp β) :
    𝒟[(genTable K >>= fun gS =>
        liftM (F (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) :
      OptionT ProbComp β)] =
      𝒟[(genTable K' >>= fun gS =>
        liftM (F (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) :
        OptionT ProbComp β)] := by
  have hmap : ∀ Kx : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest,
      (genTable Kx >>= fun gS =>
          liftM (F (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) :
        OptionT ProbComp β)
        = ((fun g : (TagId × Fin sessionsPerTag) × Nonce → Digest =>
            g ∘ slotZeroEmbed (sessionsPerTag := sessionsPerTag)) <$> genTable Kx) >>=
            fun g0 => liftM (F g0) := by
    intro Kx
    rw [map_eq_bind_pure_comp, bind_assoc]
    exact bind_congr fun gS => by rw [Function.comp_apply, pure_bind]
  rw [hmap K, hmap K', evalDist_bind, evalDist_bind,
    evalDist_map_comp_genTable_congr
      (slotZeroEmbed_injective (TagId := TagId) (Nonce := Nonce)
        (sessionsPerTag := sessionsPerTag)) hK hK' (fun d' => hagree d'.1 d'.2)]

/-- The instrumented multiple-session experiment reads the shared table only through the
reference-slot sub-table, so it cannot distinguish two feasible knowledge states that agree on
every reference-slot cell. -/
lemma evalDist_sharpM_congr [Fintype Nonce] [Fintype Digest]
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) (sB : UnlinkBadState TagId Nonce Digest)
    {K K' : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest}
    (hK : K.Feasible) (hK' : K'.Feasible)
    (hagree : ∀ (tag : TagId) (n : Nonce),
      K ((tag, (0 : Fin sessionsPerTag)), n) = K' ((tag, (0 : Fin sessionsPerTag)), n)) :
    𝒟[sharpM oa s sB K] = 𝒟[sharpM oa s sB K'] := by
  have h := evalDist_genTable_bind_subTable_congr hK hK' hagree (fun g0 => ((do
    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g0 gFine) oa).run (s, sB)) :
    ProbComp Bool))
  exact h

/-- The bad-event experiment reads the shared table only through the reference-slot sub-table,
so it cannot distinguish two feasible knowledge states that agree on every reference-slot
cell. -/
lemma evalDist_sharpBad_congr [Fintype Nonce] [Fintype Digest]
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) (sB : UnlinkBadState TagId Nonce Digest)
    {K K' : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest}
    (hK : K.Feasible) (hK' : K'.Feasible)
    (hagree : ∀ (tag : TagId) (n : Nonce),
      K ((tag, (0 : Fin sessionsPerTag)), n) = K' ((tag, (0 : Fin sessionsPerTag)), n)) :
    𝒟[sharpBad oa s sB K] = 𝒟[sharpBad oa s sB K'] := by
  have h := evalDist_genTable_bind_subTable_congr hK hK' hagree (fun g0 => ((do
    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
        (z.1, z.2.2)) <$>
      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g0 gFine) oa).run (s, sB)) :
    ProbComp (Bool × UnlinkBadState TagId Nonce Digest)))
  exact h

/-- **Bad absorption.** From a bad state whose flag is already set, the bad flag persists
through the whole instrumented run, so the M-side success mass is dominated by the bad-event
mass of the same run. -/
lemma probOutput_sharpM_le_probEvent_sharpBad_of_bad [Fintype Nonce] [Fintype Digest]
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) {sB : UnlinkBadState TagId Nonce Digest}
    (hbad : sB.bad = true)
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest) :
    Pr[= true | sharpM oa s sB K] ≤
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        sharpBad oa s sB K] := by
  rw [← probEvent_eq_eq_probOutput]
  unfold sharpM sharpBad
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun gS => ?_
  refine mul_le_mul' le_rfl ?_
  rw [OptionT.probEvent_liftM, OptionT.probEvent_liftM,
    probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun gFine => ?_
  refine mul_le_mul' le_rfl ?_
  rw [probEvent_map, probEvent_map]
  refine probEvent_mono fun z hz _ => ?_
  exact multipleBadTableHandlerFine_run_preserves_bad _ gFine oa (s, sB) hbad z hz

end SharpSlotPositiveBridge

section SharpSlotPositiveMain

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- The slot-positive tag (`Sum.inl tag`, `1 ≤ s.sessionsUsed tag < sessionsPerTag`) induction
step of the sharp coupling aux. Each world reveals its own cell of the shared table — the
M side the reference cell `((tag, 0), n)` from its conditioned allowed set, the S side the live
cell `((tag, σ), n)` from the full range by `liveSlotsFresh`. A determined reference cell with a
recorded response fires the `bad` flag (`knownRecorded`); otherwise the reveal tilt of the
conditioned cell is paid from the averaged per-row potential `slotZeroRowExcl`, the revealed
value is identified across the worlds, and the S-side write at the live slot is normalized to
the reference slot, parking the reference cell's exclusion set at the now-dead slot. The
induction hypothesis is supplied as the explicit premise `ih`. -/
lemma sharpAux_tag_slotPositive [Fintype Nonce] [Fintype Digest]
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
    (hzero : ¬ s.sessionsUsed tag = 0) :
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
  set σf : Fin sessionsPerTag := ⟨s.sessionsUsed tag, hslot⟩ with hσf
  have hσf0 : σf ≠ 0 := by
    intro h
    apply hzero
    have := congrArg Fin.val h
    simpa [hσf] using this
  have hAdvM : σf.val < advM.sessionsUsed tag := by
    change σf.val < Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) tag
    rw [Function.update_self]
    exact Nat.lt_succ_of_le (le_of_eq (by rw [hσf]))
  -- Head-step collapse: M re-reads the reference cell, S reads the live cell at `σf`.
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
    rw [multipleTableHandler_tag_run_of_lt _ tag s hslot, ← hadvM]
    exact bind_assoc ..
  have hSstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) gS (Sum.inl tag) s
      = ($ᵗ Nonce) >>= fun n =>
          pure (some (⟨n, gS ((tag, σf), n)⟩ : TagTranscript Nonce Digest), advM) := by
    intro gS
    rw [singleTableHandler_tag_run_of_lt gS tag s hslot, ← hσf, ← hadvM]
  -- The three nonce-outermost positions of the step.
  set myF : Nonce → OptionT ProbComp Bool := fun n =>
    genTable K >>= fun gS => liftM (do
      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
          (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
          (k (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
            TagTranscript Nonce Digest)))).run
          (advM, multipleBadAdvance tag sB
            (some (⟨n, gS ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
              TagTranscript Nonce Digest)))) with hmyF
  set ocF : Nonce → OptionT ProbComp Bool := fun n =>
    genTable K >>= fun gS => liftM
      ((simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
        (k (some (⟨n, gS ((tag, σf), n)⟩ : TagTranscript Nonce Digest)))).run' advM)
    with hocF
  set obF : Nonce → OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest) := fun n =>
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
              TagTranscript Nonce Digest)))) with hobF
  -- Rewrite each position to nonce-outermost form via the shared commute helper.
  have hMcommD :
      𝒟[sharpM (liftM (OracleSpec.query (Sum.inl tag)) >>= k) s sB K]
      = 𝒟[((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= myF : OptionT ProbComp Bool)] := by
    rw [hmyF]
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
      = 𝒟[((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= ocF : OptionT ProbComp Bool)] := by
    rw [hocF]
    refine evalDist_genTable_bind_liftM_comm K _ _ fun gS => ?_
    have hprog : (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
          (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run' s
        = ($ᵗ Nonce) >>= fun n =>
            (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
              (k (some (⟨n, gS ((tag, σf), n)⟩ : TagTranscript Nonce Digest)))).run' advM := by
      rw [singleTable_run'_query_bind', hSstep gS]
      exact bind_assoc ..
    rw [hprog]
  have hBcommD :
      𝒟[sharpBad (liftM (OracleSpec.query (Sum.inl tag)) >>= k) s sB K]
      = 𝒟[((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= obF :
          OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))] := by
    rw [hobF]
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
  -- Carve one tilt unit out of the `qT' + 1` budget; the step pays it from the row potential.
  have hSplit : (((qT' + 1) * qRInit : ℕ) : ℝ≥0∞) /
      ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))
      = ((qRInit : ℕ) : ℝ≥0∞) /
          ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) +
        ((qT' * qRInit : ℕ) : ℝ≥0∞) /
          ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) := by
    rw [show (qT' + 1) * qRInit = qRInit + qT' * qRInit from by ring,
      Nat.cast_add, ENNReal.add_div]
  rw [hSplit]
  -- The induction-hypothesis slack bundle of the continuation.
  set κ : ℝ≥0∞ :=
    ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) /
      ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) +
    ((qT' * qRInit : ℕ) : ℝ≥0∞) /
      ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) +
    ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
      ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) with hκ
  -- Per-nonce bound: bad absorption at a determined cell, tilt + swap-bridge at an excluded
  -- cell.
  have hPerN : ∀ n ∈ support ((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce)),
      ¬ (fun _ : Nonce => False) n →
      Pr[(· = true) | myF n] ≤ Pr[(· = true) | ocF n] +
        Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad) | obF n] +
        ((cellExclCard (K ((tag, (0 : Fin sessionsPerTag)), n)) : ℝ≥0∞) /
          (Fintype.card Digest : ℝ≥0∞) + κ) := by
    intro n _ _
    simp only [hmyF, hocF, hobF]
    rcases hcell : K ((tag, (0 : Fin sessionsPerTag)), n) with v | S₀
    · -- Determined reference cell: the M-side transcript is constant and the recorded
      -- response fires the bad flag, absorbing the whole M-side mass.
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
              (advM, multipleBadAdvance tag sB
                (some (⟨n, u⟩ : TagTranscript Nonce Digest))))
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
              (advM, multipleBadAdvance tag sB
                (some (⟨n, u⟩ : TagTranscript Nonce Digest))))
        exact h
      rw [probEvent_eq_of_evalDist_eq hMrw _, probEvent_eq_of_evalDist_eq hBrw _]
      have hbadStart : (multipleBadAdvance tag sB
          (some (⟨n, v⟩ : TagTranscript Nonce Digest))).bad = true := by
        change (sB.bad || (sB.responses (tag, n)).isSome) = true
        rw [Option.isSome_iff_ne_none.mpr (hKresp tag n v hcell), Bool.or_true]
      have habs := probOutput_sharpM_le_probEvent_sharpBad_of_bad
        (k (some (⟨n, v⟩ : TagTranscript Nonce Digest))) advM hbadStart K
      rw [probEvent_eq_eq_probOutput]
      exact habs.trans (le_add_self.trans le_self_add)
    · -- Excluded reference cell: reveal-split both worlds, pay the tilt on the S side, and
      -- continue from the shared swapped knowledge state.
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
              (advM, multipleBadAdvance tag sB
                (some (⟨n, u⟩ : TagTranscript Nonce Digest))))
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
              (advM, multipleBadAdvance tag sB
                (some (⟨n, u⟩ : TagTranscript Nonce Digest))))
        exact h
      have hdσ : K ((tag, σf), n) = CellKnowledge.excluded ∅ :=
        hKdead tag σf hσf0 (le_of_eq (by rw [hσf])) n
      have hSrw :
          𝒟[(genTable K >>= fun gS => liftM
              ((simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
                (k (some (⟨n, gS ((tag, σf), n)⟩ : TagTranscript Nonce Digest)))).run' advM) :
              OptionT ProbComp Bool)]
          = 𝒟[(($ (Finset.univ \ (∅ : Finset Digest))) >>= fun u =>
              sharpS (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                (Function.update K ((tag, σf), n) (CellKnowledge.known u)) :
              OptionT ProbComp Bool)] := by
        have h := evalDist_genTable_bind_reveal_comp K hdσ fun u gS => liftM
          ((simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
            (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' advM)
        exact h
      rw [probEvent_eq_of_evalDist_eq hMrw _, probEvent_eq_of_evalDist_eq hSrw _,
        probEvent_eq_of_evalDist_eq hBrw _]
      -- Feasibility and reference-slot agreement facts of the per-value knowledge states.
      have hfeas1 : ∀ u : Digest,
          ProbeState.Feasible (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
            (CellKnowledge.known u)) :=
        fun u => hKfeas.update _ (Finset.singleton_nonempty u)
      have hallow : (CellKnowledge.excluded S₀ : CellKnowledge Digest).allowed.Nonempty := by
        have := hKfeas ((tag, (0 : Fin sessionsPerTag)), n)
        rwa [hcell] at this
      have hfeasStar : ∀ u : Digest,
          ProbeState.Feasible (Function.update (Function.update K
            ((tag, (0 : Fin sessionsPerTag)), n) (CellKnowledge.known u)) ((tag, σf), n)
            (CellKnowledge.excluded S₀)) :=
        fun u => (hfeas1 u).update _ hallow
      have hagree : ∀ u : Digest, ∀ (tag' : TagId) (n' : Nonce),
          (Function.update K ((tag, (0 : Fin sessionsPerTag)), n) (CellKnowledge.known u))
            ((tag', (0 : Fin sessionsPerTag)), n')
          = (Function.update (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
              (CellKnowledge.known u)) ((tag, σf), n) (CellKnowledge.excluded S₀))
            ((tag', (0 : Fin sessionsPerTag)), n') := by
        intro u tag' n'
        have hne : ((tag', (0 : Fin sessionsPerTag)), n') ≠ ((tag, σf), n) :=
          fun h => hσf0 (congrArg (fun p => p.1.2) h).symm
        rw [Function.update_of_ne hne]
      -- Move the M and bad positions to the shared swapped knowledge state.
      have hMcongr :
          𝒟[(($ (Finset.univ \ S₀)) >>= fun u =>
              sharpM (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
                (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                  (CellKnowledge.known u)) : OptionT ProbComp Bool)]
          = 𝒟[(($ (Finset.univ \ S₀)) >>= fun u =>
              sharpM (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
                (Function.update (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                  (CellKnowledge.known u)) ((tag, σf), n) (CellKnowledge.excluded S₀)) :
              OptionT ProbComp Bool)] :=
        evalDist_bind_congr fun u _ => evalDist_sharpM_congr _ _ _
          (hfeas1 u) (hfeasStar u) (hagree u)
      have hBcongr :
          𝒟[(($ (Finset.univ \ S₀)) >>= fun u =>
              sharpBad (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
                (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                  (CellKnowledge.known u)) :
              OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))]
          = 𝒟[(($ (Finset.univ \ S₀)) >>= fun u =>
              sharpBad (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
                (Function.update (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                  (CellKnowledge.known u)) ((tag, σf), n) (CellKnowledge.excluded S₀)) :
              OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))] :=
        evalDist_bind_congr fun u _ => evalDist_sharpBad_congr _ _ _
          (hfeas1 u) (hfeasStar u) (hagree u)
      -- Normalize the S position to the shared state via the swap-bridge.
      have hSbridge :
          𝒟[(($ (Finset.univ \ (∅ : Finset Digest))) >>= fun u =>
              sharpS (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                (Function.update K ((tag, σf), n) (CellKnowledge.known u)) :
              OptionT ProbComp Bool)]
          = 𝒟[(($ (Finset.univ : Finset Digest)) >>= fun u =>
              sharpS (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                (Function.update (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                  (CellKnowledge.known u)) ((tag, σf), n) (CellKnowledge.excluded S₀)) :
              OptionT ProbComp Bool)] := by
        rw [Finset.sdiff_empty]
        exact evalDist_bind_congr fun u _ =>
          evalDist_sharpS_swap_bridge (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
            advM tag σf hσf0 hAdvM n u S₀ K hcell
      rw [probEvent_eq_of_evalDist_eq hMcongr _, probEvent_eq_of_evalDist_eq hSbridge _,
        probEvent_eq_of_evalDist_eq hBcongr _]
      -- Per-value induction hypothesis at the shared swapped knowledge state.
      have hIH : ∀ u ∈ support (($ (Finset.univ \ S₀)) : OptionT ProbComp Digest),
          ¬ (fun _ : Digest => False) u →
          Pr[(· = true) | sharpM (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
              (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
              (Function.update (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                (CellKnowledge.known u)) ((tag, σf), n) (CellKnowledge.excluded S₀))] ≤
            Pr[(· = true) | sharpS (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
              (Function.update (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                (CellKnowledge.known u)) ((tag, σf), n) (CellKnowledge.excluded S₀))] +
            Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad) |
              sharpBad (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
                (Function.update (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                  (CellKnowledge.known u)) ((tag, σf), n) (CellKnowledge.excluded S₀))] +
            κ := by
        intro u _ _
        have hih := ih (some (⟨n, u⟩ : TagTranscript Nonce Digest)) qR qT' advM
          (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
          (Function.update (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
            (CellKnowledge.known u)) ((tag, σf), n) (CellKnowledge.excluded S₀))
          (hqRk _) (hqTk _) hqRle
          (slotPosExcluded_update_excluded
            (slotPosExcluded_update_slotZero hKpos tag n _) _ S₀)
          (liveSlotsFresh_update_dead
            (liveSlotsFresh_advance (liveSlotsFresh_update_slotZero hKdead tag n _) tag)
            hAdvM n _)
          (knownRecorded_update_slotPos
            (knownRecorded_badAdvance_update hKresp tag n u) hσf0 n _)
          (exclLe_update_excluded (hKexcl.update_known _ u) _ (hKexcl _ S₀ hcell))
          (fun tag' => by
            rw [slotZeroRowExcl_update_slotPos hσf0]
            exact le_trans (slotZeroRowExcl_update_known_le K _ u tag') (hKrow tag'))
          ((hfeas1 u).update _ hallow)
        rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput, hκ,
          ← add_assoc, ← add_assoc]
        exact hih
      -- Assemble: per-value coupling at the shared state, then the reveal tilt on the S side.
      rw [cellExclCard_excluded]
      calc Pr[(· = true) | (($ (Finset.univ \ S₀)) >>= fun u =>
              sharpM (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
                (Function.update (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                  (CellKnowledge.known u)) ((tag, σf), n) (CellKnowledge.excluded S₀)) :
              OptionT ProbComp Bool)]
          ≤ Pr[(· = true) | (($ (Finset.univ \ S₀)) >>= fun u =>
                sharpS (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                  (Function.update (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                    (CellKnowledge.known u)) ((tag, σf), n) (CellKnowledge.excluded S₀)) :
                OptionT ProbComp Bool)] +
              Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad) |
                (($ (Finset.univ \ S₀)) >>= fun u =>
                  sharpBad (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                    (multipleBadAdvance tag sB
                      (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
                    (Function.update (Function.update K
                      ((tag, (0 : Fin sessionsPerTag)), n)
                      (CellKnowledge.known u)) ((tag, σf), n)
                      (CellKnowledge.excluded S₀)) :
                  OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))] + 0 + κ :=
            probEvent_bind_le_add_bad_disagree (D := fun _ : Digest => False)
              (by simp) hIH
        _ ≤ (Pr[(· = true) | (($ (Finset.univ : Finset Digest)) >>= fun u =>
                sharpS (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                  (Function.update (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                    (CellKnowledge.known u)) ((tag, σf), n) (CellKnowledge.excluded S₀)) :
                OptionT ProbComp Bool)] +
              (S₀.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞)) +
              Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad) |
                (($ (Finset.univ \ S₀)) >>= fun u =>
                  sharpBad (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                    (multipleBadAdvance tag sB
                      (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
                    (Function.update (Function.update K
                      ((tag, (0 : Fin sessionsPerTag)), n)
                      (CellKnowledge.known u)) ((tag, σf), n)
                      (CellKnowledge.excluded S₀)) :
                  OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))] + 0 + κ := by
            refine add_le_add (add_le_add (add_le_add ?_ le_rfl) le_rfl) le_rfl
            exact probEvent_bind_uniformSelectFinset_sdiff_le S₀ _ _
        _ = Pr[(· = true) | (($ (Finset.univ : Finset Digest)) >>= fun u =>
                sharpS (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                  (Function.update (Function.update K ((tag, (0 : Fin sessionsPerTag)), n)
                    (CellKnowledge.known u)) ((tag, σf), n) (CellKnowledge.excluded S₀)) :
                OptionT ProbComp Bool)] +
              Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad) |
                (($ (Finset.univ \ S₀)) >>= fun u =>
                  sharpBad (k (some (⟨n, u⟩ : TagTranscript Nonce Digest))) advM
                    (multipleBadAdvance tag sB
                      (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
                    (Function.update (Function.update K
                      ((tag, (0 : Fin sessionsPerTag)), n)
                      (CellKnowledge.known u)) ((tag, σf), n)
                      (CellKnowledge.excluded S₀)) :
                  OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))] +
              ((S₀.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) + κ) := by
            ring
  -- Average the per-nonce bound over the fresh nonce draw and close the budget.
  refine le_trans (probEvent_bind_le_add_bad_disagree_tsum
      (D := fun _ : Nonce => False) (ε₁ := 0)
      (ε₂ := fun n => (cellExclCard (K ((tag, (0 : Fin sessionsPerTag)), n)) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) + κ)
      (by simp) hPerN) ?_
  -- The averaged tilt is at most one carved tilt unit; the constant slack bundle averages to
  -- itself.
  have hAvg : (∑' n : Nonce, Pr[= n | (liftM ($ᵗ Nonce) : OptionT ProbComp Nonce)] *
      ((cellExclCard (K ((tag, (0 : Fin sessionsPerTag)), n)) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) + κ)) ≤
      ((qRInit : ℕ) : ℝ≥0∞) /
        ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) + κ := by
    have hPr : ∀ n : Nonce, Pr[= n | (liftM ($ᵗ Nonce) : OptionT ProbComp Nonce)] =
        ((Fintype.card Nonce : ℝ≥0∞))⁻¹ := fun n => by
      rw [OptionT.probOutput_liftM, probOutput_uniformSample]
    rw [tsum_fintype]
    calc ∑ n : Nonce, Pr[= n | (liftM ($ᵗ Nonce) : OptionT ProbComp Nonce)] *
        ((cellExclCard (K ((tag, (0 : Fin sessionsPerTag)), n)) : ℝ≥0∞) /
          (Fintype.card Digest : ℝ≥0∞) + κ)
        = (∑ n : Nonce, ((Fintype.card Nonce : ℝ≥0∞))⁻¹ *
            ((cellExclCard (K ((tag, (0 : Fin sessionsPerTag)), n)) : ℝ≥0∞) *
              ((Fintype.card Digest : ℝ≥0∞))⁻¹)) +
          (∑ _n : Nonce, ((Fintype.card Nonce : ℝ≥0∞))⁻¹ * κ) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hPr n, div_eq_mul_inv, mul_add]
      _ ≤ ((qRInit : ℕ) : ℝ≥0∞) /
            ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) + κ := by
          refine add_le_add ?_ ?_
          · rw [← Finset.mul_sum, ← Finset.sum_mul, ← Nat.cast_sum]
            have hrow : ((∑ n : Nonce,
                cellExclCard (K ((tag, (0 : Fin sessionsPerTag)), n)) : ℕ) : ℝ≥0∞) ≤
                ((qRInit : ℕ) : ℝ≥0∞) :=
              Nat.cast_le.mpr (le_trans (hKrow tag) (Nat.sub_le qRInit qR))
            rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
              (Or.inl (ENNReal.natCast_ne_top _))]
            calc ((Fintype.card Nonce : ℝ≥0∞))⁻¹ *
                (((∑ n : Nonce, cellExclCard (K ((tag, (0 : Fin sessionsPerTag)), n)) : ℕ) :
                  ℝ≥0∞) * ((Fintype.card Digest : ℝ≥0∞))⁻¹)
                ≤ ((Fintype.card Nonce : ℝ≥0∞))⁻¹ *
                  (((qRInit : ℕ) : ℝ≥0∞) * ((Fintype.card Digest : ℝ≥0∞))⁻¹) := by
                  gcongr
              _ = ((qRInit : ℕ) : ℝ≥0∞) *
                  ((Fintype.card Nonce : ℝ≥0∞)⁻¹ * (Fintype.card Digest : ℝ≥0∞)⁻¹) := by
                  ring
          · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
            exact mul_le_of_le_one_left zero_le (ENNReal.mul_inv_le_one _)
  calc Pr[(· = true) | ((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= ocF :
          OptionT ProbComp Bool)] +
        Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad) |
          ((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= obF :
            OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))] + 0 +
        (∑' n : Nonce, Pr[= n | (liftM ($ᵗ Nonce) : OptionT ProbComp Nonce)] *
          ((cellExclCard (K ((tag, (0 : Fin sessionsPerTag)), n)) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞) + κ))
      ≤ Pr[(· = true) | ((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= ocF :
            OptionT ProbComp Bool)] +
          Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad) |
            ((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= obF :
              OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))] + 0 +
          (((qRInit : ℕ) : ℝ≥0∞) /
            ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) + κ) := by
        exact add_le_add le_rfl hAvg
    _ = Pr[(· = true) | ((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= ocF :
            OptionT ProbComp Bool)] +
          Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad) |
            ((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= obF :
              OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))] +
          ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) /
            ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) +
          (((qRInit : ℕ) : ℝ≥0∞) /
            ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) +
          ((qT' * qRInit : ℕ) : ℝ≥0∞) /
            ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))) +
          ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) := by
        rw [hκ]
        ring

end SharpSlotPositiveMain

section SharpCouplingAux

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- **Sharp direct-coupling aux.** Over a shared table drawn from the consistent-table
distribution of a knowledge state satisfying the six-conjunct invariant, the instrumented
multiple-session success probability is bounded by the single-session success probability, the
bad-flag probability, and the fire, tilt, and discard slacks. Structural induction over the
adversary; the slot-positive tag and reader steps are supplied by `sharpAux_tag_slotPositive`
and `sharpAux_reader_step`. -/
lemma sharpCoupling_aux [Fintype Nonce] [Fintype Digest]
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) (qRInit qR qT : ℕ)
    (s : UnlinkState TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest)
    (hqR : OracleComp.IsQueryBoundP oa (·.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP oa (·.isLeft) qT)
    (hqRle : qR ≤ qRInit)
    (hKpos : slotPosExcluded K)
    (hKdead : liveSlotsFresh K s)
    (hKresp : knownRecorded K sB)
    (hKexcl : K.ExclLe (qRInit - qR))
    (hKrow : ∀ tag : TagId, slotZeroRowExcl K tag ≤ qRInit - qR)
    (hKfeas : K.Feasible) :
    Pr[= true | sharpM oa s sB K] ≤
      Pr[= true | sharpS oa s K] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | sharpBad oa s sB K] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) /
        ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) +
      ((qT * qRInit : ℕ) : ℝ≥0∞) /
        ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) := by
  classical
  induction oa using OracleComp.inductionOn generalizing qR qT s sB K hqRle hKpos hKdead
      hKresp hKexcl hKrow hKfeas with
  | pure b =>
    -- Both runs collapse to the constant `b`; the table and fine draws integrate out by
    -- feasibility.
    have hM : Pr[= true | sharpM (pure b) s sB K] = if b = true then 1 else 0 := by
      change Pr[= true | genTable K >>= fun _ => liftM _] = _
      simp only [simulateQ_pure, StateT.run_pure, map_pure, bind_pure_comp,
        probOutput_bind_const, probFailure_genTable hKfeas, tsub_zero, one_mul]
      rw [OptionT.probOutput_liftM]
      simp
    have hS : Pr[= true | sharpS (pure b) s K] = if b = true then 1 else 0 := by
      change Pr[= true | genTable K >>= fun _ => liftM _] = _
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure,
        probOutput_bind_const, probFailure_genTable hKfeas, tsub_zero, one_mul]
      rw [OptionT.probOutput_liftM]
      simp
    refine le_trans (le_of_eq hM) ?_
    rw [← hS]
    exact le_add_right (le_add_right (le_add_right (le_add_right le_rfl)))
  | query_bind t k ih =>
    cases t with
    | inl tag =>
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · by_cases hzero : s.sessionsUsed tag = 0
        · exact sharpAux_tag_slotZero qRInit qR qT s sB K hqRle hKpos hKdead hKresp hKexcl
            hKrow hKfeas tag k ih hqR hqT hslot hzero
        · exact sharpAux_tag_slotPositive qRInit qR qT s sB K hqRle hKpos hKdead hKresp
            hKexcl hKrow hKfeas tag k ih hqR hqT hslot hzero
      · -- Slot-exhausted: both heads return `none` with unchanged state.
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
        have hMstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            ∀ gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest,
            multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine
              (Sum.inl tag) (s, sB)
            = pure (none, s, sB) := by
          intro gS gFine
          change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) (Sum.inl tag)) s
              >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1))
              = _
          rw [multipleTableHandler_tag_run_of_not_lt _ tag s hslot]
          rfl
        have hSstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) gS (Sum.inl tag) s
            = pure (none, s) := fun gS =>
          singleTableHandler_tag_run_of_not_lt gS tag s hslot
        have hMeq : sharpM (liftM (OracleSpec.query (Sum.inl tag)) >>= k) s sB K
            = sharpM (k none) s sB K := by
          refine bind_congr fun gS => congrArg liftM ?_
          refine bind_congr fun gFine => ?_
          rw [multipleBadTableFine_run_query_bind', hMstep gS gFine, map_bind]
          exact pure_bind _ _
        have hSeq : sharpS (liftM (OracleSpec.query (Sum.inl tag)) >>= k) s K
            = sharpS (k none) s K := by
          refine bind_congr fun gS => congrArg liftM ?_
          rw [singleTable_run'_query_bind', hSstep gS]
          exact pure_bind _ _
        have hBeq : sharpBad (liftM (OracleSpec.query (Sum.inl tag)) >>= k) s sB K
            = sharpBad (k none) s sB K := by
          refine bind_congr fun gS => congrArg liftM ?_
          refine bind_congr fun gFine => ?_
          rw [multipleBadTableFine_run_query_bind', hMstep gS gFine, map_bind]
          exact pure_bind _ _
        rw [hMeq, hSeq, hBeq]
        refine (ih none qR qT' s sB K (hqRk none) (hqTk none) hqRle hKpos hKdead hKresp
          hKexcl hKrow hKfeas).trans ?_
        gcongr
        exact Nat.le_succ qT'
    | inr transcript =>
      exact sharpAux_reader_step qRInit qR qT s sB K hqRle hKpos hKdead hKresp hKexcl
        hKrow hKfeas transcript k ih hqR hqT

end SharpCouplingAux

end UnlinkReduction

end PRFTagReader
