/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.DirectCoupling.SharpAux

/-!
# PRF Tag/Reader Protocol — Sharp Coupling: Reader Case

The reader induction step of the sharp direct M_ideal/S_ideal coupling over the experiments and
six-conjunct invariant of `DirectCoupling/SharpAux.lean`.

At a reader query the multiple-session world tests the queried transcript against the
reference-slot column of the shared consistent table, while the single-session world tests it
against the whole column. The step is lazified at the *Boolean* level by the column probe split
(`evalDist_genTable_bind_probeColumnSplit`), shared by all three positions of the coupling:

* **Fire**: some genuine probe of the reference-slot column hits. The event costs at most
  `|TagId| / (|Digest| - qRInit)` (`probEvent_probeColumnSplit_fired_le` at the per-cell
  exclusion budget), and the whole M-side mass on it is dropped against the fire slack — the
  induction hypothesis is never consulted at a fired state.
* **Off-fire, reply `true` (honest replay)**: the reply is forced by a reference cell already
  determined to the transcript's digest, so the single-session reader accepts the same
  transcript through the same cell and both worlds continue on the `ok` reply at the residual
  knowledge state. Zero charge.
* **Off-fire, reply `false` (asymmetric discard)**: every reference cell of the column now
  excludes the digest, so the single-session reply reduces to the slot-positive collision
  indicator; replacing it by `ko` costs its mass under the residual table — a union bound of
  at most `|TagId| · sessionsPerTag / (|Digest| - qRInit)` over the slot-positive cells of the
  column (`probEvent_apply_eq_genTable_le` with `slotPosExcluded`).

The bad state's reader advance only ORs the slot-positive collision indicator into `cacheBad`,
a field invisible to the output bit and to the `bad` flag; the cacheBad-erasure bridge
(`evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_pointwise_eq` composed with
`evalDist_simulateQ_multipleBadTableHandler_cacheBad_irrelevant`) lets the induction hypothesis
fire at the un-advanced bad state.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

namespace UnlinkReduction

section SharpReaderBridge

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

omit [DecidableEq TagId] [DecidableEq Nonce] [SampleableType Nonce] [SampleableType Digest] in
/-- The multiple-session reader bit at the reference-slot sub-table is the reference-slot
column existential. -/
private lemma multipleAccepts_iff' (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) :
    (unlinkReaderAccepts (Slot := TagId)
        (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
        (multiplePattern sessionsPerTag) transcript = true) ↔
      ∃ T : TagId, gS ((T, (0 : Fin sessionsPerTag)), transcript.nonce) = transcript.auth := by
  haveI : Nonempty (Fin sessionsPerTag) := ⟨0⟩
  unfold unlinkReaderAccepts tagAccepts multiplePattern
  simp only [decide_eq_true_eq, slotZeroSubTable_apply, exists_const]

omit [DecidableEq TagId] [DecidableEq Nonce] [SampleableType Nonce] [SampleableType Digest]
  [NeZero sessionsPerTag] in
/-- The single-session reader bit is the full-column existential. -/
private lemma singleAccepts_iff' (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) :
    (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
        (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) transcript = true) ↔
      ∃ (T : TagId) (sid : Fin sessionsPerTag),
        gS ((T, sid), transcript.nonce) = transcript.auth := by
  unfold unlinkReaderAccepts tagAccepts singlePattern
  simp only [decide_eq_true_eq]

omit [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- A residual table never takes a value its knowledge state has ruled out. -/
private lemma apply_ne_of_notMem_allowed [Fintype Nonce] [Fintype Digest]
    {K : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest}
    {gS : (TagId × Fin sessionsPerTag) × Nonce → Digest}
    (hgS : gS ∈ support (genTable K)) {d : (TagId × Fin sessionsPerTag) × Nonce} {a : Digest}
    (ha : a ∉ (K d).allowed) : gS d ≠ a := by
  rcases hc : K d with v | S
  · rw [hc, CellKnowledge.allowed_known, Finset.mem_singleton] at ha
    rw [apply_eq_of_mem_support_genTable hgS hc]
    exact fun h => ha h.symm
  · rw [hc, CellKnowledge.allowed_excluded, Finset.mem_sdiff] at ha
    push Not at ha
    intro h
    exact apply_notMem_of_mem_support_genTable hgS hc (h ▸ ha (Finset.mem_univ a))

/-! ## Erasing the reader advance of the bad state

The reader step of the instrumented multiple-session handler advances the bad state by ORing
the slot-positive collision indicator of the *fine* table into `cacheBad`. Neither the output
bit nor the `bad` flag can see that field, so the marginals consumed by the coupling are
invariant under the advance. -/

omit [SampleableType Digest] in
/-- The `cacheBad`-overwritten run marginal is invariant under the reader advance of the
initial bad state. -/
private lemma evalDist_map_proj_run_readerAdv
    (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) (sB : UnlinkBadState TagId Nonce Digest)
    (transcript : TagTranscript Nonce Digest) :
    𝒟[(fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          (z.1, z.2.1, {z.2.2 with cacheBad := false})) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run
          (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
            gFine transcript sB)]
      = 𝒟[(fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          (z.1, z.2.1, {z.2.2 with cacheBad := false})) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run (s, sB)] :=
  (evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_pointwise_eq g gFine oa
      (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
        gFine transcript sB) false).trans
    ((evalDist_simulateQ_multipleBadTableHandler_cacheBad_irrelevant g oa s
        (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB)
        sB false rfl rfl rfl).trans
      (evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_pointwise_eq
        g gFine oa (s, sB) false).symm)

omit [SampleableType Digest] in
/-- The output-bit marginal of the instrumented run is invariant under the reader advance of
the initial bad state. -/
private lemma evalDist_map_fst_run_readerAdv
    (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) (sB : UnlinkBadState TagId Nonce Digest)
    (transcript : TagTranscript Nonce Digest) :
    𝒟[(fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run
          (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
            gFine transcript sB)]
      = 𝒟[(fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run (s, sB)] := by
  refine evalDist_ext fun b => ?_
  have hto : ∀ p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest,
      Pr[= b | (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          z.1) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run p]
      = Pr[fun w : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          w.1 = b |
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          (z.1, z.2.1, {z.2.2 with cacheBad := false})) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run p] := by
    intro p
    rw [← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
    exact probEvent_ext fun z _ => Iff.rfl
  rw [hto, hto,
    probEvent_eq_of_evalDist_eq
      (evalDist_map_proj_run_readerAdv g gFine oa s sB transcript) _]

omit [SampleableType Digest] in
/-- The bad-flag event of the instrumented run is invariant under the reader advance of the
initial bad state. -/
private lemma probEvent_bad_run_readerAdv
    (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) (sB : UnlinkBadState TagId Nonce Digest)
    (transcript : TagTranscript Nonce Digest) :
    Pr[fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.2.2.bad |
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run
          (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
            gFine transcript sB)]
      = Pr[fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          z.2.2.bad |
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run (s, sB)] := by
  have hto : ∀ p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest,
      Pr[fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          z.2.2.bad |
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run p]
      = Pr[fun w : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          w.2.2.bad |
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          (z.1, z.2.1, {z.2.2 with cacheBad := false})) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run p] := by
    intro p
    rw [probEvent_map]
    exact probEvent_ext fun z _ => Iff.rfl
  rw [hto, hto,
    probEvent_eq_of_evalDist_eq
      (evalDist_map_proj_run_readerAdv g gFine oa s sB transcript) _]

/-- The M-position of a reader step continues from the un-advanced bad state: the reader
advance only writes `cacheBad`, which the output bit cannot see. -/
private lemma evalDist_genTable_bind_fst_readerAdv [Fintype Nonce] [Fintype Digest]
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) (sB : UnlinkBadState TagId Nonce Digest)
    (transcript : TagTranscript Nonce Digest)
    (K' : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest) :
    𝒟[(genTable K' >>= fun gS => liftM (do
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) oa).run
            (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
              gFine transcript sB)) : OptionT ProbComp Bool)]
      = 𝒟[sharpM oa s sB K'] := by
  have h : 𝒟[(genTable K' >>= fun gS => liftM (do
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) oa).run
            (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
              gFine transcript sB)) : OptionT ProbComp Bool)]
      = 𝒟[(genTable K' >>= fun gS => liftM (do
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) oa).run
            (s, sB)) : OptionT ProbComp Bool)] :=
    evalDist_bind_congr fun gS _ => evalDist_liftM_congr
      (evalDist_bind_congr fun gFine _ =>
        evalDist_map_fst_run_readerAdv _ gFine oa s sB transcript)
  exact h

/-- The bad-position of a reader step continues from the un-advanced bad state: the reader
advance only writes `cacheBad`, which the `bad` flag cannot see. -/
private lemma probEvent_genTable_bind_bad_readerAdv [Fintype Nonce] [Fintype Digest]
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) (sB : UnlinkBadState TagId Nonce Digest)
    (transcript : TagTranscript Nonce Digest)
    (K' : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest) :
    Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (genTable K' >>= fun gS => liftM (do
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) oa).run
              (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                gFine transcript sB)) :
          OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))]
      = Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
          sharpBad oa s sB K'] := by
  unfold sharpBad
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun gS => ?_
  refine congrArg (fun x => Pr[= gS | (genTable K' : OptionT ProbComp _)] * x) ?_
  rw [OptionT.probEvent_liftM, OptionT.probEvent_liftM, probEvent_bind_eq_tsum,
    probEvent_bind_eq_tsum]
  refine tsum_congr fun gFine => ?_
  refine congrArg
    (fun x => Pr[= gFine | $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)] * x) ?_
  rw [probEvent_map, probEvent_map]
  refine ((probEvent_ext fun z _ => Iff.rfl).trans ?_).trans
    ((probEvent_ext fun z _ => Iff.rfl).symm)
  exact probEvent_bad_run_readerAdv _ gFine oa s sB transcript

end SharpReaderBridge

section SharpReaderMain

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
  classical
  have hqRsplit := hqR
  rw [OracleComp.isQueryBoundP_query_bind_iff] at hqRsplit
  have hqRpos : 0 < qR := hqRsplit.1.resolve_left (fun h => absurd rfl h)
  obtain ⟨qR', rfl⟩ : ∃ qR', qR = qR' + 1 := ⟨qR - 1, by omega⟩
  have hqRk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isRight) qR' := fun u => by
    simpa using hqRsplit.2 u
  have hqTsplit := hqT
  rw [OracleComp.isQueryBoundP_query_bind_iff] at hqTsplit
  have hqTk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isLeft) qT := fun u => by
    simpa using hqTsplit.2 u
  have hqRle' : qR' ≤ qRInit := by omega
  -- The probed column: the reference-slot cells at the queried nonce.
  set cells : List ((TagId × Fin sessionsPerTag) × Nonce) :=
    (Finset.univ.toList).map
      (fun T : TagId => ((T, (0 : Fin sessionsPerTag)), transcript.nonce)) with hcells
  have hnd : cells.Nodup := by
    rw [hcells]
    exact (Finset.nodup_toList _).map fun T₁ T₂ h => congrArg (fun p => p.1.1) h
  have hlen : cells.length = Fintype.card TagId := by
    rw [hcells, List.length_map, Finset.length_toList, Finset.card_univ]
  have hcells0 : ∀ d ∈ cells, d.1.2 = (0 : Fin sessionsPerTag) := by
    intro d hd
    rw [hcells] at hd
    obtain ⟨T, -, rfl⟩ := List.mem_map.mp hd
    rfl
  have hcoln : ∀ d ∈ cells, d.2 = transcript.nonce := by
    intro d hd
    rw [hcells] at hd
    obtain ⟨T, -, rfl⟩ := List.mem_map.mp hd
    rfl
  have hmemcells : ∀ T : TagId,
      ((T, (0 : Fin sessionsPerTag)), transcript.nonce) ∈ cells := by
    intro T
    rw [hcells]
    exact List.mem_map.mpr ⟨T, Finset.mem_toList.mpr (Finset.mem_univ T), rfl⟩
  -- Head-step collapse: the reader replies are deterministic in the table.
  have hMstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      ∀ gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest,
      multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine
        (Sum.inr transcript) (s, sB)
      = pure (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
          (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
          (multiplePattern sessionsPerTag) transcript), s,
          multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
            gFine transcript sB) := by
    intro gS gFine
    change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) (Sum.inr transcript)) s
        >>= (fun r => pure (r.1, r.2,
          multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB))
        = _
    rw [multipleTableHandler_reader_run]
    exact pure_bind _ _
  have hSstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) gS (Sum.inr transcript) s
      = pure (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) transcript), s) :=
    fun gS => singleTableHandler_reader_run gS transcript s
  -- The three positions of the step, with the head query absorbed.
  set MBf : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → OptionT ProbComp Bool :=
    fun gS => liftM (do
      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
      (fun w : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => w.1) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
          (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
          (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
            (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
            (multiplePattern sessionsPerTag) transcript)))).run
          (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
            gFine transcript sB)) with hMBf
  set SBf : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → OptionT ProbComp Bool :=
    fun gS => liftM
      ((simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
        (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) transcript)))).run' s)
    with hSBf
  set BBf : ((TagId × Fin sessionsPerTag) × Nonce → Digest) →
      OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest) :=
    fun gS => liftM (do
      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
      (fun w : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          (w.1, w.2.2)) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
          (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
          (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
            (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
            (multiplePattern sessionsPerTag) transcript)))).run
          (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
            gFine transcript sB)) with hBBf
  have hMprog : sharpM (liftM (OracleSpec.query (Sum.inr transcript)) >>= k) s sB K
      = genTable K >>= MBf := by
    rw [hMBf]
    refine bind_congr fun gS => congrArg liftM ?_
    refine bind_congr fun gFine => ?_
    rw [multipleBadTableFine_run_query_bind', hMstep gS gFine, map_bind]
    exact pure_bind _ _
  have hSprog : sharpS (liftM (OracleSpec.query (Sum.inr transcript)) >>= k) s K
      = genTable K >>= SBf := by
    rw [hSBf]
    refine bind_congr fun gS => congrArg liftM ?_
    rw [singleTable_run'_query_bind', hSstep gS]
    exact pure_bind _ _
  have hBprog : sharpBad (liftM (OracleSpec.query (Sum.inr transcript)) >>= k) s sB K
      = genTable K >>= BBf := by
    rw [hBBf]
    refine bind_congr fun gS => congrArg liftM ?_
    refine bind_congr fun gFine => ?_
    rw [multipleBadTableFine_run_query_bind', hMstep gS gFine, map_bind]
    exact pure_bind _ _
  rw [hMprog, hSprog, hBprog,
    probOutput_eq_of_evalDist_eq (evalDist_genTable_bind_probeColumnSplit
      transcript.auth cells K MBf) true,
    probOutput_eq_of_evalDist_eq (evalDist_genTable_bind_probeColumnSplit
      transcript.auth cells K SBf) true,
    probEvent_eq_of_evalDist_eq (evalDist_genTable_bind_probeColumnSplit
      transcript.auth cells K BBf) _]
  simp only [← probEvent_eq_eq_probOutput]
  -- One reader unit of each `qR`-indexed slack is consumed by the step.
  have hSplitF : (((qR' + 1) * Fintype.card TagId : ℕ) : ℝ≥0∞) /
      ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞)
      = ((Fintype.card TagId : ℕ) : ℝ≥0∞) /
          ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) +
        ((qR' * Fintype.card TagId : ℕ) : ℝ≥0∞) /
          ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) := by
    rw [show (qR' + 1) * Fintype.card TagId
        = Fintype.card TagId + qR' * Fintype.card TagId from by ring,
      Nat.cast_add, ENNReal.add_div]
  have hSplitD : (((qR' + 1) * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
      ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞)
      = ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
          ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) +
        ((qR' * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
          ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) := by
    rw [show (qR' + 1) * Fintype.card TagId * sessionsPerTag
        = Fintype.card TagId * sessionsPerTag
          + qR' * Fintype.card TagId * sessionsPerTag from by ring,
      Nat.cast_add, ENNReal.add_div]
  rw [hSplitF, hSplitD]
  rw [show ∀ a b fU fR t dU dR : ℝ≥0∞,
      a + b + (fU + fR) + t + (dU + dR) = a + b + fU + (fR + t + dR + dU) from
      fun a b fU fR t dU dR => by ring]
  set κ : ℝ≥0∞ :=
    ((qR' * Fintype.card TagId : ℕ) : ℝ≥0∞) /
      ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) +
    ((qT * qRInit : ℕ) : ℝ≥0∞) /
      ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)) +
    ((qR' * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
      ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) with hκ
  refine probEvent_bind_le_add_bad_disagree
    (D := fun z : Bool × Bool × ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest =>
      z.2.1 = true) ?_ ?_
  · -- Fire mass: some genuine probe of the column hits.
    refine le_trans (probEvent_probeColumnSplit_fired_le transcript.auth cells
      (qRInit - (qR' + 1)) K hKexcl) ?_
    rw [hlen, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul' le_rfl (ENNReal.inv_le_inv'
      (Nat.cast_le.mpr (Nat.sub_le_sub_left (Nat.sub_le qRInit (qR' + 1)) _)))
  · intro z hz hDz
    have hfired : z.2.1 = false := Bool.eq_false_iff.mpr hDz
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
      probeColumnSplit_support transcript.auth cells K hnd hz
    obtain ⟨t1, t2, t3, t4⟩ := sharpInv_probeColumnSplit (s := s) (sB := sB)
      transcript.auth cells K hnd hcells0 hz
    have hExcl' : z.2.2.ExclLe (qRInit - qR') := by
      have h := probeColumnSplit_support_exclLe transcript.auth cells K hnd hz hKexcl
      rwa [show qRInit - (qR' + 1) + 1 = qRInit - qR' from by omega] at h
    have hRow' : ∀ tag : TagId, slotZeroRowExcl z.2.2 tag ≤ qRInit - qR' := by
      intro tag
      have h := slotZeroRowExcl_probeColumnSplit_le transcript.auth transcript.nonce
        cells K hnd hcoln hz tag
      have h2 := hKrow tag
      omega
    -- The replay witness behind a `true` reply off the fire event.
    have hknown : z.1 = true → ∃ T : TagId,
        z.2.2 ((T, (0 : Fin sessionsPerTag)), transcript.nonce)
          = CellKnowledge.known transcript.auth := by
      intro hz1
      rcases c5 hz1 with hf | ⟨d, hd, hk⟩
      · exact absurd hf (by simp [hfired])
      · have hd' := hd
        rw [hcells] at hd'
        obtain ⟨T, -, rfl⟩ := List.mem_map.mp hd'
        refine ⟨T, ?_⟩
        rcases c3 _ hd with heq | ⟨hf, -⟩ | ⟨S, hS, -, -⟩
        · rw [heq]
          exact hk
        · exact absurd hf (by simp [hfired])
        · rw [hk] at hS
          simp at hS
    -- Off the fire event the multiple-session reply equals the recorded bit.
    have hreply : ∀ gS ∈ support (genTable z.2.2), unlinkReaderAccepts (Slot := TagId)
        (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
        (multiplePattern sessionsPerTag) transcript = z.1 := by
      intro gS hgS
      cases hz1 : z.1 with
      | false =>
        refine Bool.eq_false_iff.mpr fun htrue => ?_
        obtain ⟨T, hT⟩ := (multipleAccepts_iff' gS transcript).mp htrue
        exact apply_ne_of_notMem_allowed hgS (c2 hz1 _ (hmemcells T)) hT
      | true =>
        obtain ⟨T, hc⟩ := hknown hz1
        exact (multipleAccepts_iff' gS transcript).mpr
          ⟨T, apply_eq_of_mem_support_genTable hgS hc⟩
    -- M and bad positions: constant reply, un-advanced bad state.
    have hMz : Pr[(· = true) | (genTable z.2.2 >>= MBf : OptionT ProbComp Bool)]
        = Pr[(· = true) | sharpM (k (ReaderReply.ofBool z.1)) s sB z.2.2] := by
      have h1 : 𝒟[(genTable z.2.2 >>= MBf : OptionT ProbComp Bool)]
          = 𝒟[(genTable z.2.2 >>= fun gS => liftM (do
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun w : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  w.1) <$>
                (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
                  (k (ReaderReply.ofBool z.1))).run
                  (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                    gFine transcript sB)) : OptionT ProbComp Bool)] := by
        rw [hMBf]
        exact evalDist_bind_congr fun gS hgS => by rw [hreply gS hgS]
      rw [probEvent_eq_of_evalDist_eq h1 _,
        probEvent_eq_of_evalDist_eq (evalDist_genTable_bind_fst_readerAdv
          (k (ReaderReply.ofBool z.1)) s sB transcript z.2.2) _]
    have hBz : Pr[(fun w : Bool × UnlinkBadState TagId Nonce Digest => w.2.bad) |
        (genTable z.2.2 >>= BBf :
          OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))]
        = Pr[(fun w : Bool × UnlinkBadState TagId Nonce Digest => w.2.bad) |
          sharpBad (k (ReaderReply.ofBool z.1)) s sB z.2.2] := by
      have h1 : 𝒟[(genTable z.2.2 >>= BBf :
            OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))]
          = 𝒟[(genTable z.2.2 >>= fun gS => liftM (do
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun w : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  (w.1, w.2.2)) <$>
                (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine)
                  (k (ReaderReply.ofBool z.1))).run
                  (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                    gFine transcript sB)) :
              OptionT ProbComp (Bool × UnlinkBadState TagId Nonce Digest))] := by
        rw [hBBf]
        exact evalDist_bind_congr fun gS hgS => by rw [hreply gS hgS]
      rw [probEvent_eq_of_evalDist_eq h1 _]
      exact probEvent_genTable_bind_bad_readerAdv
        (k (ReaderReply.ofBool z.1)) s sB transcript z.2.2
    rw [hMz, hBz]
    have hih := ih (ReaderReply.ofBool z.1) qR' qT s sB z.2.2 (hqRk _) (hqTk _) hqRle'
      (t1 hKpos) (t2 hKdead) (t3 hfired hKresp) hExcl' hRow' (t4 hKfeas)
    by_cases hm : z.1 = true
    · -- Honest replay: the single-session reader accepts through the same reference cell.
      have hSz : Pr[(· = true) | (genTable z.2.2 >>= SBf : OptionT ProbComp Bool)]
          = Pr[(· = true) | sharpS (k (ReaderReply.ofBool z.1)) s z.2.2] := by
        have h1 : 𝒟[(genTable z.2.2 >>= SBf : OptionT ProbComp Bool)]
            = 𝒟[(genTable z.2.2 >>= fun gS => liftM
                ((simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
                  (k (ReaderReply.ofBool z.1))).run' s) : OptionT ProbComp Bool)] := by
          rw [hSBf]
          refine evalDist_bind_congr fun gS hgS => ?_
          obtain ⟨T, hc⟩ := hknown hm
          have hacc : unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) transcript
              = z.1 := by
            rw [hm]
            exact (singleAccepts_iff' gS transcript).mpr
              ⟨T, 0, apply_eq_of_mem_support_genTable hgS hc⟩
          rw [hacc]
        exact probEvent_eq_of_evalDist_eq h1 _
      rw [hSz]
      refine le_trans ?_ (add_le_add le_rfl le_self_add)
      rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput, hκ,
        ← add_assoc, ← add_assoc]
      exact hih
    · -- Asymmetric discard: the single-session reply reduces to the slot-positive
      -- collision indicator, replaced by `ko` at the cost of its residual mass.
      have hm' : z.1 = false := Bool.eq_false_iff.mpr hm
      have hmass : Pr[fun gS : (TagId × Fin sessionsPerTag) × Nonce → Digest =>
          unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
            (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) transcript = true |
          (genTable z.2.2 : OptionT ProbComp ((TagId × Fin sessionsPerTag) × Nonce →
            Digest))] ≤
          ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) := by
        have himp : ∀ gS ∈ support (genTable z.2.2),
            unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) transcript = true →
            ∃ sl ∈ Finset.univ.filter
              (fun sl : TagId × Fin sessionsPerTag => sl.2 ≠ 0),
              gS (sl, transcript.nonce) = transcript.auth := by
          intro gS hgS hacc
          obtain ⟨T, sid, h⟩ := (singleAccepts_iff' gS transcript).mp hacc
          rcases eq_or_ne sid 0 with rfl | hsid
          · exact absurd h (apply_ne_of_notMem_allowed hgS (c2 hm' _ (hmemcells T)))
          · exact ⟨(T, sid), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsid⟩, h⟩
        refine le_trans (probEvent_mono himp) ?_
        refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
        refine le_trans (Finset.sum_le_card_nsmul _ _
          (((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞))⁻¹ fun sl hsl => ?_) ?_
        · have hsid := (Finset.mem_filter.mp hsl).2
          have hnotmem : (sl, transcript.nonce) ∉ cells := fun hmem =>
            hsid (hcells0 _ hmem)
          obtain ⟨S, hS⟩ := hKpos sl.1 sl.2 hsid transcript.nonce
          have hS' : z.2.2 (sl, transcript.nonce) = CellKnowledge.excluded S :=
            (c1 _ hnotmem).trans hS
          refine le_trans (probEvent_apply_eq_genTable_le z.2.2 hS' transcript.auth) ?_
          exact ENNReal.inv_le_inv' (Nat.cast_le.mpr (Nat.sub_le_sub_left
            (le_trans (hKexcl _ S hS) (Nat.sub_le qRInit (qR' + 1))) _))
        · rw [nsmul_eq_mul, div_eq_mul_inv]
          refine mul_le_mul' (Nat.cast_le.mpr ?_) le_rfl
          refine le_trans (Finset.card_filter_le _ _) (le_of_eq ?_)
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      have hSdisc : Pr[(· = true) | sharpS (k (ReaderReply.ofBool z.1)) s z.2.2]
          ≤ Pr[(· = true) | (genTable z.2.2 >>= SBf : OptionT ProbComp Bool)] +
            ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
              ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞) := by
        rw [hSBf]
        refine le_trans (probEvent_bind_le_add_tsum
          (mx := (genTable z.2.2 : OptionT ProbComp ((TagId × Fin sessionsPerTag) ×
            Nonce → Digest)))
          (oc := fun gS => liftM
            ((simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS)
              (k (ReaderReply.ofBool (unlinkReaderAccepts
                (Slot := TagId × Fin sessionsPerTag) (fun sl nn => gS (sl, nn))
                (singlePattern sessionsPerTag) transcript)))).run' s))
          (ε := fun gS => if unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) transcript = true
            then 1 else 0)
          fun gS _ => ?_) (add_le_add le_rfl ?_)
        · beta_reduce
          by_cases hacc : unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) transcript = true
          · rw [if_pos hacc]
            exact le_trans probEvent_le_one le_add_self
          · have hacc' : unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
                (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) transcript
                = false := Bool.eq_false_iff.mpr hacc
            rw [if_neg hacc, add_zero, hacc', hm']
        · refine le_trans (le_of_eq ?_) hmass
          rw [probEvent_eq_tsum_ite]
          exact tsum_congr fun gS => by rw [mul_ite, mul_one, mul_zero]
      calc Pr[(· = true) | sharpM (k (ReaderReply.ofBool z.1)) s sB z.2.2]
          ≤ Pr[(· = true) | sharpS (k (ReaderReply.ofBool z.1)) s z.2.2] +
            Pr[(fun w : Bool × UnlinkBadState TagId Nonce Digest => w.2.bad) |
              sharpBad (k (ReaderReply.ofBool z.1)) s sB z.2.2] + κ := by
            rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput, hκ,
              ← add_assoc, ← add_assoc]
            exact hih
        _ ≤ (Pr[(· = true) | (genTable z.2.2 >>= SBf : OptionT ProbComp Bool)] +
              ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
                ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞)) +
            Pr[(fun w : Bool × UnlinkBadState TagId Nonce Digest => w.2.bad) |
              sharpBad (k (ReaderReply.ofBool z.1)) s sB z.2.2] + κ :=
            add_le_add (add_le_add hSdisc le_rfl) le_rfl
        _ = Pr[(· = true) | (genTable z.2.2 >>= SBf : OptionT ProbComp Bool)] +
            Pr[(fun w : Bool × UnlinkBadState TagId Nonce Digest => w.2.bad) |
              sharpBad (k (ReaderReply.ofBool z.1)) s sB z.2.2] +
            (κ + ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
              ((Fintype.card Digest - qRInit : ℕ) : ℝ≥0∞)) := by
            ring

end SharpReaderMain

end UnlinkReduction

end PRFTagReader
