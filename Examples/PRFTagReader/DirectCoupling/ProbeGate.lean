/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.DirectCoupling
import Examples.PRFTagReader.MultipleToHybrid.EagerSetup
import VCVio.EvalDist.Monad.Disagreement
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeColumn
import VCVio.OracleComp.QueryTracking.RandomOracle.RevealTilt

/-!
# PRF Tag/Reader Protocol — Probe-Coupling Gate: A Two-Step Tilt Instance

A minimal two-step instance of the direct M_ideal/S_ideal coupling routed through the
consistent-table distribution `genTable`: one reader test at a fixed transcript `⟨n₀, a₀⟩`
followed by one slot-positive tag read at a fresh uniform nonce, with an arbitrary Boolean
continuation `F` of the reader bit, the nonce, and the read digest.

Both worlds read one shared table drawn from `genTable (ProbeState.init _ _)` over the
single-session cell domain `(TagId × Fin sessionsPerTag) × Nonce`. The reader step is lazified
at the *Boolean* level: `evalDist_genTable_bind_probeColumnSplit` redistributes the table draw
along the slot-zero column at `n₀`, materializing one comparison bit per tag — never the cell
values — and leaving the residual table distributed as `genTable` of the post-probe knowledge
state: hit cells `known a₀`, miss cells `excluded {a₀}`. The tag step then reveals the M-side
cell `((tag, 0), n)` from its *conditioned* allowed set, and the S-side cell `((tag, σ), n)`
with `σ ≠ 0` from the *untouched* full set — the slot-positive cells are off the probed column,
so the S-side reveal is a full uniform; the proof would not close here if the reader step had
conditioned them.

`probeGate_two_step` assembles the comparison: the M-side success probability is at most the
S-side success probability plus three explicit charges, each tied to one mechanism:

* `|TagId| / |Digest|` — the *fire* mass: some probe of the column genuinely hits
  (`probEvent_probeColumnSplit_fired_le`, with `probeColumnSplit_support` identifying the
  reply with the fired flag at the initial state); off this event the M reader bit is `false`
  deterministically in the knowledge state alone.
* `(|Nonce| · |Digest|)⁻¹` — the *reveal tilt*: the probed column carries one exclusion in the
  M-side row, so the per-nonce defect `|Digest|⁻¹` of
  `probEvent_bind_uniformSelectFinset_sdiff_le` is paid only at the aliasing nonce `n₀`,
  averaged over the fresh nonce draw by `probEvent_bind_le_add_tsum`.
* `|TagId| · sessionsPerTag / |Digest|` — the *slot-positive discard*: off the fire event the
  S reader bit equals the slot-positive collision indicator `cacheBadReader`, which is replaced
  by `false` at the cost of its mass under the residual `genTable`
  (`probEvent_apply_eq_genTable_le` and a union bound).
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section ProbeGate

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId]
  [DecidableEq Nonce] [Fintype Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [Fintype Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

omit [DecidableEq TagId] [DecidableEq Nonce] [Fintype Nonce] [SampleableType Nonce]
  [Fintype Digest] in
/-- The multiple-session reader bit at the slot-zero sub-table is the slot-zero column
existential. -/
private lemma multipleAccepts_iff (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (n₀ : Nonce) (a₀ : Digest) :
    (unlinkReaderAccepts (Slot := TagId)
        (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
        (multiplePattern sessionsPerTag) ⟨n₀, a₀⟩ = true) ↔
      ∃ T : TagId, gS ((T, (0 : Fin sessionsPerTag)), n₀) = a₀ := by
  haveI : Nonempty (Fin sessionsPerTag) := ⟨0⟩
  unfold unlinkReaderAccepts tagAccepts multiplePattern
  simp only [decide_eq_true_eq, slotZeroSubTable_apply, exists_const]

omit [DecidableEq TagId] [DecidableEq Nonce] [Fintype Nonce] [SampleableType Nonce]
  [Fintype Digest] [NeZero sessionsPerTag] in
/-- The single-session reader bit is the full-column existential. -/
private lemma singleAccepts_iff (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (n₀ : Nonce) (a₀ : Digest) :
    (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
        (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) ⟨n₀, a₀⟩ = true) ↔
      ∃ (T : TagId) (sid : Fin sessionsPerTag), gS ((T, sid), n₀) = a₀ := by
  unfold unlinkReaderAccepts tagAccepts singlePattern
  simp only [decide_eq_true_eq]

/-- **Tag-step reveal tilt.** With the M-side row fresh everywhere except the probed column
`n₀` — where it has excluded exactly `a₀` — and the S-side slot untouched everywhere, the
M-side read of `((tag, 0), n)` at a fresh uniform nonce is within
`(|Nonce| · |Digest|)⁻¹` of the S-side read of `((tag, σ), n)`: off `n₀` the two reveals are
the same full uniform, and at `n₀` the reveal tilt `|Digest|⁻¹` is averaged by the nonce
draw. -/
private lemma probOutput_tag_reveal_tilt
    (K' : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest) (hfeas : K'.Feasible)
    (tag : TagId) (σ : Fin sessionsPerTag) (n₀ : Nonce) (a₀ : Digest)
    (h0 : K' ((tag, (0 : Fin sessionsPerTag)), n₀) = CellKnowledge.excluded {a₀})
    (hfresh : ∀ n, n ≠ n₀ →
      K' ((tag, (0 : Fin sessionsPerTag)), n) = CellKnowledge.excluded ∅)
    (hσ : ∀ n : Nonce, K' ((tag, σ), n) = CellKnowledge.excluded ∅)
    (G : Nonce → Digest → Bool) :
    Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
        pure (G n (gS ((tag, (0 : Fin sessionsPerTag)), n))) : OptionT ProbComp Bool)] ≤
      Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (G n (gS ((tag, σ), n))) : OptionT ProbComp Bool)] +
        ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))⁻¹ := by
  classical
  have hMcomm : Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
      pure (G n (gS ((tag, (0 : Fin sessionsPerTag)), n))) : OptionT ProbComp Bool)]
      = Pr[= true | ((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= fun n =>
        genTable K' >>= fun gS =>
          pure (G n (gS ((tag, (0 : Fin sessionsPerTag)), n))) : OptionT ProbComp Bool)] :=
    probOutput_eq_of_evalDist_eq (evalDist_bind_bind_comm _ _ _) true
  have hScomm : Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
      pure (G n (gS ((tag, σ), n))) : OptionT ProbComp Bool)]
      = Pr[= true | ((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= fun n =>
        genTable K' >>= fun gS =>
          pure (G n (gS ((tag, σ), n))) : OptionT ProbComp Bool)] :=
    probOutput_eq_of_evalDist_eq (evalDist_bind_bind_comm _ _ _) true
  rw [hMcomm, hScomm, ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  refine le_trans (probEvent_bind_le_add_tsum
    (oc := fun n => genTable K' >>= fun gS => pure (G n (gS ((tag, σ), n))))
    (ε := fun n => if n = n₀ then (Fintype.card Digest : ℝ≥0∞)⁻¹ else 0)
    fun n _ => ?_) ?_
  · beta_reduce
    simp only [probEvent_eq_eq_probOutput]
    have hS : Pr[= true | (genTable K' >>= fun gS =>
        pure (G n (gS ((tag, σ), n))) : OptionT ProbComp Bool)]
        = Pr[= true | ($ (Finset.univ \ (∅ : Finset Digest))) >>= fun v =>
            (pure (G n v) : OptionT ProbComp Bool)] :=
      probOutput_genTable_bind_pure_comp K' hfeas (hσ n) (G n) true
    by_cases hn : n = n₀
    · subst hn
      rw [probOutput_genTable_bind_pure_comp K' hfeas h0 (G n) true, hS,
        Finset.sdiff_empty, if_pos rfl]
      have htilt := probEvent_bind_uniformSelectFinset_sdiff_le (V := Digest) {a₀}
        (fun v => (pure (G n v) : OptionT ProbComp Bool)) (· = true)
      simp only [probEvent_eq_eq_probOutput, Finset.card_singleton, Nat.cast_one,
        one_div] at htilt
      exact htilt
    · rw [probOutput_genTable_bind_pure_comp K' hfeas (hfresh n hn) (G n) true, hS,
        Finset.sdiff_empty, if_neg hn, add_zero]
  · refine add_le_add le_rfl ?_
    have hw : ∀ n : Nonce, Pr[= n | (liftM ($ᵗ Nonce) : OptionT ProbComp Nonce)]
        = (Fintype.card Nonce : ℝ≥0∞)⁻¹ := fun n => by
      rw [OptionT.probOutput_liftM, probOutput_uniformSample]
    rw [tsum_fintype]
    simp only [hw, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ n₀
      (fun _ => (Fintype.card Nonce : ℝ≥0∞)⁻¹ * (Fintype.card Digest : ℝ≥0∞)⁻¹),
      if_pos (Finset.mem_univ n₀)]
    exact le_of_eq (ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))).symm

/-- **Off-fire step.** From a residual knowledge state whose slot-zero column at `n₀` has
excluded exactly `a₀`, whose remaining `tag`-row slot-zero cells are fresh, and whose
slot-positive cells are all fresh: the M-side continuation (reader bit `false` forced by the
recorded misses, tag read at slot zero) is within `(|Nonce| · |Digest|)⁻¹ +
|TagId| · sessionsPerTag / |Digest|` of the S-side continuation (actual reader bit, tag read at
the live slot `σ`). -/
private lemma probeGate_offFire (tag : TagId) (σ : Fin sessionsPerTag) (hσ0 : σ ≠ 0)
    (n₀ : Nonce) (a₀ : Digest) (F : Bool → Nonce → Digest → Bool)
    (K' : ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest) (hfeas : K'.Feasible)
    (hcol : ∀ T : TagId,
      K' ((T, (0 : Fin sessionsPerTag)), n₀) = CellKnowledge.excluded {a₀})
    (hfresh : ∀ n, n ≠ n₀ →
      K' ((tag, (0 : Fin sessionsPerTag)), n) = CellKnowledge.excluded ∅)
    (hpos : ∀ (T : TagId) (sid : Fin sessionsPerTag), sid ≠ 0 → ∀ n : Nonce,
      K' ((T, sid), n) = CellKnowledge.excluded ∅) :
    Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
        pure (F (unlinkReaderAccepts (Slot := TagId)
            (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
            (multiplePattern sessionsPerTag) ⟨n₀, a₀⟩)
          n (gS ((tag, (0 : Fin sessionsPerTag)), n))) : OptionT ProbComp Bool)] ≤
      Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (F (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) ⟨n₀, a₀⟩)
            n (gS ((tag, σ), n))) : OptionT ProbComp Bool)] +
        (((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))⁻¹ +
          ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞)) := by
  classical
  -- The M reader bit is deterministically `false` on the support of the residual table.
  have hLcongr : Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
      pure (F (unlinkReaderAccepts (Slot := TagId)
          (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
          (multiplePattern sessionsPerTag) ⟨n₀, a₀⟩)
        n (gS ((tag, (0 : Fin sessionsPerTag)), n))) : OptionT ProbComp Bool)]
      = Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
        pure (F false n (gS ((tag, (0 : Fin sessionsPerTag)), n))) : OptionT ProbComp Bool)] :=
    probOutput_bind_congr fun gS hgS => by
      have hmB : unlinkReaderAccepts (Slot := TagId)
          (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
          (multiplePattern sessionsPerTag)
          (⟨n₀, a₀⟩ : TagTranscript Nonce Digest) = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        obtain ⟨T, hT⟩ := (multipleAccepts_iff gS n₀ a₀).mp htrue
        exact apply_notMem_of_mem_support_genTable hgS (hcol T)
          (Finset.mem_singleton.mpr hT)
      rw [hmB]
  -- The S reader bit equals the slot-positive collision indicator on the support.
  have hScongr : Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
      pure (F (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) ⟨n₀, a₀⟩)
        n (gS ((tag, σ), n))) : OptionT ProbComp Bool)]
      = Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
        pure (F (cacheBadReader (sessionsPerTag := sessionsPerTag) gS ⟨n₀, a₀⟩)
          n (gS ((tag, σ), n))) : OptionT ProbComp Bool)] :=
    probOutput_bind_congr fun gS hgS => by
      have hsB : unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag)
          (⟨n₀, a₀⟩ : TagTranscript Nonce Digest)
          = cacheBadReader (sessionsPerTag := sessionsPerTag) gS ⟨n₀, a₀⟩ := by
        rw [Bool.eq_iff_iff, singleAccepts_iff, cacheBadReader_eq_true_iff]
        constructor
        · rintro ⟨T, sid, h⟩
          rcases eq_or_ne sid 0 with rfl | hsid
          · exact absurd (Finset.mem_singleton.mpr h)
              (apply_notMem_of_mem_support_genTable hgS (hcol T))
          · exact ⟨T, sid, hsid, h⟩
        · rintro ⟨T, sid, -, h⟩
          exact ⟨T, sid, h⟩
      rw [hsB]
  -- Discard the slot-positive collision branch of the S reader bit.
  have hdisc : Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
      pure (F false n (gS ((tag, σ), n))) : OptionT ProbComp Bool)] ≤
      Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
        pure (F (cacheBadReader (sessionsPerTag := sessionsPerTag) gS ⟨n₀, a₀⟩)
          n (gS ((tag, σ), n))) : OptionT ProbComp Bool)] +
      Pr[fun gS => cacheBadReader (sessionsPerTag := sessionsPerTag) gS
          (⟨n₀, a₀⟩ : TagTranscript Nonce Digest) = true | genTable K'] := by
    rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
    refine le_trans (probEvent_bind_le_add_tsum
      (oc := fun gS => liftM ($ᵗ Nonce) >>= fun n =>
        pure (F (cacheBadReader (sessionsPerTag := sessionsPerTag) gS ⟨n₀, a₀⟩)
          n (gS ((tag, σ), n))))
      (ε := fun gS => if cacheBadReader (sessionsPerTag := sessionsPerTag) gS
        (⟨n₀, a₀⟩ : TagTranscript Nonce Digest) = true then 1 else 0)
      fun gS _ => ?_) ?_
    · beta_reduce
      simp only [probEvent_eq_eq_probOutput]
      by_cases hcb : cacheBadReader (sessionsPerTag := sessionsPerTag) gS
          (⟨n₀, a₀⟩ : TagTranscript Nonce Digest) = true
      · rw [if_pos hcb]
        exact le_trans probOutput_le_one le_add_self
      · have hcb' : cacheBadReader (sessionsPerTag := sessionsPerTag) gS
            (⟨n₀, a₀⟩ : TagTranscript Nonce Digest) = false := Bool.eq_false_iff.mpr hcb
        rw [if_neg hcb, add_zero, hcb']
    · refine add_le_add le_rfl (le_of_eq ?_)
      rw [probEvent_eq_tsum_ite]
      exact tsum_congr fun gS => by rw [mul_ite, mul_one, mul_zero]
  -- The collision indicator's mass under the residual table: a union bound over the
  -- slot-positive cells of the queried column, each read fresh.
  have hmass : Pr[fun gS => cacheBadReader (sessionsPerTag := sessionsPerTag) gS
      (⟨n₀, a₀⟩ : TagTranscript Nonce Digest) = true | genTable K'] ≤
      ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
    have hiff : ∀ gS : ((TagId × Fin sessionsPerTag) × Nonce) → Digest,
        (cacheBadReader (sessionsPerTag := sessionsPerTag) gS
          (⟨n₀, a₀⟩ : TagTranscript Nonce Digest) = true) ↔
        ∃ sl ∈ Finset.univ.filter (fun sl : TagId × Fin sessionsPerTag => sl.2 ≠ 0),
          gS (sl, n₀) = a₀ := by
      intro gS
      rw [cacheBadReader_eq_true_iff]
      constructor
      · rintro ⟨T, sid, hsid, h⟩
        exact ⟨(T, sid), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsid⟩, h⟩
      · rintro ⟨sl, hsl, h⟩
        exact ⟨sl.1, sl.2, (Finset.mem_filter.mp hsl).2, h⟩
    rw [probEvent_ext fun gS _ => hiff gS]
    refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ (Fintype.card Digest : ℝ≥0∞)⁻¹
      fun sl hsl => ?_) ?_
    · have hcell : K' (sl, n₀) = CellKnowledge.excluded ∅ :=
        hpos sl.1 sl.2 (Finset.mem_filter.mp hsl).2 n₀
      refine le_trans (probEvent_apply_eq_genTable_le K' hcell a₀) ?_
      simp
    · rw [nsmul_eq_mul, div_eq_mul_inv]
      refine mul_le_mul' (Nat.cast_le.mpr ?_) le_rfl
      refine le_trans (Finset.card_filter_le _ _) (le_of_eq ?_)
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  calc Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
        pure (F (unlinkReaderAccepts (Slot := TagId)
            (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
            (multiplePattern sessionsPerTag) ⟨n₀, a₀⟩)
          n (gS ((tag, (0 : Fin sessionsPerTag)), n))) : OptionT ProbComp Bool)]
      = Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (F false n (gS ((tag, (0 : Fin sessionsPerTag)), n))) :
            OptionT ProbComp Bool)] := hLcongr
    _ ≤ Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (F false n (gS ((tag, σ), n))) : OptionT ProbComp Bool)] +
        ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))⁻¹ :=
      probOutput_tag_reveal_tilt K' hfeas tag σ n₀ a₀ (hcol tag) hfresh
        (hpos tag σ hσ0) (F false)
    _ ≤ (Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (F (cacheBadReader (sessionsPerTag := sessionsPerTag) gS ⟨n₀, a₀⟩)
            n (gS ((tag, σ), n))) : OptionT ProbComp Bool)] +
          Pr[fun gS => cacheBadReader (sessionsPerTag := sessionsPerTag) gS
            (⟨n₀, a₀⟩ : TagTranscript Nonce Digest) = true | genTable K']) +
        ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))⁻¹ :=
      add_le_add hdisc le_rfl
    _ ≤ (Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (F (cacheBadReader (sessionsPerTag := sessionsPerTag) gS ⟨n₀, a₀⟩)
            n (gS ((tag, σ), n))) : OptionT ProbComp Bool)] +
          ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞)) +
        ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))⁻¹ :=
      add_le_add (add_le_add le_rfl hmass) le_rfl
    _ = Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (F (cacheBadReader (sessionsPerTag := sessionsPerTag) gS ⟨n₀, a₀⟩)
            n (gS ((tag, σ), n))) : OptionT ProbComp Bool)] +
        (((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))⁻¹ +
          ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞)) := by ring
    _ = Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (F (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) ⟨n₀, a₀⟩)
            n (gS ((tag, σ), n))) : OptionT ProbComp Bool)] +
        (((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))⁻¹ +
          ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞)) := by rw [hScongr]

/-- **Two-step gate.** One reader test at the transcript `⟨n₀, a₀⟩` followed by one
slot-positive tag read at a fresh uniform nonce, with an arbitrary Boolean continuation `F`,
both worlds reading one shared table drawn from the initial consistent-table distribution: the
M-side (slot-zero reader column, slot-zero tag cell) success probability exceeds the S-side
(full reader column, live-slot tag cell) success probability by at most the fire mass
`|TagId| / |Digest|`, the averaged reveal tilt `(|Nonce| · |Digest|)⁻¹`, and the slot-positive
discard `|TagId| · sessionsPerTag / |Digest|`. -/
theorem probeGate_two_step (tag : TagId) (σ : Fin sessionsPerTag) (hσ0 : σ ≠ 0)
    (n₀ : Nonce) (a₀ : Digest) (F : Bool → Nonce → Digest → Bool) :
    Pr[= true |
      (genTable (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest) >>= fun gS =>
        liftM ($ᵗ Nonce) >>= fun n =>
          pure (F (unlinkReaderAccepts (Slot := TagId)
              (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
              (multiplePattern sessionsPerTag) ⟨n₀, a₀⟩)
            n (gS ((tag, (0 : Fin sessionsPerTag)), n))) : OptionT ProbComp Bool)] ≤
      Pr[= true |
        (genTable (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest) >>=
          fun gS => liftM ($ᵗ Nonce) >>= fun n =>
            pure (F (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
                (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) ⟨n₀, a₀⟩)
              n (gS ((tag, σ), n))) : OptionT ProbComp Bool)] +
      (Fintype.card TagId : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))⁻¹ +
      ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  haveI : Nonempty Digest := ⟨a₀⟩
  set cells : List ((TagId × Fin sessionsPerTag) × Nonce) :=
    (Finset.univ.toList).map
      (fun T : TagId => ((T, (0 : Fin sessionsPerTag)), n₀)) with hcells
  have hnd : cells.Nodup := by
    rw [hcells]
    exact (Finset.nodup_toList _).map fun T₁ T₂ h => congrArg (fun p => p.1.1) h
  -- Redistribute both worlds' table draws along the column split.
  rw [probOutput_eq_of_evalDist_eq (evalDist_genTable_bind_probeColumnSplit a₀ cells _
        (fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (F (unlinkReaderAccepts (Slot := TagId)
              (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
              (multiplePattern sessionsPerTag) ⟨n₀, a₀⟩)
            n (gS ((tag, (0 : Fin sessionsPerTag)), n))))) true,
      probOutput_eq_of_evalDist_eq (evalDist_genTable_bind_probeColumnSplit a₀ cells _
        (fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (F (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) ⟨n₀, a₀⟩)
            n (gS ((tag, σ), n))))) true]
  simp only [← probEvent_eq_eq_probOutput]
  have hlen : cells.length = Fintype.card TagId := by
    rw [hcells, List.length_map, Finset.length_toList, Finset.card_univ]
  -- Fire mass: at the initial state every `true` reply is a genuine hit.
  have hfire : Pr[fun z : Bool × Bool ×
      ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest => z.1 = true |
      probeColumnSplit a₀ cells
        (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest)] ≤
      (Fintype.card TagId : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
    refine le_trans (probEvent_mono ?_) (le_trans
      (probEvent_probeColumnSplit_fired_le a₀ cells 0 _ ProbeState.exclLe_init)
      (le_of_eq ?_))
    · intro z hz h1
      rcases (probeColumnSplit_support a₀ cells _ hnd hz).2.2.2.2.1 h1 with hf | ⟨d, -, hk⟩
      · exact hf
      · exact absurd hk (by simp [ProbeState.init])
    · rw [hlen, Nat.sub_zero]
  -- Off-fire, the per-branch comparison is the off-fire step at the recorded state.
  have hperz : ∀ z ∈ support (probeColumnSplit a₀ cells
      (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest)),
      ¬ z.1 = true →
      Pr[(· = true) | genTable z.2.2 >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (F (unlinkReaderAccepts (Slot := TagId)
              (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
              (multiplePattern sessionsPerTag) ⟨n₀, a₀⟩)
            n (gS ((tag, (0 : Fin sessionsPerTag)), n)))] ≤
        Pr[(· = true) | genTable z.2.2 >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
            pure (F (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
                (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) ⟨n₀, a₀⟩)
              n (gS ((tag, σ), n)))] +
          (((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))⁻¹ +
            ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
              (Fintype.card Digest : ℝ≥0∞)) := by
    intro z hz hDz
    have hz1 : z.1 = false := Bool.eq_false_iff.mpr hDz
    obtain ⟨c1, c2, c3, c4, -, c6⟩ := probeColumnSplit_support a₀ cells _ hnd hz
    simp only [probEvent_eq_eq_probOutput]
    refine probeGate_offFire tag σ hσ0 n₀ a₀ F z.2.2 (c4 ProbeState.feasible_init)
      (fun T => ?_) (fun n hn => ?_) (fun T sid hsid n => ?_)
    · -- The probed column carries exactly the exclusion `{a₀}` on a no-reply path.
      have hmem : ((T, (0 : Fin sessionsPerTag)), n₀) ∈ cells := by
        rw [hcells]
        exact List.mem_map.mpr ⟨T, Finset.mem_toList.mpr (Finset.mem_univ T), rfl⟩
      rcases c3 _ hmem with heq | ⟨hfired, -⟩ | ⟨S, hKd, -, hupd⟩
      · exfalso
        refine c2 hz1 _ hmem ?_
        rw [heq]
        simp [ProbeState.init]
      · exact absurd (c6 hfired) (by simp [hz1])
      · have hS : (∅ : Finset Digest) = S := by injection hKd
        rw [hupd, ← hS, Finset.insert_empty]
    · refine (c1 _ fun hmem => ?_).trans rfl
      rw [hcells] at hmem
      obtain ⟨T, -, hT⟩ := List.mem_map.mp hmem
      exact hn (congrArg Prod.snd hT).symm
    · refine (c1 _ fun hmem => ?_).trans rfl
      rw [hcells] at hmem
      obtain ⟨T', -, hT⟩ := List.mem_map.mp hmem
      exact hsid (congrArg (fun p => p.1.2) hT).symm
  exact le_trans (probEvent_bind_le_add_of_disagree hfire hperz)
    (le_of_eq (by rw [← add_assoc]))

end ProbeGate

end PRFTagReader
