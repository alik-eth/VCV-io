/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import VCVio.OracleComp.ProbComp

/-!
# Reveal Tilt: Restricted Versus Full Uniform Selection

A draw uniform on the complement `Finset.univ \ S` of an exclusion set — the law of a probe-state
*reveal* at a cell that has excluded the values in `S` — is close to the full uniform draw: for
every continuation and every event, the restricted draw exceeds the full draw by at most
`|S| / |V|` (`probEvent_bind_uniformSelectFinset_sdiff_le`).

The constant `|S| / |V|` is the exact coupling defect: each surviving value `v ∉ S` carries weight
`(|V| - |S|)⁻¹ = |V|⁻¹ + (|S| / |V|) · (|V| - |S|)⁻¹` (`inv_sub_card_le_inv_add`), so the excess
over the full-uniform weight totals `|S| / |V|` across the complement. In particular the bound is
sharper than both `|S| / (|V| - |S|)` and the trivial bound `1`.

This is the per-cell comparison consumed by coupling arguments in which one world reveals a cell
conditioned by earlier probe misses while the other world reveals an untouched cell.
-/

open OracleComp ENNReal

namespace OracleComp

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Weight comparison for one surviving value: the restricted-uniform weight `(|V| - s)⁻¹`
splits exactly into the full-uniform weight `|V|⁻¹` plus the per-value excess
`(s / |V|) · (|V| - s)⁻¹`, provided some value survives (`c - s ≠ 0`). -/
private lemma inv_sub_card_le_inv_add {c s : ℕ} (hcs : c - s ≠ 0) :
    ((c - s : ℕ) : ℝ≥0∞)⁻¹ =
      (c : ℝ≥0∞)⁻¹ + (s : ℝ≥0∞) * (c : ℝ≥0∞)⁻¹ * ((c - s : ℕ) : ℝ≥0∞)⁻¹ := by
  have hsc : s < c := Nat.lt_of_sub_ne_zero hcs
  have hx0 : ((c - s : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hcs
  have hc0 : (c : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc ((c - s : ℕ) : ℝ≥0∞)⁻¹
      = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ((c - s : ℕ) : ℝ≥0∞)⁻¹) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 (ENNReal.natCast_ne_top c), one_mul]
    _ = (c : ℝ≥0∞)⁻¹ * ((((c - s : ℕ) : ℝ≥0∞) + (s : ℝ≥0∞)) * ((c - s : ℕ) : ℝ≥0∞)⁻¹) := by
        rw [← Nat.cast_add, Nat.sub_add_cancel hsc.le]
    _ = (c : ℝ≥0∞)⁻¹ * (1 + (s : ℝ≥0∞) * ((c - s : ℕ) : ℝ≥0∞)⁻¹) := by
        rw [add_mul, ENNReal.mul_inv_cancel hx0 (ENNReal.natCast_ne_top _)]
    _ = (c : ℝ≥0∞)⁻¹ + (s : ℝ≥0∞) * (c : ℝ≥0∞)⁻¹ * ((c - s : ℕ) : ℝ≥0∞)⁻¹ := by
        ring

/-- **Reveal tilt.** A computation that draws its seed uniformly from the complement of an
exclusion set `S` satisfies any event with probability at most that of the same computation
seeded by the full uniform draw, plus the tilt `|S| / |V|`. -/
theorem probEvent_bind_uniformSelectFinset_sdiff_le {β : Type}
    (S : Finset V) (f : V → OptionT ProbComp β) (p : β → Prop) :
    Pr[ p | ($ (Finset.univ \ S)) >>= f ] ≤
      Pr[ p | ($ (Finset.univ : Finset V)) >>= f ] +
        (S.card : ℝ≥0∞) / (Fintype.card V : ℝ≥0∞) := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, tsum_fintype, tsum_fintype]
  simp only [ProbComp.probOutput_uniformSelectFinset,
    Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Finset.mem_univ,
    if_true, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  by_cases hcs : Fintype.card V - S.card = 0
  · have hS : Finset.univ \ S = ∅ := by
      rw [Finset.sdiff_eq_empty_iff_subset]
      intro v _
      by_contra hv
      have : S.card < Fintype.card V :=
        Finset.card_lt_card (Finset.ssubset_univ_iff.mpr fun h => hv (h ▸ Finset.mem_univ v))
      omega
    rw [hS, Finset.sum_empty]
    exact bot_le
  · calc ∑ v ∈ Finset.univ \ S, ((Fintype.card V - S.card : ℕ) : ℝ≥0∞)⁻¹ * Pr[p | f v]
        = ∑ v ∈ Finset.univ \ S, ((Fintype.card V : ℝ≥0∞)⁻¹ * Pr[p | f v]
            + (S.card : ℝ≥0∞) * (Fintype.card V : ℝ≥0∞)⁻¹ *
              (((Fintype.card V - S.card : ℕ) : ℝ≥0∞)⁻¹ * Pr[p | f v])) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          conv_lhs => rw [inv_sub_card_le_inv_add hcs]
          rw [add_mul, mul_assoc]
      _ = ∑ v ∈ Finset.univ \ S, (Fintype.card V : ℝ≥0∞)⁻¹ * Pr[p | f v]
            + (S.card : ℝ≥0∞) * (Fintype.card V : ℝ≥0∞)⁻¹ *
              ∑ v ∈ Finset.univ \ S, ((Fintype.card V - S.card : ℕ) : ℝ≥0∞)⁻¹ * Pr[p | f v] := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ v : V, (Fintype.card V : ℝ≥0∞)⁻¹ * Pr[p | f v]
            + (S.card : ℝ≥0∞) * (Fintype.card V : ℝ≥0∞)⁻¹ * 1 := by
          refine add_le_add (Finset.sum_le_sum_of_subset (Finset.sdiff_subset)) ?_
          refine mul_le_mul' le_rfl ?_
          refine le_trans (Finset.sum_le_card_nsmul _ _
            ((Fintype.card V - S.card : ℕ) : ℝ≥0∞)⁻¹ fun v _ =>
              le_trans (mul_le_mul' le_rfl probEvent_le_one) (mul_one _).le) ?_
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
            nsmul_eq_mul]
          exact ENNReal.mul_inv_le_one _
      _ = ∑ v : V, (Fintype.card V : ℝ≥0∞)⁻¹ * Pr[p | f v]
            + (S.card : ℝ≥0∞) / (Fintype.card V : ℝ≥0∞) := by
          rw [mul_one, div_eq_mul_inv]

end OracleComp
