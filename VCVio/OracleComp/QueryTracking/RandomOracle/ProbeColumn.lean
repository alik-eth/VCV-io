/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import VCVio.EvalDist.Monad.BindCongr
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEquiv

/-!
# Column Probes And Marginals Of The Consistent-Table Distribution

This file provides the Boolean-level lazification of a *column read* of a consistent table: a
batch of cells is compared against one target value, only the comparison bits are materialized,
and the residual table remains distributed as `genTable` of the recorded post-probe knowledge.

## The column probe split

`probeColumnSplit a₀ cells K` visits the cells of `cells` in order. A `known v` cell contributes
the deterministic bit `v = a₀`; an `excluded S` cell with `a₀ ∈ S` contributes `false`; otherwise
the probe is *genuine* — the cell's value is drawn from its allowed set and only the comparison
bit is retained, determining the cell to `a₀` on a hit and excluding `a₀` there on a miss. The
program returns the OR of all bits, the OR of the *genuine-hit* (fired) bits, and the post-probe
knowledge state.

* `evalDist_genTable_bind_probeColumnSplit` — the redistribution law: drawing a consistent table
  and running any continuation equals drawing the column bits first and the residual table from
  the post-probe knowledge. The split is a single shared prefix, so several probabilities of the
  same table draw (success, reference, and bad-event positions of a coupling) can be rewritten
  along it simultaneously, with no freshness hypothesis on the column.
* `probEvent_probeColumnSplit_fired_le` — the fired mass: from a state whose exclusion sets have
  cardinality at most `m`, some genuine probe of the column hits with probability at most
  `(number of cells) / (|R| - m)`, by the first-fire telescope.
* `probeColumnSplit_support` — the support shape: cells off the column are untouched; on a
  `false` reply every column cell rules out the target; every column cell is either untouched,
  determined to the target on a fired path, or has exactly the target newly excluded;
  feasibility is preserved; the fired flag implies the reply, and a `true` reply is a fire or a
  pre-determined match. `probeColumnSplit_support_exclLe` bounds the exclusion growth by one.

## Reads of the residual table

* `probOutput_genTable_bind_pure_comp` — a continuation reading the table only at one
  undetermined cell sees exactly the uniform draw from that cell's allowed set.
* `probEvent_apply_eq_genTable_le` — the chance that one undetermined cell matches a target is
  at most the inverse size of its allowed set.

## Pushforwards along cell embeddings

Precomposition reindexes a consistent table: along an equivalence the law is exactly the
consistent-table law of the reindexed knowledge (`evalDist_map_comp_equiv_genTable`), and
along an injection the off-range cells integrate out by feasibility
(`evalDist_map_comp_injective_genTable`, via the per-cell mass
`CellKnowledge.sum_cellProb_eq_one`). Consequently two feasible states agreeing on the range
of an injection have identical pushforward laws (`evalDist_map_comp_genTable_congr`) — a
sub-table read cannot distinguish them.
-/

open OracleComp OracleSpec ENNReal

namespace OracleComp

variable {D R : Type} [DecidableEq D] [DecidableEq R] [Fintype R]

/-! ## The column probe split -/

/-- Probe the cells of a column in order against the target `a₀`, materializing only the
comparison bits: the result is the OR of all bits, the OR of the genuine-hit bits, and the
post-probe knowledge state. -/
noncomputable def probeColumnSplit (a₀ : R) :
    List D → ProbeState D R → OptionT ProbComp (Bool × Bool × ProbeState D R)
  | [], K => pure (false, false, K)
  | d :: ds, K =>
    match K d with
    | .known v =>
      (fun z : Bool × Bool × ProbeState D R => (decide (v = a₀) || z.1, z.2)) <$>
        probeColumnSplit a₀ ds K
    | .excluded S =>
      if a₀ ∈ S then probeColumnSplit a₀ ds K
      else
        ($ (Finset.univ \ S)) >>= fun v =>
          probeColumnSplit a₀ ds (Function.update K d
            (if v = a₀ then .known a₀ else .excluded (insert a₀ S))) >>= fun z =>
          pure (decide (v = a₀) || z.1, decide (v = a₀) || z.2.1, z.2.2)

/-- Splitting an empty column draws nothing, reports no hit and no fire. -/
@[simp] lemma probeColumnSplit_nil (a₀ : R) (K : ProbeState D R) :
    probeColumnSplit a₀ [] K = pure (false, false, K) := rfl

/-- A determined head cell contributes its deterministic comparison bit and is never charged. -/
lemma probeColumnSplit_known {K : ProbeState D R} {d : D} {v : R} (a₀ : R) (ds : List D)
    (hcell : K d = .known v) :
    probeColumnSplit a₀ (d :: ds) K =
      (fun z : Bool × Bool × ProbeState D R => (decide (v = a₀) || z.1, z.2)) <$>
        probeColumnSplit a₀ ds K := by
  rw [probeColumnSplit, hcell]

/-- A head cell that has already excluded the target contributes a `false` bit and changes
nothing. -/
lemma probeColumnSplit_excluded_mem {K : ProbeState D R} {d : D} {S : Finset R} (a₀ : R)
    (ds : List D) (hcell : K d = .excluded S) (ha : a₀ ∈ S) :
    probeColumnSplit a₀ (d :: ds) K = probeColumnSplit a₀ ds K := by
  rw [probeColumnSplit, hcell]
  exact if_pos ha

/-- A genuine head probe draws the cell's value from its allowed set, retains the comparison
bit, ORs a hit onto the fired flag, and records the knowledge update. -/
lemma probeColumnSplit_excluded_notMem {K : ProbeState D R} {d : D} {S : Finset R} (a₀ : R)
    (ds : List D) (hcell : K d = .excluded S) (ha : a₀ ∉ S) :
    probeColumnSplit a₀ (d :: ds) K =
      ($ (Finset.univ \ S)) >>= fun v =>
        probeColumnSplit a₀ ds (Function.update K d
          (if v = a₀ then .known a₀ else .excluded (insert a₀ S))) >>= fun z =>
        pure (decide (v = a₀) || z.1, decide (v = a₀) || z.2.1, z.2.2) := by
  rw [probeColumnSplit, hcell]
  exact if_neg ha

/-! ## The redistribution law -/

/-- **Column redistribution.** Drawing a consistent table and running any continuation is the
same as splitting a column — drawing only the per-cell comparison bits against `a₀` — and then
drawing the residual table consistent with the recorded post-probe knowledge. Iterates
`evalDist_genTable_probe_split` along the column; determined and already-excluded cells are
answered deterministically, so no freshness or distinctness hypothesis is needed. -/
theorem evalDist_genTable_bind_probeColumnSplit [Fintype D] {β : Type} (a₀ : R)
    (cells : List D) (K : ProbeState D R) (F : (D → R) → OptionT ProbComp β) :
    𝒟[genTable K >>= F] =
      𝒟[probeColumnSplit a₀ cells K >>= fun z => genTable z.2.2 >>= F] := by
  induction cells generalizing K with
  | nil => rw [probeColumnSplit_nil, pure_bind]
  | cons d ds ih =>
    rcases hcell : K d with v | S
    · rw [probeColumnSplit_known a₀ ds hcell, bind_map_left]
      exact ih K
    · by_cases ha : a₀ ∈ S
      · rw [probeColumnSplit_excluded_mem a₀ ds hcell ha]
        exact ih K
      · rw [probeColumnSplit_excluded_notMem a₀ ds hcell ha]
        conv_lhs => rw [evalDist_bind, evalDist_genTable_probe_split hcell ha,
          ← evalDist_bind, bind_assoc]
        rw [bind_assoc]
        refine evalDist_bind_congr fun v _ => ?_
        rw [bind_assoc]
        simp only [pure_bind]
        by_cases hva : v = a₀
        · simp only [if_pos hva]
          exact ih _
        · simp only [if_neg hva]
          exact ih _

/-! ## The fired mass -/

/-- **Fired mass of a column split.** From a state whose exclusion sets all have cardinality at
most `m`, some genuine probe of the column hits with probability at most
`(number of cells) / (|R| - m)`: determined and already-excluded cells are uncharged, a genuine
hit is charged its draw probability, and each miss continues with the grown state, folded back
into the budget by the first-fire telescope. -/
theorem probEvent_probeColumnSplit_fired_le (a₀ : R) (cells : List D) (m : ℕ)
    (K : ProbeState D R) (hst : K.ExclLe m) :
    Pr[fun z : Bool × Bool × ProbeState D R => z.2.1 = true |
        probeColumnSplit a₀ cells K] ≤
      (cells.length : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞) := by
  classical
  induction cells generalizing m K with
  | nil =>
    rw [probeColumnSplit_nil]
    simp
  | cons d ds ih =>
    have hmono : (ds.length : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞) ≤
        ((d :: ds).length : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞) :=
      ENNReal.div_le_div_right (by exact_mod_cast (ds.length).le_succ) _
    rcases hcell : K d with v | S
    · rw [probeColumnSplit_known a₀ ds hcell, probEvent_map]
      refine le_trans (le_of_eq (probEvent_ext fun z _ => Iff.rfl)) ?_
      exact le_trans (ih m K hst) hmono
    · by_cases ha : a₀ ∈ S
      · rw [probeColumnSplit_excluded_mem a₀ ds hcell ha]
        exact le_trans (ih m K hst) hmono
      · have hk : S.card ≤ m := hst d S hcell
        rw [probeColumnSplit_excluded_notMem a₀ ds hcell ha, probEvent_bind_eq_tsum,
          tsum_fintype, ← Finset.sum_erase_add _ _ (Finset.mem_univ a₀), List.length_cons,
          show ((ds.length + 1 : ℕ) : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞)
              = (ds.length : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞)
                + 1 / ((Fintype.card R - m : ℕ) : ℝ≥0∞) from by
            rw [Nat.cast_succ, ENNReal.add_div]]
        refine add_le_add ?_ ?_
        · -- Miss branches: each continues from the grown state with the tail budget.
          refine le_trans (Finset.sum_le_sum (g := fun v => Pr[= v | $ (Finset.univ \ S)] *
            ((ds.length : ℝ≥0∞) /
              ((Fintype.card R - max m (S.card + 1) : ℕ) : ℝ≥0∞)))
            fun v hv => ?_) ?_
          · obtain ⟨hv_ne, -⟩ := Finset.mem_erase.mp hv
            refine mul_le_mul' le_rfl ?_
            have htail : (probeColumnSplit a₀ ds (Function.update K d
                (if v = a₀ then CellKnowledge.known a₀ else .excluded (insert a₀ S)))
                  >>= fun z =>
                    (pure (decide (v = a₀) || z.1, decide (v = a₀) || z.2.1, z.2.2) :
                      OptionT ProbComp (Bool × Bool × ProbeState D R)))
                = probeColumnSplit a₀ ds (Function.update K d
                    (if v = a₀ then CellKnowledge.known a₀ else .excluded (insert a₀ S))) := by
              simp only [decide_eq_false hv_ne, Bool.false_or, Prod.mk.eta]
              exact bind_pure _
            rw [htail, if_neg hv_ne]
            exact ih _ _ (hst.update_insert d a₀ S)
          · -- Survival mass `(|R| - S.card - 1) / (|R| - S.card)` times the tail budget.
            rw [← Finset.sum_mul]
            have hcard : ((Finset.univ.erase a₀) ∩ (Finset.univ \ S)).card =
                Fintype.card R - (S.card + 1) := by
              have hset : (Finset.univ.erase a₀) ∩ (Finset.univ \ S) =
                  Finset.univ \ insert a₀ S := by
                ext v
                simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_sdiff,
                  Finset.mem_univ, Finset.mem_insert, true_and, and_true, not_or]
              rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _),
                Finset.card_univ, Finset.card_insert_of_notMem ha]
            have hPsum : ∑ v ∈ Finset.univ.erase a₀, Pr[= v | $ (Finset.univ \ S)] =
                ((Fintype.card R - (S.card + 1) : ℕ) : ℝ≥0∞) *
                  ((Fintype.card R - S.card : ℕ) : ℝ≥0∞)⁻¹ := by
              simp only [ProbComp.probOutput_uniformSelectFinset]
              rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, hcard,
                Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
            rw [hPsum]
            exact firstFire_telescope_step _ hk
        · -- Hit branch: the fired flag is set; charge the reach probability.
          refine le_trans (mul_le_mul' le_rfl probEvent_le_one) ?_
          rw [mul_one, ProbComp.probOutput_uniformSelectFinset,
            if_pos (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩),
            Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, one_div]
          exact ENNReal.inv_le_inv' (Nat.cast_le.mpr (Nat.sub_le_sub_left hk _))

/-! ## The support shape -/

/-- **Support shape of a column split.** Along every path of `probeColumnSplit a₀ cells K`,
writing the result `z = (reply, fired, K')`:

1. cells off the column keep their knowledge;
2. on a `false` reply every column cell rules out the target `a₀`;
3. every column cell is untouched, or determined to `a₀` on a fired path, or has exactly `a₀`
   newly excluded over its previous exclusion set;
4. feasibility is preserved (each miss draw witnesses a surviving value);
5. a `true` reply is a fire or a match at a cell already determined to `a₀`;
6. the fired flag implies the reply. -/
theorem probeColumnSplit_support (a₀ : R) (cells : List D) (K : ProbeState D R)
    (hnd : cells.Nodup) {z : Bool × Bool × ProbeState D R}
    (hz : z ∈ support (probeColumnSplit a₀ cells K)) :
    (∀ d, d ∉ cells → z.2.2 d = K d) ∧
      (z.1 = false → ∀ d ∈ cells, a₀ ∉ (z.2.2 d).allowed) ∧
      (∀ d ∈ cells, z.2.2 d = K d ∨ (z.2.1 = true ∧ z.2.2 d = .known a₀) ∨
        ∃ S, K d = .excluded S ∧ a₀ ∉ S ∧ z.2.2 d = .excluded (insert a₀ S)) ∧
      (K.Feasible → z.2.2.Feasible) ∧
      (z.1 = true → z.2.1 = true ∨ ∃ d ∈ cells, K d = .known a₀) ∧
      (z.2.1 = true → z.1 = true) := by
  classical
  induction cells generalizing K z with
  | nil =>
    rw [probeColumnSplit_nil, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨fun d _ => rfl, fun _ d hd => absurd hd (List.not_mem_nil),
      fun d hd => absurd hd (List.not_mem_nil), fun h => h,
      fun h => absurd h Bool.false_ne_true, fun h => absurd h Bool.false_ne_true⟩
  | cons d ds ih =>
    have hd_ds : d ∉ ds := (List.nodup_cons.mp hnd).1
    have hnd' : ds.Nodup := (List.nodup_cons.mp hnd).2
    rcases hcell : K d with v | S
    · -- Determined head cell: deterministic bit, no state change.
      rw [probeColumnSplit_known a₀ ds hcell, support_map] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := ih K hnd' hz'
      refine ⟨fun d' hd' => c1 d' fun h => hd' (List.mem_cons_of_mem d h), ?_, ?_, c4, ?_, ?_⟩
      · intro hz1 d' hd'
        simp only [Bool.or_eq_false_iff] at hz1
        rcases List.mem_cons.mp hd' with rfl | hd'
        · by_cases hmem : d' ∈ ds
          · exact c2 hz1.2 d' hmem
          · rw [c1 d' hmem, hcell, CellKnowledge.allowed_known, Finset.mem_singleton]
            exact fun h => of_decide_eq_false hz1.1 h.symm
        · exact c2 hz1.2 d' hd'
      · intro d' hd'
        rcases List.mem_cons.mp hd' with rfl | hd'
        · by_cases hmem : d' ∈ ds
          · exact c3 d' hmem
          · exact Or.inl (c1 d' hmem)
        · exact c3 d' hd'
      · intro hz1
        simp only [Bool.or_eq_true] at hz1
        rcases hz1 with hb | hz1
        · exact Or.inr ⟨d, List.mem_cons_self, by rw [hcell, of_decide_eq_true hb]⟩
        · rcases c5 hz1 with hf | ⟨d', hd', hk⟩
          · exact Or.inl hf
          · exact Or.inr ⟨d', List.mem_cons_of_mem d hd', hk⟩
      · intro hf
        simp only [Bool.or_eq_true]
        exact Or.inr (c6 hf)
    · by_cases ha : a₀ ∈ S
      · -- Already-excluded head cell: `false` bit, no state change.
        rw [probeColumnSplit_excluded_mem a₀ ds hcell ha] at hz
        obtain ⟨c1, c2, c3, c4, c5, c6⟩ := ih K hnd' hz
        refine ⟨fun d' hd' => c1 d' fun h => hd' (List.mem_cons_of_mem d h), ?_, ?_, c4, ?_, c6⟩
        · intro hz1 d' hd'
          rcases List.mem_cons.mp hd' with rfl | hd'
          · by_cases hmem : d' ∈ ds
            · exact c2 hz1 d' hmem
            · rw [c1 d' hmem, hcell, CellKnowledge.allowed_excluded, Finset.mem_sdiff]
              exact fun h => h.2 ha
          · exact c2 hz1 d' hd'
        · intro d' hd'
          rcases List.mem_cons.mp hd' with rfl | hd'
          · by_cases hmem : d' ∈ ds
            · exact c3 d' hmem
            · exact Or.inl (c1 d' hmem)
          · exact c3 d' hd'
        · intro hz1
          rcases c5 hz1 with hf | ⟨d', hd', hk⟩
          · exact Or.inl hf
          · exact Or.inr ⟨d', List.mem_cons_of_mem d hd', hk⟩
      · -- Genuine head probe.
        rw [probeColumnSplit_excluded_notMem a₀ ds hcell ha, mem_support_bind_iff] at hz
        obtain ⟨v, hv, hz⟩ := hz
        rw [mem_support_bind_iff] at hz
        obtain ⟨z', hz', hzz⟩ := hz
        rw [support_pure, Set.mem_singleton_iff] at hzz
        subst hzz
        obtain ⟨c1, c2, c3, c4, c5, c6⟩ := ih _ hnd' hz'
        have hvS : v ∉ S := by
          rw [ProbComp.support_uniformSelectFinset,
            if_pos ⟨a₀, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a₀, ha⟩⟩, Finset.mem_coe,
            Finset.mem_sdiff] at hv
          exact hv.2
        have hKd' : ∀ d' ∈ ds, Function.update K d
            (if v = a₀ then CellKnowledge.known a₀ else .excluded (insert a₀ S)) d' = K d' :=
          fun d' hd' => Function.update_of_ne (ne_of_mem_of_not_mem hd' hd_ds) _ _
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro d' hd'
          have hne : d' ≠ d := fun h => hd' (h ▸ List.mem_cons_self)
          rw [c1 d' fun h => hd' (List.mem_cons_of_mem d h), Function.update_of_ne hne]
        · intro hz1 d' hd'
          simp only [Bool.or_eq_false_iff] at hz1
          have hv_ne : v ≠ a₀ := of_decide_eq_false hz1.1
          rcases List.mem_cons.mp hd' with rfl | hd'
          · rw [c1 d' hd_ds, Function.update_self, if_neg hv_ne,
              CellKnowledge.allowed_excluded, Finset.mem_sdiff]
            exact fun h => h.2 (Finset.mem_insert_self a₀ S)
          · exact c2 hz1.2 d' hd'
        · intro d' hd'
          rcases List.mem_cons.mp hd' with rfl | hd'
          · by_cases hva : v = a₀
            · -- Hit at the head cell: the head fired, and the cell stays determined to `a₀`.
              refine Or.inr (Or.inl ⟨by simp [hva], ?_⟩)
              rw [c1 d' hd_ds, Function.update_self, if_pos hva]
            · refine Or.inr (Or.inr ⟨S, hcell, ha, ?_⟩)
              rw [c1 d' hd_ds, Function.update_self, if_neg hva]
          · rcases c3 d' hd' with heq | ⟨hf, hk⟩ | ⟨S', hS', haS', hupd⟩
            · exact Or.inl (by rw [heq, hKd' d' hd'])
            · exact Or.inr (Or.inl ⟨by simp [hf], hk⟩)
            · exact Or.inr (Or.inr ⟨S', by rw [← hKd' d' hd']; exact hS', haS', hupd⟩)
        · intro hKf
          refine c4 ?_
          by_cases hva : v = a₀
          · rw [if_pos hva]
            exact hKf.update d ⟨a₀, by simp⟩
          · rw [if_neg hva]
            exact hKf.update d ⟨v, by simp [hva, hvS]⟩
        · intro hz1
          simp only [Bool.or_eq_true] at hz1
          rcases hz1 with hb | hz1
          · exact Or.inl (by simp [hb])
          · rcases c5 hz1 with hf | ⟨d', hd', hk⟩
            · exact Or.inl (by simp [hf])
            · exact Or.inr ⟨d', List.mem_cons_of_mem d hd',
                by rw [← hKd' d' hd']; exact hk⟩
        · intro hf
          simp only [Bool.or_eq_true] at hf ⊢
          rcases hf with hb | hf
          · exact Or.inl hb
          · exact Or.inr (c6 hf)

/-- Exclusion-cardinality growth of a column split: every cell gains at most one excluded
value, so an `m`-bounded state yields an `(m + 1)`-bounded residual state. -/
theorem probeColumnSplit_support_exclLe (a₀ : R) (cells : List D) (K : ProbeState D R)
    (hnd : cells.Nodup) {z : Bool × Bool × ProbeState D R}
    (hz : z ∈ support (probeColumnSplit a₀ cells K)) {m : ℕ} (hst : K.ExclLe m) :
    z.2.2.ExclLe (m + 1) := by
  obtain ⟨c1, -, c3, -⟩ := probeColumnSplit_support a₀ cells K hnd hz
  intro d S' hS'
  by_cases hd : d ∈ cells
  · rcases c3 d hd with heq | ⟨-, hk⟩ | ⟨S, hKd, -, hupd⟩
    · exact le_trans (hst d S' (heq ▸ hS')) (Nat.le_succ m)
    · rw [hk] at hS'
      cases hS'
    · rw [hupd] at hS'
      injection hS' with h
      calc S'.card = (insert a₀ S).card := by rw [← h]
        _ ≤ S.card + 1 := Finset.card_insert_le a₀ S
        _ ≤ m + 1 := Nat.add_le_add_right (hst d S hKd) 1
  · exact le_trans (hst d S' ((c1 d hd) ▸ hS')) (Nat.le_succ m)

/-! ## Reads of the residual table -/

variable [Fintype D]

/-- A continuation that reads the table only at one undetermined cell sees exactly the uniform
draw from that cell's allowed set: the reveal split of the consistent-table distribution,
specialized to a single read. -/
theorem probOutput_genTable_bind_pure_comp {β : Type} (K : ProbeState D R)
    (hK : K.Feasible) {d : D} {S : Finset R} (hcell : K d = CellKnowledge.excluded S)
    (g : R → β) (y : β) :
    Pr[= y | genTable K >>= fun gS => (pure (g (gS d)) : OptionT ProbComp β)] =
      Pr[= y | ($ (Finset.univ \ S)) >>= fun v => (pure (g v) : OptionT ProbComp β)] := by
  have hL : Pr[= y | genTable K >>= fun gS => (pure (g (gS d)) : OptionT ProbComp β)]
      = Pr[= y | ($ (Finset.univ \ S)) >>= fun v =>
          genTable (Function.update K d (CellKnowledge.known v)) >>= fun gS =>
            (pure (g (gS d)) : OptionT ProbComp β)] := by
    refine probOutput_eq_of_evalDist_eq ?_ y
    conv_lhs => rw [evalDist_bind, evalDist_genTable_reveal_split hcell, ← evalDist_bind,
      bind_assoc]
  rw [hL, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun v => ?_
  congr 1
  have hfeas' : ProbeState.Feasible (Function.update K d (CellKnowledge.known v)) :=
    hK.update d (Finset.singleton_nonempty v)
  have hval : Pr[= y | genTable (Function.update K d (CellKnowledge.known v)) >>= fun gS =>
      (pure (g (gS d)) : OptionT ProbComp β)]
      = Pr[= y | genTable (Function.update K d (CellKnowledge.known v)) >>= fun _ =>
        (pure (g v) : OptionT ProbComp β)] :=
    probOutput_bind_congr fun gS hgS => by
      rw [apply_eq_of_mem_support_genTable hgS (Function.update_self d _ K)]
  rw [hval, probOutput_bind_const, probFailure_genTable hfeas', tsub_zero, one_mul]

/-- **Reveal redistribution at one cell.** A continuation reading the table at one undetermined
cell `d` (and arbitrarily elsewhere) can have the cell's value drawn first: the draw is uniform
on the allowed set, and the residual table is consistent with the cell determined to the drawn
value. The bind-level form of `evalDist_genTable_reveal_split`, with the read value abstracted
so that downstream occurrences are rewritten to the drawn value. -/
theorem evalDist_genTable_bind_reveal_comp {β : Type} (K : ProbeState D R)
    {d : D} {S : Finset R} (hcell : K d = CellKnowledge.excluded S)
    (G : R → (D → R) → OptionT ProbComp β) :
    𝒟[genTable K >>= fun gS => G (gS d) gS] =
      𝒟[($ (Finset.univ \ S)) >>= fun u =>
        genTable (Function.update K d (CellKnowledge.known u)) >>= fun gS => G u gS] := by
  conv_lhs => rw [evalDist_bind, evalDist_genTable_reveal_split hcell, ← evalDist_bind,
    bind_assoc]
  refine evalDist_bind_congr fun u _ => ?_
  refine evalDist_bind_congr fun gS hgS => ?_
  rw [apply_eq_of_mem_support_genTable hgS (Function.update_self d _ K)]

/-- A continuation reading the table at one *determined* cell sees the determined value: the
read can be replaced by the constant. -/
theorem evalDist_genTable_bind_known_comp {β : Type} (K : ProbeState D R)
    {d : D} {v : R} (hcell : K d = CellKnowledge.known v)
    (G : R → (D → R) → OptionT ProbComp β) :
    𝒟[genTable K >>= fun gS => G (gS d) gS] = 𝒟[genTable K >>= fun gS => G v gS] :=
  evalDist_bind_congr fun gS hgS => by
    rw [apply_eq_of_mem_support_genTable hgS hcell]

/-- The probability that the residual table matches a target value at one undetermined cell is
at most the inverse size of that cell's allowed set. -/
theorem probEvent_apply_eq_genTable_le (K : ProbeState D R) {d : D} {S : Finset R}
    (hcell : K d = CellKnowledge.excluded S) (a : R) :
    Pr[fun gS : D → R => gS d = a | genTable K] ≤
      ((Fintype.card R - S.card : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  rw [probEvent_eq_of_evalDist_eq (evalDist_genTable_reveal_split hcell) _,
    probEvent_bind_eq_tsum, tsum_fintype]
  have hinner : ∀ v : R,
      Pr[fun gS : D → R => gS d = a |
          genTable (Function.update K d (CellKnowledge.known v))] ≤
        if v = a then 1 else 0 := by
    intro v
    by_cases hva : v = a
    · rw [if_pos hva]
      exact probEvent_le_one
    · rw [if_neg hva]
      refine le_of_eq (probEvent_eq_zero fun gS hgS h => hva ?_)
      exact (apply_eq_of_mem_support_genTable hgS (Function.update_self d _ K)).symm.trans h
  calc ∑ v : R, Pr[= v | ($ (Finset.univ \ S))] *
        Pr[fun gS : D → R => gS d = a |
          genTable (Function.update K d (CellKnowledge.known v))]
      ≤ ∑ v : R, Pr[= v | ($ (Finset.univ \ S))] * (if v = a then 1 else 0) :=
        Finset.sum_le_sum fun v _ => mul_le_mul' le_rfl (hinner v)
    _ = Pr[= a | ($ (Finset.univ \ S) : OptionT ProbComp R)] := by
        simp only [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ a
          (fun v => Pr[= v | ($ (Finset.univ \ S) : OptionT ProbComp R)]),
          if_pos (Finset.mem_univ a)]
    _ ≤ ((Fintype.card R - S.card : ℕ) : ℝ≥0∞)⁻¹ := by
        rw [ProbComp.probOutput_uniformSelectFinset]
        split_ifs with h
        · rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
        · exact bot_le

/-! ## Pushforwards along cell embeddings -/

/-- The per-cell weights of the consistent-table distribution sum to `1` at every cell that
still admits a value. -/
lemma CellKnowledge.sum_cellProb_eq_one {c : CellKnowledge R} (hc : c.allowed.Nonempty) :
    ∑ v : R, c.cellProb v = 1 := by
  simp only [CellKnowledge.cellProb_def]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hc))
    (ENNReal.natCast_ne_top _)

/-- **Pushforward along an equivalence.** Precomposing a consistent table with an equivalence of
cell domains reindexes the law: the result is distributed as the consistent table of the
reindexed knowledge state. -/
theorem evalDist_map_comp_equiv_genTable {D' : Type} [Fintype D'] [DecidableEq D']
    (e : D' ≃ D) (K : ProbeState D R) :
    𝒟[(fun g : D → R => g ∘ e) <$> genTable K] = 𝒟[genTable (fun d' => K (e d'))] := by
  classical
  refine evalDist_ext fun g' => ?_
  have hfib : ∀ g : D → R, (g' = g ∘ e) ↔ g = g' ∘ e.symm := by
    intro g
    constructor
    · intro h
      funext d
      have h1 := congrFun h (e.symm d)
      rw [Function.comp_apply, Equiv.apply_symm_apply] at h1
      exact h1.symm
    · rintro rfl
      funext d'
      simp
  rw [probOutput_map_eq_sum_fintype_ite,
    Finset.sum_congr rfl fun g _ => if_congr (hfib g) rfl rfl,
    Finset.sum_ite_eq' Finset.univ (g' ∘ e.symm)
      (fun g => Pr[= g | (genTable K : OptionT ProbComp (D → R))]),
    if_pos (Finset.mem_univ _), probOutput_genTable, probOutput_genTable,
    ← Equiv.prod_comp e fun d => (K d).cellProb ((g' ∘ e.symm) d)]
  exact Finset.prod_congr rfl fun d' _ => by
    rw [Function.comp_apply, Equiv.symm_apply_apply]

/-- **Pushforward along an injection.** Precomposing a feasible consistent table with an
injection of cell domains marginalizes the off-range cells: the result is distributed as the
consistent table of the restricted knowledge state. -/
theorem evalDist_map_comp_injective_genTable {D' : Type} [Fintype D'] [DecidableEq D']
    {e : D' → D} (he : Function.Injective e) (K : ProbeState D R) (hK : K.Feasible) :
    𝒟[(fun g : D → R => g ∘ e) <$> genTable K] = 𝒟[genTable (fun d' => K (e d'))] := by
  classical
  refine evalDist_ext fun g' => ?_
  rw [probOutput_map_eq_sum_fintype_ite]
  set fib : D → Finset R := fun d =>
    if h : ∃ d', e d' = d then {g' h.choose} else Finset.univ with hfib_def
  have hmem : ∀ g : D → R, (g' = g ∘ e) ↔ g ∈ Fintype.piFinset fib := by
    intro g
    rw [Fintype.mem_piFinset, funext_iff]
    constructor
    · intro h d
      simp only [hfib_def]
      by_cases hd : ∃ d', e d' = d
      · rw [dif_pos hd, Finset.mem_singleton]
        exact ((h hd.choose).trans (congrArg g hd.choose_spec)).symm
      · rw [dif_neg hd]
        exact Finset.mem_univ _
    · intro h d'
      have hex : ∃ d'', e d'' = e d' := ⟨d', rfl⟩
      have hd := h (e d')
      simp only [hfib_def, dif_pos hex, Finset.mem_singleton] at hd
      have hch : hex.choose = d' := he hex.choose_spec
      rw [Function.comp_apply, hd, hch]
  rw [Finset.sum_congr rfl fun g _ => if_congr (hmem g) rfl rfl]
  simp only [probOutput_genTable]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.prod_univ_sum,
    ← Finset.prod_mul_prod_compl (Finset.univ.image e)
      (fun d => ∑ v ∈ fib d, (K d).cellProb v)]
  have hoff : ∀ d ∈ (Finset.univ.image e)ᶜ, ∑ v ∈ fib d, (K d).cellProb v = 1 := by
    intro d hd
    rw [Finset.mem_compl] at hd
    have hne : ¬ ∃ d', e d' = d := by
      rintro ⟨d', rfl⟩
      exact hd (Finset.mem_image_of_mem e (Finset.mem_univ d'))
    simp only [hfib_def, dif_neg hne]
    exact CellKnowledge.sum_cellProb_eq_one (hK d)
  rw [Finset.prod_congr rfl hoff, Finset.prod_const_one, mul_one,
    Finset.prod_image fun d' _ d'' _ h => he h]
  refine Finset.prod_congr rfl fun d' _ => ?_
  have hex : ∃ d'', e d'' = e d' := ⟨d', rfl⟩
  have hch : hex.choose = d' := he hex.choose_spec
  simp only [hfib_def, dif_pos hex]
  rw [Finset.sum_singleton, hch]

/-- **Marginal congruence.** Two feasible knowledge states that agree on the range of an
injection of cell domains induce the same law on the pushforward sub-table: a continuation that
reads the table only through the injection cannot distinguish them. -/
theorem evalDist_map_comp_genTable_congr {D' : Type} [Finite D']
    {e : D' → D} (he : Function.Injective e) {K K' : ProbeState D R}
    (hK : K.Feasible) (hK' : K'.Feasible) (hagree : ∀ d', K (e d') = K' (e d')) :
    𝒟[(fun g : D → R => g ∘ e) <$> genTable K] =
      𝒟[(fun g : D → R => g ∘ e) <$> genTable K'] := by
  classical
  letI := Fintype.ofFinite D'
  rw [evalDist_map_comp_injective_genTable he K hK,
    evalDist_map_comp_injective_genTable he K' hK']
  exact congrArg evalDist (congrArg genTable (funext hagree))

end OracleComp
