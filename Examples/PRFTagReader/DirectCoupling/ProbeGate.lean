/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.DirectCoupling
import Examples.PRFTagReader.MultipleToHybrid.EagerSetup
import VCVio.EvalDist.Monad.Disagreement
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEquiv
import VCVio.OracleComp.QueryTracking.RandomOracle.RevealTilt

/-!
# PRF Tag/Reader Protocol — Probe-Coupling Gate: A Two-Step Tilt Instance

A minimal two-step instance of the direct M_ideal/S_ideal coupling routed through the
consistent-table distribution `genTable`: one reader test at a fixed transcript `⟨n₀, a₀⟩`
followed by one slot-positive tag read at a fresh uniform nonce, with an arbitrary Boolean
continuation `F` of the reader bit, the nonce, and the read digest.

Both worlds read one shared table drawn from `genTable (ProbeState.init _ _)` over the
single-session cell domain `(TagId × Fin sessionsPerTag) × Nonce`. The reader step is lazified at
the *Boolean* level: `freshColumnSplit` folds `evalDist_genTable_probe_split` over the slot-zero
column at `n₀` (`evalDist_genTable_bind_freshColumnSplit`), materializing one comparison bit per
tag — never the cell values — and leaving the residual table distributed as `genTable` of the
post-probe knowledge state: hit cells `known a₀`, miss cells `excluded {a₀}`. The tag step then
reveals the M-side cell `((tag, 0), n)` from its *conditioned* allowed set, and the S-side cell
`((tag, σ), n)` with `σ ≠ 0` from the *untouched* full set — the slot-positive cells are off the
probed column, so the S-side reveal is a full uniform; the proof would not close here if the
reader step had conditioned them.

`probeGate_two_step` assembles the comparison: the M-side success probability is at most the
S-side success probability plus three explicit charges, each tied to one mechanism:

* `|TagId| / |Digest|` — the *fire* mass: some probe of the column genuinely hits
  (`probEvent_fst_freshColumnSplit_le`); off this event the M reader bit is `false`
  deterministically in the knowledge state alone.
* `(|Nonce| · |Digest|)⁻¹` — the *reveal tilt*: the probed column carries one exclusion in the
  M-side row, so the per-nonce defect `|Digest|⁻¹` of
  `probEvent_bind_uniformSelectFinset_sdiff_le` is paid only at the aliasing nonce `n₀`,
  averaging to `(|Nonce| · |Digest|)⁻¹` over the fresh nonce draw.
* `|TagId| · sessionsPerTag / |Digest|` — the *slot-positive discard*: off the fire event the
  S reader bit equals the slot-positive collision indicator `cacheBadReader`, which is replaced
  by `false` at the cost of its mass under the residual `genTable`
  (`probEvent_apply_eq_genTable_le` and a union bound).
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

/-! ## Boolean-level column lazification

`freshColumnSplit a₀ cells K` draws, for each cell of `cells` in turn, a uniform value, retains
only its comparison bit against the target `a₀` (OR-accumulated across the column), and records
the corresponding knowledge update — the program form of folding
`evalDist_genTable_probe_split` over a column of cells that are fresh in `K`. -/

section ColumnSplit

variable {D R : Type} [DecidableEq D] [DecidableEq R] [Fintype R]

/-- Draw the cells of a column one at a time, keeping only the OR of the comparison bits against
the target `a₀` together with the post-probe knowledge state: a hit determines the cell to `a₀`,
a miss excludes `a₀` there. -/
noncomputable def freshColumnSplit (a₀ : R) :
    List D → ProbeState D R → OptionT ProbComp (Bool × ProbeState D R)
  | [], K => pure (false, K)
  | d :: ds, K =>
    ($ (Finset.univ \ (∅ : Finset R))) >>= fun v =>
      freshColumnSplit a₀ ds (Function.update K d
        (if v = a₀ then .known a₀ else .excluded (insert a₀ ∅))) >>= fun z =>
      pure (decide (v = a₀) || z.1, z.2)

/-- Splitting an empty column draws nothing and reports no hit. -/
@[simp] lemma freshColumnSplit_nil (a₀ : R) (K : ProbeState D R) :
    freshColumnSplit a₀ [] K = pure (false, K) := rfl

/-- Splitting a column is one probe-shaped draw at the head cell followed by the split of the
tail from the updated knowledge state, with the head bit OR-ed onto the result. -/
lemma freshColumnSplit_cons (a₀ : R) (d : D) (ds : List D) (K : ProbeState D R) :
    freshColumnSplit a₀ (d :: ds) K =
      ($ (Finset.univ \ (∅ : Finset R))) >>= fun v =>
        freshColumnSplit a₀ ds (Function.update K d
          (if v = a₀ then .known a₀ else .excluded (insert a₀ ∅))) >>= fun z =>
        pure (decide (v = a₀) || z.1, z.2) := rfl

/-- Congruence for `evalDist` under `bind`: continuations that agree in distribution on the
support of the first computation yield equal bind distributions. -/
private lemma evalDist_optionT_bind_congr {α β : Type} {mx : OptionT ProbComp α}
    {f f' : α → OptionT ProbComp β}
    (h : ∀ x ∈ support mx, 𝒟[f x] = 𝒟[f' x]) : 𝒟[mx >>= f] = 𝒟[mx >>= f'] :=
  evalDist_ext fun y => probOutput_bind_congr fun x hx => by
    rw [probOutput_def, probOutput_def, h x hx]

/-- **Column redistribution.** Drawing a table consistent with `K` and running any continuation
is the same as first splitting a column of fresh cells — drawing only the per-cell comparison
bits against `a₀` — and then drawing the residual table consistent with the recorded post-probe
knowledge. Iterates `evalDist_genTable_probe_split` along the column. -/
lemma evalDist_genTable_bind_freshColumnSplit [Fintype D] {β : Type} (a₀ : R)
    (cells : List D) (K : ProbeState D R) (hnd : cells.Nodup)
    (hK : ∀ d ∈ cells, K d = .excluded ∅) (F : (D → R) → OptionT ProbComp β) :
    𝒟[genTable K >>= F] =
      𝒟[freshColumnSplit a₀ cells K >>= fun z => genTable z.2 >>= F] := by
  induction cells generalizing K with
  | nil => rw [freshColumnSplit_nil, pure_bind]
  | cons d ds ih =>
    have hd_ds : d ∉ ds := (List.nodup_cons.mp hnd).1
    have hcell : K d = .excluded ∅ := hK d List.mem_cons_self
    conv_lhs => rw [evalDist_bind,
      evalDist_genTable_probe_split hcell (Finset.notMem_empty a₀), ← evalDist_bind,
      bind_assoc]
    rw [freshColumnSplit_cons, bind_assoc]
    refine evalDist_optionT_bind_congr fun v _ => ?_
    rw [bind_assoc]
    simp only [pure_bind]
    have hKtail : ∀ d' ∈ ds, Function.update K d
        (if v = a₀ then CellKnowledge.known a₀ else .excluded (insert a₀ ∅)) d'
          = CellKnowledge.excluded ∅ := fun d' hd' => by
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hd' hd_ds)]
      exact hK d' (List.mem_cons_of_mem d hd')
    by_cases hva : v = a₀
    · simp only [if_pos hva]
      simp only [if_pos hva] at hKtail
      exact ih _ (List.nodup_cons.mp hnd).2 hKtail
    · simp only [if_neg hva]
      simp only [if_neg hva] at hKtail
      exact ih _ (List.nodup_cons.mp hnd).2 hKtail

/-- **Fire mass of a column split.** The probability that some bit of the column split comes up
`true` is at most `(number of cells) / |R|`: each head draw hits with probability `|R|⁻¹` and
the misses carry the tail bound. -/
lemma probEvent_fst_freshColumnSplit_le (a₀ : R) (cells : List D) (K : ProbeState D R) :
    Pr[fun z : Bool × ProbeState D R => z.1 = true | freshColumnSplit a₀ cells K] ≤
      (cells.length : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞) := by
  classical
  induction cells generalizing K with
  | nil =>
    rw [freshColumnSplit_nil]
    simp
  | cons d ds ih =>
    rw [freshColumnSplit_cons, Finset.sdiff_empty, probEvent_bind_eq_tsum, tsum_fintype,
      ← Finset.sum_erase_add _ _ (Finset.mem_univ a₀), List.length_cons,
      show ((ds.length + 1 : ℕ) : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞)
          = (ds.length : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞)
            + 1 / (Fintype.card R : ℝ≥0∞) from by rw [Nat.cast_succ, ENNReal.add_div]]
    simp only [ProbComp.probOutput_uniformSelectFinset, Finset.mem_univ, if_true,
      Finset.card_univ]
    refine add_le_add ?_ ?_
    · refine le_trans (Finset.sum_le_sum (g := fun _ => (Fintype.card R : ℝ≥0∞)⁻¹ *
        ((ds.length : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞))) fun v hv => ?_) ?_
      · obtain ⟨hv_ne, -⟩ := Finset.mem_erase.mp hv
        refine mul_le_mul' le_rfl ?_
        have htail : (freshColumnSplit a₀ ds (Function.update K d
            (if v = a₀ then CellKnowledge.known a₀ else .excluded (insert a₀ ∅)))
              >>= fun z => pure (decide (v = a₀) || z.1, z.2))
            = freshColumnSplit a₀ ds (Function.update K d
                (if v = a₀ then CellKnowledge.known a₀ else .excluded (insert a₀ ∅))) := by
          simp only [decide_eq_false hv_ne, Bool.false_or, Prod.mk.eta]
          exact bind_pure _
        rw [htail]
        exact ih _
      · rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a₀),
          Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
        calc ((Fintype.card R - 1 : ℕ) : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ *
              ((ds.length : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞))
            ≤ 1 * ((ds.length : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞)) :=
              mul_le_mul' (le_trans (mul_le_mul' (Nat.cast_le.mpr (Nat.sub_le _ _)) le_rfl)
                (ENNReal.mul_inv_le_one _)) le_rfl
          _ = (ds.length : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞) := one_mul _
    · refine le_trans (mul_le_mul' le_rfl probEvent_le_one) ?_
      rw [mul_one, one_div]

/-- **Support shape of a column split.** Along every path: cells off the column keep their
knowledge, on a no-hit path every column cell has excluded exactly `a₀`, and feasibility is
preserved (each miss draw itself witnesses the surviving value). -/
lemma freshColumnSplit_support (a₀ : R) (cells : List D) (K : ProbeState D R)
    (hnd : cells.Nodup) {z : Bool × ProbeState D R}
    (hz : z ∈ support (freshColumnSplit a₀ cells K)) :
    (∀ d, d ∉ cells → z.2 d = K d) ∧
      (z.1 = false → ∀ d ∈ cells, z.2 d = CellKnowledge.excluded {a₀}) ∧
      (K.Feasible → z.2.Feasible) := by
  induction cells generalizing K z with
  | nil =>
    rw [freshColumnSplit_nil, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨fun d _ => rfl, fun _ d hd => absurd hd (List.not_mem_nil), fun h => h⟩
  | cons d ds ih =>
    rw [freshColumnSplit_cons, mem_support_bind_iff] at hz
    obtain ⟨v, -, hz⟩ := hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨z', hz', hzz⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hzz
    subst hzz
    have hd_ds : d ∉ ds := (List.nodup_cons.mp hnd).1
    obtain ⟨c1, c2, c3⟩ := ih _ (List.nodup_cons.mp hnd).2 hz'
    refine ⟨?_, ?_, ?_⟩
    · intro d' hd'
      have hne : d' ≠ d := fun h => hd' (h ▸ List.mem_cons_self)
      rw [c1 d' fun h => hd' (List.mem_cons_of_mem d h), Function.update_of_ne hne]
    · intro hz1 d' hd'
      have hor := Bool.or_eq_false_iff.mp hz1
      have hv_ne : v ≠ a₀ := of_decide_eq_false hor.1
      rcases List.mem_cons.mp hd' with rfl | hd'
      · rw [c1 d' hd_ds, Function.update_self, if_neg hv_ne, Finset.insert_empty]
      · exact c2 hor.2 d' hd'
    · intro hKf
      refine c3 (hKf.update d ?_)
      by_cases hva : v = a₀
      · rw [if_pos hva]
        exact ⟨a₀, by simp⟩
      · rw [if_neg hva]
        exact ⟨v, by simp [hva]⟩

end ColumnSplit

/-! ## Reads of the residual table -/

section ResidualReads

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-- Transport of an output probability along an `evalDist` identity. -/
private lemma probOutput_congr_dist {α : Type} {mx my : OptionT ProbComp α} (x : α)
    (h : 𝒟[mx] = 𝒟[my]) : Pr[= x | mx] = Pr[= x | my] := by
  rw [probOutput_def, probOutput_def, h]

/-- Transport of an event probability along an `evalDist` identity. -/
private lemma probEvent_congr_dist {α : Type} {mx my : OptionT ProbComp α} (p : α → Prop)
    (h : 𝒟[mx] = 𝒟[my]) : Pr[ p | mx] = Pr[ p | my] := by
  rw [probEvent_def, probEvent_def, h]

/-- Two draws may be taken in either order: the output distribution of drawing `mx` then `my`
and combining is the same as drawing `my` then `mx`. -/
private lemma evalDist_bind_bind_comm {α₁ α₂ β : Type} (mx : OptionT ProbComp α₁)
    (my : OptionT ProbComp α₂) (F : α₁ → α₂ → OptionT ProbComp β) :
    𝒟[mx >>= fun a => my >>= fun b => F a b] =
      𝒟[my >>= fun b => mx >>= fun a => F a b] := by
  refine evalDist_ext fun y => ?_
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  have hL : ∀ a, Pr[= a | mx] * Pr[= y | my >>= fun b => F a b] =
      ∑' b, Pr[= a | mx] * (Pr[= b | my] * Pr[= y | F a b]) := fun a => by
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_left]
  have hR : ∀ b, Pr[= b | my] * Pr[= y | mx >>= fun a => F a b] =
      ∑' a, Pr[= b | my] * (Pr[= a | mx] * Pr[= y | F a b]) := fun b => by
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_left]
  rw [tsum_congr hL, tsum_congr hR, ENNReal.tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => by ring

/-- Averaged comparison of two continuations of a shared draw: a pointwise gap `ε x` integrates
to the average `∑' x, Pr[= x | mx] * ε x`. -/
private lemma probOutput_true_bind_le_bind_add_of_le {α : Type} (mx : OptionT ProbComp α)
    (f g : α → OptionT ProbComp Bool) (ε : α → ℝ≥0∞)
    (h : ∀ x, Pr[= true | f x] ≤ Pr[= true | g x] + ε x) :
    Pr[= true | mx >>= f] ≤ Pr[= true | mx >>= g] + ∑' x, Pr[= x | mx] * ε x := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [← mul_add]
  exact mul_le_mul' le_rfl (h x)

/-- A continuation that reads the table only at one undetermined cell sees exactly the uniform
draw from that cell's allowed set: the reveal split of the consistent-table distribution,
specialized to a single read. -/
private lemma probOutput_genTable_bind_pure_comp {β : Type} (K : ProbeState D R)
    (hK : K.Feasible) {d : D} {S : Finset R} (hcell : K d = CellKnowledge.excluded S)
    (g : R → β) (y : β) :
    Pr[= y | genTable K >>= fun gS => (pure (g (gS d)) : OptionT ProbComp β)] =
      Pr[= y | ($ (Finset.univ \ S)) >>= fun v => (pure (g v) : OptionT ProbComp β)] := by
  have hL : Pr[= y | genTable K >>= fun gS => (pure (g (gS d)) : OptionT ProbComp β)]
      = Pr[= y | ($ (Finset.univ \ S)) >>= fun v =>
          genTable (Function.update K d (CellKnowledge.known v)) >>= fun gS =>
            (pure (g (gS d)) : OptionT ProbComp β)] := by
    refine probOutput_congr_dist y ?_
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

/-- The probability that the residual table matches a target value at one undetermined cell is
at most the inverse size of that cell's allowed set. -/
private lemma probEvent_apply_eq_genTable_le (K : ProbeState D R) {d : D} {S : Finset R}
    (hcell : K d = CellKnowledge.excluded S) (a : R) :
    Pr[fun gS : D → R => gS d = a | genTable K] ≤
      ((Fintype.card R - S.card : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  rw [probEvent_congr_dist _ (evalDist_genTable_reveal_split hcell),
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

end ResidualReads

/-! ## The two-step gate -/

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
    probOutput_congr_dist true (evalDist_bind_bind_comm _ _ _)
  have hScomm : Pr[= true | (genTable K' >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
      pure (G n (gS ((tag, σ), n))) : OptionT ProbComp Bool)]
      = Pr[= true | ((liftM ($ᵗ Nonce) : OptionT ProbComp Nonce) >>= fun n =>
        genTable K' >>= fun gS =>
          pure (G n (gS ((tag, σ), n))) : OptionT ProbComp Bool)] :=
    probOutput_congr_dist true (evalDist_bind_bind_comm _ _ _)
  rw [hMcomm, hScomm]
  refine le_trans (probOutput_true_bind_le_bind_add_of_le (liftM ($ᵗ Nonce))
    (fun n => genTable K' >>= fun gS =>
      pure (G n (gS ((tag, (0 : Fin sessionsPerTag)), n))))
    (fun n => genTable K' >>= fun gS => pure (G n (gS ((tag, σ), n))))
    (fun n => if n = n₀ then (Fintype.card Digest : ℝ≥0∞)⁻¹ else 0) fun n => ?_) ?_
  · beta_reduce
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
    refine le_trans (probOutput_true_bind_le_bind_add_of_le (genTable K')
      (fun gS => liftM ($ᵗ Nonce) >>= fun n =>
        pure (F false n (gS ((tag, σ), n))))
      (fun gS => liftM ($ᵗ Nonce) >>= fun n =>
        pure (F (cacheBadReader (sessionsPerTag := sessionsPerTag) gS ⟨n₀, a₀⟩)
          n (gS ((tag, σ), n))))
      (fun gS => if cacheBadReader (sessionsPerTag := sessionsPerTag) gS
        (⟨n₀, a₀⟩ : TagTranscript Nonce Digest) = true then 1 else 0) fun gS => ?_) ?_
    · beta_reduce
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
  have hKinit : ∀ d ∈ cells,
      (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest) d =
        CellKnowledge.excluded ∅ := fun d _ => rfl
  -- Redistribute both worlds' table draws along the column split.
  rw [probOutput_congr_dist true (evalDist_genTable_bind_freshColumnSplit a₀ cells _ hnd
        hKinit (fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (F (unlinkReaderAccepts (Slot := TagId)
              (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
              (multiplePattern sessionsPerTag) ⟨n₀, a₀⟩)
            n (gS ((tag, (0 : Fin sessionsPerTag)), n))))),
      probOutput_congr_dist true (evalDist_genTable_bind_freshColumnSplit a₀ cells _ hnd
        hKinit (fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (F (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) ⟨n₀, a₀⟩)
            n (gS ((tag, σ), n)))))]
  simp only [← probEvent_eq_eq_probOutput]
  -- Fire mass of the column split.
  have hfire : Pr[fun z : Bool ×
      ProbeState ((TagId × Fin sessionsPerTag) × Nonce) Digest => z.1 = true |
      freshColumnSplit a₀ cells
        (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest)] ≤
      (Fintype.card TagId : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
    refine le_trans (probEvent_fst_freshColumnSplit_le a₀ cells _) (le_of_eq ?_)
    rw [hcells, List.length_map, Finset.length_toList, Finset.card_univ]
  -- Off-fire, the per-branch comparison is the off-fire step at the recorded state.
  have hperz : ∀ z ∈ support (freshColumnSplit a₀ cells
      (ProbeState.init ((TagId × Fin sessionsPerTag) × Nonce) Digest)),
      ¬ z.1 = true →
      Pr[(· = true) | genTable z.2 >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
          pure (F (unlinkReaderAccepts (Slot := TagId)
              (fun T nn => slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (T, nn))
              (multiplePattern sessionsPerTag) ⟨n₀, a₀⟩)
            n (gS ((tag, (0 : Fin sessionsPerTag)), n)))] ≤
        Pr[(· = true) | genTable z.2 >>= fun gS => liftM ($ᵗ Nonce) >>= fun n =>
            pure (F (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
                (fun sl nn => gS (sl, nn)) (singlePattern sessionsPerTag) ⟨n₀, a₀⟩)
              n (gS ((tag, σ), n)))] +
          (((Fintype.card Nonce : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞))⁻¹ +
            ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
              (Fintype.card Digest : ℝ≥0∞)) := by
    intro z hz hDz
    have hz1 : z.1 = false := Bool.eq_false_iff.mpr hDz
    obtain ⟨hoff, hcolF, hfeasF⟩ := freshColumnSplit_support a₀ cells _ hnd hz
    simp only [probEvent_eq_eq_probOutput]
    refine probeGate_offFire tag σ hσ0 n₀ a₀ F z.2 (hfeasF ProbeState.feasible_init)
      (fun T => hcolF hz1 _ ?_) (fun n hn => ?_) (fun T sid hsid n => ?_)
    · rw [hcells]
      exact List.mem_map.mpr ⟨T, Finset.mem_toList.mpr (Finset.mem_univ T), rfl⟩
    · refine (hoff _ fun hmem => ?_).trans rfl
      rw [hcells] at hmem
      obtain ⟨T, -, hT⟩ := List.mem_map.mp hmem
      exact hn (congrArg Prod.snd hT).symm
    · refine (hoff _ fun hmem => ?_).trans rfl
      rw [hcells] at hmem
      obtain ⟨T', -, hT⟩ := List.mem_map.mp hmem
      exact hsid (congrArg (fun p => p.1.2) hT).symm
  refine le_trans (probEvent_bind_le_add_of_disagree hfire hperz) (le_of_eq ?_)
  rw [← add_assoc]

end ProbeGate

end PRFTagReader
