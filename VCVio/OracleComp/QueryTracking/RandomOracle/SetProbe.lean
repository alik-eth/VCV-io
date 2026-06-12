/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeOracle

/-!
# Set Probes: Reveal-and-Check Birthday Bounds

This file extends the first-fire probe oracle of
`VCVio.OracleComp.QueryTracking.RandomOracle.FirstFire` with *multi-target* probes: a cell is
checked against a whole target set `A : Finset R` rather than a single value, and the per-step
firing charge is `|A| / (|R| - |S|)` instead of `1 / (|R| - |S|)`. Sequenced over `q` steps with
adaptively growing target sets, these charges add up to a birthday-class bound.

## The reveal-check step

`revealCheckStep st d A` reveals the value of cell `d` — via `revealStep`, so at an undetermined
cell a uniform draw from the allowed set `Finset.univ \ S` that is then recorded as `known` —
and additionally reports the boolean `v ∈ A`. The step *fires* when the cell was undetermined
and the boolean is `true`. This matches the shape of birthday-style consumers exactly: each
query freshly samples a value, hands it to the adversary, and the bad event is that the fresh
value collides with an adaptively chosen set of previously seen values.

Folding the reveal into the step is what keeps the state representation of
`FirstFire` unchanged: the revealed cell becomes `known v`, so exclusion sets never grow and an
`ExclLe` threshold is preserved verbatim across steps. A boolean-only set probe (reply `v ∈ A`
without revealing `v`) would instead require a richer `CellKnowledge` — on a hit the adversary
learns `v ∈ A` but not which element — and is not provided here; no current consumer needs it.

## The additive first-fire telescope

`probEvent_revealCheckStep_excluded_eq` is the single-step law: from an `excluded S` cell the
step fires with probability exactly `|A \ S| / (|R| - |S|)`. `probEvent_revealCheckTwo_le` is
the two-step instance with an adaptively grown second target set, with total bound
`|A₁| / |R| + (|A₁| + 1) / |R|`.

`probEvent_revealCheckMany_le` is the general bound: an adaptive strategy issuing `q`
reveal-check steps from a state whose exclusion sets have at most `m` elements, with the `i`-th
target set of size at most `a i`, fires somewhere with probability at most
`(∑ i < q, a i) / (|R| - m)`. Unlike the equality-probe bound `probEvent_probeMany_le`, no
survival-factor cancellation is needed: a reveal-check step never grows an exclusion set (the
probed cell becomes `known`), so the threshold `m` is preserved exactly and the per-step charges
`a i / (|R| - m)` simply add. `probEvent_revealCheckMany_birthday_le` instantiates `a i = i` to
get the birthday sum `(q * (q - 1) / 2) / (|R| - m)`, and
`probEvent_revealCheckMany_init_revealed_le` is the canonical consumer shape: from the initial
state, with each target set drawn from the previously revealed values, the collision probability
is at most `(q * (q - 1) / 2) / |R|`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp

/-- Whether a cell with this knowledge is still undetermined: a reveal at such a cell draws
fresh randomness, so only there can a reveal-check step fire. The deterministic reply at a
`known` cell is never charged. -/
def CellKnowledge.undetermined {R : Type} : CellKnowledge R → Bool
  | .known _ => false
  | .excluded _ => true

/-- A `known` cell is determined. -/
@[simp]
lemma CellKnowledge.undetermined_known {R : Type} (v : R) :
    (CellKnowledge.known v).undetermined = false := rfl

/-- An `excluded` cell is undetermined. -/
@[simp]
lemma CellKnowledge.undetermined_excluded {R : Type} (S : Finset R) :
    (CellKnowledge.excluded S).undetermined = true := rfl

variable {D R : Type} [DecidableEq D] [DecidableEq R] [Fintype R]

/-! ## The reveal-check step -/

/-- Reveal the value of cell `d` and report whether it lies in the target set `A`: the value is
obtained by `revealStep` — the determined value at a `known` cell, and otherwise a uniform draw
from the allowed set `Finset.univ \ S` that is then recorded as `known` — and the boolean reply
is the membership test of the revealed value in `A`. -/
noncomputable def revealCheckStep (st : ProbeState D R) (d : D) (A : Finset R) :
    OptionT ProbComp (R × Bool × ProbeState D R) :=
  (fun z => (z.1, decide (z.1 ∈ A), z.2)) <$> revealStep st d

/-- A reveal-check at a `known` cell returns the determined value and its membership test, and
changes nothing; it never fires. -/
theorem revealCheckStep_known {st : ProbeState D R} {d : D} {v : R} (A : Finset R)
    (hst : st d = .known v) :
    revealCheckStep st d A = pure (v, decide (v ∈ A), st) := by
  rw [revealCheckStep, revealStep_known hst, map_pure]

/-- A reveal-check at an undetermined cell draws the value uniformly from the allowed set,
records the cell as `known`, and reports membership of the drawn value in the target set. -/
theorem revealCheckStep_excluded {st : ProbeState D R} {d : D} {S : Finset R} (A : Finset R)
    (hst : st d = .excluded S) :
    revealCheckStep st d A = (fun v => (v, decide (v ∈ A), Function.update st d (.known v))) <$>
      ($ (Finset.univ \ S)) := by
  rw [revealCheckStep, revealStep_excluded hst, Functor.map_map]

/-! ## The single-step firing probability -/

/-- A reveal-check at a `known` cell replies deterministically. -/
theorem probEvent_revealCheckStep_known {st : ProbeState D R} {d : D} {v : R} (A : Finset R)
    (hst : st d = .known v) :
    Pr[ (fun z : R × Bool × ProbeState D R => z.2.1 = true) | revealCheckStep st d A ] =
      if v ∈ A then 1 else 0 := by
  rw [revealCheckStep_known A hst, probEvent_pure]
  simp only [decide_eq_true_eq]

/-- **Single reveal-check step.** At an `excluded S` cell, a reveal-check against the target set
`A` fires with probability exactly `|A \ S| / (|R| - |S|)`: the revealed value is uniform on the
`|R| - |S|` allowed values, of which exactly the elements of `A \ S` lie in `A`. -/
theorem probEvent_revealCheckStep_excluded_eq {st : ProbeState D R} {d : D} {S : Finset R}
    (A : Finset R) (hst : st d = .excluded S) :
    Pr[ (fun z : R × Bool × ProbeState D R => z.2.1 = true) | revealCheckStep st d A ] =
      ((A \ S).card : ℝ≥0∞) / ((Fintype.card R - S.card : ℕ) : ℝ≥0∞) := by
  rw [revealCheckStep_excluded A hst, probEvent_map]
  have hpred : ((fun z : R × Bool × ProbeState D R => z.2.1 = true) ∘
      (fun v : R => (v, decide (v ∈ A), Function.update st d (.known v)))) =
      fun v : R => v ∈ A := by
    funext v
    rw [Function.comp_apply, decide_eq_true_eq]
  rw [hpred, ProbComp.probEvent_uniformSelectFinset]
  have hfilter : {x ∈ Finset.univ \ S | x ∈ A} = A \ S := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]

/-- The consumable form of the single-step law: a reveal-check against `A` fires with
probability at most `|A| / (|R| - |S|)`. -/
theorem probEvent_revealCheckStep_excluded_le {st : ProbeState D R} {d : D} {S : Finset R}
    (A : Finset R) (hst : st d = .excluded S) :
    Pr[ (fun z : R × Bool × ProbeState D R => z.2.1 = true) | revealCheckStep st d A ] ≤
      (A.card : ℝ≥0∞) / ((Fintype.card R - S.card : ℕ) : ℝ≥0∞) := by
  rw [probEvent_revealCheckStep_excluded_eq A hst]
  exact ENNReal.div_le_div_right (Nat.cast_le.2 (Finset.card_le_card Finset.sdiff_subset)) _

/-- The firing probability of a reveal-check step, read off the projected boolean reply. This is
the form consumed at the second step of the two-step bound, where the program keeps only the
boolean. -/
theorem probEvent_revealCheckStep_bind_eq {st : ProbeState D R} {d : D} {S : Finset R}
    (A : Finset R) (hst : st d = .excluded S) :
    Pr[ (fun b : Bool => b = true) | revealCheckStep st d A >>= fun z => pure z.2.1 ] =
      ((A \ S).card : ℝ≥0∞) / ((Fintype.card R - S.card : ℕ) : ℝ≥0∞) := by
  have hmap : (revealCheckStep st d A >>= fun z => pure z.2.1) =
      (fun z : R × Bool × ProbeState D R => z.2.1) <$> revealCheckStep st d A := by
    rw [map_eq_bind_pure_comp]
    rfl
  rw [hmap, probEvent_map]
  exact probEvent_revealCheckStep_excluded_eq A hst

/-! ## Two adaptive reveal-check steps

The adversary reveal-checks a first cell against `A₁`, sees the revealed value `v₁`, and
adaptively chooses the second target set `f v₁` — canonically `insert v₁ A₁`, the previously
seen values grown by the fresh one. The second step's charge is therefore against the *grown*
set, of size at most `|A₁| + 1`, and the total is the two-term birthday sum. -/

/-- Two adaptive reveal-check steps: check cell `d₁` against `A₁`, observe the revealed value
`v₁`, then check cell `d₂` against the adaptively chosen target set `f v₁`; return whether
either boolean reply was `true`. -/
noncomputable def revealCheckTwo (st : ProbeState D R) (d₁ d₂ : D) (A₁ : Finset R)
    (f : R → Finset R) : OptionT ProbComp Bool :=
  revealCheckStep st d₁ A₁ >>= fun z₁ =>
    revealCheckStep z₁.2.2 d₂ (f z₁.1) >>= fun z₂ => pure (z₁.2.1 || z₂.2.1)

/-- **Two adaptive reveal-check steps.** From a state where both (distinct) cells are
undetermined with empty exclusion sets, checking `d₁` against `A₁` and then `d₂` against an
adaptively chosen set of size at most `|A₁| + 1` replies `true` somewhere with probability at
most `|A₁| / |R| + (|A₁| + 1) / |R|` — the second charge is against the grown target set. -/
theorem probEvent_revealCheckTwo_le (st : ProbeState D R) (d₁ d₂ : D) (A₁ : Finset R)
    (f : R → Finset R) (hst₁ : st d₁ = .excluded ∅) (hst₂ : st d₂ = .excluded ∅)
    (hne : d₂ ≠ d₁) (hf : ∀ v, (f v).card ≤ A₁.card + 1) :
    Pr[ (fun b : Bool => b = true) | revealCheckTwo st d₁ d₂ A₁ f ] ≤
      (A₁.card : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞) +
        ((A₁.card + 1 : ℕ) : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞) := by
  rw [revealCheckTwo, revealCheckStep_excluded A₁ hst₁, Finset.sdiff_empty, bind_map_left,
    probEvent_bind_eq_tsum, tsum_fintype,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ A₁)]
  refine add_le_add ?_ ?_
  · -- First-step hits `v₁ ∈ A₁`: charge the full reach probability of each hit.
    refine le_trans (Finset.sum_le_sum (g := fun v => Pr[= v | $ (Finset.univ : Finset R)])
      fun v _ => le_trans (mul_le_mul' le_rfl probEvent_le_one) (le_of_eq (mul_one _))) ?_
    rw [Finset.filter_univ_mem]
    simp only [ProbComp.probOutput_uniformSelectFinset, Finset.mem_univ, if_true,
      Finset.card_univ]
    rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  · -- First-step misses `v₁ ∉ A₁`: only the second step can fire, against the grown set.
    refine le_trans (Finset.sum_le_card_nsmul _ _ ((Fintype.card R : ℝ≥0∞)⁻¹ *
      (((A₁.card + 1 : ℕ) : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞))) fun v hv => ?_) ?_
    · have hv' : v ∉ A₁ := by simpa using (Finset.mem_filter.1 hv).2
      dsimp only
      rw [decide_eq_false hv']
      simp only [Bool.false_or]
      refine mul_le_mul' (le_of_eq (by simp)) ?_
      -- Second step from the post-reveal state, at the untouched cell `d₂`.
      have hupd : Function.update st d₁ (CellKnowledge.known v) d₂ =
          CellKnowledge.excluded ∅ := by
        rw [Function.update_of_ne hne, hst₂]
      rw [probEvent_revealCheckStep_bind_eq (f v) hupd]
      simp only [Finset.sdiff_empty, Finset.card_empty, Nat.sub_zero]
      exact ENNReal.div_le_div_right (Nat.cast_le.2 (hf v)) _
    · -- At most `|R|` miss branches, each reached with probability `|R|⁻¹`.
      rw [nsmul_eq_mul, ← mul_assoc]
      refine le_trans (mul_le_mul' (mul_le_mul' (Nat.cast_le.2 (Finset.card_le_univ _))
        le_rfl) le_rfl) ?_
      exact le_trans (mul_le_mul' (ENNReal.mul_inv_le_one _) le_rfl) (le_of_eq (one_mul _))

/-- **Fresh-pair collision (q = 2).** Reveal two distinct undetermined cells, checking the
second value against a single adaptively chosen target — canonically the first revealed value.
The first check is against the empty set, so only the second step can fire, and the collision
probability is at most `1 / |R|`. -/
theorem probEvent_revealCheckTwo_empty_le (st : ProbeState D R) (d₁ d₂ : D)
    (f : R → Finset R) (hst₁ : st d₁ = .excluded ∅) (hst₂ : st d₂ = .excluded ∅)
    (hne : d₂ ≠ d₁) (hf : ∀ v, (f v).card ≤ 1) :
    Pr[ (fun b : Bool => b = true) | revealCheckTwo st d₁ d₂ ∅ f ] ≤
      (Fintype.card R : ℝ≥0∞)⁻¹ := by
  have hb := probEvent_revealCheckTwo_le st d₁ d₂ ∅ f hst₁ hst₂ hne (by simpa using hf)
  simpa using hb

/-! ## The general adaptive birthday bound -/

/-- An adaptive `q`-step reveal-check program: the strategy `σ` maps the list of revealed values
seen so far to the next `(cell, target set)` pair, and the program returns whether some step
*fired* — revealed an undetermined cell whose drawn value lay in the chosen target set. The
revealed values determine every boolean reply, so they are the adversary's full view. -/
noncomputable def revealCheckMany :
    ℕ → ProbeState D R → (List R → D × Finset R) → OptionT ProbComp Bool
  | 0, _, _ => pure false
  | q + 1, st, σ =>
    revealCheckStep st (σ []).1 (σ []).2 >>= fun z =>
      (fun b => ((st (σ []).1).undetermined && z.2.1) || b) <$>
        revealCheckMany q z.2.2 fun h => σ (z.1 :: h)

/-- Zero reveal-check steps never fire. -/
@[simp]
theorem revealCheckMany_zero (st : ProbeState D R) (σ : List R → D × Finset R) :
    revealCheckMany 0 st σ = pure false := rfl

/-- `q + 1` reveal-check steps are one `revealCheckStep` at the strategy's first choice followed
by `q` steps from the updated state, with the head step's fire flag OR-ed onto the tail
result. -/
theorem revealCheckMany_succ (q : ℕ) (st : ProbeState D R) (σ : List R → D × Finset R) :
    revealCheckMany (q + 1) st σ =
      revealCheckStep st (σ []).1 (σ []).2 >>= fun z =>
        (fun b => ((st (σ []).1).undetermined && z.2.1) || b) <$>
          revealCheckMany q z.2.2 fun h => σ (z.1 :: h) := rfl

/-- **Adaptive multi-target first-fire bound.** An adaptive strategy issuing `q` reveal-check
steps from a state whose exclusion sets have at most `m` elements, choosing at the `i`-th step a
target set of size at most `a i`, fires somewhere with probability at most
`(∑ i < q, a i) / (|R| - m)`.

The head step either replies deterministically at a `known` cell (uncharged, state unchanged),
or reveals an `excluded S` cell with `S.card ≤ m`: it fires with probability
`|A₀ \ S| / (|R| - S.card) ≤ a 0 / (|R| - m)`, and every continuation state records the revealed
cell as `known` — exclusion sets never grow, so the threshold `m` is preserved exactly and the
tail budget `(∑ i < q, a (i + 1)) / (|R| - m)` applies verbatim on every branch. The charges
simply add; no survival-factor cancellation is needed. -/
theorem probEvent_revealCheckMany_le (q m : ℕ) (a : ℕ → ℕ) (st : ProbeState D R)
    (σ : List R → D × Finset R) (hst : st.ExclLe m)
    (hσ : ∀ h : List R, h.length < q → ((σ h).2).card ≤ a h.length) :
    Pr[ (fun b : Bool => b = true) | revealCheckMany q st σ ] ≤
      ((∑ i ∈ Finset.range q, a i : ℕ) : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞) := by
  induction q generalizing a st σ with
  | zero => simp
  | succ q ih =>
    have hsum : ((∑ i ∈ Finset.range (q + 1), a i : ℕ) : ℝ≥0∞) /
        ((Fintype.card R - m : ℕ) : ℝ≥0∞) =
        ((a 0 : ℕ) : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞) +
          ((∑ i ∈ Finset.range q, a (i + 1) : ℕ) : ℝ≥0∞) /
            ((Fintype.card R - m : ℕ) : ℝ≥0∞) := by
      rw [Finset.sum_range_succ', Nat.cast_add, ENNReal.add_div, add_comm]
    rcases hcell : st (σ []).1 with v | S
    · -- `known` cell: deterministic uncharged reply, state and threshold unchanged.
      rw [revealCheckMany_succ, revealCheckStep_known (σ []).2 hcell, pure_bind]
      simp only [hcell, CellKnowledge.undetermined_known, Bool.false_and, Bool.false_or,
        id_map']
      refine le_trans (ih (fun i => a (i + 1)) st _ hst fun h hh => ?_) ?_
      · simpa using hσ (v :: h) (by simpa using hh)
      · rw [hsum]
        exact le_add_self
    · -- Undetermined cell: a genuine reveal-check, charged `a 0 / (|R| - m)`.
      have hk : S.card ≤ m := hst _ _ hcell
      have ha0 : ((σ []).2).card ≤ a 0 := by simpa using hσ [] (Nat.succ_pos q)
      rw [revealCheckMany_succ, revealCheckStep_excluded (σ []).2 hcell, bind_map_left]
      simp only [hcell, CellKnowledge.undetermined_excluded, Bool.true_and]
      rw [probEvent_bind_eq_tsum, tsum_fintype,
        ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ (σ []).2), hsum]
      refine add_le_add ?_ ?_
      · -- Hit branches `v ∈ A₀`: total reach probability `|A₀ \ S| / (|R| - S.card)`.
        refine le_trans (Finset.sum_le_sum (g := fun v => Pr[= v | $ (Finset.univ \ S)])
          fun v _ => le_trans (mul_le_mul' le_rfl probEvent_le_one) (le_of_eq (mul_one _))) ?_
        simp only [ProbComp.probOutput_uniformSelectFinset]
        rw [Finset.sum_ite_mem, Finset.filter_univ_mem,
          show (σ []).2 ∩ (Finset.univ \ S) = (σ []).2 \ S from by
            ext v
            simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and],
          Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff_of_subset (Finset.subset_univ S),
          Finset.card_univ, div_eq_mul_inv]
        exact mul_le_mul'
          (Nat.cast_le.2 (le_trans (Finset.card_le_card Finset.sdiff_subset) ha0))
          (ENNReal.inv_le_inv' (Nat.cast_le.2 (Nat.sub_le_sub_left hk _)))
      · -- Miss branches `v ∉ A₀`: the tail continues at the unchanged threshold `m`.
        refine le_trans (Finset.sum_le_sum (g := fun v => Pr[= v | $ (Finset.univ \ S)] *
          (((∑ i ∈ Finset.range q, a (i + 1) : ℕ) : ℝ≥0∞) /
            ((Fintype.card R - m : ℕ) : ℝ≥0∞))) fun v hv => ?_) ?_
        · have hv' : v ∉ (σ []).2 := by simpa using (Finset.mem_filter.1 hv).2
          dsimp only
          rw [decide_eq_false hv']
          simp only [Bool.false_or, id_map']
          refine mul_le_mul' le_rfl
            (ih (fun i => a (i + 1)) _ _ (hst.update_known (σ []).1 v) fun h hh => ?_)
          simpa using hσ (v :: h) (by simpa using hh)
        · -- The miss branches' total reach probability is at most one.
          rw [← Finset.sum_mul]
          refine le_trans (mul_le_mul' ?_ le_rfl) (le_of_eq (one_mul _))
          simp only [ProbComp.probOutput_uniformSelectFinset]
          rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
          exact le_trans (mul_le_mul' (Nat.cast_le.2 (Finset.card_le_card
            Finset.inter_subset_right)) le_rfl) (ENNReal.mul_inv_le_one _)

/-- **Birthday bound.** If the `i`-th target set has size at most `i` — as when targets are
drawn from the values revealed so far — then `q` adaptive reveal-check steps fire with
probability at most `(q * (q - 1) / 2) / (|R| - m)`. -/
theorem probEvent_revealCheckMany_birthday_le (q m : ℕ) (st : ProbeState D R)
    (σ : List R → D × Finset R) (hst : st.ExclLe m)
    (hσ : ∀ h : List R, h.length < q → ((σ h).2).card ≤ h.length) :
    Pr[ (fun b : Bool => b = true) | revealCheckMany q st σ ] ≤
      ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞) := by
  have hb := probEvent_revealCheckMany_le q m (fun i => i) st σ hst hσ
  rwa [Finset.sum_range_id] at hb

/-- **Birthday bound from the initial state, canonical instance.** From the initial probe
state, `q` adaptive reveal-check steps whose target sets are drawn from the previously revealed
values fire — i.e. some fresh value collides with an earlier one the adversary selected — with
probability at most `(q * (q - 1) / 2) / |R|`. -/
theorem probEvent_revealCheckMany_init_revealed_le (q : ℕ) (σ : List R → D × Finset R)
    (hσ : ∀ h : List R, h.length < q → (σ h).2 ⊆ h.toFinset) :
    Pr[ (fun b : Bool => b = true) | revealCheckMany q (ProbeState.init D R) σ ] ≤
      ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞) := by
  have hb := probEvent_revealCheckMany_birthday_le q 0 (ProbeState.init D R) σ
    ProbeState.exclLe_init fun h hh =>
      le_trans (Finset.card_le_card (hσ h hh)) h.toFinset_card_le
  simpa using hb

end OracleComp
