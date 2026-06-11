/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import VCVio.OracleComp.ProbComp

/-!
# First-Fire Probe Oracle

This file defines a *probe oracle*: a lazily sampled oracle with cells indexed by `D` and values
in `R`, where the adversary never sees a cell's value directly. A probe `(d, a)` reveals only the
boolean "does cell `d` hold the value `a`?". The oracle's state (`ProbeState`) records, per cell,
exactly what the boolean replies so far have determined: either the value is `known v` (after a
hit), or a finite set `S` of values has been `excluded` (one per miss).

## The probe step

`probeStep st d a` is the single-probe transition:

* if cell `d` is `known v`, the reply is the deterministic comparison `v = a` and the state is
  unchanged — a determined cell never adds randomness;
* if cell `d` is `excluded S` and `a ∈ S`, the reply is `false` and the state is unchanged — the
  adversary re-asks a value it already ruled out;
* if cell `d` is `excluded S` and `a ∉ S`, the probe is *genuine*: a value `v` is drawn uniformly
  from the allowed set `Finset.univ \ S`, the reply is `v = a`, and only the boolean and the
  exclusion are retained — on a hit the cell becomes `known a`, on a miss `excluded (insert a S)`.

The draw-and-forget in the genuine branch is the point of the representation: the state never
remembers the drawn value beyond the one-bit reply, so it records precisely the conditional
distribution of the still-undetermined cell — uniform on `Finset.univ \ S`.

The step lives in `OptionT ProbComp`, the monad of the `Finset` uniform selector `$ s`, whose
failure branch accounts for an empty allowed set. Under the hypotheses of every lemma below the
allowed set contains the probe target, so the failure branch never contributes.

A probe **fires** when it is genuine and the reply is `true`. The lemmas below bound the
probability that some probe in an adaptive sequence fires.

## The repeat-target subtlety

A cell whose value was drawn at an earlier probe but only partially revealed (one boolean) can be
*re-targeted*: after a miss at `a₁`, a second probe at the same cell fires with probability
`1 / (|R| - 1)`, strictly larger than the single-draw bound `1 / |R|`. Any analysis that charges
each step the *maximum* per-step firing probability therefore overshoots: across two probes the
per-step charge reaches `2 · (1 / (|R| - 1))`, exceeding the true total. The honest total for two
same-cell probes is the telescope
`1/|R| + (1 - 1/|R|) · 1/(|R| - 1) = 2/|R|`,
which is exactly `q / |R|` for `q = 2` — a *first-fire* bound: each summand is the probability
that the current probe is the first to fire, and the conditioning that inflates the per-step
charge is cancelled by the probability of reaching that step without a prior fire. The probe
state makes this telescope provable, because `excluded S` is exactly the conditioning event.

`probEvent_probeTwo_retarget_le` is the decisive instance: two adaptive probes at the *same* cell,
the second target chosen as an arbitrary function of the first reply, with total firing
probability `≤ 2 / |R|`. `probEvent_probeTwo_distinct_le` is the analogous bound when the second
probe targets a different cell.

## The general first-fire bound (not yet formalized here)

For an adaptive adversary making `q` probes from a state `K`, the target statement is

`Pr[ some genuine probe fires within q probes from K ] ≤ q / (|R| - maxExcl K)`,

where `maxExcl K` is the supremum of `S.card` over the `excluded S` cells of `K`. The intended
proof is a head-first induction on `q` whose telescope is exact: with `D = |R|` and
`m = maxExcl K`,

`1/(D - m) + (1 - 1/(D - m)) · (q - 1)/(D - m - 1) = q/(D - m)`,

since a genuine probe at an `excluded S` cell fires with probability `1/(D - S.card)` and on a
miss grows that cell's exclusion set by one. The lemmas in this file are the `q = 1` and `q = 2`
instances of that bound.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp

/-- Adversary-side knowledge about a single probe-oracle cell, as determined by the boolean
replies so far: either the cell's value is fully determined, or a finite set of candidate values
has been ruled out (and the value is uniform on the complement). -/
inductive CellKnowledge (R : Type) where
  /-- The cell's value is determined to be `v` (a previous probe at `v` hit). -/
  | known (v : R)
  /-- The cell's value is undetermined; every value in `S` has been ruled out by a miss. -/
  | excluded (S : Finset R)

/-- Probe-oracle state: per-cell knowledge. The initial state is `ProbeState.init`, where no cell
holds any information. -/
abbrev ProbeState (D R : Type) := D → CellKnowledge R

/-- The initial probe state: every cell is undetermined with empty exclusion set. -/
def ProbeState.init (D R : Type) : ProbeState D R := fun _ => .excluded ∅

variable {D R : Type} [DecidableEq D] [DecidableEq R] [Fintype R]

/-- One probe at cell `d` with target `a`: deterministic comparison at a `known` cell, a `false`
reply at an already-excluded target, and otherwise a genuine probe — a uniform draw from the
allowed set `Finset.univ \ S`, of which only the boolean reply and the resulting knowledge update
are retained. -/
noncomputable def probeStep (st : ProbeState D R) (d : D) (a : R) :
    OptionT ProbComp (Bool × ProbeState D R) :=
  match st d with
  | .known v => pure (decide (v = a), st)
  | .excluded S =>
    if a ∈ S then pure (false, st)
    else (fun v => (decide (v = a),
      Function.update st d (if v = a then .known a else .excluded (insert a S)))) <$>
      ($ (Finset.univ \ S))

/-! ## Probe-step equations -/

/-- A probe at a `known` cell is the deterministic comparison; it never fires. -/
theorem probeStep_known {st : ProbeState D R} {d : D} {v : R} (a : R) (hst : st d = .known v) :
    probeStep st d a = pure (decide (v = a), st) := by
  rw [probeStep, hst]

/-- A probe at an already-excluded target replies `false` and changes nothing; it never fires. -/
theorem probeStep_excluded_mem {st : ProbeState D R} {d : D} {S : Finset R} (a : R)
    (hst : st d = .excluded S) (ha : a ∈ S) :
    probeStep st d a = pure (false, st) := by
  rw [probeStep, hst]
  exact if_pos ha

/-- A genuine probe is a uniform draw from the allowed set `Finset.univ \ S`, of which only the
boolean reply and the knowledge update are retained. -/
theorem probeStep_excluded_notMem {st : ProbeState D R} {d : D} {S : Finset R} (a : R)
    (hst : st d = .excluded S) (ha : a ∉ S) :
    probeStep st d a = (fun v => (decide (v = a),
      Function.update st d (if v = a then .known a else .excluded (insert a S)))) <$>
      ($ (Finset.univ \ S)) := by
  rw [probeStep, hst]
  exact if_neg ha

/-! ## q = 1 : the single-probe firing probability -/

/-- **Single genuine probe (q = 1).** A genuine probe at an `excluded S` cell fires with
probability exactly `1 / (|R| - S.card)`: the cell's value is uniform on the allowed set
`Finset.univ \ S`, and the target `a` is one of its `|R| - S.card` elements. -/
theorem probEvent_probeStep_fresh_eq {st : ProbeState D R} {d : D} {S : Finset R} (a : R)
    (hst : st d = .excluded S) (ha : a ∉ S) :
    Pr[ (fun z : Bool × ProbeState D R => z.1 = true) | probeStep st d a ] =
      ((Fintype.card R - S.card : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [probeStep_excluded_notMem a hst ha, probEvent_map]
  have hpred : ((fun z : Bool × ProbeState D R => z.1 = true) ∘ (fun v : R => (decide (v = a),
      Function.update st d (if v = a then .known a else .excluded (insert a S))))) =
      fun v : R => v = a := by
    funext v
    rw [Function.comp_apply, decide_eq_true_eq]
  rw [hpred, ProbComp.probEvent_uniformSelectFinset]
  rw [Finset.filter_eq', if_pos (Finset.mem_sdiff.2 ⟨Finset.mem_univ a, ha⟩),
    Finset.card_singleton, Finset.card_sdiff_of_subset (Finset.subset_univ S),
    Finset.card_univ, Nat.cast_one, one_div]

/-- **Single genuine probe from the initial state.** At a cell with empty exclusion set, a probe
fires with probability exactly `1 / |R|`. -/
theorem probEvent_probeStep_init_eq {st : ProbeState D R} {d : D} (a : R)
    (hst : st d = .excluded ∅) :
    Pr[ (fun z : Bool × ProbeState D R => z.1 = true) | probeStep st d a ] =
      (Fintype.card R : ℝ≥0∞)⁻¹ := by
  simpa using probEvent_probeStep_fresh_eq a hst (Finset.notMem_empty a)

/-- A probe at a `known` cell never fires: its reply is deterministic, so it carries probability
`1` exactly when the adversary asks the value it already knows — never a genuine charge. -/
theorem probEvent_probeStep_known {st : ProbeState D R} {d : D} {v : R} (a : R)
    (hst : st d = .known v) :
    Pr[ (fun z : Bool × ProbeState D R => z.1 = true) | probeStep st d a ] =
      if v = a then 1 else 0 := by
  rw [probeStep_known a hst, probEvent_pure]
  simp only [decide_eq_true_eq]

/-- A probe at an already-excluded target never fires. -/
theorem probEvent_probeStep_excluded_mem {st : ProbeState D R} {d : D} {S : Finset R} (a : R)
    (hst : st d = .excluded S) (ha : a ∈ S) :
    Pr[ (fun z : Bool × ProbeState D R => z.1 = true) | probeStep st d a ] = 0 := by
  rw [probeStep_excluded_mem a hst ha, probEvent_pure]
  simp

/-- The firing probability of a genuine probe, read off the projected boolean reply. This is the
form consumed at the second step of the two-probe bounds, where the program keeps only the
reply. -/
theorem probEvent_probeStep_bind_fst_eq {st : ProbeState D R} {d : D} {S : Finset R} (a : R)
    (hst : st d = .excluded S) (ha : a ∉ S) :
    Pr[ (fun b : Bool => b = true) | probeStep st d a >>= fun z => pure z.1 ] =
      ((Fintype.card R - S.card : ℕ) : ℝ≥0∞)⁻¹ := by
  have hmap : (probeStep st d a >>= fun z => pure z.1) = Prod.fst <$> probeStep st d a := by
    rw [map_eq_bind_pure_comp]
    rfl
  rw [hmap, probEvent_map]
  exact probEvent_probeStep_fresh_eq a hst ha

/-! ## q = 2 : two adaptive probes

The adversary makes a first probe `(d₁, a₁)` at a cell with empty exclusion set, observes the
boolean reply `b₁`, and *adaptively* picks the second target `f b₁` as a function of that reply.
The decisive case is `d₂ = d₁`: on a first miss the second probe re-targets the same cell, whose
value is now uniform on `|R| - 1` values, so the conditional firing probability is
`1 / (|R| - 1) > 1 / |R|`. The total is nevertheless `≤ 2 / |R|`, because the inflated second
charge only arises after a first miss — the first-fire telescope
`1/|R| + (1 - 1/|R|) · 1/(|R| - 1) = 2/|R|` is exact. -/

/-- Two adaptive probes: probe `(d₁, a₁)`, observe the reply `b₁`, then probe `(d₂, f b₁)` with
the second target chosen adaptively from the first reply; return whether either probe replied
`true`. Both the same-cell re-target (`d₂ = d₁`) and the distinct-cell case are instances. -/
noncomputable def probeTwo (st : ProbeState D R) (d₁ d₂ : D) (a₁ : R) (f : Bool → R) :
    OptionT ProbComp Bool :=
  probeStep st d₁ a₁ >>= fun z₁ =>
    probeStep z₁.2 d₂ (f z₁.1) >>= fun z₂ => pure (z₁.1 || z₂.1)

/-- **Two adaptive probes (general form).** From a state whose cell `d₁` (and cell `d₂`, if
distinct) has empty exclusion set, two adaptive probes reply `true` somewhere with probability
`≤ 2 / |R|` — covering in particular the same-cell re-target `d₂ = d₁`, where the second probe's
conditional firing probability is `1 / (|R| - 1)` and a per-step union bound would overshoot. -/
theorem probEvent_probeTwo_le (st : ProbeState D R) (d₁ d₂ : D) (a₁ : R) (f : Bool → R)
    (hst₁ : st d₁ = .excluded ∅) (hst₂ : d₂ ≠ d₁ → st d₂ = .excluded ∅) :
    Pr[ (fun b : Bool => b = true) | probeTwo st d₁ d₂ a₁ f ] ≤
      2 / (Fintype.card R : ℝ≥0∞) := by
  classical
  rw [probeTwo, probeStep_excluded_notMem a₁ hst₁ (Finset.notMem_empty a₁), Finset.sdiff_empty,
    bind_map_left, probEvent_bind_eq_tsum, tsum_fintype,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ a₁), div_eq_mul_inv, two_mul]
  refine add_le_add ?_ ?_
  · -- Sum over first replies `v ≠ a₁`: each summand is a first-miss branch, where the second
    -- probe fires with conditional probability at most `1 / (|R| - 1)`.
    refine le_trans (Finset.sum_le_card_nsmul _ _
      ((Fintype.card R : ℝ≥0∞)⁻¹ * ((Fintype.card R - 1 : ℕ) : ℝ≥0∞)⁻¹) fun v hv => ?_) ?_
    · obtain ⟨hv_ne, -⟩ := Finset.mem_erase.1 hv
      dsimp only
      rw [decide_eq_false hv_ne, if_neg hv_ne, Finset.insert_empty]
      simp only [Bool.false_or]
      refine mul_le_mul' (le_of_eq (by simp)) ?_
      -- Second probe from the post-miss state `Function.update st d₁ (.excluded {a₁})`.
      by_cases hd : d₂ = d₁
      · subst hd
        have hupd : Function.update st d₂ (CellKnowledge.excluded {a₁}) d₂ =
            CellKnowledge.excluded {a₁} := Function.update_self d₂ _ st
        by_cases hf : f false = a₁
        · -- Re-target of the already-excluded value: the second probe cannot fire.
          rw [probeStep_excluded_mem (f false) hupd (Finset.mem_singleton.2 hf), pure_bind]
          simp
        · -- Genuine re-target at the same cell: fires with probability `1 / (|R| - 1)`.
          rw [probEvent_probeStep_bind_fst_eq (f false) hupd (by simp [hf])]
          simp
      · -- Distinct cell: a genuine probe at an untouched cell, probability `1 / |R|`.
        have hupd : Function.update st d₁ (CellKnowledge.excluded {a₁}) d₂ =
            CellKnowledge.excluded ∅ := by
          rw [Function.update_of_ne hd, hst₂ hd]
        rw [probEvent_probeStep_bind_fst_eq (f false) hupd (Finset.notMem_empty _)]
        simp only [Finset.card_empty, Nat.sub_zero]
        exact ENNReal.inv_le_inv' (Nat.cast_le.2 (Nat.sub_le _ _))
    · -- `(|R| - 1)` first-miss branches, each charged `|R|⁻¹ · (|R| - 1)⁻¹`, total `≤ |R|⁻¹`.
      rw [Finset.card_erase_of_mem (Finset.mem_univ a₁), Finset.card_univ, nsmul_eq_mul,
        ← mul_assoc, mul_comm ((Fintype.card R - 1 : ℕ) : ℝ≥0∞), mul_assoc]
      exact le_trans (mul_le_mul' le_rfl (ENNReal.mul_inv_le_one _)) (by rw [mul_one])
  · -- The first-hit branch `v = a₁`: probability `|R|⁻¹` of reaching it, event bounded by `1`.
    dsimp only
    refine le_trans (mul_le_mul' le_rfl probEvent_le_one) ?_
    simp

/-- **Adaptive re-target at the same cell (q = 2).** Probe `(d, a₁)`, then probe the *same* cell
with the adaptively chosen target `f b₁`; the probability that some probe replies `true` is at
most `2 / |R|`. This is the decisive gate: after a first miss the re-target fires with conditional
probability `1 / (|R| - 1)`, so a per-step union charge overshoots, while the first-fire telescope
`1/|R| + (1 - 1/|R|) · 1/(|R| - 1) = 2/|R|` is exact (and this bound is tight for
`f false ≠ a₁`). -/
theorem probEvent_probeTwo_retarget_le (st : ProbeState D R) (d : D) (a₁ : R) (f : Bool → R)
    (hst : st d = .excluded ∅) :
    Pr[ (fun b : Bool => b = true) | probeTwo st d d a₁ f ] ≤
      2 / (Fintype.card R : ℝ≥0∞) :=
  probEvent_probeTwo_le st d d a₁ f hst fun h => absurd rfl h

/-- **Adaptive second probe at a distinct cell (q = 2).** Probe `(d₁, a₁)`, then probe a different
cell `d₂ ≠ d₁` at the adaptively chosen target `f b₁`; the probability that some probe replies
`true` is again at most `2 / |R|`. -/
theorem probEvent_probeTwo_distinct_le (st : ProbeState D R) (d₁ d₂ : D) (a₁ : R) (f : Bool → R)
    (hst₁ : st d₁ = .excluded ∅) (hst₂ : st d₂ = .excluded ∅) (_hne : d₂ ≠ d₁) :
    Pr[ (fun b : Bool => b = true) | probeTwo st d₁ d₂ a₁ f ] ≤
      2 / (Fintype.card R : ℝ≥0∞) :=
  probEvent_probeTwo_le st d₁ d₂ a₁ f hst₁ fun _ => hst₂

end OracleComp
