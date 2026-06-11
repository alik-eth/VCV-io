/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeOracle
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Deferred Sampling: Probe Oracle Equals Eager Consistent Table

The lazy probe oracle `probeImpl` samples cell values on demand: a genuine probe draws from the
cell's allowed set and retains only the boolean reply. This file proves the *deferred-sampling
equivalence*: running an adversary against `probeImpl` from a knowledge state `K` is
distributionally identical to first drawing a full table `g : D → R` from the *consistent-table
distribution* `genTable K` — every cell independent, uniform on its allowed set — and then
answering all queries deterministically from `g`, threading the same knowledge state through
`eagerProbeImpl g`.

## The consistent-table distribution

`CellKnowledge.allowed` is the set of values a cell may still take: a `known v` cell admits
exactly `v`, an `excluded S` cell admits `Finset.univ \ S`. `genTable K` draws uniformly from
the product set `Fintype.piFinset fun d => (K d).allowed` of all tables consistent with `K`;
since this is a product set, the cells of the drawn table are independent and each is uniform
on its allowed set. The pointwise law `probOutput_genTable` expresses this as a product of the
per-cell weights `CellKnowledge.cellProb`.

The draw fails exactly when some cell has excluded the whole range; `ProbeState.Feasible` rules
this out and holds at `ProbeState.init` (for nonempty `R`). Feasibility is *necessary* for the
equivalence theorem: from an infeasible state `genTable` fails almost surely while `probeImpl`
answers a pure adversary without failing. The probability bounds below avoid the hypothesis,
since against an infeasible state the eager world fires with probability `0`.

## Knowledge splits

The induction engine consists of two redistribution laws for `genTable`, mirroring the two ways
`probeImpl` consumes randomness at an `excluded S` cell:

* `evalDist_genTable_reveal_split`: drawing a consistent table is the same as first drawing the
  value `v` of one undetermined cell uniformly from its allowed set and then drawing a table
  consistent with the cell `known v`.
* `evalDist_genTable_probe_split`: alternatively, draw `v` and remember only the comparison
  with a target `a ∉ S`: on a hit continue with the cell `known a`, on a miss with the cell
  `excluded (insert a S)`. These are exactly the post-states written by `probeStep`, which is
  what makes the per-query case of the equivalence close.

`apply_eq_of_mem_support_genTable` is the corresponding fact for `known` cells: every table in
the support of `genTable K` agrees with each determined cell, so queries there are answered
deterministically on both sides.

## Main results

* `evalDist_genTable_bind_eagerProbeImpl`: the deferred-sampling equivalence, by free-monad
  induction over the adversary with the knowledge state and fired flag generalized.
* `probEvent_genTable_bind_eagerProbeImpl_le`: the first-fire bound `q / (|R| - m)` transferred
  to the eager world (no feasibility hypothesis), with the initial-state form
  `probEvent_genTable_init_bind_eagerProbeImpl_le` reading `q / |R|`.
* `evalDist_genTable_init`: at the initial state the consistent-table distribution is the
  uniform table draw `$ᵗ (D → R)`, connecting to eager full-table sampling;
  `probEvent_uniformSample_bind_eagerProbeImpl_le` restates the initial-state bound for a
  `$ᵗ (D → R)` table draw.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-! ## Allowed values and per-cell weights -/

/-- The set of values a cell with knowledge `c` may still take: a `known v` cell admits exactly
`v`, an `excluded S` cell admits every value outside `S`. -/
def CellKnowledge.allowed : CellKnowledge R → Finset R
  | .known v => {v}
  | .excluded S => Finset.univ \ S

/-- A determined cell admits exactly its value. -/
@[simp]
lemma CellKnowledge.allowed_known (v : R) : (CellKnowledge.known v).allowed = {v} := rfl

/-- An undetermined cell admits every value outside its exclusion set. -/
@[simp]
lemma CellKnowledge.allowed_excluded (S : Finset R) :
    (CellKnowledge.excluded S : CellKnowledge R).allowed = Finset.univ \ S := rfl

/-- The probability weight that a cell with knowledge `c` takes the value `x` under the
consistent-table distribution: uniform on the allowed set `c.allowed`. -/
noncomputable def CellKnowledge.cellProb (c : CellKnowledge R) (x : R) : ℝ≥0∞ :=
  if x ∈ c.allowed then (c.allowed.card : ℝ≥0∞)⁻¹ else 0

lemma CellKnowledge.cellProb_def (c : CellKnowledge R) (x : R) :
    c.cellProb x = if x ∈ c.allowed then (c.allowed.card : ℝ≥0∞)⁻¹ else 0 := rfl

/-- The weight of a determined cell is the indicator of its value. -/
@[simp]
lemma CellKnowledge.cellProb_known (v x : R) :
    (CellKnowledge.known v).cellProb x = if x = v then 1 else 0 := by
  simp [cellProb]

/-- The weight of an undetermined cell is uniform on the complement of its exclusion set. -/
lemma CellKnowledge.cellProb_excluded (S : Finset R) (x : R) :
    (CellKnowledge.excluded S : CellKnowledge R).cellProb x =
      if x ∈ Finset.univ \ S then ((Fintype.card R - S.card : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  rw [cellProb_def, allowed_excluded,
    Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]

/-! ## Feasible probe states -/

/-- A probe state is *feasible* when every cell still admits at least one value, i.e. no
exclusion set covers the whole range. Feasibility is exactly the existence of a consistent
table, hence exactly the event that `genTable` succeeds. It holds at `ProbeState.init` for
nonempty `R` and is preserved by every probe-oracle transition that occurs with nonzero
probability. -/
def ProbeState.Feasible (K : ProbeState D R) : Prop := ∀ d, (K d).allowed.Nonempty

omit [Fintype D] [DecidableEq D] in
/-- The initial probe state is feasible whenever the value range is nonempty. -/
lemma ProbeState.feasible_init [Nonempty R] : (ProbeState.init D R).Feasible := fun _ => by
  simp [ProbeState.init, Finset.univ_nonempty]

omit [Fintype D] in
/-- Overwriting one cell with knowledge that admits a value preserves feasibility. -/
lemma ProbeState.Feasible.update {K : ProbeState D R} (hK : K.Feasible) (d : D)
    {c : CellKnowledge R} (hc : c.allowed.Nonempty) :
    ProbeState.Feasible (Function.update K d c) := by
  intro d'
  rcases eq_or_ne d' d with rfl | hne
  · rwa [Function.update_self]
  · rw [Function.update_of_ne hne]
    exact hK d'

/-! ## The consistent-table distribution -/

/-- The consistent-table distribution for the knowledge state `K`: a uniform draw from the set
of tables `g : D → R` with `g d ∈ (K d).allowed` at every cell. Since the consistent tables
form a product set, this is the same as drawing every cell independently from its allowed set:
`known v` cells are the constant `v`, `excluded S` cells are uniform on `Finset.univ \ S`. The
draw fails exactly when `K` is not `ProbeState.Feasible`. -/
noncomputable def genTable (K : ProbeState D R) : OptionT ProbComp (D → R) :=
  $ (Fintype.piFinset fun d => (K d).allowed)

/-- A feasible state admits a consistent table, so `genTable` never fails. -/
lemma probFailure_genTable {K : ProbeState D R} (hK : K.Feasible) :
    Pr[⊥ | genTable K] = 0 := by
  rw [genTable, ProbComp.probFailure_uniformSelectFinset,
    if_pos (Fintype.piFinset_nonempty.2 hK)]

/-- Every table in the support of `genTable K` takes allowed values at every cell. -/
lemma mem_allowed_of_mem_support_genTable {K : ProbeState D R} {g : D → R}
    (hg : g ∈ support (genTable K)) (d : D) : g d ∈ (K d).allowed := by
  rw [genTable, ProbComp.support_uniformSelectFinset] at hg
  split_ifs at hg with h
  · exact Fintype.mem_piFinset.1 (Finset.mem_coe.1 hg) d
  · exact absurd hg (Set.notMem_empty g)

/-- Every table in the support of `genTable K` agrees with each determined cell. -/
lemma apply_eq_of_mem_support_genTable {K : ProbeState D R} {g : D → R}
    (hg : g ∈ support (genTable K)) {d : D} {v : R} (hcell : K d = .known v) : g d = v := by
  have h := mem_allowed_of_mem_support_genTable hg d
  rw [hcell, CellKnowledge.allowed_known, Finset.mem_singleton] at h
  exact h

/-- Every table in the support of `genTable K` avoids each cell's exclusion set. -/
lemma apply_notMem_of_mem_support_genTable {K : ProbeState D R} {g : D → R}
    (hg : g ∈ support (genTable K)) {d : D} {S : Finset R} (hcell : K d = .excluded S) :
    g d ∉ S := by
  have h := mem_allowed_of_mem_support_genTable hg d
  rw [hcell, CellKnowledge.allowed_excluded, Finset.mem_sdiff] at h
  exact h.2

/-- Inverses of casts of nonzero naturals distribute over finite products in `ℝ≥0∞`. -/
private lemma inv_natCast_prod {ι : Type} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    ((∏ i ∈ s, f i : ℕ) : ℝ≥0∞)⁻¹ = ∏ i ∈ s, ((f i : ℝ≥0∞))⁻¹ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Nat.cast_mul,
      ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.2 (hf a (Finset.mem_cons_self a s))))
        (Or.inl (ENNReal.natCast_ne_top _)),
      ih fun i hi => hf i (Finset.mem_cons_of_mem hi)]

/-- **Pointwise law of the consistent-table distribution.** The probability that `genTable K`
returns `g` is the product over all cells of the per-cell weights: the indicator of the
determined value at a `known` cell, and the uniform weight on the complement of the exclusion
set at an `excluded` cell. The cells of the drawn table are therefore independent, each with
the conditional law recorded by `K`. -/
theorem probOutput_genTable (K : ProbeState D R) (g : D → R) :
    Pr[= g | genTable K] = ∏ d, (K d).cellProb (g d) := by
  rw [genTable, ProbComp.probOutput_uniformSelectFinset]
  by_cases hg : g ∈ Fintype.piFinset fun d => (K d).allowed
  · rw [if_pos hg, Fintype.card_piFinset,
      inv_natCast_prod _ _ fun d _ => Finset.card_ne_zero_of_mem (Fintype.mem_piFinset.1 hg d)]
    exact Finset.prod_congr rfl fun d _ => by
      rw [CellKnowledge.cellProb_def, if_pos (Fintype.mem_piFinset.1 hg d)]
  · rw [if_neg hg]
    rw [Fintype.mem_piFinset] at hg
    obtain ⟨d, hd⟩ := not_forall.1 hg
    exact (Finset.prod_eq_zero (Finset.mem_univ d)
      (by rw [CellKnowledge.cellProb_def, if_neg hd])).symm

/-- The pointwise law after overwriting one cell, with the overwritten cell's weight split off
the product. -/
private lemma probOutput_genTable_update (K : ProbeState D R) (d : D) (c : CellKnowledge R)
    (g : D → R) :
    Pr[= g | genTable (Function.update K d c)] =
      c.cellProb (g d) * ∏ d' ∈ Finset.univ.erase d, (K d').cellProb (g d') := by
  rw [probOutput_genTable, ← Finset.mul_prod_erase _ _ (Finset.mem_univ d),
    Function.update_self]
  exact congrArg _ (Finset.prod_congr rfl fun d' hd' => by
    rw [Function.update_of_ne (Finset.mem_erase.1 hd').1])

/-- The pointwise law with the weight of one distinguished cell split off the product. -/
private lemma probOutput_genTable_erase (K : ProbeState D R) (d : D) (g : D → R) :
    Pr[= g | genTable K] =
      (K d).cellProb (g d) * ∏ d' ∈ Finset.univ.erase d, (K d').cellProb (g d') := by
  rw [probOutput_genTable, ← Finset.mul_prod_erase _ _ (Finset.mem_univ d)]

/-! ## Knowledge-split laws -/

/-- **Reveal split.** Drawing a table consistent with `K`, where cell `d` is undetermined with
exclusion set `S`, is the same as first drawing that cell's value `v` uniformly from its
allowed set and then drawing a table consistent with the cell determined to `v`. This is the
redistribution consumed by the reveal case of the deferred-sampling equivalence. -/
theorem evalDist_genTable_reveal_split {K : ProbeState D R} {d : D} {S : Finset R}
    (hcell : K d = .excluded S) :
    𝒟[genTable K] =
      𝒟[do let v ← $ (Finset.univ \ S)
           genTable (Function.update K d (.known v))] := by
  refine evalDist_ext fun g => ?_
  symm
  rw [probOutput_bind_eq_tsum, tsum_fintype]
  simp only [ProbComp.probOutput_uniformSelectFinset, probOutput_genTable_update,
    CellKnowledge.cellProb_known]
  rw [Finset.sum_eq_single (g d)]
  · rw [if_pos rfl, one_mul, probOutput_genTable_erase K d g, hcell,
      CellKnowledge.cellProb_def, CellKnowledge.allowed_excluded]
  · intro v _ hvne
    rw [if_neg (show ¬g d = v from fun h => hvne h.symm), zero_mul, mul_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- **Probe split.** Drawing a table consistent with `K`, where cell `d` is undetermined with
exclusion set `S`, is the same as drawing that cell's value `v` uniformly from its allowed set
and remembering only its comparison against a target `a ∉ S`: on a hit continue with the cell
determined to `a`, on a miss with the target additionally excluded. The two continuation states
are exactly the post-states of `probeStep`, which is the redistribution consumed by the genuine
probe case of the deferred-sampling equivalence. -/
theorem evalDist_genTable_probe_split {K : ProbeState D R} {d : D} {S : Finset R} {a : R}
    (hcell : K d = .excluded S) (ha : a ∉ S) :
    𝒟[genTable K] =
      𝒟[do let v ← $ (Finset.univ \ S)
           if v = a then genTable (Function.update K d (.known a))
           else genTable (Function.update K d (.excluded (insert a S)))] := by
  have ha' : a ∈ Finset.univ \ S := Finset.mem_sdiff.2 ⟨Finset.mem_univ a, ha⟩
  refine evalDist_ext fun g => ?_
  symm
  rw [probOutput_bind_eq_tsum, tsum_fintype]
  simp only [apply_ite (fun mx : OptionT ProbComp (D → R) => Pr[= g | mx]),
    ProbComp.probOutput_uniformSelectFinset, probOutput_genTable_update, ite_mul, zero_mul]
  rw [probOutput_genTable_erase K d g, hcell]
  set rest : ℝ≥0∞ := ∏ d' ∈ Finset.univ.erase d, (K d').cellProb (g d') with hrest
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.add_sum_erase _ _ ha', if_pos rfl,
    ← Finset.sdiff_insert]
  have hsum : ∑ v ∈ Finset.univ \ insert a S,
      (((Finset.univ \ S).card : ℝ≥0∞)⁻¹ *
        if v = a then (CellKnowledge.known a).cellProb (g d) * rest
        else (CellKnowledge.excluded (insert a S)).cellProb (g d) * rest) =
      ((Finset.univ \ insert a S).card : ℝ≥0∞) *
        (((Finset.univ \ S).card : ℝ≥0∞)⁻¹ *
          ((CellKnowledge.excluded (insert a S)).cellProb (g d) * rest)) := by
    trans ∑ _v ∈ Finset.univ \ insert a S,
        (((Finset.univ \ S).card : ℝ≥0∞)⁻¹ *
          ((CellKnowledge.excluded (insert a S)).cellProb (g d) * rest))
    · refine Finset.sum_congr rfl fun v hv => ?_
      rw [if_neg (show ¬v = a from fun h =>
        (Finset.mem_sdiff.1 hv).2 (h ▸ Finset.mem_insert_self a S))]
    · rw [Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  simp only [CellKnowledge.cellProb_def, CellKnowledge.allowed_excluded,
    CellKnowledge.allowed_known, Finset.mem_singleton, Finset.card_singleton, Nat.cast_one,
    inv_one]
  by_cases hgda : g d = a
  · have hB : g d ∉ Finset.univ \ insert a S := fun h =>
      (Finset.mem_sdiff.1 h).2 (hgda ▸ Finset.mem_insert_self a S)
    rw [if_pos hgda, if_neg hB, if_pos (show g d ∈ Finset.univ \ S by rw [hgda]; exact ha')]
    simp
  · by_cases hgdS : g d ∈ S
    · have hB : g d ∉ Finset.univ \ insert a S := fun h =>
        (Finset.mem_sdiff.1 h).2 (Finset.mem_insert_of_mem hgdS)
      rw [if_neg hgda, if_neg hB, if_neg fun h => (Finset.mem_sdiff.1 h).2 hgdS]
      simp
    · have hB : g d ∈ Finset.univ \ insert a S :=
        Finset.mem_sdiff.2 ⟨Finset.mem_univ _, by simp [hgda, hgdS]⟩
      rw [if_neg hgda, if_pos hB, if_pos (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hgdS⟩),
        zero_mul, mul_zero, zero_add]
      calc ((Finset.univ \ insert a S).card : ℝ≥0∞) *
            (((Finset.univ \ S).card : ℝ≥0∞)⁻¹ *
              (((Finset.univ \ insert a S).card : ℝ≥0∞)⁻¹ * rest))
          = ((Finset.univ \ insert a S).card : ℝ≥0∞) *
              ((Finset.univ \ insert a S).card : ℝ≥0∞)⁻¹ *
              (((Finset.univ \ S).card : ℝ≥0∞)⁻¹ * rest) := by ring
        _ = ((Finset.univ \ S).card : ℝ≥0∞)⁻¹ * rest := by
            rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hB))
              (ENNReal.natCast_ne_top _), one_mul]

/-! ## The eager implementation -/

omit [Fintype D] [Fintype R] in
/-- Knowledge update of a probe `(d, a)` answered from the fixed table `g`: a `known` cell and
an already-excluded target leave the knowledge unchanged; otherwise a hit (`g d = a`)
determines the cell to `a` and a miss inserts `a` into the exclusion set. These are exactly the
post-states of `probeStep`, with the lazy draw replaced by the table value `g d`. -/
def eagerProbeState (g : D → R) (st : ProbeState D R) (d : D) (a : R) : ProbeState D R :=
  match st d with
  | .known _ => st
  | .excluded S =>
    if a ∈ S then st
    else if g d = a then Function.update st d (.known a)
    else Function.update st d (.excluded (insert a S))

omit [Fintype D] [Fintype R] in
/-- A probe at a `known` cell leaves the knowledge unchanged. -/
lemma eagerProbeState_known {g : D → R} {st : ProbeState D R} {d : D} {v : R} (a : R)
    (hcell : st d = .known v) : eagerProbeState g st d a = st := by
  rw [eagerProbeState, hcell]

omit [Fintype D] [Fintype R] in
/-- A probe at an already-excluded target leaves the knowledge unchanged. -/
lemma eagerProbeState_excluded_mem {g : D → R} {st : ProbeState D R} {d : D} {S : Finset R}
    {a : R} (hcell : st d = .excluded S) (ha : a ∈ S) : eagerProbeState g st d a = st := by
  rw [eagerProbeState, hcell]
  exact if_pos ha

omit [Fintype D] [Fintype R] in
/-- A genuine probe that hits determines the cell to the target. -/
lemma eagerProbeState_excluded_hit {g : D → R} {st : ProbeState D R} {d : D} {S : Finset R}
    {a : R} (hcell : st d = .excluded S) (ha : a ∉ S) (hgd : g d = a) :
    eagerProbeState g st d a = Function.update st d (.known a) := by
  rw [eagerProbeState, hcell]
  exact (if_neg ha).trans (if_pos hgd)

omit [Fintype D] [Fintype R] in
/-- A genuine probe that misses excludes the target. -/
lemma eagerProbeState_excluded_miss {g : D → R} {st : ProbeState D R} {d : D} {S : Finset R}
    {a : R} (hcell : st d = .excluded S) (ha : a ∉ S) (hgd : g d ≠ a) :
    eagerProbeState g st d a = Function.update st d (.excluded (insert a S)) := by
  rw [eagerProbeState, hcell]
  exact (if_neg ha).trans (if_neg hgd)

omit [Fintype D] [Fintype R] [DecidableEq R] in
/-- Knowledge update of a reveal at cell `d` answered from the fixed table `g`: a `known` cell
is unchanged, an undetermined cell is determined to the table value `g d`. -/
def eagerRevealState (g : D → R) (st : ProbeState D R) (d : D) : ProbeState D R :=
  match st d with
  | .known _ => st
  | .excluded _ => Function.update st d (.known (g d))

omit [Fintype D] [Fintype R] [DecidableEq R] in
/-- A reveal at a `known` cell leaves the knowledge unchanged. -/
lemma eagerRevealState_known {g : D → R} {st : ProbeState D R} {d : D} {v : R}
    (hcell : st d = .known v) : eagerRevealState g st d = st := by
  rw [eagerRevealState, hcell]

omit [Fintype D] [Fintype R] [DecidableEq R] in
/-- A reveal at an undetermined cell determines it to the table value. -/
lemma eagerRevealState_excluded {g : D → R} {st : ProbeState D R} {d : D} {S : Finset R}
    (hcell : st d = .excluded S) :
    eagerRevealState g st d = Function.update st d (.known (g d)) := by
  rw [eagerRevealState, hcell]

omit [Fintype D] [Fintype R] in
/-- Deterministic implementation of `probeSpec D R` answering every query from the fixed table
`g : D → R`, threading the same `ProbeState D R × Bool` state as `probeImpl`: a probe `(d, a)`
replies with the comparison `g d = a`, updates the knowledge via `eagerProbeState`, and ORs
onto the fired flag the genuine-fire indicator — `CellKnowledge.genuine` judged at the pre-step
state, AND-ed with the reply, exactly as in `probeImpl`; a reveal replies with `g d`, updates
the knowledge via `eagerRevealState`, and leaves the flag unchanged. The monad is `OptionT
ProbComp` only for alignment with `probeImpl`; no sampling or failure occurs. -/
def eagerProbeImpl (g : D → R) :
    QueryImpl (probeSpec D R) (StateT (ProbeState D R × Bool) (OptionT ProbComp))
  | .probe d a => fun s =>
      pure (decide (g d = a),
        (eagerProbeState g s.1 d a, s.2 || ((s.1 d).genuine a && decide (g d = a))))
  | .reveal d => fun s => pure (g d, (eagerRevealState g s.1 d, s.2))

omit [Fintype D] [Fintype R] in
/-- A probe query replies with the table comparison, updates the knowledge, and ORs the
genuine-fire indicator onto the flag. -/
@[simp]
lemma eagerProbeImpl_run_probe (g : D → R) (d : D) (a : R) (s : ProbeState D R × Bool) :
    (eagerProbeImpl g (ProbeOp.probe d a)).run s =
      pure (decide (g d = a),
        (eagerProbeState g s.1 d a, s.2 || ((s.1 d).genuine a && decide (g d = a)))) := rfl

omit [Fintype D] [Fintype R] in
/-- A reveal query replies with the table value, updates the knowledge, and leaves the flag
unchanged. -/
@[simp]
lemma eagerProbeImpl_run_reveal (g : D → R) (d : D) (s : ProbeState D R × Bool) :
    (eagerProbeImpl g (ProbeOp.reveal d)).run s =
      pure (g d, (eagerRevealState g s.1 d, s.2)) := rfl

/-! ## The deferred-sampling equivalence -/

universe u v

/-- Congruence for `evalDist` under `bind`: continuations that agree in distribution on the
support of the first computation yield equal bind distributions. -/
private lemma evalDist_bind_congr {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    {α β : Type u} {mx : m α} {f f' : α → m β}
    (h : ∀ x ∈ support mx, 𝒟[f x] = 𝒟[f' x]) : 𝒟[mx >>= f] = 𝒟[mx >>= f'] :=
  evalDist_ext fun y => probOutput_bind_congr fun x hx => by
    rw [probOutput_def, probOutput_def, h x hx]

/-- **Deferred-sampling equivalence.** For every adversary with probe and reveal access, every
feasible knowledge state `K`, and every initial flag `b`: drawing a consistent table from
`genTable K` and answering all queries deterministically from it via `eagerProbeImpl` has the
same output distribution (including the final knowledge state and fired flag) as the lazily
sampling `probeImpl`.

The proof is a free-monad induction over the adversary, generalizing the state and the flag.
Queries with deterministic answers (`known` cells, already-excluded targets, and reveals of
determined cells) are answered identically on both sides since every supported table agrees
with the determined knowledge; queries that consume randomness are matched by redistributing
the table draw via `evalDist_genTable_reveal_split` / `evalDist_genTable_probe_split`, whose
per-branch leftover tables are distributed as `genTable` of exactly the state the eager
implementation writes.

Feasibility is necessary: from an infeasible state the left side fails almost surely while the
right side answers a query-free adversary without failing. -/
theorem evalDist_genTable_bind_eagerProbeImpl {α : Type}
    (adv : OracleComp (probeSpec D R) α) (K : ProbeState D R) (b : Bool) (hK : K.Feasible) :
    𝒟[do let g ← genTable K
         (simulateQ (eagerProbeImpl g) adv).run (K, b)] =
      𝒟[(simulateQ probeImpl adv).run (K, b)] := by
  classical
  induction adv using OracleComp.inductionOn generalizing K b with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    refine evalDist_ext fun z => ?_
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
      tsum_probOutput_eq_one' (probFailure_genTable hK), one_mul]
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, StateT.run_bind]
    rcases t with ⟨d, a⟩ | d
    · -- Probe query.
      simp only [fun g => eagerProbeImpl_run_probe g d a (K, b), pure_bind]
      rcases hcell : K d with v | S
      · -- `known` cell: both sides reply with the deterministic comparison.
        rw [probeImpl_run_probe, probeStep_known a hcell, map_pure, pure_bind]
        simp only [hcell, CellKnowledge.genuine_known, Bool.false_and, Bool.or_false,
          eagerProbeState_known a hcell]
        refine (evalDist_bind_congr fun g hg => ?_).trans (ih (decide (v = a)) K b hK)
        rw [apply_eq_of_mem_support_genTable hg hcell]
        rfl
      · by_cases ha : a ∈ S
        · -- Already-excluded target: both sides reply `false` and change nothing.
          rw [probeImpl_run_probe, probeStep_excluded_mem a hcell ha, map_pure, pure_bind]
          simp only [Bool.and_false, Bool.or_false]
          refine (evalDist_bind_congr fun g hg => ?_).trans (ih false K b hK)
          have hne : g d ≠ a := fun h =>
            apply_notMem_of_mem_support_genTable hg hcell (h ▸ ha)
          rw [decide_eq_false hne, eagerProbeState_excluded_mem hcell ha]
          simp only [Bool.and_false, Bool.or_false]
          rfl
        · -- Genuine probe: redistribute the table draw along the probe split.
          rw [probeImpl_run_probe, probeStep_excluded_notMem a hcell ha, Functor.map_map,
            bind_map_left]
          simp only [hcell, CellKnowledge.genuine_excluded, ha, not_false_eq_true,
            decide_true, Bool.true_and]
          conv_lhs => rw [evalDist_bind, evalDist_genTable_probe_split hcell ha,
            ← evalDist_bind, bind_assoc]
          refine evalDist_bind_congr fun u hu => ?_
          have hu' : u ∈ Finset.univ \ S := by
            rwa [ProbComp.support_uniformSelectFinset,
              if_pos ⟨a, Finset.mem_sdiff.2 ⟨Finset.mem_univ a, ha⟩⟩, Finset.mem_coe] at hu
          by_cases hua : u = a
          · -- Hit branch: the leftover table is consistent with the cell `known a`.
            subst hua
            simp only [if_true, decide_true]
            refine (evalDist_bind_congr fun g hg => ?_).trans
              (ih true (Function.update K d (.known u)) (b || true)
                (hK.update d (Finset.singleton_nonempty u)))
            have hgd : g d = u := by
              have h := mem_allowed_of_mem_support_genTable hg d
              rwa [Function.update_self, CellKnowledge.allowed_known,
                Finset.mem_singleton] at h
            rw [eagerProbeState_excluded_hit hcell ha hgd, hgd]
            simp only [decide_true]
            rfl
          · -- Miss branch: the leftover table is consistent with the grown exclusion set.
            have huB : u ∈ Finset.univ \ insert a S :=
              Finset.mem_sdiff.2 ⟨Finset.mem_univ u,
                by simp [hua, (Finset.mem_sdiff.1 hu').2]⟩
            rw [if_neg hua, if_neg hua, decide_eq_false hua]
            simp only [Bool.or_false]
            refine (evalDist_bind_congr fun g hg => ?_).trans
              (ih false (Function.update K d (.excluded (insert a S))) b
                (hK.update d ⟨u, huB⟩))
            have hgd : g d ∈ Finset.univ \ insert a S := by
              have h := mem_allowed_of_mem_support_genTable hg d
              rwa [Function.update_self, CellKnowledge.allowed_excluded] at h
            have hgdne : g d ≠ a := fun h =>
              (Finset.mem_sdiff.1 hgd).2 (h ▸ Finset.mem_insert_self a S)
            rw [decide_eq_false hgdne, eagerProbeState_excluded_miss hcell ha hgdne]
            simp only [Bool.or_false]
            rfl
    · -- Reveal query.
      simp only [fun g => eagerProbeImpl_run_reveal g d (K, b), pure_bind]
      rcases hcell : K d with v | S
      · -- `known` cell: both sides reply with the determined value.
        rw [probeImpl_run_reveal, revealStep_known hcell, map_pure, pure_bind]
        simp only [eagerRevealState_known hcell]
        refine (evalDist_bind_congr fun g hg => ?_).trans (ih v K b hK)
        rw [apply_eq_of_mem_support_genTable hg hcell]
        rfl
      · -- Undetermined cell: redistribute the table draw along the reveal split.
        rw [probeImpl_run_reveal, revealStep_excluded hcell, Functor.map_map, bind_map_left]
        conv_lhs => rw [evalDist_bind, evalDist_genTable_reveal_split hcell,
          ← evalDist_bind, bind_assoc]
        refine evalDist_bind_congr fun u _ => ?_
        refine (evalDist_bind_congr fun g hg => ?_).trans
          (ih u (Function.update K d (.known u)) b
            (hK.update d (Finset.singleton_nonempty u)))
        have hgd : g d = u := by
          have h := mem_allowed_of_mem_support_genTable hg d
          rwa [Function.update_self, CellKnowledge.allowed_known, Finset.mem_singleton] at h
        rw [eagerRevealState_excluded hcell, hgd]
        rfl

/-! ## Consumer-facing corollaries -/

/-- **First-fire bound in the eager world.** An adversary making at most `q` probe queries
(reveal queries unconstrained), answered from a table drawn consistent with a state whose
exclusion sets all have cardinality at most `m` and starting with the flag unset, terminates
with the flag set with probability at most `q / (|R| - m)`. No feasibility hypothesis is
needed: against an infeasible state the table draw fails and the event has probability `0`. -/
theorem probEvent_genTable_bind_eagerProbeImpl_le {α : Type} (q m : ℕ)
    (adv : OracleComp (probeSpec D R) α) (st : ProbeState D R) (hst : st.ExclLe m)
    (hq : adv.IsQueryBoundP (fun t => t.isProbe = true) q) :
    Pr[ (fun z : α × (ProbeState D R × Bool) => z.2.2 = true) |
        do let g ← genTable st
           (simulateQ (eagerProbeImpl g) adv).run (st, false) ] ≤
      (q : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞) := by
  by_cases hfeas : st.Feasible
  · rw [probEvent_def, evalDist_genTable_bind_eagerProbeImpl adv st false hfeas,
      ← probEvent_def]
    exact probEvent_simulateQ_probeImpl_le q m adv st hst hq
  · have hzero : ∀ g : D → R, Pr[= g | genTable st] = 0 := by
      intro g
      refine probOutput_eq_zero_of_not_mem_support fun hg => hfeas fun d => ?_
      exact ⟨g d, mem_allowed_of_mem_support_genTable hg d⟩
    rw [probEvent_bind_eq_tsum]
    simp only [hzero, zero_mul, tsum_zero]
    exact bot_le

/-- **First-fire bound in the eager world, from the initial state.** An adversary making at
most `q` probe queries, answered from a table drawn consistent with the initial state (i.e.
uniformly, see `evalDist_genTable_init`), terminates with the flag set with probability at most
`q / |R|`. -/
theorem probEvent_genTable_init_bind_eagerProbeImpl_le {α : Type} (q : ℕ)
    (adv : OracleComp (probeSpec D R) α)
    (hq : adv.IsQueryBoundP (fun t => t.isProbe = true) q) :
    Pr[ (fun z : α × (ProbeState D R × Bool) => z.2.2 = true) |
        do let g ← genTable (ProbeState.init D R)
           (simulateQ (eagerProbeImpl g) adv).run (ProbeState.init D R, false) ] ≤
      (q : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞) := by
  simpa using probEvent_genTable_bind_eagerProbeImpl_le q 0 adv (ProbeState.init D R)
    ProbeState.exclLe_init hq

/-- At the initial probe state every value is allowed at every cell, so the consistent-table
distribution is the uniform draw over all tables `D → R`. -/
theorem evalDist_genTable_init [SampleableType (D → R)] :
    𝒟[genTable (ProbeState.init D R)] = 𝒟[$ᵗ (D → R)] := by
  refine evalDist_ext fun g => ?_
  have hpi : (Fintype.piFinset fun d : D => ((ProbeState.init D R) d).allowed) =
      Finset.univ := by
    simp [ProbeState.init]
  rw [genTable, hpi, ProbComp.probOutput_uniformSelectFinset, if_pos (Finset.mem_univ g),
    Finset.card_univ, probOutput_uniformSample]

omit [Fintype D] in
/-- **First-fire bound for a uniform table draw.** The initial-state eager bound restated for a
table drawn uniformly via `$ᵗ (D → R)`, the form matching eager full-table sampling. -/
theorem probEvent_uniformSample_bind_eagerProbeImpl_le {α : Type} [Finite D]
    [SampleableType (D → R)]
    (q : ℕ) (adv : OracleComp (probeSpec D R) α)
    (hq : adv.IsQueryBoundP (fun t => t.isProbe = true) q) :
    Pr[ (fun z : α × (ProbeState D R × Bool) => z.2.2 = true) |
        (liftM ($ᵗ (D → R)) : OptionT ProbComp (D → R)) >>= fun g =>
           (simulateQ (eagerProbeImpl g) adv).run (ProbeState.init D R, false) ] ≤
      (q : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞) := by
  letI := Fintype.ofFinite D
  refine le_trans (le_of_eq ?_) (probEvent_genTable_init_bind_eagerProbeImpl_le q adv hq)
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun g => ?_
  rw [OptionT.probOutput_liftM, probOutput_def, probOutput_def, ← evalDist_genTable_init]

end OracleComp
