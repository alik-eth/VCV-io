/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.RandomOracle.AdaptiveUnion
import VCVio.OracleComp.QueryTracking.RandomOracle.FirstFire

/-!
# Probe Oracle as a Query Implementation

This file packages the first-fire probe oracle of
`VCVio.OracleComp.QueryTracking.RandomOracle.FirstFire` as a stateful `QueryImpl` over the
two-operation oracle signature `probeSpec D R`, indexed by `ProbeOp D R`:

* a **probe** query `ProbeOp.probe d a` replies with the boolean "does cell `d` hold the value
  `a`?", via `probeStep`;
* a **reveal** query `ProbeOp.reveal d` replies with the value of cell `d`, via `revealStep`:
  at a `known` cell the determined value, and at an undetermined cell a uniform draw from the
  allowed set `Finset.univ \ S` — the conditional law of the cell given the misses recorded so
  far — which is then recorded as `known`.

Reveals model oracle interfaces that hand a cell's value directly to the adversary, while
probes model equality tests; both operations read and update the shared `ProbeState`.

The implementation `probeImpl` threads a `ProbeState D R × Bool` state through
`StateT _ (OptionT ProbComp)`. The boolean component is a *fired* flag: each probe ORs onto it
the genuine-fire indicator (`CellKnowledge.genuine` at the pre-step state, AND-ed with the
reply), so the flag is monotone — once set it is never reset
(`probeImpl_run_support_fired_mono`). Reveal queries leave the flag untouched, so they are
never charged by the first-fire bound.

The main result `probEvent_simulateQ_probeImpl_le` is the `simulateQ`-level first-fire bound:
an adversary `adv : OracleComp (probeSpec D R) α` making at most `q` *probe* queries
(`IsQueryBoundP` at the probe indices; reveal queries are unconstrained), run from a state
whose exclusion sets all have cardinality at most `m` and with the flag unset, terminates with
the flag set with probability at most `q / (|R| - m)`. The proof is a free-monad induction over
the adversary: reveals and non-genuine probes recurse without touching the flag (reveals at an
unchanged budget), and a genuine probe pays the head/tail telescope of
`firstFire_telescope_step` exactly as in `probEvent_probeMany_le`.
`probEvent_simulateQ_probeImpl_init_le` instantiates the bound at the initial state, where it
reads `q / |R|`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp

/-- A single probe-oracle operation over cells `D` with values `R`: either an equality *probe*
of a cell against a target value, or a *reveal* of a cell's value. -/
inductive ProbeOp (D R : Type) where
  /-- Probe cell `d` against the target value `a`; the oracle replies with a boolean. -/
  | probe (d : D) (a : R)
  /-- Reveal the value of cell `d`; the oracle replies with an element of `R`. -/
  | reveal (d : D)

/-- Whether a probe-oracle operation is a probe (as opposed to a reveal). The first-fire bound
counts exactly the operations satisfying this predicate. -/
def ProbeOp.isProbe {D R : Type} : ProbeOp D R → Bool
  | .probe _ _ => true
  | .reveal _ => false

/-- A probe operation is a probe. -/
@[simp]
lemma ProbeOp.isProbe_probe {D R : Type} (d : D) (a : R) :
    (ProbeOp.probe d a).isProbe = true := rfl

/-- A reveal operation is not a probe. -/
@[simp]
lemma ProbeOp.isProbe_reveal {D R : Type} (d : D) :
    (ProbeOp.reveal d : ProbeOp D R).isProbe = false := rfl

/-- Two-operation signature of the probe oracle over cells `D` with values `R`: a probe replies
with the boolean comparison of the cell against the target, and a reveal replies with the value
of the cell. -/
@[reducible]
def probeSpec (D R : Type) : OracleSpec (ProbeOp D R) :=
  fun t => match t with
  | .probe _ _ => Bool
  | .reveal _ => R

variable {D R : Type} [DecidableEq D] [DecidableEq R] [Fintype R]

/-! ## The reveal step -/

/-- Reveal the value of cell `d`: at a `known` cell return the determined value and leave the
state unchanged, and at an undetermined cell draw the value uniformly from the allowed set
`Finset.univ \ S` — the conditional law of the cell given the misses recorded so far — and
record the cell as `known`. -/
noncomputable def revealStep (st : ProbeState D R) (d : D) :
    OptionT ProbComp (R × ProbeState D R) :=
  match st d with
  | .known v => pure (v, st)
  | .excluded S => (fun v => (v, Function.update st d (.known v))) <$> ($ (Finset.univ \ S))

/-- A reveal at a `known` cell returns the determined value and changes nothing. -/
theorem revealStep_known {st : ProbeState D R} {d : D} {v : R} (hst : st d = .known v) :
    revealStep st d = pure (v, st) := by
  rw [revealStep, hst]

/-- A reveal at an undetermined cell draws uniformly from the allowed set and determines the
cell to the drawn value. -/
theorem revealStep_excluded {st : ProbeState D R} {d : D} {S : Finset R}
    (hst : st d = .excluded S) :
    revealStep st d =
      (fun v => (v, Function.update st d (.known v))) <$> ($ (Finset.univ \ S)) := by
  rw [revealStep, hst]

/-! ## The stateful implementation -/

/-- Stateful implementation of `probeSpec D R` over a `ProbeState D R` paired with a monotone
*fired* flag: a probe `(d, a)` runs `probeStep` and ORs onto the flag whether the probe was
genuine (judged by `CellKnowledge.genuine` at the pre-step state) and replied `true`; a reveal
runs `revealStep` and leaves the flag unchanged. -/
noncomputable def probeImpl :
    QueryImpl (probeSpec D R) (StateT (ProbeState D R × Bool) (OptionT ProbComp))
  | .probe d a => fun s =>
      (fun z => (z.1, (z.2, s.2 || ((s.1 d).genuine a && z.1)))) <$> probeStep s.1 d a
  | .reveal d => fun s =>
      (fun z => (z.1, (z.2, s.2))) <$> revealStep s.1 d

/-- A probe query runs `probeStep` on the `ProbeState` component and ORs the genuine-fire
indicator onto the flag. -/
@[simp]
lemma probeImpl_run_probe (d : D) (a : R) (s : ProbeState D R × Bool) :
    (probeImpl (ProbeOp.probe d a)).run s =
      (fun z : Bool × ProbeState D R =>
        (z.1, (z.2, s.2 || ((s.1 d).genuine a && z.1)))) <$> probeStep s.1 d a := rfl

/-- A reveal query runs `revealStep` on the `ProbeState` component and leaves the flag
unchanged. -/
@[simp]
lemma probeImpl_run_reveal (d : D) (s : ProbeState D R × Bool) :
    (probeImpl (ProbeOp.reveal d)).run s =
      (fun z : R × ProbeState D R => (z.1, (z.2, s.2))) <$> revealStep s.1 d := rfl

/-! ## Support-level invariants -/

omit [DecidableEq D] [DecidableEq R] [Fintype R] in
/-- Exclusion-cardinality bounds are monotone in the threshold. -/
lemma ProbeState.ExclLe.mono {st : ProbeState D R} {m m' : ℕ} (hst : st.ExclLe m)
    (hle : m ≤ m') : st.ExclLe m' :=
  fun d S hS => le_trans (hst d S hS) hle

/-- A reveal step preserves any exclusion-cardinality bound: a `known` cell is untouched, and
determining an undetermined cell removes its exclusion set. -/
lemma revealStep_support_exclLe {st : ProbeState D R} {m : ℕ} (hst : st.ExclLe m) (d : D)
    {z : R × ProbeState D R} (hz : z ∈ support (revealStep st d)) :
    z.2.ExclLe m := by
  rcases hcell : st d with v | S
  · rw [revealStep_known hcell, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hst
  · rw [revealStep_excluded hcell, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hst.update_known d u

/-- A probe step grows exclusion cardinalities by at most one: from an `m`-bounded state every
reachable post-step state is `(m + 1)`-bounded. Deterministic replies leave the state
unchanged; a genuine probe either determines the cell or inserts the target into its exclusion
set, which had cardinality at most `m`. -/
lemma probeStep_support_exclLe {st : ProbeState D R} {m : ℕ} (hst : st.ExclLe m) (d : D) (a : R)
    {z : Bool × ProbeState D R} (hz : z ∈ support (probeStep st d a)) :
    z.2.ExclLe (m + 1) := by
  rcases hcell : st d with v | S
  · rw [probeStep_known a hcell, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hst.mono (Nat.le_succ m)
  · by_cases ha : a ∈ S
    · rw [probeStep_excluded_mem a hcell ha, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hst.mono (Nat.le_succ m)
    · rw [probeStep_excluded_notMem a hcell ha, support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      dsimp only
      by_cases hu : u = a
      · rw [if_pos hu]
        exact (hst.update_known d a).mono (Nat.le_succ m)
      · rw [if_neg hu]
        exact (hst.update_insert d a S).mono
          (max_le (Nat.le_succ m) (Nat.succ_le_succ (hst d S hcell)))

/-- The fired flag is monotone through any single `probeImpl` step: once set, neither a probe
nor a reveal can reset it. -/
lemma probeImpl_run_support_fired_mono (t : ProbeOp D R) {s : ProbeState D R × Bool}
    {z : (probeSpec D R).Range t × (ProbeState D R × Bool)}
    (hz : z ∈ support ((probeImpl t).run s)) (hs : s.2 = true) :
    z.2.2 = true := by
  rcases t with ⟨d, a⟩ | d
  · rw [probeImpl_run_probe, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    simp [hs]
  · rw [probeImpl_run_reveal, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hs

/-- A reveal query preserves the exclusion-cardinality bound and leaves the fired flag exactly
as it was. This is the per-step fact consumed by the reveal case of the main bound: reveals are
never charged. -/
lemma probeImpl_run_reveal_support {m : ℕ} (d : D) (s : ProbeState D R × Bool)
    (hs : s.1.ExclLe m)
    {z : R × (ProbeState D R × Bool)}
    (hz : z ∈ support ((probeImpl (ProbeOp.reveal d)).run s)) :
    z.2.1.ExclLe m ∧ z.2.2 = s.2 := by
  rw [probeImpl_run_reveal, support_map] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  exact ⟨revealStep_support_exclLe hs d hu, rfl⟩

/-! ## The simulateQ-level first-fire bound -/

/-- **First-fire bound for the probe-oracle implementation.** An adversary with probe and
reveal access, making at most `q` probe queries (reveal queries are unconstrained), run by
`probeImpl` from a state whose exclusion sets all have cardinality at most `m` and with the
fired flag unset, terminates with the flag set with probability at most `q / (|R| - m)`.

The induction is over the adversary's free-monad structure, generalizing the budget, the
threshold, and the state. A reveal or a non-genuine probe replies without touching the flag and
recurses (reveals at an unchanged budget); a genuine probe at an `excluded S` cell fires with
probability `1 / (|R| - S.card) ≤ 1 / (|R| - m)` — and by monotonicity of the flag the hit
branch needs no further accounting — while each missing draw continues from the grown state,
folded back into the budget by the exact telescope of `firstFire_telescope_step`. -/
theorem probEvent_simulateQ_probeImpl_le {α : Type} (q m : ℕ)
    (adv : OracleComp (probeSpec D R) α) (st : ProbeState D R) (hst : st.ExclLe m)
    (hq : adv.IsQueryBoundP (fun t => t.isProbe = true) q) :
    Pr[ (fun z : α × (ProbeState D R × Bool) => z.2.2 = true) |
        (simulateQ probeImpl adv).run (st, false) ] ≤
      (q : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞) := by
  classical
  induction adv using OracleComp.inductionOn generalizing q m st with
  | pure x => simp [simulateQ_pure]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, StateT.run_bind]
    rcases t with ⟨d, a⟩ | d
    · -- Probe query: one unit of budget is consumed.
      have hq0 : 0 < q := hq.1.resolve_left (by simp)
      have htail : ∀ u, (k u).IsQueryBoundP (fun t => t.isProbe = true) (q - 1) := by
        simpa using hq.2
      rcases hcell : st d with v | S
      · -- `known` cell: deterministic uncharged reply, state and flag unchanged.
        rw [probeImpl_run_probe, probeStep_known a hcell, map_pure, pure_bind]
        simp only [hcell, CellKnowledge.genuine_known, Bool.false_and, Bool.or_false]
        exact le_trans (ih _ (q - 1) m st hst (htail _))
          (ENNReal.div_le_div_right (Nat.cast_le.2 (Nat.sub_le q 1)) _)
      · by_cases ha : a ∈ S
        · -- Already-excluded target: deterministic `false` reply, state and flag unchanged.
          rw [probeImpl_run_probe, probeStep_excluded_mem a hcell ha, map_pure, pure_bind]
          simp only [Bool.and_false, Bool.or_false]
          exact le_trans (ih _ (q - 1) m st hst (htail _))
            (ENNReal.div_le_div_right (Nat.cast_le.2 (Nat.sub_le q 1)) _)
        · -- Genuine probe: expand the uniform draw and split off the hit branch.
          have hk : S.card ≤ m := hst _ _ hcell
          rw [probeImpl_run_probe, probeStep_excluded_notMem a hcell ha, Functor.map_map,
            bind_map_left]
          simp only [hcell, CellKnowledge.genuine_excluded, ha, not_false_eq_true, decide_true,
            Bool.true_and, Bool.false_or]
          rw [probEvent_bind_eq_tsum, tsum_fintype,
            ← Finset.sum_erase_add _ _ (Finset.mem_univ a),
            show (q : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞) =
                ((q - 1 : ℕ) : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞) +
                  1 / ((Fintype.card R - m : ℕ) : ℝ≥0∞) from by
              rw [← ENNReal.add_div]
              congr 1
              exact_mod_cast (Nat.succ_pred_eq_of_pos hq0).symm]
          refine add_le_add ?_ ?_
          · -- Miss branches: each continues from the grown state with the tail budget.
            refine le_trans (Finset.sum_le_sum (g := fun v => Pr[= v | $ (Finset.univ \ S)] *
              (((q - 1 : ℕ) : ℝ≥0∞) /
                ((Fintype.card R - max m (S.card + 1) : ℕ) : ℝ≥0∞)))
              fun v hv => ?_) ?_
            · obtain ⟨hv_ne, -⟩ := Finset.mem_erase.1 hv
              refine mul_le_mul' le_rfl ?_
              rw [decide_eq_false hv_ne, if_neg hv_ne]
              exact ih false (q - 1) _ _ (hst.update_insert d a S) (htail false)
            · -- Survival mass `(|R| - S.card - 1) / (|R| - S.card)` times the tail budget.
              rw [← Finset.sum_mul]
              have hcard : ((Finset.univ.erase a) ∩ (Finset.univ \ S)).card =
                  Fintype.card R - (S.card + 1) := by
                have hset : (Finset.univ.erase a) ∩ (Finset.univ \ S) =
                    Finset.univ \ insert a S := by
                  ext v
                  simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_sdiff,
                    Finset.mem_univ, Finset.mem_insert, true_and, and_true, not_or]
                rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _),
                  Finset.card_univ, Finset.card_insert_of_notMem ha]
              have hPsum : ∑ v ∈ Finset.univ.erase a, Pr[= v | $ (Finset.univ \ S)] =
                  ((Fintype.card R - (S.card + 1) : ℕ) : ℝ≥0∞) *
                    ((Fintype.card R - S.card : ℕ) : ℝ≥0∞)⁻¹ := by
                simp only [ProbComp.probOutput_uniformSelectFinset]
                rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, hcard,
                  Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
              rw [hPsum]
              exact firstFire_telescope_step _ hk
          · -- Hit branch: the flag is set and stays set; charge the reach probability.
            refine le_trans (mul_le_mul' le_rfl probEvent_le_one) ?_
            rw [mul_one, ProbComp.probOutput_uniformSelectFinset,
              if_pos (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ha⟩),
              Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, one_div]
            exact ENNReal.inv_le_inv' (Nat.cast_le.2 (Nat.sub_le_sub_left hk _))
    · -- Reveal query: no charge, the budget is untouched and the flag is preserved.
      have htail : ∀ u, (k u).IsQueryBoundP (fun t => t.isProbe = true) q := by
        simpa using hq.2
      refine probEvent_bind_le_of_forall_le fun x hx => ?_
      obtain ⟨hexcl, hfired⟩ := probeImpl_run_reveal_support d (st, false) hst hx
      have hfired' : x.2.2 = false := hfired
      have hx2 : x.2 = (x.2.1, false) := by rw [← hfired']
      have hbound := ih x.1 q m x.2.1 hexcl (htail x.1)
      rwa [← hx2] at hbound

/-- **First-fire bound from the initial state.** An adversary making at most `q` probe queries
(reveal queries unconstrained), run by `probeImpl` from the initial probe state with the fired
flag unset, terminates with the flag set with probability at most `q / |R|`. -/
theorem probEvent_simulateQ_probeImpl_init_le {α : Type} (q : ℕ)
    (adv : OracleComp (probeSpec D R) α)
    (hq : adv.IsQueryBoundP (fun t => t.isProbe = true) q) :
    Pr[ (fun z : α × (ProbeState D R × Bool) => z.2.2 = true) |
        (simulateQ probeImpl adv).run (ProbeState.init D R, false) ] ≤
      (q : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞) := by
  simpa using probEvent_simulateQ_probeImpl_le q 0 adv (ProbeState.init D R)
    ProbeState.exclLe_init hq

end OracleComp
