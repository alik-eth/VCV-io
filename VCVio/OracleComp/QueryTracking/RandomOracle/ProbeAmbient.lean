/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEquiv

/-!
# Probe Oracle With An Ambient Oracle

This file generalizes the first-fire probe oracle of
`VCVio.OracleComp.QueryTracking.RandomOracle.ProbeOracle` and the deferred-sampling equivalence
of `VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEquiv` to adversaries that interleave
probe/reveal operations with queries to an arbitrary *ambient* oracle `spec`, answered by a
fixed implementation `im : QueryImpl spec ProbComp`. The combined signature is the sum
`spec + probeSpec D R`, with left queries answered by `im` (lifted into the state monad, with
the probe state and fired flag untouched) and right queries answered exactly as before:

* `probeImplWith im` extends `probeImpl` — right queries sample lazily via
  `probeStep` / `revealStep`;
* `eagerProbeImplWith im g` extends `eagerProbeImpl g` — right queries are answered
  deterministically from the fixed table `g : D → R`.

Ambient queries carry no information about the probed cells (their replies are independent of
the table), so both the first-fire bound and the lazy/eager equivalence extend verbatim:

* `probEvent_simulateQ_probeImplWith_le`: an adversary making at most `q` probe queries
  (ambient and reveal queries unconstrained), run by `probeImplWith im` from a state whose
  exclusion sets have cardinality at most `m`, fires with probability at most `q / (|R| - m)`.
* `evalDist_genTable_bind_eagerProbeImplWith`: from a feasible knowledge state, drawing a
  consistent table and answering eagerly is distributionally identical to lazy sampling, with
  ambient queries commuted past the table draw (they are independent of it).
* `probEvent_genTable_bind_eagerProbeImplWith_le` and
  `probEvent_uniformSample_bind_eagerProbeImplWith_le`: the first-fire bound transferred to the
  eager world, including the uniform-table form `q / |R|`.

## Bridging query caches to knowledge states

A consumer that has already fixed some cells of the table through a `QueryCache c` (e.g. the
lazy random oracle's cache) can enter the eager probe world directly:
`knowledgeOfCache c` is the probe state that records each cached cell as `known` and leaves
every other cell undetermined with empty exclusion set, and the bridge
`evalDist_map_tableExtending_uniformSample` identifies the law of `tableExtending c g` for a
uniform `g` with the consistent-table distribution `genTable (knowledgeOfCache c)`. The
combined entry point `probEvent_uniformSample_tableExtending_bind_eagerProbeImplWith_le` then
bounds the firing probability of an eager run over `tableExtending c g` started at
`knowledgeOfCache c` by `q / |R|`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp

universe u v

variable {ι : Type} {spec : OracleSpec ι} {D R : Type}
  [DecidableEq D] [DecidableEq R] [Fintype R]

/-! ## The combined implementations -/

/-- Stateful implementation of the combined signature `spec + probeSpec D R` over a
`ProbeState D R` paired with the fired flag: a left (ambient) query is answered by `im`, lifted
into the state monad with both the probe state and the flag untouched; a right (probe-oracle)
query is answered exactly as in `probeImpl` — probes run `probeStep` and OR the genuine-fire
indicator onto the flag, reveals run `revealStep` and leave the flag unchanged. -/
noncomputable def probeImplWith (im : QueryImpl spec ProbComp) :
    QueryImpl (spec + probeSpec D R) (StateT (ProbeState D R × Bool) (OptionT ProbComp))
  | .inl t => fun s => (fun u => (u, s)) <$> liftM (im t)
  | .inr (.probe d a) => fun s =>
      (fun z : Bool × ProbeState D R =>
        (z.1, (z.2, s.2 || ((s.1 d).genuine a && z.1)))) <$> probeStep s.1 d a
  | .inr (.reveal d) => fun s =>
      (fun z : R × ProbeState D R => (z.1, (z.2, s.2))) <$> revealStep s.1 d

/-- An ambient query is answered by `im`, with the probe state and fired flag untouched. -/
@[simp]
lemma probeImplWith_run_inl (im : QueryImpl spec ProbComp) (t : ι)
    (s : ProbeState D R × Bool) :
    (probeImplWith (D := D) (R := R) im (Sum.inl t)).run s =
      (fun u : (spec + probeSpec D R).Range (Sum.inl t) => (u, s)) <$> liftM (im t) := rfl

/-- A probe query runs `probeStep` on the `ProbeState` component and ORs the genuine-fire
indicator onto the flag, exactly as in `probeImpl`. -/
@[simp]
lemma probeImplWith_run_probe (im : QueryImpl spec ProbComp) (d : D) (a : R)
    (s : ProbeState D R × Bool) :
    (probeImplWith im (Sum.inr (ProbeOp.probe d a))).run s =
      (fun z : Bool × ProbeState D R =>
        ((z.1, (z.2, s.2 || ((s.1 d).genuine a && z.1))) :
          (spec + probeSpec D R).Range (Sum.inr (ProbeOp.probe d a)) ×
            (ProbeState D R × Bool))) <$> probeStep s.1 d a := rfl

/-- A reveal query runs `revealStep` on the `ProbeState` component and leaves the flag
unchanged, exactly as in `probeImpl`. -/
@[simp]
lemma probeImplWith_run_reveal (im : QueryImpl spec ProbComp) (d : D)
    (s : ProbeState D R × Bool) :
    (probeImplWith im (Sum.inr (ProbeOp.reveal d))).run s =
      (fun z : R × ProbeState D R =>
        ((z.1, (z.2, s.2)) :
          (spec + probeSpec D R).Range (Sum.inr (ProbeOp.reveal d)) ×
            (ProbeState D R × Bool))) <$> revealStep s.1 d := rfl

omit [Fintype R] in
/-- Deterministic-table implementation of the combined signature `spec + probeSpec D R`: a left
(ambient) query is answered by `im`, lifted into the state monad with both the probe state and
the fired flag untouched; a right (probe-oracle) query is answered exactly as in
`eagerProbeImpl g` — from the fixed table `g : D → R`, updating the knowledge state and ORing
the genuine-fire indicator onto the flag at probes. -/
def eagerProbeImplWith (im : QueryImpl spec ProbComp) (g : D → R) :
    QueryImpl (spec + probeSpec D R) (StateT (ProbeState D R × Bool) (OptionT ProbComp))
  | .inl t => fun s => (fun u => (u, s)) <$> liftM (im t)
  | .inr (.probe d a) => fun s =>
      pure (decide (g d = a),
        (eagerProbeState g s.1 d a, s.2 || ((s.1 d).genuine a && decide (g d = a))))
  | .inr (.reveal d) => fun s => pure (g d, (eagerRevealState g s.1 d, s.2))

omit [Fintype R] in
/-- An ambient query is answered by `im`, with the probe state and fired flag untouched. -/
@[simp]
lemma eagerProbeImplWith_run_inl (im : QueryImpl spec ProbComp) (g : D → R) (t : ι)
    (s : ProbeState D R × Bool) :
    (eagerProbeImplWith (D := D) (R := R) im g (Sum.inl t)).run s =
      (fun u : (spec + probeSpec D R).Range (Sum.inl t) => (u, s)) <$> liftM (im t) := rfl

omit [Fintype R] in
/-- A probe query replies with the table comparison, updates the knowledge, and ORs the
genuine-fire indicator onto the flag, exactly as in `eagerProbeImpl`. -/
@[simp]
lemma eagerProbeImplWith_run_probe (im : QueryImpl spec ProbComp) (g : D → R) (d : D) (a : R)
    (s : ProbeState D R × Bool) :
    (eagerProbeImplWith im g (Sum.inr (ProbeOp.probe d a))).run s =
      pure ((decide (g d = a),
          (eagerProbeState g s.1 d a, s.2 || ((s.1 d).genuine a && decide (g d = a)))) :
        (spec + probeSpec D R).Range (Sum.inr (ProbeOp.probe d a)) ×
          (ProbeState D R × Bool)) := rfl

omit [Fintype R] in
/-- A reveal query replies with the table value, updates the knowledge, and leaves the flag
unchanged, exactly as in `eagerProbeImpl`. -/
@[simp]
lemma eagerProbeImplWith_run_reveal (im : QueryImpl spec ProbComp) (g : D → R) (d : D)
    (s : ProbeState D R × Bool) :
    (eagerProbeImplWith im g (Sum.inr (ProbeOp.reveal d))).run s =
      pure (((g d, (eagerRevealState g s.1 d, s.2))) :
        (spec + probeSpec D R).Range (Sum.inr (ProbeOp.reveal d)) ×
          (ProbeState D R × Bool)) := rfl

/-! ## The first-fire bound with ambient queries -/

/-- **First-fire bound with ambient queries.** An adversary with ambient, probe, and reveal
access, making at most `q` probe queries (ambient and reveal queries are unconstrained), run by
`probeImplWith im` from a state whose exclusion sets all have cardinality at most `m` and with
the fired flag unset, terminates with the flag set with probability at most `q / (|R| - m)`.

The induction extends `probEvent_simulateQ_probeImpl_le` with one extra case: an ambient query
replies from `im` without touching the probe state, the flag, or the budget, so each reply
recurses at the unchanged `(st, m, q)`. -/
theorem probEvent_simulateQ_probeImplWith_le {α : Type} (q m : ℕ)
    (im : QueryImpl spec ProbComp) (adv : OracleComp (spec + probeSpec D R) α)
    (st : ProbeState D R) (hst : st.ExclLe m)
    (hq : adv.IsQueryBoundP (fun i => Sum.elim (fun _ => false) ProbeOp.isProbe i = true) q) :
    Pr[ (fun z : α × (ProbeState D R × Bool) => z.2.2 = true) |
        (simulateQ (probeImplWith im) adv).run (st, false) ] ≤
      (q : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞) := by
  classical
  induction adv using OracleComp.inductionOn generalizing q m st with
  | pure x => simp [simulateQ_pure]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, StateT.run_bind]
    rcases t with t | (⟨d, a⟩ | d)
    · -- Ambient query: no charge, the state and flag are untouched.
      have htail : ∀ u, (k u).IsQueryBoundP
          (fun i => Sum.elim (fun _ => false) ProbeOp.isProbe i = true) q := by
        simpa using hq.2
      refine probEvent_bind_le_of_forall_le fun x hx => ?_
      rw [probeImplWith_run_inl, support_map] at hx
      obtain ⟨u, -, rfl⟩ := hx
      exact ih u q m st hst (htail u)
    · -- Probe query: one unit of budget is consumed.
      have hq0 : 0 < q := hq.1.resolve_left (by simp)
      have htail : ∀ u, (k u).IsQueryBoundP
          (fun i => Sum.elim (fun _ => false) ProbeOp.isProbe i = true) (q - 1) := by
        simpa using hq.2
      rcases hcell : st d with v | S
      · -- `known` cell: deterministic uncharged reply, state and flag unchanged.
        rw [probeImplWith_run_probe, probeStep_known a hcell, map_pure, pure_bind]
        simp only [hcell, CellKnowledge.genuine_known, Bool.false_and, Bool.or_false]
        exact le_trans (ih _ (q - 1) m st hst (htail _))
          (ENNReal.div_le_div_right (Nat.cast_le.2 (Nat.sub_le q 1)) _)
      · by_cases ha : a ∈ S
        · -- Already-excluded target: deterministic `false` reply, state and flag unchanged.
          rw [probeImplWith_run_probe, probeStep_excluded_mem a hcell ha, map_pure, pure_bind]
          simp only [Bool.and_false, Bool.or_false]
          exact le_trans (ih _ (q - 1) m st hst (htail _))
            (ENNReal.div_le_div_right (Nat.cast_le.2 (Nat.sub_le q 1)) _)
        · -- Genuine probe: expand the uniform draw and split off the hit branch.
          have hk : S.card ≤ m := hst _ _ hcell
          rw [probeImplWith_run_probe, probeStep_excluded_notMem a hcell ha,
            Functor.map_map, bind_map_left]
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
      have htail : ∀ u, (k u).IsQueryBoundP
          (fun i => Sum.elim (fun _ => false) ProbeOp.isProbe i = true) q := by
        simpa using hq.2
      refine probEvent_bind_le_of_forall_le fun x hx => ?_
      rw [probeImplWith_run_reveal, support_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      exact ih u.1 q m u.2 (revealStep_support_exclLe hst d hu) (htail u.1)

/-! ## The deferred-sampling equivalence with ambient queries -/

/-- Congruence for `evalDist` under `bind`: continuations that agree in distribution on the
support of the first computation yield equal bind distributions. -/
private lemma evalDist_bind_congr {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α β : Type u} {mx : m α} {f f' : α → m β}
    (h : ∀ x ∈ support mx, 𝒟[f x] = 𝒟[f' x]) : 𝒟[mx >>= f] = 𝒟[mx >>= f'] :=
  evalDist_ext fun y => probOutput_bind_congr fun x hx => by
    rw [probOutput_def, probOutput_def, h x hx]

/-- Two draws may be taken in either order: the output distribution of drawing `mx` then `my`
and combining is the same as drawing `my` then `mx`. Proven at the distribution level by `tsum`
rearrangement; the underlying monad need not be commutative as terms. -/
private lemma evalDist_bind_bind_comm {m : Type → Type v} [Monad m] [HasEvalSPMF m]
    {α₁ α₂ β : Type} (mx : m α₁) (my : m α₂) (F : α₁ → α₂ → m β) :
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

variable [Fintype D]

/-- **Deferred-sampling equivalence with ambient queries.** For every adversary with ambient,
probe, and reveal access, every feasible knowledge state `K`, and every initial flag `b`:
drawing a consistent table from `genTable K` and answering all probe-oracle queries
deterministically from it via `eagerProbeImplWith im` has the same output distribution
(including the final knowledge state and fired flag) as the lazily sampling `probeImplWith im`.

The induction extends `evalDist_genTable_bind_eagerProbeImpl` with one extra case: an ambient
query's reply from `im` is independent of the table draw, so the draw commutes past it and each
reply recurses at the unchanged knowledge state and flag.

Feasibility is necessary: from an infeasible state the left side fails almost surely while the
right side answers a query-free adversary without failing. -/
theorem evalDist_genTable_bind_eagerProbeImplWith {α : Type}
    (im : QueryImpl spec ProbComp) (adv : OracleComp (spec + probeSpec D R) α)
    (K : ProbeState D R) (b : Bool) (hK : K.Feasible) :
    𝒟[do let g ← genTable K
         (simulateQ (eagerProbeImplWith im g) adv).run (K, b)] =
      𝒟[(simulateQ (probeImplWith im) adv).run (K, b)] := by
  classical
  induction adv using OracleComp.inductionOn generalizing K b with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    refine evalDist_ext fun z => ?_
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
      tsum_probOutput_eq_one' (probFailure_genTable hK), one_mul]
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, StateT.run_bind]
    rcases t with t | (⟨d, a⟩ | d)
    · -- Ambient query: commute the table draw past the reply, then recurse per reply.
      simp only [eagerProbeImplWith_run_inl, probeImplWith_run_inl, bind_map_left]
      rw [evalDist_bind_bind_comm, evalDist_bind, evalDist_bind]
      exact congrArg _ (funext fun u => ih u K b hK)
    · -- Probe query.
      simp only [eagerProbeImplWith_run_probe, pure_bind]
      rcases hcell : K d with v | S
      · -- `known` cell: both sides reply with the deterministic comparison.
        rw [probeImplWith_run_probe, probeStep_known a hcell, map_pure, pure_bind]
        simp only [hcell, CellKnowledge.genuine_known, Bool.false_and, Bool.or_false,
          eagerProbeState_known a hcell]
        refine (evalDist_bind_congr fun g hg => ?_).trans (ih (decide (v = a)) K b hK)
        rw [apply_eq_of_mem_support_genTable hg hcell]
        rfl
      · by_cases ha : a ∈ S
        · -- Already-excluded target: both sides reply `false` and change nothing.
          rw [probeImplWith_run_probe, probeStep_excluded_mem a hcell ha, map_pure, pure_bind]
          simp only [Bool.and_false, Bool.or_false]
          refine (evalDist_bind_congr fun g hg => ?_).trans (ih false K b hK)
          have hne : g d ≠ a := fun h =>
            apply_notMem_of_mem_support_genTable hg hcell (h ▸ ha)
          rw [decide_eq_false hne, eagerProbeState_excluded_mem hcell ha]
          simp only [Bool.and_false, Bool.or_false]
          rfl
        · -- Genuine probe: redistribute the table draw along the probe split.
          rw [probeImplWith_run_probe, probeStep_excluded_notMem a hcell ha,
            Functor.map_map, bind_map_left]
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
      simp only [eagerProbeImplWith_run_reveal, pure_bind]
      rcases hcell : K d with v | S
      · -- `known` cell: both sides reply with the determined value.
        rw [probeImplWith_run_reveal, revealStep_known hcell, map_pure, pure_bind]
        simp only [eagerRevealState_known hcell]
        refine (evalDist_bind_congr fun g hg => ?_).trans (ih v K b hK)
        rw [apply_eq_of_mem_support_genTable hg hcell]
        rfl
      · -- Undetermined cell: redistribute the table draw along the reveal split.
        rw [probeImplWith_run_reveal, revealStep_excluded hcell,
          Functor.map_map, bind_map_left]
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

/-- **First-fire bound in the eager world, with ambient queries.** An adversary making at most
`q` probe queries (ambient and reveal queries unconstrained), answered from a table drawn
consistent with a state whose exclusion sets all have cardinality at most `m` and starting with
the flag unset, terminates with the flag set with probability at most `q / (|R| - m)`. No
feasibility hypothesis is needed: against an infeasible state the table draw fails and the
event has probability `0`. -/
theorem probEvent_genTable_bind_eagerProbeImplWith_le {α : Type} (q m : ℕ)
    (im : QueryImpl spec ProbComp) (adv : OracleComp (spec + probeSpec D R) α)
    (st : ProbeState D R) (hst : st.ExclLe m)
    (hq : adv.IsQueryBoundP (fun i => Sum.elim (fun _ => false) ProbeOp.isProbe i = true) q) :
    Pr[ (fun z : α × (ProbeState D R × Bool) => z.2.2 = true) |
        do let g ← genTable st
           (simulateQ (eagerProbeImplWith im g) adv).run (st, false) ] ≤
      (q : ℝ≥0∞) / ((Fintype.card R - m : ℕ) : ℝ≥0∞) := by
  by_cases hfeas : st.Feasible
  · rw [probEvent_def, evalDist_genTable_bind_eagerProbeImplWith im adv st false hfeas,
      ← probEvent_def]
    exact probEvent_simulateQ_probeImplWith_le q m im adv st hst hq
  · have hzero : ∀ g : D → R, Pr[= g | genTable st] = 0 := by
      intro g
      refine probOutput_eq_zero_of_not_mem_support fun hg => hfeas fun d => ?_
      exact ⟨g d, mem_allowed_of_mem_support_genTable hg d⟩
    rw [probEvent_bind_eq_tsum]
    simp only [hzero, zero_mul, tsum_zero]
    exact bot_le

/-- **First-fire bound in the eager world with ambient queries, from the initial state.** An
adversary making at most `q` probe queries, answered from a table drawn consistent with the
initial state, terminates with the flag set with probability at most `q / |R|`. -/
theorem probEvent_genTable_init_bind_eagerProbeImplWith_le {α : Type} (q : ℕ)
    (im : QueryImpl spec ProbComp) (adv : OracleComp (spec + probeSpec D R) α)
    (hq : adv.IsQueryBoundP (fun i => Sum.elim (fun _ => false) ProbeOp.isProbe i = true) q) :
    Pr[ (fun z : α × (ProbeState D R × Bool) => z.2.2 = true) |
        do let g ← genTable (ProbeState.init D R)
           (simulateQ (eagerProbeImplWith im g) adv).run (ProbeState.init D R, false) ] ≤
      (q : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞) := by
  simpa using probEvent_genTable_bind_eagerProbeImplWith_le q 0 im adv (ProbeState.init D R)
    ProbeState.exclLe_init hq

omit [Fintype D] in
/-- **First-fire bound for a uniform table draw, with ambient queries.** The initial-state
eager bound restated for a table drawn uniformly via `$ᵗ (D → R)`, the form matching eager
full-table sampling. -/
theorem probEvent_uniformSample_bind_eagerProbeImplWith_le {α : Type} [Finite D]
    [SampleableType (D → R)] (q : ℕ) (im : QueryImpl spec ProbComp)
    (adv : OracleComp (spec + probeSpec D R) α)
    (hq : adv.IsQueryBoundP (fun i => Sum.elim (fun _ => false) ProbeOp.isProbe i = true) q) :
    Pr[ (fun z : α × (ProbeState D R × Bool) => z.2.2 = true) |
        (liftM ($ᵗ (D → R)) : OptionT ProbComp (D → R)) >>= fun g =>
           (simulateQ (eagerProbeImplWith im g) adv).run (ProbeState.init D R, false) ] ≤
      (q : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞) := by
  letI := Fintype.ofFinite D
  refine le_trans (le_of_eq ?_) (probEvent_genTable_init_bind_eagerProbeImplWith_le q im adv hq)
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun g => ?_
  rw [OptionT.probOutput_liftM, probOutput_def, probOutput_def, ← evalDist_genTable_init]

/-! ## Bridging query caches to knowledge states -/

/-- The probe-state knowledge recorded by a query cache for the oracle `D →ₒ R`: a cached cell
is `known` with its cached value, an uncached cell is undetermined with empty exclusion set. -/
def knowledgeOfCache (c : (D →ₒ R).QueryCache) : ProbeState D R := fun d =>
  match c d with
  | some v => .known v
  | none => .excluded ∅

omit [DecidableEq D] [DecidableEq R] [Fintype R] [Fintype D] in
/-- A cached cell is recorded as `known` with its cached value. -/
lemma knowledgeOfCache_some {c : (D →ₒ R).QueryCache} {d : D} {v : R} (hc : c d = some v) :
    knowledgeOfCache c d = .known v := by
  simp only [knowledgeOfCache]
  rw [hc]

omit [DecidableEq D] [DecidableEq R] [Fintype R] [Fintype D] in
/-- An uncached cell is recorded as undetermined with empty exclusion set. -/
lemma knowledgeOfCache_none {c : (D →ₒ R).QueryCache} {d : D} (hc : c d = none) :
    knowledgeOfCache c d = .excluded ∅ := by
  simp only [knowledgeOfCache]
  rw [hc]

omit [DecidableEq D] [DecidableEq R] [Fintype R] [Fintype D] in
/-- The knowledge state of a cache has every exclusion set empty. -/
lemma exclLe_knowledgeOfCache (c : (D →ₒ R).QueryCache) :
    (knowledgeOfCache c).ExclLe 0 := by
  intro d S hS
  rcases hc : c d with _ | v
  · rw [knowledgeOfCache_none hc] at hS
    injection hS with h
    simp [← h]
  · rw [knowledgeOfCache_some hc] at hS
    exact absurd hS (by simp)

omit [DecidableEq D] [Fintype D] in
/-- The knowledge state of a cache is feasible whenever the value range is nonempty. -/
lemma feasible_knowledgeOfCache [Nonempty R] (c : (D →ₒ R).QueryCache) :
    (knowledgeOfCache c).Feasible := by
  intro d
  rcases hc : c d with _ | v
  · rw [knowledgeOfCache_none hc]
    simp [Finset.univ_nonempty]
  · rw [knowledgeOfCache_some hc]
    simp

/-- Inverses of casts of naturals distribute over finite products in `ℝ≥0∞`: every factor is
finite, so no zero/infinity side condition is needed. -/
private lemma inv_natCast_prod {κ : Type} (s : Finset κ) (f : κ → ℕ) :
    ((∏ i ∈ s, f i : ℕ) : ℝ≥0∞)⁻¹ = ∏ i ∈ s, ((f i : ℝ≥0∞))⁻¹ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
      ih]

/-- The per-cell fiber of `tableExtending c · = g0` at one cell: at a cached cell the table
value is irrelevant (every value if the cache agrees with `g0`, none otherwise), at an uncached
cell the table value must be exactly `g0`'s. -/
private def cellFiber : Option R → R → Finset R
  | some v, x => if x = v then Finset.univ else ∅
  | none, x => {x}

/-- **Cache-extension bridge.** Overlaying a query cache `c` on a uniformly drawn table is
distributed as the consistent-table distribution of the knowledge state `knowledgeOfCache c`:
cached cells are point masses at their cached values, uncached cells are independent uniforms.

Pointwise both sides are products of per-cell weights: the fiber of `tableExtending c · = g0`
is a product set that is free exactly on the cached cells, so its uniform mass is the product
of the indicator weights at cached cells and `|R|⁻¹` at uncached ones — the law
`probOutput_genTable` of `genTable (knowledgeOfCache c)`. -/
theorem evalDist_map_tableExtending_uniformSample [SampleableType (D → R)]
    (c : (D →ₒ R).QueryCache) :
    𝒟[(tableExtending c <$> ($ᵗ (D → R)) : ProbComp (D → R))] =
      𝒟[genTable (knowledgeOfCache c)] := by
  classical
  refine evalDist_ext fun g0 => ?_
  rw [probOutput_genTable, probOutput_map_eq_sum_fintype_ite]
  simp only [probOutput_uniformSample]
  have hfib : ∀ g : D → R, (g0 = tableExtending c g) ↔
      g ∈ Fintype.piFinset fun d => cellFiber (c d) (g0 d) := by
    intro g
    rw [funext_iff, Fintype.mem_piFinset]
    refine forall_congr' fun d => ?_
    rcases hc : c d with _ | v
    · simp [cellFiber, tableExtending, hc, eq_comm]
    · rcases eq_or_ne (g0 d) v with hv | hv
      · simp [cellFiber, tableExtending, hc, hv]
      · simp [cellFiber, tableExtending, hc, hv]
  rw [Finset.sum_congr rfl fun g _ => if_congr (hfib g) rfl rfl, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset, Fintype.card_pi,
    Nat.cast_prod, inv_natCast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun d _ => ?_
  rcases hc : c d with _ | v
  · rw [knowledgeOfCache_none hc, CellKnowledge.cellProb_excluded]
    simp [cellFiber]
  · rw [knowledgeOfCache_some hc, CellKnowledge.cellProb_known]
    rcases eq_or_ne (g0 d) v with hv | hv
    · haveI : Nonempty R := ⟨v⟩
      simp only [cellFiber, hv, if_true, Finset.card_univ]
      exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _)
    · simp [cellFiber, hv]

omit [Fintype D] in
/-- **First-fire bound for a cache-extended uniform table, with ambient queries.** An adversary
making at most `q` probe queries (ambient and reveal queries unconstrained), answered eagerly
from the table `tableExtending c g` for a uniformly drawn `g` and starting from the knowledge
state `knowledgeOfCache c` with the flag unset, terminates with the flag set with probability
at most `q / |R|`.

This is the entry point for consumers that have already fixed some table cells through a query
cache: by `evalDist_map_tableExtending_uniformSample` the extended table is distributed as a
consistent table for `knowledgeOfCache c`, whose exclusion sets are all empty, so the eager
bound applies at threshold `m = 0`. -/
theorem probEvent_uniformSample_tableExtending_bind_eagerProbeImplWith_le {α : Type} [Finite D]
    [SampleableType (D → R)] (q : ℕ) (im : QueryImpl spec ProbComp)
    (adv : OracleComp (spec + probeSpec D R) α) (c : (D →ₒ R).QueryCache)
    (hq : adv.IsQueryBoundP (fun i => Sum.elim (fun _ => false) ProbeOp.isProbe i = true) q) :
    Pr[ (fun z : α × (ProbeState D R × Bool) => z.2.2 = true) |
        (liftM ($ᵗ (D → R)) : OptionT ProbComp (D → R)) >>= fun g =>
          (simulateQ (eagerProbeImplWith im (tableExtending c g)) adv).run
            (knowledgeOfCache c, false) ] ≤
      (q : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞) := by
  classical
  letI := Fintype.ofFinite D
  have hmap : 𝒟[tableExtending c <$> (liftM ($ᵗ (D → R)) : OptionT ProbComp (D → R))] =
      𝒟[genTable (knowledgeOfCache c)] := by
    refine evalDist_ext fun h =>
      Eq.trans ?_ (evalDist_ext_iff.1 (evalDist_map_tableExtending_uniformSample c) h)
    rw [probOutput_map_eq_tsum, probOutput_map_eq_tsum]
    exact tsum_congr fun g => by
      rw [OptionT.probOutput_liftM, probOutput_pure, probOutput_pure]
  have hdist : 𝒟[(liftM ($ᵗ (D → R)) : OptionT ProbComp (D → R)) >>= fun g =>
        (simulateQ (eagerProbeImplWith im (tableExtending c g)) adv).run
          (knowledgeOfCache c, false)]
      = 𝒟[genTable (knowledgeOfCache c) >>= fun h =>
          (simulateQ (eagerProbeImplWith im h) adv).run (knowledgeOfCache c, false)] := by
    rw [show ((liftM ($ᵗ (D → R)) : OptionT ProbComp (D → R)) >>= fun g =>
          (simulateQ (eagerProbeImplWith im (tableExtending c g)) adv).run
            (knowledgeOfCache c, false))
        = (tableExtending c <$> (liftM ($ᵗ (D → R)) : OptionT ProbComp (D → R))) >>= fun h =>
            (simulateQ (eagerProbeImplWith im h) adv).run (knowledgeOfCache c, false) from
      (bind_map_left (tableExtending c) (liftM ($ᵗ (D → R))) fun h =>
        (simulateQ (eagerProbeImplWith im h) adv).run (knowledgeOfCache c, false)).symm]
    rw [evalDist_bind, evalDist_bind, hmap]
  rw [probEvent_def, hdist, ← probEvent_def]
  simpa using probEvent_genTable_bind_eagerProbeImplWith_le q 0 im adv (knowledgeOfCache c)
    (exclLe_knowledgeOfCache c) hq

end OracleComp
