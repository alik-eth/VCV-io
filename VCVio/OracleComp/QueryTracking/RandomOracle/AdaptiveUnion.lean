/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# Adaptive Union Bound at First Read — Stage 0 (Falsifiability Gate)

This file establishes the smallest concrete instances of the *adaptive-union /
freshness-at-first-read* bound over the framework's lazy random oracle
(`OracleSpec.randomOracle`, i.e. `uniformSampleImpl.withCaching`), for a finite
oracle `D →ₒ R` with a single constant range `R`.

## The bound, informally

An adversary interacts with the lazy oracle. At each step it reads one cell `d`,
the lazy oracle replies with the cached value if `d` is already cached, or a
fresh uniform draw `$ᵗ R` otherwise (caching it). We want to bound the
probability that *some* step's adaptively-chosen event fires on the value that
step reads, by `q · maxProb`, where `q` is the number of queries and `maxProb`
is an upper bound on the single-draw event probability `Pr[· | $ᵗ R]`.

## The repeat-read subtlety (why the statement is shaped the way it is)

A cell that is read a *second* time returns a value the adversary has already
seen, so an event targeting that known value fires with probability `1`. The
honest bound therefore charges events **at first read of each distinct cell
only**. The fresh-uniform draw at the first read of a cell already "decides" the
value of every later read of that same cell; a re-read adds no new randomness and
cannot be charged again.

Concretely, the q=2 lemma below charges the second event **only on the fresh
branch** (`f r₁ ≠ d₁`), where the second cell is genuinely read fresh. On the
cached branch (`f r₁ = d₁`) the second read returns `r₁`, which is exactly the
value the first event already saw: the union is over first reads, and the
cached re-read is subsumed by the first read's charge. This is exactly the
repeat-read case that refuted the per-path coupling shortcuts (see the
collision-reader-union-discard analysis): the statement must not promise a
`maxProb` charge for an adaptively-chosen target at a re-read.

## Stage-0 scope

* `probEvent_randomOracle_step_eq` / `probEvent_randomOracle_step_le_uniform`:
  the q=1 freshness lemma — at an uncached cell, the reply event probability
  equals (resp. is bounded by) the single-draw `$ᵗ R` event probability.
* `probEvent_adaptiveUnion_one`: the q=1 union bound (`≤ maxProb`).
* `probEvent_adaptiveUnion_two`: the q=2 adaptive union bound (`≤ 2 · maxProb`),
  with the second event charged at first read (fresh branch) and the cached
  re-read subsumed by the first read.

## Stage 1 (general q)

The general statement, proven by induction on the query count in a later stage,
is: for an adversary making at most `q` queries to the lazy oracle from cache
`c`, the probability that some step's adaptively-chosen event fires on the value
of the *cell it reads at first read* is `≤ q · maxProb`. The induction threads
the monotone cache (`simulateQ_cachingOracle_cache_le`) and charges each fresh
first-read draw by the point mass of the just-drawn cell, which is independent of
the continuation by construction in the lazy world.
-/

open OracleComp OracleSpec

namespace OracleComp

/-- **Bind union helper.** If every reachable continuation `my x` satisfies the event with
probability `≤ r`, then so does the whole bind. The base shape used to discharge the second-read
charge in the two-step adaptive union: each fresh first read of `f r₁` is bounded by `maxProb`
uniformly in `r₁`. -/
theorem probEvent_bind_le_of_forall_le {m : Type _ → Type _} [Monad m] [HasEvalSPMF m]
    {α β : Type _} {mx : m α} {my : α → m β} {q : β → Prop} {r : ENNReal}
    (h : ∀ x ∈ support mx, Pr[ q | my x] ≤ r) :
    Pr[ q | mx >>= my] ≤ r := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' x : α, Pr[= x | mx] * Pr[ q | my x]
      ≤ ∑' x : α, Pr[= x | mx] * r := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · exact mul_le_mul' le_rfl (h x hx)
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x : α, Pr[= x | mx]) * r := by rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * r := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = r := one_mul r

variable {D R : Type} [DecidableEq D] [SampleableType R]

/-! ## q = 1 : freshness at first read -/

/-- **Freshness at first read (q = 1).** Running the lazy random oracle on a single query at an
*uncached* cell `d` (`c d = none`), the probability that the reply satisfies `p` equals the
single-draw event probability `Pr[p | $ᵗ R]`: the reply is a fresh uniform draw. -/
theorem probEvent_randomOracle_step_eq (c : (D →ₒ R).QueryCache) (d : D) (hc : c d = none)
    (p : R → Prop) :
    Pr[ (fun z : R × (D →ₒ R).QueryCache => p z.1) |
          (randomOracle (spec := (D →ₒ R)) d).run c ] = Pr[ p | ($ᵗ R) ] := by
  rw [QueryImpl.withCaching_run_none _ hc, probEvent_map]
  rfl

/-- **q = 1 uniform bound.** The reply event probability at a fresh cell is bounded by any
`maxProb` that dominates the single-draw event probability. The hypothesis `hmax` mirrors the
`hmax` idiom of the collision/eager-table bounds. -/
theorem probEvent_randomOracle_step_le_uniform {maxProb : ENNReal}
    (c : (D →ₒ R).QueryCache) (d : D) (hc : c d = none) (p : R → Prop)
    (hmax : Pr[ p | ($ᵗ R)] ≤ maxProb) :
    Pr[ (fun z : R × (D →ₒ R).QueryCache => p z.1) |
          (randomOracle (spec := (D →ₒ R)) d).run c ] ≤ maxProb := by
  rw [probEvent_randomOracle_step_eq c d hc p]; exact hmax

/-- **Adaptive union bound, q = 1.** A single-query adversary's event probability is `≤ maxProb`.
This is the base case of the Stage-1 induction. -/
theorem probEvent_adaptiveUnion_one {maxProb : ENNReal}
    (c : (D →ₒ R).QueryCache) (d : D) (hc : c d = none) (p : R → Prop)
    (hmax : Pr[ p | ($ᵗ R)] ≤ maxProb) :
    Pr[ (fun z : R × (D →ₒ R).QueryCache => p z.1) |
          (randomOracle (spec := (D →ₒ R)) d).run c ] ≤ maxProb :=
  probEvent_randomOracle_step_le_uniform c d hc p hmax

/-! ## q = 2 : adaptive union at first read

The adversary makes a first query at an uncached cell `d₁`, observes its fresh reply `r₁`, then
*adaptively* picks the second target `d₂ = f r₁` and the second event `p₂ = g r₁` as functions of
`r₁`. The two-step lazy run is `runTwo`, and the union event `unionEvent` charges the first event
on `r₁` and the second event on the value read at the second step **only when that step is a fresh
first read** (`f r₁ ≠ d₁`).

The cached re-read branch (`f r₁ = d₁`) is deliberately excluded from `unionEvent`: there the second
read returns `r₁`, a value the first event already saw, so the adversary could force the event with
probability `1` by targeting the known value. Charging it would be both unsound (no `maxProb`
bound) and double-counting the single fresh draw at `d₁`. The bound is therefore over **first reads
of distinct cells**. -/

/-- The two-step adaptive lazy run: query `d₁`, observe `r₁`, then query the adaptively chosen
`f r₁`, returning the pair of values read `(r₁, r₂)`. -/
@[reducible] def runTwo (c : (D →ₒ R).QueryCache) (d₁ : D) (f : R → D) :
    ProbComp (R × R) :=
  (randomOracle (spec := (D →ₒ R)) d₁).run c >>= fun z₁ =>
    (randomOracle (spec := (D →ₒ R)) (f z₁.1)).run z₁.2 >>= fun z₂ =>
      pure (z₁.1, z₂.1)

/-- The first-read union event for the two-step adaptive run: the first event `p₁` fires on `r₁`,
or the second step is a *genuine first read* — the post-step-1 cache `c.cacheQuery d₁ r₁` has no
entry at `f r₁`, equivalently `f r₁ ≠ d₁` and `c (f r₁) = none` — and the second event `g r₁`
fires on `r₂`.

Requiring `(c.cacheQuery d₁ z.1) (f z.1) = none` (rather than merely `f z.1 ≠ d₁`) is what makes
the bound true when the starting cache `c` already holds entries: a second read of any cell that is
already cached — whether the freshly written `d₁` or a pre-existing entry — returns a known value
and is excluded from the charge. -/
@[reducible] def unionEvent (c : (D →ₒ R).QueryCache) (d₁ : D) (f : R → D)
    (p₁ : R → Prop) (g : R → R → Prop) : R × R → Prop :=
  fun z => p₁ z.1 ∨ ((c.cacheQuery d₁ z.1) (f z.1) = none ∧ g z.1 z.2)

/-- **Adaptive union bound, q = 2.** A two-query adaptive adversary's first-read union event has
probability `≤ 2 · maxProb`, where `maxProb` dominates every single-draw event probability used:
the first event `p₁`, and (on the fresh branch) each adaptively chosen second event `g r₁`.

The second event is charged at the *first read* of its cell only: the cached re-read branch
`f r₁ = d₁` is excluded from `unionEvent`, since there the second read returns the already-seen
`r₁` and admits no `maxProb` bound (it is the repeat-read case that refutes per-path coupling). -/
theorem probEvent_adaptiveUnion_two {maxProb : ENNReal}
    (c : (D →ₒ R).QueryCache) (d₁ : D) (hc : c d₁ = none)
    (f : R → D) (p₁ : R → Prop) (g : R → R → Prop)
    (hmax₁ : Pr[ p₁ | ($ᵗ R)] ≤ maxProb)
    (hmax₂ : ∀ r₁ : R, Pr[ g r₁ | ($ᵗ R)] ≤ maxProb) :
    Pr[ unionEvent c d₁ f p₁ g | runTwo c d₁ f] ≤ 2 * maxProb := by
  -- Split the union into the first-read event and the fresh-second-read event.
  have hsplit : Pr[ unionEvent c d₁ f p₁ g | runTwo c d₁ f] ≤
      Pr[ fun z : R × R => p₁ z.1 | runTwo c d₁ f] +
      Pr[ fun z : R × R => (c.cacheQuery d₁ z.1) (f z.1) = none ∧ g z.1 z.2 |
            runTwo c d₁ f] :=
    probEvent_or_le _ _ _
  have htwo : (2 : ENNReal) * maxProb = maxProb + maxProb := by ring
  rw [htwo]
  refine le_trans hsplit (add_le_add ?_ ?_)
  · -- Term A: the first event depends only on the first read, which is a fresh `$ᵗ R` draw.
    refine le_trans (le_of_eq ?_) (probEvent_randomOracle_step_le_uniform c d₁ hc p₁ hmax₁)
    classical
    rw [runTwo, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    refine tsum_congr fun z₁ => ?_
    rw [probEvent_bind_of_const _ (p := fun z : R × R => p₁ z.1) (r := if p₁ z₁.1 then 1 else 0)
        (fun z₂ _ => by simp [probEvent_pure]), probFailure_eq_zero, tsub_zero, one_mul]
    by_cases hp : p₁ z₁.1 <;> simp [hp]
  · -- Term B: the second event is charged only on a genuine first read of `f r₁`, where the
    -- reply is a fresh `$ᵗ R` draw; the cached/known-value branch makes the event false.
    rw [runTwo]
    refine probEvent_bind_le_of_forall_le (fun z₁ hz₁ => ?_)
    -- After step 1 the cache is `c.cacheQuery d₁ z₁.1`, so the freshness test on `f z₁.1` reads
    -- the post-step-1 cache.
    have hz₁eq : z₁.2 = c.cacheQuery d₁ z₁.1 := by
      rw [QueryImpl.withCaching_run_none _ hc, support_map] at hz₁
      obtain ⟨u, _, hu⟩ := hz₁
      rw [← hu]
    rcases hfresh : z₁.2 (f z₁.1) with _ | v
    · -- Genuine first read of `f z₁.1`: the reply is a fresh uniform draw.
      have hcfresh : (c.cacheQuery d₁ z₁.1) (f z₁.1) = none := hz₁eq ▸ hfresh
      have hgoal : (probEvent
          ((randomOracle (spec := (D →ₒ R)) (f z₁.1)).run z₁.2 >>= fun z₂ => pure (z₁.1, z₂.1))
          fun z : R × R => c.cacheQuery d₁ z.1 (f z.1) = none ∧ g z.1 z.2)
          = Pr[ g z₁.1 | ($ᵗ R)] := by
        classical
        rw [QueryImpl.withCaching_run_none _ (hz₁eq ▸ hfresh : z₁.2 (f z₁.1) = none)]
        rw [bind_map_left, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
        refine tsum_congr fun u => ?_
        rw [probEvent_pure]
        by_cases hg : g z₁.1 u
        · simp only [hcfresh, hg, true_and, if_true, mul_one]; rfl
        · simp only [hg, and_false, if_false, mul_zero]
      rw [hgoal]; exact hmax₂ z₁.1
    · -- Cached re-read of `f z₁.1`: the freshness test fails, so the event is impossible.
      have hcached : (c.cacheQuery d₁ z₁.1) (f z₁.1) = some v := hz₁eq ▸ hfresh
      refine le_trans (le_of_eq ?_) (zero_le (a := maxProb))
      refine probEvent_eq_zero (fun z hz => ?_)
      rintro ⟨hnone, -⟩
      have hz1 : z.1 = z₁.1 := by
        obtain ⟨z₂, _, hzmem⟩ := (mem_support_bind_iff _ _ _).1 hz
        rw [support_pure, Set.mem_singleton_iff] at hzmem
        rw [hzmem]
      rw [hz1, hcached] at hnone
      exact absurd hnone (by simp)

/-! ## Stage 1 : the per-step toolkit (general `q`)

Both downstream consumers — the unlinkability slot-positive tag step
(`PRFTagReader.UnlinkReduction.dcAux_tag_slotPositive`) and the collision reader-loop bound
(`PRFTagReader.…AuthTable`) — perform their *own* structural induction over the adversary
`query >>= k`, carrying the induction hypothesis as an explicit premise. What they consume at each
reader/tag step is not a monolithic `q`-ary union bound but a **per-step toolkit**:

* the Stage-0 single-step freshness charge `probEvent_randomOracle_step_eq` (already established),
* **freshness-preservation** lemmas, which re-establish their per-step cache invariants
  (`hcInv` / `hRespInv` in the unlinkability aux; `hCacheHonest` in the collision branch) after a
  lazy-oracle step, so the IH's freshness hypothesis is available at the next step;
* a **post-step cache characterization** `randomOracle_run_support_cache`, the exact statement
  that a first read at `d` overwrites the cache with `c.cacheQuery d r` for the drawn `r`, while a
  cached re-read leaves the cache untouched — this is the obligation Stage 0 flagged and is what
  discharges the freshness conjunct at the call sites.

For callers that *do* want the rolled-up bound, the explicit `runMany` fold below plus the
probability-level first-fire telescope `probEvent_adaptiveUnion_le` deliver `≤ q · maxProb`
directly from the per-step charge, by induction on the query list. The fold is deliberately the
simplest reusable shape (a `List` of adaptive `(target, event)` selectors threaded through the
monotone cache); the consumers may but need not route through it. -/

/-! ### Post-step cache characterization (the freshness obligation) -/

/-- **Post-step cache, fresh branch.** Every `(value, cache)` pair in the support of a single lazy
random-oracle step at an *uncached* cell `d` has its second component equal to `c.cacheQuery d r`,
where `r` is the drawn value (the first component). This is the exact post-step cache used to
discharge the freshness conjunct at a first read. -/
theorem randomOracle_run_support_cache (c : (D →ₒ R).QueryCache) (d : D) (hc : c d = none)
    {z : R × (D →ₒ R).QueryCache} (hz : z ∈ support ((randomOracle (spec := (D →ₒ R)) d).run c)) :
    z.2 = c.cacheQuery d z.1 := by
  rw [QueryImpl.withCaching_run_none _ hc, support_map] at hz
  obtain ⟨u, _, hu⟩ := hz
  rw [← hu]

/-- **Post-step cache, cached branch.** A lazy random-oracle step at an *already cached* cell `d`
leaves the cache untouched: every pair in its support has second component `c`. A re-read draws no
new randomness. -/
theorem randomOracle_run_support_cache_some (c : (D →ₒ R).QueryCache) (d : D) {u : R}
    (hc : c d = some u)
    {z : R × (D →ₒ R).QueryCache} (hz : z ∈ support ((randomOracle (spec := (D →ₒ R)) d).run c)) :
    z.2 = c := by
  rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hz
  rw [hz]

/-! ### Freshness preservation -/

omit [SampleableType R] in
/-- **Caching preserves freshness off the written cell.** Writing a fresh entry at `d` keeps every
cell `e ≠ d` at its prior cache status. The consumers instantiate this with `e` ranging over the
cells their invariant tracks (the non-zero slots in the unlinkability aux, the honest column in the
collision branch), having separately ensured those cells differ from the just-read `d`. -/
theorem cacheQuery_preserves_freshness (c : (D →ₒ R).QueryCache) (d : D) (r : R)
    {e : D} (hne : e ≠ d) : (c.cacheQuery d r) e = c e :=
  QueryCache.cacheQuery_of_ne _ _ hne

/-- **A lazy step preserves freshness off the read cell.** After running one lazy random-oracle
step at `d` from cache `c`, every cell `e ≠ d` that was fresh (`c e = none`) is still fresh in the
post-step cache. Covers both branches: a cached re-read leaves the whole cache fixed; a fresh first
read only writes cell `d`, which is `≠ e`. -/
theorem randomOracle_run_preserves_freshness (c : (D →ₒ R).QueryCache) (d : D)
    {e : D} (hne : e ≠ d) (he : c e = none)
    {z : R × (D →ₒ R).QueryCache} (hz : z ∈ support ((randomOracle (spec := (D →ₒ R)) d).run c)) :
    z.2 e = none := by
  rcases hcd : c d with _ | u
  · rw [randomOracle_run_support_cache c d hcd hz, cacheQuery_preserves_freshness c d z.1 hne, he]
  · rw [randomOracle_run_support_cache_some c d hcd hz, he]

end OracleComp
