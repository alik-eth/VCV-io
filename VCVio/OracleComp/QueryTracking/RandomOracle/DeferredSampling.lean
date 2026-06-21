/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEps

/-!
# Deferred sampling: tape factorization of answer-irrelevant draws

This module collects the reusable, scheme-independent kernels behind the
*deferred-sampling* technique: rewriting a probabilistic computation whose per-step
draws do not influence the control flow into one where those draws are *front-loaded*
into a single independent "tape", drawn ahead of time and then consumed.

The technique underlies several proofs in this library (Fiat–Shamir with abort, GPV
preimage sampling, collision/birthday bounds). Those proofs each instantiate a bespoke
state machine; what is genuinely generic — and lives here — is:

* **Expectation algebra** (`tsum_probOutput_*`): Tonelli-style rearrangements of an
  expected nonnegative functional through `pure` / `bind` / `Functor.map`, and the
  collapse of a constant-on-support functional. These are the workhorses for pushing a
  fold's expected observable through the monad structure.
* **i.i.d. bind-commutation** (`evalDist_bind_comm`, `evalDist_bind_const_neverFails`,
  `evalDist_bind_congr_left`): the *answer-irrelevant draw commutes past its
  continuation* step at the distribution level. `OracleComp`'s syntactic `bind` is not
  commutative, but its `evalDist` image into `SPMF` is; this is what lets a per-step draw
  be moved to the front tape.
* **The list-multiplicity ε-kernel** (`tsum_count_eq_length`,
  `tsum_probOutput_fresh_mul_count_le`): one fresh draw `w ← oa`, *independent of* a
  value-free list `rl`, contributes expected multiplicity
  `E[rl.count (key w)] ≤ ε · rl.length` whenever each slot is hit with probability `≤ ε`.
  This is the single source of the `ε` in deferred-sampling read bounds.
* **The general factorization statement** (`DeferredTape.Factorizes`): an abstract
  predicate packaging "the read-recording run distributes as a single front draw block
  followed by a tape-consuming run". Scheme-specific factorizations (e.g.
  `FiatShamirWithAbort.evalDist_deferredDrawRead_eq_drawList_tapeDrawRead`) are instances
  of this shape; the predicate names the target so downstream consumers share vocabulary.

The genuinely hard, scheme-specific glue — proving a particular state machine's run *is*
a tape factorization — is not generic and stays with each scheme. What this module
provides is the toolbox that those proofs are built out of.
-/

open OracleComp OracleSpec
open scoped BigOperators ENNReal

namespace OracleComp.DeferredSampling

/-! ## Expectation algebra for nonnegative functionals -/

/-- Expectation of a nonnegative functional under a `pure` computation. -/
lemma tsum_probOutput_pure_mul {β : Type} (y : β) (f : β → ℝ≥0∞) :
    ∑' z, Pr[= z | (pure y : ProbComp β)] * f z = f y := by
  rw [tsum_eq_single y fun z hz => by
    rw [probOutput_eq_zero_of_not_mem_support (by simp [hz]), zero_mul]]
  rw [probOutput_pure_self, one_mul]

/-- Tonelli-style rearrangement: the expectation of a nonnegative functional under a
`bind` is the outer expectation of the inner expectations. -/
lemma tsum_probOutput_bind_mul {α β : Type} (oa : ProbComp α)
    (g : α → ProbComp β) (f : β → ℝ≥0∞) :
    ∑' z, Pr[= z | oa >>= g] * f z =
      ∑' x, Pr[= x | oa] * ∑' z, Pr[= z | g x] * f z := by
  simp_rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]

/-- Expectation of a nonnegative functional under a `Functor.map`: the functional is
precomposed with the map. -/
lemma tsum_probOutput_map_mul {α β : Type} (oa : ProbComp α) (f : α → β) (g : β → ℝ≥0∞) :
    ∑' z, Pr[= z | f <$> oa] * g z = ∑' x, Pr[= x | oa] * g (f x) := by
  rw [map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
  refine tsum_congr fun x => ?_
  simp only [Function.comp_apply]
  rw [tsum_probOutput_pure_mul]

/-- The expectation of a nonnegative functional `F` that is constant (equal to `c`) on the
support of a never-failing (sub)probability computation equals `c`. -/
lemma tsum_probOutput_mul_of_const_on_support {β : Type} (run : ProbComp β) {c : ℝ≥0∞}
    {F : β → ℝ≥0∞} (hconst : ∀ z ∈ support run, F z = c) (hmass : Pr[⊥ | run] = 0) :
    ∑' z, Pr[= z | run] * F z = c := by
  have hsum : (∑' z, Pr[= z | run] * F z) = ∑' z, Pr[= z | run] * c := by
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ support run
    · rw [hconst z hz]
    · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
  rw [hsum, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' hmass, one_mul]

/-! ## i.i.d. bind-commutation at the distribution level

These lemmas implement the *answer-irrelevant draw commutes past its continuation* step.
`OracleComp`'s `bind` is syntactic and *not* commutative as a free monad, but its
`evalDist` image into `SPMF` is — the two iterated sums over independent draws exchange by
`ENNReal.tsum_comm`. This is the local resampling step that front-loads a draw whose value
the rest of the computation may use but whose *position* is irrelevant. -/

/-- **i.i.d. bind-commutation.** Two independent draws `oa`, `ob` feeding a common
continuation `k` may be drawn in either order without changing the output distribution. -/
theorem evalDist_bind_comm {α β γ : Type} (oa : ProbComp α) (ob : ProbComp β)
    (k : α → β → ProbComp γ) :
    𝒟[oa >>= fun a => ob >>= fun b => k a b] = 𝒟[ob >>= fun b => oa >>= fun a => k a b] := by
  refine SPMF.ext fun x => ?_
  rw [show 𝒟[oa >>= fun a => ob >>= fun b => k a b] x
        = Pr[= x | oa >>= fun a => ob >>= fun b => k a b] from (probOutput_def _ _).symm,
    show 𝒟[ob >>= fun b => oa >>= fun a => k a b] x
        = Pr[= x | ob >>= fun b => oa >>= fun a => k a b] from (probOutput_def _ _).symm]
  rw [probOutput_bind_eq_tsum]
  rw [show (∑' a : α, Pr[= a | oa] * Pr[= x | ob >>= fun b => k a b])
      = ∑' (a : α) (b : β), Pr[= a | oa] * (Pr[= b | ob] * Pr[= x | k a b]) from
    tsum_congr fun a => by rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_left]]
  rw [probOutput_bind_eq_tsum]
  rw [show (∑' b : β, Pr[= b | ob] * Pr[= x | oa >>= fun a => k a b])
      = ∑' (b : β) (a : α), Pr[= b | ob] * (Pr[= a | oa] * Pr[= x | k a b]) from
    tsum_congr fun b => by rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_left]]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun a => tsum_congr fun b => by ring

/-- **Dropping a never-failing value-irrelevant prefix.** A leading draw `od` whose
continuation ignores its value contributes only its total mass; when `od` never fails
(mass `1`, e.g. a `drawList` front block) it can be discarded from the output
distribution. -/
theorem evalDist_bind_const_neverFails {α γ : Type} (od : ProbComp α) (hmass : Pr[⊥ | od] = 0)
    (k : ProbComp γ) : 𝒟[od >>= fun _ => k] = 𝒟[k] := by
  refine SPMF.ext fun x => ?_
  rw [show 𝒟[od >>= fun _ => k] x = Pr[= x | od >>= fun _ => k] from (probOutput_def _ _).symm,
    show 𝒟[k] x = Pr[= x | k] from (probOutput_def _ _).symm]
  rw [probOutput_bind_const, hmass]; simp

/-- **Distribution-level congruence under a leading bind.** If two continuations agree as
distributions pointwise then the bound computations agree as distributions. -/
theorem evalDist_bind_congr_left {α β : Type} (oa : ProbComp α) (f g : α → ProbComp β)
    (h : ∀ a, 𝒟[f a] = 𝒟[g a]) : 𝒟[oa >>= f] = 𝒟[oa >>= g] := by
  rw [evalDist_bind, evalDist_bind]; exact congrArg _ (funext h)

/-! ## The list-multiplicity ε-kernel

The single source of the `ε` in a deferred-sampling read bound: one fresh draw,
independent of a value-free list, hits each list slot with probability `≤ ε`. -/

/-- Summing the multiplicity `rl.count rc` of every element `rc` over the whole index type
recovers the list length (the multiplicities partition the list). -/
lemma tsum_count_eq_length {C : Type} [DecidableEq C] (rl : List C) :
    (∑' rc : C, (rl.count rc : ℝ≥0∞)) = (rl.length : ℝ≥0∞) := by
  induction rl with
  | nil => simp
  | cons a rl ih =>
      have hsplit : ∀ rc : C,
          ((a :: rl).count rc : ℝ≥0∞) = (if rc = a then 1 else 0) + (rl.count rc : ℝ≥0∞) := by
        intro rc; rw [List.count_cons]; by_cases h : rc = a
        · subst h; simp [add_comm]
        · simp [h, Ne.symm h]
      simp_rw [hsplit]
      rw [ENNReal.tsum_add, ih, List.length_cons, tsum_ite_eq]
      push_cast; ring

/-- **The atomic value-free charge.** One fresh draw `w ← oa : ProbComp (C × P)`,
*independent of* a value-free list `rl : List C`, contributes expected multiplicity
`E[rl.count (key w)] ≤ ε · rl.length`: each of the `rl.length` slots of `rl` is hit by the
fresh draw's key with probability `Pr[= slot | key <$> oa] ≤ ε`.

Stated for `key = Prod.fst` (a draw of a `(C × P)`-pair, of which only the `C`-component is
matched against the list), as it arises when a commitment draw carries an auxiliary private
state. This is the irreducible probabilistic kernel of a deferred-sampling read bound. -/
lemma tsum_probOutput_fresh_mul_count_le {C P : Type} [DecidableEq C]
    (oa : ProbComp (C × P)) (rl : List C) (ε : ℝ)
    (hGuess : ∀ cm : C, Pr[= cm | Prod.fst <$> oa] ≤ ENNReal.ofReal ε) :
    (∑' w : C × P, Pr[= w | oa] * (rl.count w.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * (rl.length : ℝ≥0∞) := by
  have hcount : ∀ w : C × P,
      ((rl.count w.1 : ℕ) : ℝ≥0∞)
        = ∑' rc : C, (rl.count rc : ℝ≥0∞) * (if w.1 = rc then 1 else 0) := by
    intro w; rw [tsum_eq_single w.1 (fun rc hrc => by simp [Ne.symm hrc])]; simp
  simp_rw [hcount]
  rw [show (∑' w : C × P, Pr[= w | oa] *
        ∑' rc : C, (rl.count rc : ℝ≥0∞) * (if w.1 = rc then 1 else 0))
      = ∑' rc : C, ∑' w : C × P,
          Pr[= w | oa] * ((rl.count rc : ℝ≥0∞) * (if w.1 = rc then 1 else 0)) from by
    rw [ENNReal.tsum_comm]; exact tsum_congr fun w => by rw [ENNReal.tsum_mul_left]]
  have hmarg : ∀ rc : C,
      (∑' w : C × P, Pr[= w | oa] * ((rl.count rc : ℝ≥0∞) * (if w.1 = rc then 1 else 0)))
        = (rl.count rc : ℝ≥0∞) * Pr[= rc | Prod.fst <$> oa] := by
    intro rc
    rw [show Pr[= rc | Prod.fst <$> oa]
          = ∑' w : C × P, Pr[= w | oa] * (if w.1 = rc then 1 else 0) from by
      rw [probOutput_map_eq_tsum]; refine tsum_congr fun w => ?_
      simp only [eq_comm]; split <;> rename_i h <;> simp [h]]
    rw [show (∑' w : C × P,
            Pr[= w | oa] * ((rl.count rc : ℝ≥0∞) * (if w.1 = rc then 1 else 0)))
          = ∑' w : C × P,
              (rl.count rc : ℝ≥0∞) * (Pr[= w | oa] * (if w.1 = rc then 1 else 0)) from
      tsum_congr fun w => by ring]
    rw [ENNReal.tsum_mul_left]
  simp_rw [hmarg]
  calc (∑' rc : C, (rl.count rc : ℝ≥0∞) * Pr[= rc | Prod.fst <$> oa])
      ≤ ∑' rc : C, (rl.count rc : ℝ≥0∞) * ENNReal.ofReal ε :=
        ENNReal.tsum_le_tsum fun rc => by gcongr; exact hGuess rc
    _ = ENNReal.ofReal ε * (rl.length : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, mul_comm, tsum_count_eq_length]

/-! ## The general factorization shape

The hard, scheme-specific content of deferred sampling is proving that a particular
read-recording run *equals* a front-tape factorization. The shape of that target is
generic and named here, so that scheme instances and downstream consumers share a single
vocabulary. -/

/-- **The deferred-tape factorization predicate.** `Factorizes run tape tapeRun` asserts
that running the deferred-draw computation `run : ProbComp γ` is distributionally identical
to first drawing an independent front tape `tape : ProbComp τ` and then running the
tape-consuming variant `tapeRun : τ → ProbComp γ` that reads its per-step draws off the
tape head-first:

`𝒟[run] = 𝒟[tape >>= tapeRun]`.

A scheme establishes this by induction on its adversary computation: at an
*answer-irrelevant* step the front tape commutes past the query (`evalDist_bind_comm`), and
at a *drawing* step the inline draw block is split off the front tape. The
over-provisioned suffix of the tape is discarded by the never-failing prefix lemma
(`evalDist_bind_const_neverFails`). See
`FiatShamirWithAbort.evalDist_deferredDrawRead_eq_drawList_tapeDrawRead` for a worked
instance. -/
def Factorizes {γ τ : Type} (run : ProbComp γ) (tape : ProbComp τ)
    (tapeRun : τ → ProbComp γ) : Prop :=
  𝒟[run] = 𝒟[tape >>= tapeRun]

/-- A factorization may be rewritten through any distribution-level continuation: if
`run` factorizes through `tape`/`tapeRun`, then binding a continuation `k` after `run`
factorizes through `tape` and `tapeRun >=> k` (definitional unfolding plus `evalDist_bind`
associativity). This is the recombination step used when a factorized head feeds a fold. -/
theorem Factorizes.bind {γ τ δ : Type} {run : ProbComp γ} {tape : ProbComp τ}
    {tapeRun : τ → ProbComp γ} (h : Factorizes run tape tapeRun) (k : γ → ProbComp δ) :
    Factorizes (run >>= k) tape (fun t => tapeRun t >>= k) := by
  simp only [Factorizes, evalDist_bind] at h ⊢
  rw [h, bind_assoc]

end OracleComp.DeferredSampling
