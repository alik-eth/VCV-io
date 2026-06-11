/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import VCVio.EvalDist.Monad.Basic

/-!
# Distribution-Level Congruence And Commutation Under Bind

Helpers for rewriting probabilities along `evalDist` identities:

* `probOutput_eq_of_evalDist_eq` and `probEvent_eq_of_evalDist_eq` transport output and event
  probabilities across an equality of distributions, so a distribution-level identity can be
  consumed pointwise without unfolding `evalDist`.
* `evalDist_bind_congr` upgrades a support-restricted family of distribution identities on the
  continuations of a bind to a distribution identity of the whole bind.
* `evalDist_bind_bind_comm` commutes two independent draws: the output distribution of drawing
  `mx` then `my` and combining is the same as drawing `my` then `mx`, proven by `tsum`
  rearrangement — the underlying monad need not be commutative as terms.

These are stated for any monad with the standard distribution-semantics lifts; the canonical
consumers are `ProbComp` and `OptionT ProbComp` programs.
-/

open ENNReal

universe u v

variable {α β : Type u} {m : Type u → Type v} [Monad m]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]

omit [Monad m] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m] in
/-- Transport of an output probability along an `evalDist` identity. -/
lemma probOutput_eq_of_evalDist_eq {mx my : m α} (h : 𝒟[mx] = 𝒟[my]) (x : α) :
    Pr[= x | mx] = Pr[= x | my] := by
  rw [probOutput_def, probOutput_def, h]

omit [Monad m] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m] in
/-- Transport of an event probability along an `evalDist` identity. -/
lemma probEvent_eq_of_evalDist_eq {mx my : m α} (h : 𝒟[mx] = 𝒟[my]) (p : α → Prop) :
    Pr[ p | mx] = Pr[ p | my] := by
  rw [probEvent_def, probEvent_def, h]

/-- Congruence for `evalDist` under `bind`: continuations that agree in distribution on the
support of the first computation yield equal bind distributions. -/
lemma evalDist_bind_congr {mx : m α} {f f' : α → m β}
    (h : ∀ x ∈ support mx, 𝒟[f x] = 𝒟[f' x]) : 𝒟[mx >>= f] = 𝒟[mx >>= f'] :=
  evalDist_ext fun y => probOutput_bind_congr fun x hx =>
    probOutput_eq_of_evalDist_eq (h x hx) y

omit [MonadLiftT m SetM] [EvalDistCompatible m] in
/-- Two draws may be taken in either order: the output distribution of drawing `mx` then `my`
and combining is the same as drawing `my` then `mx`. -/
lemma evalDist_bind_bind_comm {γ : Type u} (mx : m α) (my : m β) (F : α → β → m γ) :
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
