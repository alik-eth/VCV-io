/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Concrete.Instance

/-!
# Concrete ML-DSA Primitive Laws

This file discharges the deterministically-provable fields of `MLDSA.Primitives.Laws` for the
concrete `concretePrimitives` instance built from the FIPS 204 rounding, NTT, and byte-encoding
layers, for any approved parameter set. Each provable field is banked as a standalone theorem
(`concrete_*`).

## What is proven

The eight rounding/transform fields follow directly from the verified concrete rounding lemmas
in `Concrete/Rounding.lean` and the concrete NTT laws in `Concrete/NTT.lean`, bridged across the
`polyNorm` / `LatticeCrypto.cInfNorm` definitional identity (`polyNorm_eq_cInfNorm`):

- `transform`, `high_low_decomp`, `lowBits_bound`, `hide_low`, `highBitsShift_injective`,
  `useHint_makeHint`, `power2Round_decomp`, `power2Round_bound`.

Two further fields are discharged from the concrete byte-encoding decode ranges and packer
roundtrip in `Concrete/Encoding.lean`:

- `expandMask_bound` (`concrete_expandMask_bound`): every `expandMask` coefficient is a value
  decoded by `polyZUnpack` over the range `[-γ₁ + 1, γ₁]`, so its centered infinity norm is at
  most `γ₁`. This is a property of the decoder's output window (`bitUnpackPoly_get`) and is
  independent of the opaque SHAKE byte stream. It matches the restated abstract bound `γ₁`.
- `w1Encode_injective` (`concrete_w1Encode_injOn`): on the valid commitment range — every
  component an actual `highBits` output — each coefficient lies in `[0, (q-1)/(2γ₂) - 1]`
  (`highBits_coeff_val_lt_m`), which fits the `w₁` packer's bit width, so `simpleBitPackPoly` is
  inverted by `simpleBitUnpackPoly` and `w1Encode` is injective. This matches the restated
  abstract `Set.InjOn` field, whose validity set is exactly the image of `highBits`.

Two further sampler-bound fields are discharged from the fuel-recursive rejection samplers in
`Concrete/Sampling.lean` (whose structural output ranges are now provable by fuel induction):

- `sampleInBall_norm` (`concrete_sampleInBall_norm`): `SampleInBall(c̃)`'s accumulator only ever
  holds the values `0`, `+1`, `-1`, so every coefficient has centered absolute value at most `1`.
- `expandS_bound` (`concrete_expandS_bound`): `ExpandS(ρ')` pushes only the centered `η`-bounded
  values (`2 - u` for `η = 2`, `4 - t` for `η = 4`; nothing otherwise), so every coefficient of
  both secret vectors has centered absolute value at most `η`.

## What is NOT proven (and why)

Three fields remain, in two honest categories — there are no longer any false-as-stated fields:

1. **Blocked by missing convolution-norm infrastructure** (structurally true, but not yet
   extractable):
   - `sampleInBall_smul_bound`: `SampleInBall(c̃)` has at most `τ` nonzero coefficients, each `±1`,
     so for `‖s‖∞ ≤ η` the challenge–secret product `c · s` satisfies `‖c · s‖∞ ≤ τ · η = β`. This
     is true (it also holds trivially when `β ≥ q/2`, since a centered representative never exceeds
     `q/2`). Proving it requires two pieces of theory not present in the tree: (a) the
     `ℓ₁`-norm count `‖SampleInBall(c̃)‖₁ ≤ τ` (a Fisher–Yates nonzero-count invariant over the
     τ challenge writes), and (b) a generic negacyclic-convolution bound
     `‖f · g‖∞ ≤ ‖f‖₁ · ‖g‖∞` over centered `ZMod` representatives (whose proof must track the
     *true integer* convolution sum to avoid modular wraparound). Both are isolated here pending
     that convolution-norm infrastructure.

2. **Random-oracle modeling assumptions** (inherent to the ML-DSA security model, not derivable
   from any fixed deterministic instantiation — see their docstrings in `Primitives.lean`):
   - `expandS_honest_sampling`, `keyVector_t0_determined`: standard ROM idealizations of the
     SHAKE XOFs (`ExpandSeed` / `ExpandS`). These are model assumptions, left abstract.

The abstract `Primitives.Laws` statement is **not** modified by this file; the banked `concrete_*`
theorems make explicit which concrete obligations are discharged and which remain.
-/


namespace MLDSA.Concrete

open MLDSA LatticeCrypto

set_option maxRecDepth 4000

/-- The ML-DSA centered infinity norm `polyNorm` agrees with the backend-generic
`LatticeCrypto.cInfNorm` on the canonical vector backend. This is the bridge that lets the
`polyNorm`-stated `Primitives.Laws` fields consume the `cInfNorm`-stated rounding lemmas. -/
theorem polyNorm_eq_cInfNorm (f : Rq) : polyNorm f = LatticeCrypto.cInfNorm f := by
  unfold polyNorm normOps LatticeCrypto.cInfNorm LatticeCrypto.zmodPolyNormOps
    LatticeCrypto.normOpsOfCenteredView
  rfl

variable (p : Params)

/-! ## Provable algebraic fields (banked) -/

/-- `Primitives.Laws.transform` for the concrete instance. -/
theorem concrete_transform : NTTRingLaws concreteNTTRingOps :=
  concreteNTTRingLaws

/-- `Primitives.Laws.high_low_decomp` for the concrete instance. -/
theorem concrete_high_low_decomp (r : Rq) :
    (concretePrimitives p).highBitsShift ((concretePrimitives p).highBits r)
      + (concretePrimitives p).lowBits r = r :=
  concreteRounding_high_low_decomp p r

/-- `Primitives.Laws.lowBits_bound` for the concrete instance (approved parameters). -/
theorem concrete_lowBits_bound (hp : p.isApproved) (r : Rq) :
    polyNorm ((concretePrimitives p).lowBits r) ≤ p.gamma2 := by
  rw [polyNorm_eq_cInfNorm]
  exact concreteRounding_lowBits_bound p (by rcases hp with rfl | rfl | rfl <;> decide)
    (by rcases hp with rfl | rfl | rfl <;> decide) r

/-- `Primitives.Laws.hide_low` for the concrete instance (approved parameters). -/
theorem concrete_hide_low (hp : p.isApproved) (r s : Rq) (b : ℕ)
    (hs : polyNorm s ≤ b)
    (hlow : polyNorm ((concretePrimitives p).lowBits r) + b < p.gamma2) :
    (concretePrimitives p).highBits (r + s) = (concretePrimitives p).highBits r := by
  apply concreteRounding_hide_low_of_isApproved p hp r s b
  · rwa [← polyNorm_eq_cInfNorm]
  · rw [← polyNorm_eq_cInfNorm]; exact hlow

/-- `Primitives.Laws.highBitsShift_injective` for the concrete instance (approved parameters). -/
theorem concrete_highBitsShift_injective (hp : p.isApproved) :
    Function.Injective (concretePrimitives p).highBitsShift :=
  highBitsShift_injective_of_isApproved p hp

/-- `Primitives.Laws.useHint_makeHint` for the concrete instance (approved parameters). -/
theorem concrete_useHint_makeHint (hp : p.isApproved) (z r : Rq) (hz : polyNorm z ≤ p.gamma2) :
    (concretePrimitives p).useHint ((concretePrimitives p).makeHint z r) r
      = (concretePrimitives p).highBits (r + z) := by
  apply concreteRounding_useHint_correct_of_isApproved p hp z r
  rwa [← polyNorm_eq_cInfNorm]

/-- `Primitives.Laws.power2Round_decomp` for the concrete instance. -/
theorem concrete_power2Round_decomp (r : Rq) :
    (concretePrimitives p).power2RoundShift ((concretePrimitives p).power2Round r).1
      + ((concretePrimitives p).power2Round r).2 = r :=
  concretePower2Round_high_low_decomp r

/-- `Primitives.Laws.power2Round_bound` for the concrete instance. -/
theorem concrete_power2Round_bound (r : Rq) :
    polyNorm ((concretePrimitives p).power2Round r).2 ≤ 2 ^ (droppedBits - 1) := by
  rw [polyNorm_eq_cInfNorm]
  change LatticeCrypto.cInfNorm (power2RoundLow r) ≤ 2 ^ (droppedBits - 1)
  rw [← concretePower2Round_remainder_eq_low]
  exact concretePower2Round_bound r

/-! ## `expandMask_bound` (restated to the FIPS-204 `z`-range, now provable)

The concrete `expandMask` decodes each coefficient through `polyZUnpack p`, i.e.
`bitUnpackPoly bytes (-γ₁ + 1) γ₁`. By the decode-range bound `bitUnpackPoly_get`, every coefficient
is `γ₁ - v` for a `width`-bit value `v` with `width = rangeWidth (-γ₁ + 1) γ₁`. For the approved
parameter sets `2 ^ width = 2 γ₁`, so `v ≤ 2 γ₁ - 1` and `γ₁ - v ∈ [-(γ₁ - 1), γ₁]`, whose centered
representative (since `2 γ₁ < q`) is `γ₁ - v` itself, of absolute value at most `γ₁`. The argument
is purely about the decoder's output range and independent of the opaque SHAKE byte stream. -/

/-- Decode-range infinity-norm bound for a `z`-range `bitUnpackPoly`: every coefficient of
`bitUnpackPoly bytes (-γ + 1) γ` has centered absolute value at most `γ`, provided the bit width
satisfies `2 ^ width = 2 γ` (true for FIPS-204 `γ₁`, a power of two) and `2 γ < q`. -/
theorem bitUnpackPoly_z_cInfNorm_le (bytes : ByteArray) (γ : ℕ)
    (hwidth : (2 : ℕ) ^ rangeWidth (-(γ : ℤ) + 1) (γ : ℤ) = 2 * γ)
    (hq : 2 * γ < modulus) :
    LatticeCrypto.cInfNorm (bitUnpackPoly bytes (-(γ : ℤ) + 1) (γ : ℤ)) ≤ γ := by
  rw [LatticeCrypto.cInfNorm_le_iff]
  intro i
  obtain ⟨v, hv, hget⟩ := bitUnpackPoly_get bytes (-(γ : ℤ) + 1) (γ : ℤ) i
  rw [hget, hwidth] at *
  have hbound : ((γ : ℤ) - (v : ℤ)).natAbs ≤ γ := by omega
  rw [LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le ((γ : ℤ) - (v : ℤ)) hbound (by omega)]
  exact hbound

/-- For each approved parameter set the `z`-range bit width satisfies `2 ^ width = 2 γ₁` (because
`γ₁` is a power of two) and `2 γ₁ < q`. -/
private theorem approved_gamma1_width (hp : p.isApproved) :
    (2 : ℕ) ^ rangeWidth (-(p.gamma1 : ℤ) + 1) (p.gamma1 : ℤ) = 2 * p.gamma1 ∧
      2 * p.gamma1 < modulus := by
  rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- `Primitives.Laws.expandMask_bound` (restated bound `γ₁`) for the concrete instance, at any
approved parameter set. -/
theorem concrete_expandMask_bound (hp : p.isApproved) (rhoDoublePrime : Bytes 64) (kappa : ℕ) :
    polyVecBounded ((concretePrimitives p).expandMask rhoDoublePrime kappa) p.gamma1 := by
  obtain ⟨hwidth, hq⟩ := approved_gamma1_width p hp
  rw [polyVecBounded, polyVecNorm, LatticeCrypto.PolyVec.cInfNorm_le_iff]
  intro j
  -- Each component is `polyZUnpack p (<opaque SHAKE stream>)`; the bound is a decode-range
  -- property, so generalize the opaque byte argument and apply the decoder bound.
  change polyNorm ((MLDSA.Concrete.expandMask rhoDoublePrime kappa p).get j) ≤ p.gamma1
  rw [polyNorm_eq_cInfNorm]
  unfold MLDSA.Concrete.expandMask
  rw [Vector.get_ofFn]
  -- The decoder argument is an opaque SHAKE stream; the bound holds for any byte input,
  -- since `polyZUnpack p bytes = bitUnpackPoly bytes (-γ₁ + 1) γ₁`.
  exact bitUnpackPoly_z_cInfNorm_le _ p.gamma1 hwidth hq

/-! ## `w1Encode_injective` (restated to `Set.InjOn` on the valid range, now provable)

The concrete `w1Encode` packs each `High` coefficient via `simpleBitPackPoly` at the bit width
`simpleWidth ((q-1)/(2γ₂) - 1)`. On the valid commitment range — every component an actual
`highBits` output — each coefficient lies in `[0, (q-1)/(2γ₂) - 1]` (`highBits_coeff_val_lt_m`),
which fits in that bit width, so the packer is inverted by `simpleBitUnpackPoly` and is injective.
This is exactly the `Set.InjOn` predicate of the restated abstract field, since the abstract
validity set is the image of `highBits`. -/

/-- Every approved-parameter `highBits` coefficient fits in the `w₁` packer's bit width. -/
private theorem highBits_coeff_val_lt_width (hp : p.isApproved) (r : Rq) (c : Fin ringDegree) :
    ((MLDSA.Concrete.highBits p r).get c).val
      < 2 ^ MLDSA.Concrete.simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) := by
  have hlt : ((MLDSA.Concrete.highBits p r).get c).val < (modulus - 1) / (2 * p.gamma2) :=
    MLDSA.Concrete.highBits_coeff_val_lt_m p hp r c
  -- `(q-1)/(2γ₂) ≤ 2 ^ simpleWidth ((q-1)/(2γ₂) - 1)`.
  have hwin : (modulus - 1) / (2 * p.gamma2)
      ≤ 2 ^ MLDSA.Concrete.simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) := by
    rcases hp with rfl | rfl | rfl <;> decide
  omega

/-- `Primitives.Laws.w1Encode_injective` (restated to `Set.InjOn`) for the concrete instance, at any
approved parameter set: `w1Encode` is injective on commitment vectors all of whose components are
`highBits` outputs. -/
theorem concrete_w1Encode_injOn (hp : p.isApproved) :
    Set.InjOn (concretePrimitives p).w1Encode
      { w : Vector (concretePrimitives p).High p.k |
          ∀ i : Fin p.k, w.get i ∈ Set.range (concretePrimitives p).highBits } := by
  -- The concrete validity set sits inside the bit-width set on which `w1Encode_injOn` applies.
  apply Set.InjOn.mono (s₂ := { w : Vector High p.k | ∀ i : Fin p.k, ∀ c : Fin ringDegree,
      ((w.get i).get c).val
        < 2 ^ MLDSA.Concrete.simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) })
  · intro w hw i c
    obtain ⟨r, hr⟩ := hw i
    rw [show w.get i = MLDSA.Concrete.highBits p r from hr.symm]
    exact highBits_coeff_val_lt_width p hp r c
  · exact MLDSA.Concrete.w1Encode_injOn p

/-! ## Sampler-bound fields (now provable from the fuel-recursive samplers)

The `sampleInBall` and `expandS` rejection samplers are defined by fuel-bounded structural recursion
(see `Concrete/Sampling.lean`), which exposes equation lemmas. Their structural output ranges are
banked as `sampleInBall_norm` and `expandS_bound` there; the `concrete_*` wrappers below state them
at the `concretePrimitives` interface. -/

/-- `Primitives.Laws.sampleInBall_norm` for the concrete instance: `SampleInBall(c̃)` has centered
infinity norm at most `1` (its coefficients lie in `{-1, 0, +1}`). -/
theorem concrete_sampleInBall_norm (cTilde : CommitHashBytes p) :
    polyNorm ((concretePrimitives p).sampleInBall cTilde) ≤ 1 :=
  MLDSA.Concrete.sampleInBall_norm p cTilde

/-- `Primitives.Laws.expandS_bound` for the concrete instance: `ExpandS(ρ')` produces secret vectors
with every coefficient bounded by `η`. -/
theorem concrete_expandS_bound (rhoPrime : Bytes 64) :
    polyVecBounded ((concretePrimitives p).expandS rhoPrime).1 p.eta ∧
      polyVecBounded ((concretePrimitives p).expandS rhoPrime).2 p.eta :=
  MLDSA.Concrete.expandS_bound rhoPrime p

/-! ## `Primitives.Laws` status for `concretePrimitives` (no full witness — by design)

Twelve `Primitives.Laws` fields are now **proven axiom-clean** for the concrete instance at any
approved parameter set: the eight algebraic fields (`concrete_transform`,
`concrete_high_low_decomp`, `concrete_lowBits_bound`, `concrete_hide_low`,
`concrete_highBitsShift_injective`, `concrete_useHint_makeHint`, `concrete_power2Round_decomp`,
`concrete_power2Round_bound`); the two byte-encoding fields `concrete_expandMask_bound` and
`concrete_w1Encode_injOn`; and the two sampler-bound fields `concrete_sampleInBall_norm` and
`concrete_expandS_bound` (extracted by fuel induction from the structural-recursion samplers in
`Concrete/Sampling.lean`). There are no longer any false-as-stated fields.

We deliberately do **not** assemble a full `Primitives.Laws (concretePrimitives p) …` witness,
because three fields remain undischarged here for reasons that are not statement bugs:

* `sampleInBall_smul_bound`: structurally true (and trivially true once `β ≥ q/2`), but blocked by
  missing convolution-norm infrastructure — it needs the `ℓ₁` nonzero-count `‖SampleInBall‖₁ ≤ τ`
  and a generic negacyclic-convolution bound `‖f · g‖∞ ≤ ‖f‖₁ · ‖g‖∞` over centered `ZMod`
  representatives. Isolated pending that theory.
* `expandS_honest_sampling` / `keyVector_t0_determined`: inherent ROM modeling assumptions, left
  abstract (see their docstrings in `Primitives.lean`).

A `sorry`-backed aggregate witness is intentionally omitted: it would assert the still-blocked
convolution and ROM fields, which is unsound to bank. The twelve proven `concrete_*` lemmas above
stand on their own and are safe to consume. -/

end MLDSA.Concrete
