/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Concrete.Instance

/-!
# Concrete ML-DSA Primitive Laws

This file discharges the **algebraic** fields of `MLDSA.Primitives.Laws` for the concrete
`concretePrimitives` instance built from the FIPS 204 rounding and NTT layers, for any approved
parameter set. Each provable field is banked as a standalone theorem (`concrete_*`) and then
wired into a partial witness `concretePrimitivesLaws`.

## What is proven

The eight rounding/transform fields follow directly from the verified concrete rounding lemmas
in `Concrete/Rounding.lean` and the concrete NTT laws in `Concrete/NTT.lean`, bridged across the
`polyNorm` / `LatticeCrypto.cInfNorm` definitional identity (`polyNorm_eq_cInfNorm`):

- `transform`, `high_low_decomp`, `lowBits_bound`, `hide_low`, `highBitsShift_injective`,
  `useHint_makeHint`, `power2Round_decomp`, `power2Round_bound`.

## What is NOT proven (and why) — the gap in `concretePrimitivesLaws`

Five fields are left as clearly-marked `sorry` in the witness, in three honest categories:

1. **False as stated for the concrete instance** (must NOT be proven toward):
   - `expandMask_bound` (`≤ γ₁ - 1`): the concrete `expandMask` decodes via `polyZUnpack`, i.e.
     `bitUnpackPoly` on the range `[-γ₁ + 1, γ₁]`. The all-zero codeword decodes to the
     coefficient `γ₁`, whose centered representative is `γ₁ > γ₁ - 1` (ML-DSA-44:
     `centeredRepr γ₁ = 131072`). So some `(ρ'', κ)` produce a coefficient of size `γ₁`,
     violating the `γ₁ - 1` bound. This is the FIPS-204 conformance spec drift recorded in the
     gap map: the concrete decoder's upper endpoint is `γ₁`, not `γ₁ - 1`. Restating soundly
     requires either changing the concrete decode range to `[-γ₁ + 1, γ₁ - 1]` or relaxing the
     abstract bound to `γ₁` — an owner statement decision, so it is isolated rather than proven.
   - `w1Encode_injective`: `concretePrimitives.w1Encode` packs `High = Rq` (arbitrary
     coefficients) via `simpleBitPackPoly` at `simpleWidth ((modulus - 1) / (2 γ₂) - 1)` bits
     (6 bits for ML-DSA-44), keeping only the low bits of each coefficient. Distinct `High`
     vectors differing by `2^width` in a coefficient (e.g. coefficient `0` vs `64`) pack
     identically, so `w1Encode` is not injective on the full `Vector High p.k` domain. (The
     `Concrete/Encoding.lean` docstring already notes the codec is injective only on the
     FIPS-valid subset.) Injectivity holds only on the well-formed range; as a statement over
     all of `Vector High p.k` it is false.

2. **Blocked by opaque rejection samplers** (structurally true, but not extractable here):
   - `sampleInBall_norm`, `sampleInBall_smul_bound`: `concretePrimitives.sampleInBall` only
     writes the values `0`, `+1`, `-1` into its accumulator, so the output is structurally
     bounded by `1` (and has exactly `τ` nonzero `±1` coefficients). However, it does so through
     an imperative `Id.run` block with an unbounded `while !found` rejection loop reading an
     `@[extern]` SHAKE-256 stream and `Array.set!` updates. Establishing the invariant through
     that do-block is a separate imperative verification effort with no supporting infrastructure
     in the tree, so it is isolated.
   - `expandS_bound`: `concretePrimitives.expandS` samples each coefficient through
     `rejEtaCoeffs`, another `while`-loop rejection sampler over the SHAKE stream (with zero
     padding on short streams). The pushed values (`2 - u`, `4 - t`) lie in `[-η, η]`, but the
     bound is again gated behind the opaque do-block, so it is isolated for the same reason.

3. **Random-oracle modeling assumptions** (inherent to the ML-DSA security model, not derivable
   from any fixed deterministic instantiation — see their docstrings in `Primitives.lean`):
   - `expandS_honest_sampling`, `keyVector_t0_determined`: standard ROM idealizations of the
     SHAKE XOFs (`ExpandSeed` / `ExpandS`). These are model assumptions, left abstract.

The abstract `Primitives.Laws` statement is **not** modified by this file; the partial witness
simply makes explicit which concrete obligations are discharged and which remain.
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

/-! ## Partial `Primitives.Laws` witness

The eight algebraic fields above are wired in. The remaining five fields are isolated as `sorry`
with the precise reason recorded in the module docstring: `expandMask_bound` and
`w1Encode_injective` are **false as stated** for the concrete instance (FIPS conformance spec
drift / non-injective packing on the full carrier), `sampleInBall_norm` / `expandS_bound` /
`sampleInBall_smul_bound` are blocked by opaque `@[extern]` SHAKE rejection samplers, and
`expandS_honest_sampling` / `keyVector_t0_determined` are inherent ROM modeling assumptions. -/
theorem concretePrimitivesLaws (hp : p.isApproved) :
    Primitives.Laws (concretePrimitives p) concreteNTTRingOps where
  -- PROVEN algebraic fields:
  transform := concrete_transform
  high_low_decomp := concrete_high_low_decomp p
  lowBits_bound := concrete_lowBits_bound p hp
  hide_low := concrete_hide_low p hp
  highBitsShift_injective := concrete_highBitsShift_injective p hp
  useHint_makeHint := concrete_useHint_makeHint p hp
  power2Round_decomp := concrete_power2Round_decomp p
  power2Round_bound := concrete_power2Round_bound p
  -- FALSE as stated for the concrete instance (FIPS spec drift; see module docstring):
  expandMask_bound := sorry
  w1Encode_injective := sorry
  -- BLOCKED by opaque SHAKE rejection samplers (structurally true; see module docstring):
  sampleInBall_norm := sorry
  expandS_bound := sorry
  sampleInBall_smul_bound := sorry
  -- Random-oracle modeling assumptions (inherent to the model; see module docstring):
  expandS_honest_sampling := sorry
  keyVector_t0_determined := sorry

end MLDSA.Concrete
