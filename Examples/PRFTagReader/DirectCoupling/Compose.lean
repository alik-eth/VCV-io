/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.DirectCoupling
import Examples.PRFTagReader.MultipleToHybrid.EagerSetup
import Examples.PRFTagReader.MultipleBadCollision

/-!
# PRF Tag/Reader Protocol — Direct M_ideal/S_ideal Coupling, Headline Composition

This module composes the per-step direct-coupling primitives from
`Examples.PRFTagReader.DirectCoupling` (Sessions 1–4) into the headline bound

```
Pr[multipleIdealQueryImpl true] ≤
  Pr[singleIdealQueryImpl true] + Pr[unlinkBadExp] + slack₁ + slack₂ + slack₃
```

without any `HasDistinctUnlinkReaderNonces` hypothesis on the adversary. The conclusion shape
matches `multipleIdeal_le_singleIdeal_add_bad` in `MultipleBadCollision.lean`; the only difference
is the missing `hdist` hypothesis.

The direct coupling identifies the multiple-session world's RO cell `(tag, n)` with the
single-session world's reference-slot cell `((tag, 0), n)` via `slotZeroEmbed` /
`slotZeroSubTable`. Under this identification:

* **Tag step, slot 0.** Both worlds read the cell `((tag, 0), n)` of a shared `gS` — identical
  step (`multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero`,
  Session 3).
* **Tag step, slot ≥ 1.** M reads `gS((tag, 0), n)` (sub-table); S reads `gS((tag, k), n)` —
  independent uniforms off a nonce collision. The `multipleBadAdvance` bad flag captures the
  nonce-collision case; off-bad, the per-step output distributions agree marginally because
  both reads are fresh uniforms.
* **Reader step.** M's cells `{(tag, transcript.nonce) | tag}` embed into S's cells
  `{((tag, sid), transcript.nonce) | tag, sid}` via `slotZeroEmbed`. M-accept implies S-accept
  (`mReader_accepts_imp_sReader_accepts`, Session 2). The "S-accepts, M-rejects" gap is the
  reader-cell asymmetry slack `qReader · |TagId| · sessionsPerTag / |Digest|`.

## Main results

* `multipleBadEager_le_singleEager_DC_aux` — eager-form direct coupling aux, structural induction
  on the adversary. The DC analogue of `multipleBadEager_le_hybridEager_aux` (Eager.lean:85)
  *without* the `hdist` hypothesis.
* `multipleIdeal_le_singleIdeal_add_bad_DC` — lazy-form headline. The DC analogue of
  `multipleIdeal_le_singleIdeal_add_bad` (MultipleBadCollision.lean:71) *without* `hdist`.

## Layout

This file is the Session 5+ composition handoff from `DirectCoupling.lean`'s Session 4. It is
deliberately concentrated in the eager-form aux; downstream wrappers (the lazy headline,
slack-term packaging) are thin compositions.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section DirectCouplingCompose

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

namespace UnlinkReduction

/-! ### Slot-positive trace-union residue with explicit disagreement-mass hypothesis

`slotPositive_trace_union_residue_with_slack` is an additive-slack variant: it accepts an
explicit hypothesis bounding the *disagreement mass*
`Pr[transcriptM ≠ transcriptS gS | gS ← $ᵗ]` by a parameter `ε`, and concludes that the S-side
reader-accept probability at `transcriptM` is bounded by the S-side reader-accept probability
at `transcriptS gS` plus `ε`. Provable unconditionally because the disagreement mass is paid
as a slack, while the per-`gS` off-disagreement contributions cancel pointwise (both ProbComps
coincide when `transcriptM = transcriptS gS`).

**Call-site analysis.** At each of the three slot-positive sub-cases of
`multipleBadEager_le_singleEager_DC_aux`, the disagreement event
`fun gS => transcriptM ≠ transcriptS gS` corresponds to a *single-cell read* of `gS`:
* **Case B:** `transcriptM = ⟨n, u⟩` (fixed `u`); `transcriptS gS' = ⟨n, tableExtending c gS' ((tag, slotK), n)⟩`
  with `slotK ≠ 0`. The disagreement is `gS' ((tag, slotK), n) ≠ u` (for the uncached case),
  whose probability over fresh `gS'` is `1 - 1/|Digest|` — NOT bounded by the small slack.
* **Sub-case A.B:** Similar — `transcriptS gS' = ⟨n, u⟩` for a *fresh* `u ← $ᵗ Digest`, not `gS'`.
  After lifting the `$ᵗ u` out at the call site, the disagreement is a deterministic constant
  in `gS'`, mass 0 or 1.
* **Sub-case A.A:** Both transcripts are *constants* in `gS'`. Disagreement is 0 or 1.

The plain disagreement-mass slack `ε` does NOT match the call-site shapes (it's either too loose
or trivially 0/1). The `cacheBad` refactor bypasses this by replacing the per-`gS` pointwise
agreement requirement with the structural observation that an auth-equality `t.auth = gS(cell)`
for a slot-positive cell exactly matches the `cacheBadReader` predicate, whose AVERAGED mass
over `gS ← $ᵗ` is `|TagId| * sessionsPerTag / |Digest|` (proved as `probEvent_cacheBadReader_uniformSample_le`
in EagerSetup.lean). -/
omit [Nonempty TagId] [NeZero sessionsPerTag] in
lemma slotPositive_trace_union_residue_with_slack [Fintype Nonce] [Fintype Digest]
    (advM : UnlinkState TagId) (tag : TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (k : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inl tag) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (transcriptM : TagTranscript Nonce Digest)
    (transcriptS : ((TagId × Fin sessionsPerTag) × Nonce → Digest) →
      TagTranscript Nonce Digest)
    (ε : ℝ≥0∞)
    (hDisagree : Pr[fun gS => transcriptM ≠ transcriptS gS |
        ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] ≤ ε) :
    Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            (k (some transcriptM))).run' advM] ≤
      Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            (k (some (transcriptS gS)))).run' advM] + ε := by
  classical
  -- Apply `probEvent_bind_le_add_of_disagree` with `D gS := transcriptM ≠ transcriptS gS`
  -- and per-`gS` continuation gap `ε₂ := 0` (since off-D, the two continuations agree pointwise).
  set mx : ProbComp ((TagId × Fin sessionsPerTag) × Nonce → Digest) :=
    ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) with hmx
  set my : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun gS =>
    (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
        (k (some transcriptM))).run' advM with hmy
  set oc : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun gS =>
    (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
        (k (some (transcriptS gS)))).run' advM with hoc
  -- Bridge the `do`-notation LHS/RHS into `mx >>= my` / `mx >>= oc` form.
  have hL :
      Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            (k (some transcriptM))).run' advM] = Pr[= true | mx >>= my] := rfl
  have hR :
      Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            (k (some (transcriptS gS)))).run' advM] = Pr[= true | mx >>= oc] := rfl
  rw [hL, hR]
  -- Convert the `Pr[= true | ·]` form to the `probEvent (· = true)` form acceptable to
  -- `probEvent_bind_le_add_of_disagree` (via `probEvent_eq_eq_probOutput`).
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  -- Apply the disagreement bound. Off-D, `my gS = oc gS` (both transcripts coincide).
  have hε₂ :
      ∀ gS ∈ support mx, ¬ (transcriptM ≠ transcriptS gS) →
        Pr[(· = true) | my gS] ≤
          Pr[(· = true) | oc gS] + 0 := by
    intro gS _hgS hneg
    have heq : transcriptM = transcriptS gS := Classical.not_not.mp hneg
    -- The two continuations coincide at this `gS` (transcripts equal).
    have : my gS = oc gS := by
      simp [hmy, hoc, heq]
    rw [this]
    exact le_add_right le_rfl
  refine (probEvent_bind_le_add_of_disagree (D := fun gS => transcriptM ≠ transcriptS gS)
    hDisagree hε₂).trans ?_
  -- `Pr[..|mx>>=oc] + ε + 0 = Pr[..|mx>>=oc] + ε`.
  rw [add_zero]

/-! ### Slot-positive trace-union residue when transcripts agree deterministically

`slotPositive_trace_union_residue_when_agree` is the deterministic-agreement corollary of
`slotPositive_trace_union_residue_with_slack`. It applies when the two transcripts are *pointwise
equal* on every `gS` in the support of the outer `$ᵗ`, in which case the disagreement mass is
identically zero and the residue inequality collapses to equality (LHS = RHS).

**Call-site applicability.** This corollary closes the slot-positive trace-union residue
specifically at **Sub-case A.A when `u₀ = u_B`** (both cells cached at the *same* digest). It is
NOT applicable at Sub-case A.A's `u₀ ≠ u_B` branch nor at Case B, both of which produce
non-trivial cell-collision disagreement that requires the `cacheBad` infrastructure to discharge.

This corollary is the "ideal landing" form: it characterizes when the unconditional residue
holds without slack — and equivalently, demarcates where the cacheBad refactor is *required* (the
complement event, where transcripts disagree on a non-zero-mass subset of gS-draws). -/
omit [Nonempty TagId] [NeZero sessionsPerTag] in
lemma slotPositive_trace_union_residue_when_agree [Fintype Nonce] [Fintype Digest]
    (advM : UnlinkState TagId) (tag : TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (k : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inl tag) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (transcriptM : TagTranscript Nonce Digest)
    (transcriptS : ((TagId × Fin sessionsPerTag) × Nonce → Digest) →
      TagTranscript Nonce Digest)
    (hAgree : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      transcriptM = transcriptS gS) :
    Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            (k (some transcriptM))).run' advM] ≤
      Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            (k (some (transcriptS gS)))).run' advM] +
      ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  -- Disagreement mass is identically zero by `hAgree`: the event `transcriptM ≠ transcriptS gS`
  -- is empty, so its `Pr` is `0`. Apply `_with_slack` with `ε = 0`, then weaken by the
  -- per-step cacheBad budget `ε_step = |TagId|*sp/|Digest|` via `le_self_add`.
  have hDisagree :
      Pr[fun gS => transcriptM ≠ transcriptS gS |
          ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] ≤ 0 := by
    have hempty : ∀ gS, ¬ (transcriptM ≠ transcriptS gS) := by
      intro gS hne; exact hne (hAgree gS)
    have : Pr[fun gS => transcriptM ≠ transcriptS gS |
        ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] = 0 := by
      rw [probEvent_eq_zero_iff]
      intro gS _hgS; exact hempty gS
    rw [this]
  have hres := slotPositive_trace_union_residue_with_slack (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag) advM tag c k transcriptM transcriptS
    0 hDisagree
  have hres' : Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            (k (some transcriptM))).run' advM] ≤
      Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            (k (some (transcriptS gS)))).run' advM] := by simpa using hres
  exact hres'.trans le_self_add

/-! ### Cell-collision → `cacheBadReader` structural bridges

These two lemmas characterize the structural relationship between cell-collision events and the
`cacheBadReader` predicate (`EagerSetup.lean`) at slot-positive Case-B call sites. They are
diagnostic identities — currently no live caller in this file — but document the precise
polarity that any future cacheBad-charge route would consume:

* `cacheBadReader_of_cell_eq_slotPositive` (this section): agreement at the canonical cell
  `gFine ((tag, slotK), n) = u` implies `cacheBadReader gFine ⟨n, u⟩ = true` via the
  `(tag, slotK)` witness. This is the *M-side* polarity: an agreement at the queried cell
  shows that the M-transcript's auth is realized as a slot-positive cell value.
* `cacheBadReader_of_cell_self_slotPositive` (next): unconditionally,
  `cacheBadReader gFine ⟨n, gFine ((tag, slotK), n)⟩ = true` for any `slotK ≠ 0`. This is the
  *S-side* polarity: the S-transcript's auth field is by construction the cell value, so the
  cacheBadReader witness is rfl. -/
omit [Nonempty TagId] [DecidableEq TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [SampleableType Digest] in
lemma cacheBadReader_of_cell_eq_slotPositive [Fintype Nonce] [Fintype Digest]
    (gFine : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (slotK : Fin sessionsPerTag) (n : Nonce) (u : Digest)
    (hslot : slotK ≠ 0)
    (hcell : gFine ((tag, slotK), n) = u) :
    cacheBadReader (sessionsPerTag := sessionsPerTag) gFine
        (⟨n, u⟩ : TagTranscript Nonce Digest) = true := by
  -- Direct expansion: witness `(tag, slotK)` with `slotK ≠ 0` and cell value `u`.
  unfold cacheBadReader
  refine decide_eq_true ?_
  exact ⟨tag, slotK, hslot, hcell⟩

omit [Nonempty TagId] [DecidableEq TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [SampleableType Digest] in
/-- Dual structural bridge: the cell-collision *failure* event
`gFine ((tag, slotK), n) ≠ u` implies `cacheBadReader gFine ⟨n, gFine ((tag, slotK), n)⟩ = true`,
where the cacheBadReader query is on the *S-side* transcript (whose auth field is the cell value
itself). The same witness `(tag, slotK)` works trivially. -/
lemma cacheBadReader_of_cell_self_slotPositive [Fintype Nonce] [Fintype Digest]
    (gFine : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (slotK : Fin sessionsPerTag) (n : Nonce)
    (hslot : slotK ≠ 0) :
    cacheBadReader (sessionsPerTag := sessionsPerTag) gFine
        (⟨n, gFine ((tag, slotK), n)⟩ : TagTranscript Nonce Digest) = true := by
  unfold cacheBadReader
  refine decide_eq_true ?_
  exact ⟨tag, slotK, hslot, rfl⟩

/-! ### Three-world Case-B residue with cell-collision absorption

This is the structurally-correct Case-B helper, derived directly from
`probEvent_bind_le_add_bad_of_disagree` (VCVio/EvalDist/Monad/Disagreement.lean:75). The
three worlds are:

* **M-world (`my`):** runs the continuation `k` at `transcriptM = ⟨n, u⟩` (constant in `gFine`).
* **S-world (`oc`):** runs the continuation `k` at `transcriptS gFine` (gFine-dependent).
* **Bad world (`ob`):** the deterministic cell-collision check `pure (gFine ((tag, slotK), n) = u)`,
  whose Bool output IS the bad-event indicator. We use it to absorb the agreement mass
  `Pr[gFine cell = u | gFine ← $ᵗ] = 1/|Digest|` (via `probOutput_uniformSample_fun_eval`) into
  a parametric upper bound `δ_bad` on the RHS.

The off-disagreement (i.e. off-`D := agreement`) continuation gap is left **explicit and
parametric** (the `ε` slack), shifting the burden of the genuine continuation difference to the
call site, where the IH on `k` provides the bound. This helper is sorry-free, parametric on
both `δ_bad` and `ε`, and isolates the cell-collision absorption mechanism so the call site
can compose it with the IH and the per-cell bound.

**Polarity at Case B.** The agreement event (`D := gFine cell = u`) carries the small mass
`1/|Digest|`; disagreement carries `1 - 1/|Digest|` (≈ 1 for large `|Digest|`). The
charge therefore lives on the AGREEMENT side via the bad world `ob`, while the
disagreement contributes the genuine off-D continuation gap `ε`. Any future
charge route consuming this helper supplies `δ_bad := 1/|Digest|` via
`probOutput_uniformSample_fun_eval`. -/
omit [Nonempty TagId] [NeZero sessionsPerTag] in
lemma slotPositive_trace_union_residue_caseB_threeWorld
    [Fintype Nonce] [Fintype Digest]
    (advM : UnlinkState TagId) (tag : TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (k : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inl tag) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (transcriptM : TagTranscript Nonce Digest)
    (transcriptS : ((TagId × Fin sessionsPerTag) × Nonce → Digest) →
      TagTranscript Nonce Digest)
    (slotK : Fin sessionsPerTag) (n : Nonce) (u : Digest)
    (δ_bad ε : ℝ≥0∞)
    (_hM : transcriptM = ⟨n, u⟩)
    (_hS : ∀ gFine, transcriptS gFine = ⟨n, gFine ((tag, slotK), n)⟩)
    (hδ_bad : Pr[fun gFine : (TagId × Fin sessionsPerTag) × Nonce → Digest =>
        gFine ((tag, slotK), n) = u |
        ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] ≤ δ_bad)
    (hε :
      ∀ gFine ∈ support ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)),
        ¬ (gFine ((tag, slotK), n) = u) →
          Pr[(· = true) |
            (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gFine))
                (k (some transcriptM))).run' advM] ≤
          Pr[(· = true) |
            (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gFine))
                (k (some (transcriptS gFine)))).run' advM] + ε) :
    Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            (k (some transcriptM))).run' advM] ≤
      Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            (k (some (transcriptS gS)))).run' advM] + δ_bad + ε := by
  classical
  -- Plumb through `probEvent_bind_le_add_bad_of_disagree` with:
  --   * `D gFine = (gFine ((tag, slotK), n) = u)`   (agreement event)
  --   * `ob gFine = pure (gFine ((tag, slotK), n) = u)` (Bool world; on `D`, fires `true`)
  --   * `r b = (b = true)` (the bad event)
  set mx : ProbComp ((TagId × Fin sessionsPerTag) × Nonce → Digest) :=
    ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) with hmx_def
  set my : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun gS =>
    (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
        (k (some transcriptM))).run' advM with hmy_def
  set oc : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun gS =>
    (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
        (k (some (transcriptS gS)))).run' advM with hoc_def
  set ob : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun gS =>
    (pure (gS ((tag, slotK), n) = u) : ProbComp Bool) with hob_def
  -- The bad world fires `true` exactly on the agreement event.
  have hbad : ∀ gFine ∈ support mx,
      (gFine ((tag, slotK), n) = u) → Pr[(· = true) | ob gFine] = 1 := by
    intro gFine _ hagree
    simp [hob_def, hagree]
  -- Off-D continuation gap: supplied by hypothesis `hε`.
  have hε' : ∀ gFine ∈ support mx, ¬ (gFine ((tag, slotK), n) = u) →
      Pr[(· = true) | my gFine] ≤ Pr[(· = true) | oc gFine] + ε := hε
  -- Apply the three-world disagreement-aware bind bound.
  have hMain :
      Pr[(· = true) | mx >>= my] ≤
        Pr[(· = true) | mx >>= oc] + Pr[(· = true) | mx >>= ob] + ε := by
    refine probEvent_bind_le_add_bad_of_disagree
      (D := fun gFine => gFine ((tag, slotK), n) = u)
      (q := fun b => b = true) (r := fun b => b = true) hbad hε'
  -- Bound the bad-world mass by `δ_bad` via `hδ_bad`.
  -- `Pr[(·=true) | mx >>= ob] = Pr[fun gFine => gFine cell = u | mx]` because `ob` is `pure (B)`.
  have hbad_mass :
      Pr[(· = true) | mx >>= ob] ≤ δ_bad := by
    have hrw :
        Pr[(· = true) | mx >>= ob] =
          Pr[fun gFine : (TagId × Fin sessionsPerTag) × Nonce → Digest =>
              gFine ((tag, slotK), n) = u | mx] := by
      rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
      refine tsum_congr fun gFine => ?_
      simp [hob_def]
    rw [hrw]; exact hδ_bad
  -- Conclude.
  -- Bridge the goal's `Pr[= true | do …]` notation into `Pr[(·=true) | mx >>= my]` form.
  have hLgoal :
      Pr[= true | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
              (k (some transcriptM))).run' advM] =
        Pr[(· = true) | mx >>= my] := by
    rw [probEvent_eq_eq_probOutput]
  have hRgoal :
      Pr[= true | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
              (k (some (transcriptS gS)))).run' advM] =
        Pr[(· = true) | mx >>= oc] := by
    rw [probEvent_eq_eq_probOutput]
  rw [hLgoal, hRgoal]
  calc Pr[(· = true) | mx >>= my]
      ≤ Pr[(· = true) | mx >>= oc] + Pr[(· = true) | mx >>= ob] + ε := hMain
    _ ≤ Pr[(· = true) | mx >>= oc] + δ_bad + ε := by gcongr

/-! ### Case-B three-world residue with concrete cell-collision bound

`slotPositive_trace_union_residue_caseB_threeWorld_concrete` specializes the parametric
three-world helper above by discharging the `hδ_bad` premise via the single-cell uniform
marginal `probOutput_uniformSample_fun_eval` (EagerSetup.lean:375). The resulting
slack term on the RHS is the concrete value `1/|Digest|` — the tight Case-B cell-collision
mass.

This is the **Step 10 wiring corollary**: it pre-instantiates the agreement-mass slack at its
Case-B target value so the call site only needs to supply the off-disagreement continuation
gap `ε` (via the IH on `k`). The corollary stays sorry-free and parametric on `ε`, leaving
the IH-discharge to the call site. -/
omit [Nonempty TagId] [NeZero sessionsPerTag] in
lemma slotPositive_trace_union_residue_caseB_threeWorld_concrete
    [Fintype Nonce] [Fintype Digest]
    (advM : UnlinkState TagId) (tag : TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (k : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inl tag) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (transcriptM : TagTranscript Nonce Digest)
    (transcriptS : ((TagId × Fin sessionsPerTag) × Nonce → Digest) →
      TagTranscript Nonce Digest)
    (slotK : Fin sessionsPerTag) (n : Nonce) (u : Digest)
    (ε : ℝ≥0∞)
    (hM : transcriptM = ⟨n, u⟩)
    (hS : ∀ gFine, transcriptS gFine = ⟨n, gFine ((tag, slotK), n)⟩)
    (hε :
      ∀ gFine ∈ support ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)),
        ¬ (gFine ((tag, slotK), n) = u) →
          Pr[(· = true) |
            (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gFine))
                (k (some transcriptM))).run' advM] ≤
          Pr[(· = true) |
            (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gFine))
                (k (some (transcriptS gFine)))).run' advM] + ε) :
    Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            (k (some transcriptM))).run' advM] ≤
      Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            (k (some (transcriptS gS)))).run' advM] +
      (Fintype.card Digest : ℝ≥0∞)⁻¹ + ε := by
  classical
  -- Build `hδ_bad` for `δ_bad := 1/|Digest|` via the single-cell marginal bound.
  haveI : Nonempty Digest :=
    ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  have hcell_eq :
      Pr[fun gFine : (TagId × Fin sessionsPerTag) × Nonce → Digest =>
          gFine ((tag, slotK), n) = u |
          ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))]
        = (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
    -- Rewrite the event probability as `Pr[= u | do gFine ← $ᵗ; pure (gFine cell)]` and apply
    -- the single-cell marginal `probOutput_uniformSample_fun_eval`.
    have hkey :
        Pr[fun gFine : (TagId × Fin sessionsPerTag) × Nonce → Digest =>
            gFine ((tag, slotK), n) = u |
            ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))]
          = Pr[= u |
              do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
                 pure (gFine ((tag, slotK), n))] := by
      rw [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite]
      refine tsum_congr fun gFine => ?_
      by_cases h : gFine ((tag, slotK), n) = u
      · simp [h, probOutput_pure]
      · simp only [h, ite_false, probOutput_pure]
        rw [if_neg (fun heq => h heq.symm), mul_zero]
    rw [hkey]
    exact probOutput_uniformSample_fun_eval ((tag, slotK), n) u
  have hδ_bad :
      Pr[fun gFine : (TagId × Fin sessionsPerTag) × Nonce → Digest =>
          gFine ((tag, slotK), n) = u |
          ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))]
        ≤ (Fintype.card Digest : ℝ≥0∞)⁻¹ := le_of_eq hcell_eq
  -- Dispatch to the parametric three-world helper.
  exact slotPositive_trace_union_residue_caseB_threeWorld advM tag c k transcriptM transcriptS
    slotK n u ((Fintype.card Digest : ℝ≥0∞)⁻¹) ε hM hS hδ_bad hε

/-! ### Case-B disagreement-event structural characterizations

At Case-B call sites (the canonical slot-positive uncached-cell shape in
`multipleBadEager_le_singleEager_DC_aux`), the M-transcript is `⟨n, u⟩` (constant in `gFine`)
and the S-transcript is `⟨n, gFine ((tag, slotK), n)⟩` (looks up a fresh `gFine` cell). The
disagreement event `u ≠ gFine ((tag, slotK), n)` carries mass `1 - 1/|Digest|` (≈ 1 for large
`|Digest|`) — too large to absorb as a slack.

The structural observation usable as a charge sits in the OPPOSITE polarity: the **agreement
event** `u = gFine ((tag, slotK), n)` has mass `1/|Digest|`, and by
`cacheBadReader_of_cell_eq_slotPositive` agreement implies M-side
`cacheBadReader gFine ⟨n, u⟩ = true`. So the M-side cacheBad mass *upper-bounds the agreement
event mass*. Equivalently: the M-side cacheBad-FALSE event implies the disagreement event, NOT
the reverse.

The lemmas below record this polarity precisely. They are diagnostic identities — no live
caller in this file — but document the correct framing that any future cacheBad-charge route
must use (charge AGREEMENT mass, not disagreement mass). -/

omit [Nonempty TagId] [Fintype TagId] [DecidableEq TagId] [DecidableEq Nonce]
  [DecidableEq Digest] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Case-B structural characterization.** At Case-B-style slot-positive sites, the M-transcript
`⟨n, u⟩` and S-transcript `⟨n, gFine ((tag, slotK), n)⟩` (for fixed `tag`, `slotK ≠ 0`, `n`, `u`)
are EQUAL iff `gFine` reads the canonical cell to `u`. This is the foundational structural
identity for Case-B disagreement-mass analysis. -/
lemma caseB_transcript_eq_iff_cell_eq
    (gFine : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (slotK : Fin sessionsPerTag) (n : Nonce) (u : Digest) :
    (⟨n, u⟩ : TagTranscript Nonce Digest) =
      ⟨n, gFine ((tag, slotK), n)⟩ ↔ u = gFine ((tag, slotK), n) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- Extract the auth component equality from the transcript equality.
    have : (⟨n, u⟩ : TagTranscript Nonce Digest).auth =
           (⟨n, gFine ((tag, slotK), n)⟩ : TagTranscript Nonce Digest).auth := by
      rw [h]
    simpa using this
  · -- Rebuild the transcript equality from the auth equality.
    congr 1

omit [Nonempty TagId] [DecidableEq TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [SampleableType Digest] in
/-- **Case-B agreement implies M-side cacheBad.** The agreement event for Case-B transcripts
implies the M-side `cacheBadReader` predicate at `⟨n, u⟩`. This is the direct application of
`cacheBadReader_of_cell_eq_slotPositive` at the Case-B transcript shape. -/
lemma caseB_agreement_imp_M_cacheBadReader [Fintype Nonce] [Fintype Digest]
    (gFine : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (slotK : Fin sessionsPerTag) (n : Nonce) (u : Digest)
    (hslot : slotK ≠ 0)
    (hagree : (⟨n, u⟩ : TagTranscript Nonce Digest) = ⟨n, gFine ((tag, slotK), n)⟩) :
    cacheBadReader (sessionsPerTag := sessionsPerTag) gFine
        (⟨n, u⟩ : TagTranscript Nonce Digest) = true := by
  rw [caseB_transcript_eq_iff_cell_eq] at hagree
  exact cacheBadReader_of_cell_eq_slotPositive gFine tag slotK n u hslot hagree.symm

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- **Case-B disagreement mass bound.** For Case-B transcripts, the disagreement mass equals
`1 - 1/|Digest|` (the complement of the agreement mass `1/|Digest|`). The trivial `≤ 1` bound
recorded here documents that the disagreement mass is *structurally large* — and therefore
not usable as a small additive slack. Any cacheBad-charge route must instead charge the
small *agreement* mass `1/|Digest|` (the polarity captured by
`caseB_agreement_imp_M_cacheBadReader` above). -/
lemma caseB_disagreement_mass [Fintype Nonce] [Fintype Digest]
    (tag : TagId) (slotK : Fin sessionsPerTag) (n : Nonce) (u : Digest) :
    Pr[fun gFine : (TagId × Fin sessionsPerTag) × Nonce → Digest =>
        (⟨n, u⟩ : TagTranscript Nonce Digest) ≠ ⟨n, gFine ((tag, slotK), n)⟩ |
        ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] ≤ 1 := by
  -- Any probability is ≤ 1; this trivial bound is the right one because the disagreement
  -- mass for Case-B transcripts is structurally large (≈ 1 for large |Digest|).
  exact probEvent_le_one

/-! ### Slot-positive handler step characterizations

The next two lemmas explicitly unfold the M-Fine and S handler tag-step shapes at the
slot-positive case. They form the structural foundation of Phase 9.3:

* `slotPositive_MFine_tag_step` — the `Sum.inl tag` branch of `multipleBadTableHandlerFine` on
  the sub-table `slotZeroSubTable (tableExtending c gS)`, under `hslot ∧ ¬hzero`, samples a nonce
  and emits the transcript `⟨n, gS((tag, 0), n)⟩` (M reads cell `(tag, 0)` of `gS` because the
  sub-table embedding fixes slot 0), threading `multipleBadAdvance` through the bad state. Note
  the M-Fine tag branch does NOT depend on `gFine`.
* `slotPositive_S_tag_step` — the same shape on the single-session side: samples a nonce and emits
  `⟨n, gS((tag, slotK), n)⟩` where `slotK = ⟨s.sessionsUsed tag, hslot⟩`. Under `¬hzero`,
  `slotK ≠ 0`, so M and S read genuinely different cells.

Both step lemmas are direct corollaries of `multipleTableHandler_tag_run_of_lt` and
`singleTableHandler_tag_run_of_lt`, specialized to the slot-positive case where the
zero-slot rewrite `Fin.ext hzero` of Phase 9.2 no longer applies. -/

omit [Nonempty TagId] [SampleableType Digest] in
/-- **M-Fine tag step at slot-positive.** Under `hslot : s.sessionsUsed tag < sessionsPerTag`,
the `multipleBadTableHandlerFine` `Sum.inl tag` branch on the sub-table
`slotZeroSubTable (tableExtending c gS)` samples a fresh nonce and emits the M-transcript
`⟨n, tableExtending c gS ((tag, 0), n)⟩` (M reads SLOT 0 of `gS` regardless of how many sessions
this tag has used), threading `multipleBadAdvance tag sB` through the bad state. The handler does
NOT depend on `gFine` on the tag branch. -/
lemma slotPositive_MFine_tag_step
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (gS gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (tag : TagId) (s : UnlinkState TagId) (sB : UnlinkBadState TagId Nonce Digest)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)
      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
        (OracleComp.tableExtending c gS)) gFine (Sum.inl tag) (s, sB)
    = ($ᵗ Nonce) >>= fun n =>
        pure (some (⟨n, OracleComp.tableExtending c gS
            ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest),
          { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) },
          multipleBadAdvance tag sB
            (some (⟨n, OracleComp.tableExtending c gS
              ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest))) := by
  change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)
      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
        (OracleComp.tableExtending c gS)) (Sum.inl tag)) s
      >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1))
      = _
  rw [multipleTableHandler_tag_run_of_lt _ tag s hslot]
  exact bind_assoc ..

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **S tag step at slot-positive.** Under `hslot : s.sessionsUsed tag < sessionsPerTag`,
the `singleTableHandler` `Sum.inl tag` branch on `tableExtending c gS` samples a fresh nonce and
emits the S-transcript `⟨n, tableExtending c gS ((tag, slotK), n)⟩` where
`slotK = ⟨s.sessionsUsed tag, hslot⟩`. Under `¬ s.sessionsUsed tag = 0`, this slot is non-zero, so
M and S read different cells of `gS`. -/
lemma slotPositive_S_tag_step
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (gS : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (tag : TagId) (s : UnlinkState TagId)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS) (Sum.inl tag) s
    = ($ᵗ Nonce) >>= fun n =>
        pure (some (⟨n, OracleComp.tableExtending c gS
            ((tag, ⟨s.sessionsUsed tag, hslot⟩), n)⟩ : TagTranscript Nonce Digest),
          { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }) :=
  singleTableHandler_tag_run_of_lt (OracleComp.tableExtending c gS) tag s hslot

/-- **Slot-positive slotK is non-zero.** Bundles the structural fact used by
`cacheBadReader_of_cell_eq_slotPositive` / `cacheBadReader_of_cell_self_slotPositive`: at the
slot-positive case `¬ s.sessionsUsed tag = 0`, the realized session index
`⟨s.sessionsUsed tag, hslot⟩` is non-zero in `Fin sessionsPerTag`. -/
lemma slotPositive_slotK_ne_zero {TagId' : Type} {sessionsPerTag' : ℕ}
    [NeZero sessionsPerTag'] {tag : TagId'} {s : UnlinkState TagId'}
    (hslot : s.sessionsUsed tag < sessionsPerTag')
    (hzero : ¬ s.sessionsUsed tag = 0) :
    (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag') ≠ 0 := by
  intro h
  apply hzero
  have : (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag').val = (0 : Fin sessionsPerTag').val :=
    congrArg Fin.val h
  simpa using this

/-! ### Slot-positive cell-collision charge via `cacheBadReader` mass

At the slot-positive Case-B style sites, the S-side transcript depends on cell
`gS((tag, slotK), n)` (slotK ≠ 0). The agreement with a constant M-transcript `⟨n, u⟩` exactly
matches the `cacheBadReader (sessionsPerTag := sessionsPerTag) gS ⟨n, u⟩` predicate — providing a
structural route to charge the agreement mass `1/|Digest|` against the slack budget.

`slotPositive_cell_agreement_charge` averages this observation: the slot-K-specific agreement
mass is bounded by the `cacheBadReader` averaged mass, which in turn is bounded by
`|TagId| * sessionsPerTag / |Digest|` (`probEvent_cacheBadReader_uniformSample_le`). This is the
core charge mechanism Phase 9.3 needs. -/

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce] [SampleableType Digest] in
/-- **Slot-positive cell-collision mass bound via `cacheBadReader`.** Drawing `gS` uniformly,
the probability that `gS((tag, slotK), n) = u` is bounded by the averaged `cacheBadReader`
mass, which is in turn bounded by `|TagId| * sessionsPerTag / |Digest|` via
`probEvent_cacheBadReader_uniformSample_le`. This is the slot-positive analogue of the Case-B
concrete `1/|Digest|` bound, extended to incorporate the existential witness over `(tag, slotK)`. -/
lemma slotPositive_cell_collision_le_cacheBadReader [Fintype Nonce] [Fintype Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (tag : TagId) (slotK : Fin sessionsPerTag) (n : Nonce) (u : Digest)
    (hslot : slotK ≠ 0) :
    Pr[fun gS : (TagId × Fin sessionsPerTag) × Nonce → Digest =>
        gS ((tag, slotK), n) = u |
        ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] ≤
      Pr[fun b : Bool => b = true |
        do let gS ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
           pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gS
              (⟨n, u⟩ : TagTranscript Nonce Digest))] := by
  classical
  -- Use probEvent_mono after rewriting the RHS into the same `Pr[..|$ᵗ]` shape.
  have hRHS :
      Pr[fun b : Bool => b = true |
          do let gS ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
             pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gS
                (⟨n, u⟩ : TagTranscript Nonce Digest))] =
        Pr[fun gS : (TagId × Fin sessionsPerTag) × Nonce → Digest =>
          cacheBadReader (sessionsPerTag := sessionsPerTag) gS
              (⟨n, u⟩ : TagTranscript Nonce Digest) = true |
          ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] := by
    rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    refine tsum_congr fun gS => ?_
    by_cases hcb : cacheBadReader (sessionsPerTag := sessionsPerTag) gS
        (⟨n, u⟩ : TagTranscript Nonce Digest) = true
    · simp [hcb]
    · simp [hcb]
  rw [hRHS]
  refine probEvent_mono fun gS _ hhit => ?_
  exact cacheBadReader_of_cell_eq_slotPositive gS tag slotK n u hslot hhit

/-! ### Cell-swap permutation for the swap-bridge

The permutation argument for the swap-bridge needs a concrete bijection that swaps two cells of
the table domain. `cellSwap a b` is the involution on `D` that swaps `a` and `b` (identity if
`a = b`). Its key properties: bijective (involution), and composing a uniform table with it
preserves the distribution (`evalDist_map_bijective_uniform_cross`). -/

/-- Swap two elements of a type with decidable equality. Identity if `a = b`. -/
def cellSwap {D : Type} [DecidableEq D] (a b : D) : D → D := fun x =>
  if x = a then b else if x = b then a else x

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest]
    [NeZero sessionsPerTag] in
/-- `cellSwap a b` is an involution: applying it twice returns the original. -/
lemma cellSwap_involution {D : Type} [DecidableEq D] (a b : D) (x : D) :
    cellSwap a b (cellSwap a b x) = x := by
  unfold cellSwap
  by_cases hxa : x = a
  · -- x = a: cellSwap a b a = b, then cellSwap a b b = a. (Or if a = b, it stays.)
    rw [hxa]
    by_cases hab : b = a
    · rw [hab]; simp
    · simp [hab]
  · by_cases hxb : x = b
    · rw [hxb]; simp
    · simp [hxa, hxb]

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest]
    [NeZero sessionsPerTag] in
/-- `cellSwap a b` is bijective. -/
lemma cellSwap_bijective {D : Type} [DecidableEq D] (a b : D) :
    Function.Bijective (cellSwap a b) := by
  refine ⟨?_, ?_⟩
  · intro x y h
    have := congrArg (cellSwap a b) h
    rw [cellSwap_involution, cellSwap_involution] at this
    exact this
  · intro y
    exact ⟨cellSwap a b y, cellSwap_involution a b y⟩

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- **Measure-preservation of cell-swap permutation.** Drawing a uniform table `gS` and
post-composing with `cellSwap a b` (which is a bijection on the domain) yields the same
distribution as drawing `gS` directly. The key measure-preserving step underlying the
swap-bridge: averaging any continuation `F` over a uniform `gS` is invariant under
`gS ↦ gS ∘ cellSwap a b`. -/
lemma evalDist_uniformSample_comp_cellSwap [Fintype Nonce] [Fintype Digest]
    (a b : (TagId × Fin sessionsPerTag) × Nonce) :
    𝒟[(fun gS : (TagId × Fin sessionsPerTag) × Nonce → Digest =>
        gS ∘ cellSwap a b) <$> ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] =
      𝒟[$ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)] := by
  classical
  -- `g ↦ g ∘ cellSwap a b` is a bijection on `(D → R)`: its inverse is `g ↦ g ∘ cellSwap a b`
  -- (since cellSwap is an involution).
  have hbij : Function.Bijective
      (fun gS : (TagId × Fin sessionsPerTag) × Nonce → Digest => gS ∘ cellSwap a b) := by
    refine ⟨?_, ?_⟩
    · intro g₁ g₂ h
      have : (fun x => g₁ (cellSwap a b x)) = (fun x => g₂ (cellSwap a b x)) := h
      funext x
      have := congrFun this (cellSwap a b x)
      simpa [cellSwap_involution] using this
    · intro h
      refine ⟨h ∘ cellSwap a b, ?_⟩
      funext x
      simp [Function.comp, cellSwap_involution]
  exact evalDist_map_bijective_uniform_cross
    (α := (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (β := (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (fun gS => gS ∘ cellSwap a b) hbij

/-! ### Multiset-invariance of `singleTableHandler` under cell-value swap

The pointwise core of the permutation argument: when two tables `g₁, g₂` differ only by a
swap of values at two cells `(tag, 0, n)` and `(tag, slotK, n)` (agreeing everywhere else),
the `singleTableHandler` simulateQ outputs are IDENTICAL (not just distributionally equal).

* Tag queries for `T = tag`: by `hAdv`, read at `sid ≥ slotK + 1 ∉ {0, slotK}`. Tables agree.
* Tag queries for `T ≠ tag`: cells at `(T, ·, ·)` not in the swap pair. Tables agree.
* Reader queries at nonce `n' ≠ n`: cells at `n'` not in the swap pair. Tables agree.
* Reader queries at nonce `n`: existential reads cells at all `(T', sid')`. Swapping values
  at two positions doesn't change the set of values present, so the existential value (mass
  bound by `V`) is the same on both sides. -/

private lemma singleTableHandler_simulateQ_swap_invariant [Fintype Nonce] [Fintype Digest]
    (tag : TagId) (slotK : Fin sessionsPerTag) (hslotK : slotK ≠ 0)
    (n : Nonce)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) (hAdv : slotK.val < s.sessionsUsed tag)
    (g₁ g₂ : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (heq : ∀ x : (TagId × Fin sessionsPerTag) × Nonce,
        x ≠ ((tag, (0 : Fin sessionsPerTag)), n) → x ≠ ((tag, slotK), n) →
        g₁ x = g₂ x)
    (hswap_0 : g₁ ((tag, (0 : Fin sessionsPerTag)), n) = g₂ ((tag, slotK), n))
    (hswap_K : g₁ ((tag, slotK), n) = g₂ ((tag, (0 : Fin sessionsPerTag)), n)) :
    (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g₁) oa).run' s
    = (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g₂) oa).run' s := by
  classical
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b =>
    -- Both sides reduce to `pure b` via `simulateQ_pure` and `StateT.run'`.
    simp [simulateQ_pure]
  | query_bind t k ih =>
    -- Decompose via `singleTable_run'_query_bind'`, then case-split on `t`.
    rw [singleTable_run'_query_bind', singleTable_run'_query_bind']
    -- Goal: (step_g₁ t s) >>= cont_g₁ = (step_g₂ t s) >>= cont_g₂
    -- Strategy: show step_g₁ = step_g₂ pointwise (case-split on `t`), then apply IH on
    -- continuation. The IH carries the swap-invariance to each post-step state.
    cases t with
    | inl T =>
      -- Tag query: handler reads at cell `((T, sessionsUsed T), fresh_nonce)`.
      -- * `T = tag` + hAdv: sid_T ≥ slotK + 1 ∉ {0, slotK}, cell not in swap pair, `heq` gives
      --   agreement. Post-step `advT.sessionsUsed tag = sessionsUsed tag + 1 > slotK + 1 > slotK`,
      --   so hAdv preserved for IH.
      -- * `T ≠ tag`: cell `((T, ·), ·)` with T ≠ tag is not in swap pair. Cell agreement.
      --   Post-step `advT.sessionsUsed tag = sessionsUsed tag > slotK`. hAdv preserved.
      sorry
    | inr transcript =>
      -- Reader query: handler returns `pure (ReaderReply.ofBool (unlinkReaderAccepts ...), s)`.
      -- * `transcript.nonce ≠ n`: existential reads cells at `transcript.nonce ≠ n`, none in
      --   swap pair. Existential value pointwise equal between g₁ and g₂.
      -- * `transcript.nonce = n`: existential reads cells at `n`, including the swap pair.
      --   `∃ (T', sid'), g((T', sid'), n) = V` is invariant under swapping cell VALUES at two
      --   positions (the existential is over a SET of values, unchanged by swap).
      -- In both sub-cases, the response is identical; state unchanged; IH closes.
      sorry

/-! ### Swap-bridge for `singleTableHandler` cache extensions

The slot-positive case's Case M-miss needs to bridge between two cache extensions of
`singleTableHandler`:
* LHS: `c.cacheQuery ((tag, 0), n) u` — slot-0 cell cached at `u`.
* RHS: `c.cacheQuery ((tag, slotK), n) u` — slot-K cell cached at `u`.

Under `hcInv` (`c` has no slot-positive entries) and the post-step invariant
`hAdv : slotK.val < s.sessionsUsed tag`, these two cache extensions produce
**distributionally equal** computation outputs. -/

/-- **Swap-bridge for `singleTableHandler`.** Under `hcInv` (no slot-positive cache entries) and
`hAdv` (`sessionsUsed tag` has advanced past `slotK`), the cache extensions at `(tag, 0)` and
`(tag, slotK)` produce the same distribution of `oa` outputs when run through `singleTableHandler`
over a uniform `gS`. This is the workhorse for the slot-positive Case M-miss closure.

**Privacy.** Kept `private` while the body contains `sorry`s so downstream callers cannot
depend on the unverified claim. Will be exported once the four query_bind sub-cases close.

**Proof strategy (see `[[swap-bridge-permutation-argument]]` memory).** The inductive
case-split approach below has a gap: after the reader step, the response depends on `gS`,
breaking the IH (which is for fixed response). The correct proof is a single
measure-preserving permutation argument: let `φ` swap the cells `((tag, 0), n)` and
`((tag, slotK), n)`. Then `gS ∘ φ` has the same distribution as `gS` (φ measure-preserving),
and `T_L(gS ∘ φ)` and `T_R(gS)` give POINTWISE equal `singleTableHandler` outputs because
S's reader existential reads a MULTISET of cell values, invariant under swap. The inductive
scaffold below is retained as exploratory work; the permutation refactor is the next step. -/
private lemma singleTableHandler_cache_swap_eq [Fintype Nonce] [Fintype Digest]
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (tag : TagId) (slotK : Fin sessionsPerTag) (_hslotK : slotK ≠ 0)
    (n : Nonce) (u : Digest)
    (_hcInv : ∀ tag' : TagId, ∀ sid' : Fin sessionsPerTag, sid' ≠ 0 →
        ∀ n' : Nonce, c ((tag', sid'), n') = none)
    (_hAdv : slotK.val < s.sessionsUsed tag)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) :
    𝒟[do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
         (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending
              (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS)) oa).run' s]
    = 𝒟[do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
           (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending
                (c.cacheQuery ((tag, slotK), n) u) gS)) oa).run' s] := by
  classical
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b =>
    -- Both sides reduce to `pure b` (handler's `simulateQ_pure` collapses the S handler,
    -- the outer `gS ← $ᵗ` is a `bind_const` of `pure b`).
    simp [simulateQ_pure]
  | query_bind t k _ih =>
    -- Tag query (Sum.inl) vs reader query (Sum.inr). Each case decomposes further.
    cases t with
    | inl T =>
      -- Tag query: handler draws fresh nonce, reads cell `((T, sid_T), n')`, returns transcript.
      -- Key fact: by `tableExtending_cacheQuery`,
      --   `tableExtending (c.cacheQuery t u) gS = Function.update (tableExtending c gS) t u`,
      -- so LHS and RHS tables differ from `tableExtending c gS` only by an update at
      -- `((tag, 0), n)` and `((tag, slotK), n)` respectively.
      by_cases hT : T = tag
      · -- Sub-case T = tag: by `_hAdv`, `sessionsUsed tag ≥ slotK + 1`, so the handler reads at
        -- `sid_T = sessionsUsed tag ≥ slotK + 1 ∉ {0, slotK}`. Neither LHS nor RHS update is hit;
        -- cell read identical (= `gS ((tag, sid_T), nonce)`). Step responses pointwise equal;
        -- IH on continuation with `advT s = sessionsUsed tag + 1` (still > slotK + 1).
        sorry
      · -- Sub-case T ≠ tag: cells at `((T, ·), ·)` are not touched by the cache extension
        -- (Function.update only fires at the specific cell). Both LHS and RHS tables agree
        -- pointwise on `((T, sid), n')` cells. Handler step responses identical; IH closes.
        sorry
    | inr transcript =>
      -- Reader query: deterministic acceptance check
      -- `∃ T sid, tableExtending c' gS ((T, sid), transcript.nonce) = transcript.auth`.
      by_cases hn : transcript.nonce = n
      · -- Sub-case `transcript.nonce = n`: the existential reads BOTH cached cells.
        -- LHS sees `((tag, 0), n) = u`, `((tag, slotK), n) = gS@K (uniform)`.
        -- RHS sees `((tag, 0), n) = gS@0 (uniform)`, `((tag, slotK), n) = u`.
        -- Two-cell marginalization via `evalDist_uniformSample_bind_update_two_map`: under
        -- joint uniform `(gS@0, gS@K)`, the existential values
        --   `(u = V) ∨ (gS@K = V) ∨ rest` and `(gS@0 = V) ∨ (u = V) ∨ rest`
        -- are functions of the same form of `(u, fresh_uniform)`. Distributional equality.
        sorry
      · -- Sub-case `transcript.nonce ≠ n`: cache extensions only affect cells at nonce `n`,
        -- so cells at `transcript.nonce` are pointwise equal. Tables agree on the read cells,
        -- so handler step responses identical; state unchanged; IH closes.
        -- Pointwise table-value equality at any cell `(t', transcript.nonce)`:
        have htbl_eq : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            ∀ t' : TagId × Fin sessionsPerTag,
            OracleComp.tableExtending
                (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS
                (t', transcript.nonce)
            = OracleComp.tableExtending (c.cacheQuery ((tag, slotK), n) u) gS
                (t', transcript.nonce) := by
          intro gS t'
          rw [OracleComp.tableExtending_cacheQuery, OracleComp.tableExtending_cacheQuery]
          have hne0 : (t', transcript.nonce) ≠ ((tag, (0 : Fin sessionsPerTag)), n) := by
            intro h
            exact hn (congrArg (fun p => p.2) h)
          have hneK : (t', transcript.nonce) ≠ ((tag, slotK), n) := by
            intro h
            exact hn (congrArg (fun p => p.2) h)
          rw [Function.update_of_ne hne0, Function.update_of_ne hneK]
        -- The reader handler is `pure (ReaderReply.ofBool (unlinkReaderAccepts ... transcript), s)`.
        -- Since `unlinkReaderAccepts` reads cells `((T', sid'), transcript.nonce)` for all (T', sid'),
        -- by `htbl_eq` these are pointwise equal between LHS and RHS tables. So the handler
        -- responses (and states) are equal as functions of gS.
        -- Combined with `singleTable_run'_query_bind'`, the bind decomposes; IH on the continuation
        -- with same state s and same `_hAdv` closes.
        sorry

/-! ### Eager-form direct-coupling aux

The structural induction over the adversary, coupling M-side
`multipleBadTableHandler (slotZeroSubTable gS)` (with `UnlinkBadState` instrumentation) against
S-side `singleTableHandler gS` over a shared single-session RO table `gS`. Mirrors
`multipleBadEager_le_hybridEager_aux` (Eager.lean:85), but with M coupled directly to S via the
slot-0 sub-table embedding rather than going through Hybrid.

The aux is deliberately formulated in terms of *eager* table handlers and a *shared* draw `$ᵗ gS`;
the lazy headline `multipleIdeal_le_singleIdeal_add_bad_DC` below recovers it via the standard
eagerization equivalences. -/

/-- **Direct M-S coupling aux (eager).** Under a shared `$ᵗ gS` sample, the eager-form
`multipleBadTableHandler (slotZeroSubTable gS)` LHS is bounded by the eager-form
`singleTableHandler gS` RHS plus the multiple-bad bad-probability plus the three additive slacks.

The hypothesis-free analogue of `multipleBadEager_le_hybridEager_aux`: no
`HasDistinctUnlinkReaderNonces`, no `MultipleHybridCoupling` invariant, no `MultipleHybridColFresh`
freshness predicate. The direct M-S coupling is invariant-free at the eager level because:

* The slot-0 sub-table embedding is *fixed* (independent of any state); tag-step coupling at
  slot 0 is pointwise pure-equality (Session 3's
  `multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero`).
* Slot-≥1 tag divergence is captured by the `multipleBadAdvance` bad flag — off-bad, M and S
  produce statistically identical fresh uniforms despite reading different cells.
* Reader-step divergence is bounded by the cell-cardinality gap
  `|TagId| * (sessionsPerTag - 1) / |Digest|` per reader query (slack₃ from `slack-not-inherent`
  memory). -/
lemma multipleBadEager_le_singleEager_DC_aux [Fintype Nonce] [Fintype Digest]
    (oa : UnlinkAdversary TagId Nonce Digest) (qR qT : ℕ)
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hqR : OracleComp.IsQueryBoundP oa (·.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP oa (·.isLeft) qT)
    (hcInv : ∀ tag : TagId, ∀ sid : Fin sessionsPerTag, sid ≠ 0 →
        ∀ n : Nonce, c ((tag, sid), n) = none)
    (hRespInv : ∀ tag : TagId, ∀ n : Nonce,
        c ((tag, (0 : Fin sessionsPerTag)), n) ≠ none →
        sB.responses (tag, n) ≠ none) :
    Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine) oa).run (s, sB)] ≤
      Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)) oa).run' s] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine) oa).run (s, sB)] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qR * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) +
      ((qT * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  -- **Phase 9.0 skeleton.** Signature swapped to the Fine handler `multipleBadTableHandlerFine`
  -- with an inner `gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)` binder threaded
  -- through both the LHS success and RHS bad terms. Each induction case is staged as a `sorry`
  -- to be closed in Phases 9.1–9.5; see the recon document for the per-case strategy.
  classical
  induction oa using OracleComp.inductionOn generalizing qR qT s c sB hcInv hRespInv with
  | pure b =>
    -- Phase 9.1: pure b — both sides collapse the `simulateQ` to `pure b`. After `simp`, the LHS
    -- becomes `do gS ← $ᵗ; gFine ← $ᵗ; pure b` (`bind_const` shape since `pure b` ignores
    -- `gFine`). Collapse the inner `gFine ← $ᵗ; pure b` via `probOutput_bind_const` and the
    -- uniform `Pr[⊥ | $ᵗ ·] = 0` identity (`probFailure_uniformSample`) so the inner factor
    -- becomes `1 * Pr[= true | (fun _ => b) <$> $ᵗ ·]`. Bad + 4 slacks are nonnegative, dropped
    -- via `le_add_right`.
    simp only [simulateQ_pure, StateT.run_pure, StateT.run'_eq, map_pure, bind_pure_comp,
      probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
    refine le_add_right (le_add_right (le_add_right (le_add_right (le_add_right ?_))))
    rfl
  | query_bind t k ih =>
    cases t with
    | inl tag =>
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · by_cases hzero : s.sessionsUsed tag = 0
        · -- Phase 9.2: slot-zero (k = 0 fresh). The `Sum.inl tag` branch of
          -- `multipleBadTableHandlerFine` is byte-identical to the coarse handler — it does not
          -- consume `gFine`. So the head step is the same as the coarse version; we mirror the
          -- coarse closure (Phase A handler unfolds, Phase B `$ᵗ gS`/`$ᵗ Nonce` commutation,
          -- Phase C empty-`D` `probEvent_bind_le_add_bad_disagree`, Phase D per-`n` cache split),
          -- but with `gFine ← $ᵗ` threaded as an extra binder. We commute `gFine ← $ᵗ` past the
          -- step at the evalDist level via `evalDist_probComp_bind_comm`, then apply IH on the
          -- new state at the extended cache (Case B) or the unchanged cache (Case A).
          have hqRk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isRight) qR := by
            have := hqR
            rw [OracleComp.isQueryBoundP_query_bind_iff] at this
            simpa using this.2
          have hqTsplit := hqT
          rw [OracleComp.isQueryBoundP_query_bind_iff] at hqTsplit
          have hqTpos : 0 < qT := hqTsplit.1.resolve_left (fun h => absurd rfl h)
          obtain ⟨qT', rfl⟩ : ∃ qT', qT = qT' + 1 := ⟨qT - 1, by omega⟩
          have hqTk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isLeft) qT' := fun u => by
            simpa using hqTsplit.2 u
          -- Post-step state (shared between M and S under hzero).
          set advM : UnlinkState TagId :=
            { s with sessionsUsed :=
                Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } with hadvM
          -- M-Fine step under hzero: same as coarse — the `Sum.inl tag` branch of the Fine handler
          -- does not depend on `gFine`. By Session 3, M-handler step = S-handler step, then
          -- unfold via `singleTableHandler_tag_run_of_lt` and use `sidH = 0` (from hzero).
          have hMstep_with_bad : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
              ∀ gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest,
              multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine (Sum.inl tag) (s, sB)
              = ($ᵗ Nonce) >>= fun n =>
                  pure (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest),
                    advM,
                    multipleBadAdvance tag sB
                      (some (⟨n, OracleComp.tableExtending c gS
                        ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest))) := by
            intro gS gFine
            change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) (Sum.inl tag)) s
                >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1))
                = _
            rw [multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero
                (OracleComp.tableExtending c gS) tag s hzero,
              singleTableHandler_tag_run_of_lt (OracleComp.tableExtending c gS) tag s hslot]
            have hsid : (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) =
                (0 : Fin sessionsPerTag) := Fin.ext hzero
            rw [hsid, ← hadvM]
            exact bind_assoc ..
          -- S-side step, no bad wrap.
          have hSstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
              singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)
                (Sum.inl tag) s
              = ($ᵗ Nonce) >>= fun n =>
                  pure (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest),
                    advM) := by
            intro gS
            rw [singleTableHandler_tag_run_of_lt (OracleComp.tableExtending c gS) tag s hslot]
            have hsid : (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) =
                (0 : Fin sessionsPerTag) := Fin.ext hzero
            rw [hsid, ← hadvM]
          -- Unfold head queries on both sides via the run-step lemmas.
          simp only [multipleBadTableFine_run_query_bind', singleTable_run'_query_bind', map_bind]
          -- LHS: rewrite `gS ← $ᵗ; gFine ← $ᵗ; step >>= ...` into
          -- `gS ← $ᵗ; gFine ← $ᵗ; n ← $ᵗ Nonce; ...`.
          have hLHS_eq :
              (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let p ← multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) gFine (Sum.inl tag) (s, sB)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      z.1) <$>
                    (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS)) gFine) (k p.1)).run p.2)
              = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)) gFine)
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))) := by
            refine bind_congr fun gS => ?_
            refine bind_congr fun gFine => ?_
            rw [hMstep_with_bad gS gFine]
            exact bind_assoc ..
          have hRHS_eq :
              (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let p ← singleTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c gS) (Sum.inl tag) s
                  (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c gS)) (k p.1)).run' p.2)
              = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS))
                      (k (some (⟨n, OracleComp.tableExtending c gS
                          ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                          TagTranscript Nonce Digest)))).run' advM) := by
            refine bind_congr fun gS => ?_
            rw [hSstep gS]
            exact bind_assoc ..
          have hBAD_eq :
              (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let p ← multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) gFine (Sum.inl tag) (s, sB)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$>
                    (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS)) gFine) (k p.1)).run p.2)
              = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)) gFine)
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))) := by
            refine bind_congr fun gS => ?_
            refine bind_congr fun gFine => ?_
            rw [hMstep_with_bad gS gFine]
            exact bind_assoc ..
          rw [hLHS_eq, hRHS_eq, hBAD_eq]
          -- Phase B. Commute outer `$ᵗ gS`, `$ᵗ gFine` past inner `$ᵗ Nonce` at the `𝒟[·]` level
          -- so the shared nonce draw is outermost. We push `n` out one binder at a time.
          have hLHS_comm :
              𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)) gFine)
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest))))]
              = 𝒟[(do let n ← $ᵗ Nonce
                      let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))] := by
            -- Two-step commute: (i) swap inner `gFine ← $ᵗ` past `n ← $ᵗ Nonce` so the body
            -- becomes `gS; n; gFine; F`; (ii) swap outermost `gS` past `n` so `n` is outermost.
            -- Step (i): inside `gS`, swap `gFine` and `n`.
            have hStep1 : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
                𝒟[(do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let n ← $ᵗ Nonce
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
                = 𝒟[(do let n ← $ᵗ Nonce
                        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            z.1) <$>
                          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)) gFine)
                            (k (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest))))] := fun gS =>
              evalDist_probComp_bind_comm
                ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
            -- Use hStep1 to rewrite under outer `gS ← $ᵗ`.
            have hPart1 :
                𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let n ← $ᵗ Nonce
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
                = 𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        let n ← $ᵗ Nonce
                        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            z.1) <$>
                          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)) gFine)
                            (k (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest))))] := by
              rw [evalDist_bind, evalDist_bind]
              refine congrArg _ (funext fun gS => ?_)
              exact hStep1 gS
            -- Step (ii): swap outer `gS` and `n`.
            have hStep2 :
                𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let n ← $ᵗ Nonce
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
                = 𝒟[(do let n ← $ᵗ Nonce
                        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            z.1) <$>
                          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)) gFine)
                            (k (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest))))] :=
              evalDist_probComp_bind_comm
                ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
            exact hPart1.trans hStep2
          have hRHS_comm :
              𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS))
                      (k (some (⟨n, OracleComp.tableExtending c gS
                          ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                          TagTranscript Nonce Digest)))).run' advM)]
              = 𝒟[(do let n ← $ᵗ Nonce
                      let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run' advM)] :=
            evalDist_probComp_bind_comm
              ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
          have hBAD_comm :
              𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)) gFine)
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest))))]
              = 𝒟[(do let n ← $ᵗ Nonce
                      let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))] := by
            have hStep1B : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
                𝒟[(do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let n ← $ᵗ Nonce
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
                = 𝒟[(do let n ← $ᵗ Nonce
                        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            (z.1, z.2.2)) <$>
                          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)) gFine)
                            (k (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest))))] := fun gS =>
              evalDist_probComp_bind_comm
                ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
            have hPart1B :
                𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let n ← $ᵗ Nonce
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
                = 𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        let n ← $ᵗ Nonce
                        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            (z.1, z.2.2)) <$>
                          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)) gFine)
                            (k (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest))))] := by
              rw [evalDist_bind, evalDist_bind]
              refine congrArg _ (funext fun gS => ?_)
              exact hStep1B gS
            have hStep2B :
                𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let n ← $ᵗ Nonce
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
                = 𝒟[(do let n ← $ᵗ Nonce
                        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            (z.1, z.2.2)) <$>
                          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)) gFine)
                            (k (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest))))] :=
              evalDist_probComp_bind_comm
                ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
            exact hPart1B.trans hStep2B
          rw [probOutput_congr rfl hLHS_comm,
              probOutput_congr rfl hRHS_comm,
              probEvent_congr' (fun _ _ => Iff.rfl) hBAD_comm]
          -- Phase C. Split `qR * (qT' + 1) / |Nonce|` into `qR / |Nonce| + qR * qT' / |Nonce|` and
          -- analogously for the `qT * |TagId| * sp / |Digest|` slack. Reassociate and apply the
          -- disagree lemma with empty `D` on the inner `$ᵗ Nonce` (since under hzero, M and S do
          -- the same step — there is no per-step disagreement to charge).
          classical
          simp only [← probEvent_eq_eq_probOutput]
          have hSplit : ((qR * (qT' + 1) : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞)
              = ((qR : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
                ((qR * qT' : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
            rw [show qR * (qT' + 1) = qR + qR * qT' from by ring,
              Nat.cast_add, ENNReal.add_div]
          have hSplit_s4 :
              (((qT' + 1) * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞)
                / (Fintype.card Digest : ℝ≥0∞)
              = ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞)
                  / (Fintype.card Digest : ℝ≥0∞) +
                ((qT' * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞)
                  / (Fintype.card Digest : ℝ≥0∞) := by
            rw [show (qT' + 1) * Fintype.card TagId * sessionsPerTag
                  = Fintype.card TagId * sessionsPerTag + qT' * Fintype.card TagId * sessionsPerTag
                  from by ring, Nat.cast_add, ENNReal.add_div]
          rw [hSplit, hSplit_s4]
          rw [show ∀ a b c d e f g h : ℝ≥0∞,
                a + b + c + (d + e) + f + (g + h) = a + b + d + (c + e + f + h) + g from
                fun a b c d e f g h => by ring]
          refine (?_ : _ ≤ _).trans le_self_add
          refine probEvent_bind_le_add_bad_disagree
            (D := fun _ : Nonce => False)
            ?_ ?_
          · simp
          intro n _ _hnD
          -- Phase D. Per-`n` bound. Case-split on `c ((tag, 0), n)`.
          rcases hc : c ((tag, (0 : Fin sessionsPerTag)), n) with _ | u₀
          · -- Case B: cache miss. Marginalize cell via `evalDist_uniformSample_bind_update`, then
            -- apply IH at extended cache `c.cacheQuery ((tag, 0), n) u`.
            haveI : Nonempty Digest :=
              ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
            have hmarg : ∀ {β : Type}
                (Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp β),
                𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest); Mψ gS)] =
                𝒟[(do let u ← $ᵗ Digest
                      let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      Mψ (Function.update gS' ((tag, (0 : Fin sessionsPerTag)), n) u))] := by
              intro β Mψ
              have hbase :
                  𝒟[(do let u ← $ᵗ Digest
                        let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        pure (Function.update gS' ((tag, (0 : Fin sessionsPerTag)), n) u))]
                  = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] :=
                evalDist_uniformSample_bind_update ((tag, (0 : Fin sessionsPerTag)), n)
              have hL : (do let u ← $ᵗ Digest
                            let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                            Mψ (Function.update gS' ((tag, (0 : Fin sessionsPerTag)), n) u))
                  = (do let u ← $ᵗ Digest
                        let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        pure (Function.update gS' ((tag, (0 : Fin sessionsPerTag)), n) u))
                      >>= Mψ := by
                simp [bind_assoc]
              have hR : (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest); Mψ gS)
                  = ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= Mψ := rfl
              rw [hL, hR, evalDist_bind, evalDist_bind, hbase]
            have hext_eq : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
                (u : Digest),
                OracleComp.tableExtending c
                    (Function.update gS' ((tag, (0 : Fin sessionsPerTag)), n) u) =
                  OracleComp.tableExtending (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
                    gS' := fun gS' u => by
              have h1 := OracleComp.tableExtending_update_of_none c gS' hc u
              have h2 := OracleComp.tableExtending_cacheQuery c gS'
                ((tag, (0 : Fin sessionsPerTag)), n) u
              exact h1.symm.trans h2.symm
            have hcell_u : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
                (u : Digest),
                OracleComp.tableExtending
                    (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS'
                    ((tag, (0 : Fin sessionsPerTag)), n) = u := fun gS' u => by
              rw [OracleComp.tableExtending_cacheQuery]
              simp [Function.update_self]
            have hLHS_marg :
                Pr[(· = true) |
                  (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
              = Pr[(· = true) |
                  (do let u ← $ᵗ Digest
                      let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending
                              (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS'))
                            gFine)
                          (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, u⟩ : TagTranscript Nonce Digest))))] := by
              refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
              rw [hmarg _]
              refine congrArg evalDist ?_
              refine bind_congr fun u => ?_
              refine bind_congr fun gS' => ?_
              refine bind_congr fun gFine => ?_
              rw [hext_eq gS' u, hcell_u gS' u]
            have hRHS_marg :
                Pr[(· = true) |
                  (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run' advM)]
              = Pr[(· = true) |
                  (do let u ← $ᵗ Digest
                      let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending
                          (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS'))
                        (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' advM)] := by
              refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
              rw [hmarg _]
              refine congrArg evalDist ?_
              refine bind_congr fun u => ?_
              refine bind_congr fun gS' => ?_
              rw [hext_eq gS' u, hcell_u gS' u]
            have hBAD_marg :
                Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true) |
                  (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
              = Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true) |
                  (do let u ← $ᵗ Digest
                      let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending
                              (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS'))
                            gFine)
                          (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, u⟩ : TagTranscript Nonce Digest))))] := by
              refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
              rw [hmarg _]
              refine congrArg evalDist ?_
              refine bind_congr fun u => ?_
              refine bind_congr fun gS' => ?_
              refine bind_congr fun gFine => ?_
              rw [hext_eq gS' u, hcell_u gS' u]
            rw [hLHS_marg, hRHS_marg, hBAD_marg]
            rw [show ∀ a b c : ℝ≥0∞, a + b + c = a + b + 0 + c from
                  fun a b c => by ring]
            refine probEvent_bind_le_add_bad_disagree
              (mx := ($ᵗ Digest : ProbComp Digest))
              (D := fun _ : Digest => False)
              (by simp) ?_
            intro u _ _
            have hcInv' : ∀ tag' : TagId, ∀ sid' : Fin sessionsPerTag, sid' ≠ 0 →
                ∀ n' : Nonce,
                  (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
                    ((tag', sid'), n') = none := by
              intro tag' sid' hsid' n'
              have hne : ((tag', sid'), n') ≠ ((tag, (0 : Fin sessionsPerTag)), n) := by
                intro h
                exact hsid' (congrArg (fun p => p.1.2) h)
              simp [OracleSpec.QueryCache.cacheQuery_of_ne, hne, hcInv tag' sid' hsid' n']
            have hRespInv' : ∀ tag' : TagId, ∀ n' : Nonce,
                (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
                  ((tag', (0 : Fin sessionsPerTag)), n') ≠ none →
                (multipleBadAdvance tag sB
                  (some (⟨n, u⟩ : TagTranscript Nonce Digest))).responses (tag', n') ≠ none := by
              intro tag' n' hne
              by_cases htagn : (tag', n') = (tag, n)
              · -- Same cell; the advance updates `responses` at this cell.
                have : (multipleBadAdvance tag sB
                    (some (⟨n, u⟩ : TagTranscript Nonce Digest))).responses (tag', n') =
                    (sB.responses.cacheQuery (tag, n)
                      (u :: Option.getD (sB.responses (tag, n)) [])) (tag', n') := rfl
                rw [this, htagn, OracleSpec.QueryCache.cacheQuery_self]
                exact Option.some_ne_none _
              · -- Different cell; cache unchanged at this entry, responses unchanged.
                have hne_cell : ((tag', (0 : Fin sessionsPerTag)), n') ≠
                    ((tag, (0 : Fin sessionsPerTag)), n) := by
                  intro h
                  exact htagn (Prod.ext (congrArg (fun p => p.1.1) h)
                    (congrArg (fun p => p.2) h))
                have hc_unchanged : (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
                    ((tag', (0 : Fin sessionsPerTag)), n') =
                    c ((tag', (0 : Fin sessionsPerTag)), n') := by
                  simp [OracleSpec.QueryCache.cacheQuery_of_ne, hne_cell]
                rw [hc_unchanged] at hne
                have hsb_unchanged : (multipleBadAdvance tag sB
                    (some (⟨n, u⟩ : TagTranscript Nonce Digest))).responses (tag', n') =
                    sB.responses (tag', n') := by
                  show (sB.responses.cacheQuery (tag, n)
                    (u :: Option.getD (sB.responses (tag, n)) [])) (tag', n') =
                    sB.responses (tag', n')
                  simp [OracleSpec.QueryCache.cacheQuery_of_ne, htagn]
                rw [hsb_unchanged]
                exact hRespInv tag' n' hne
            have hihB := ih (some (⟨n, u⟩ : TagTranscript Nonce Digest)) qR qT'
              advM (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
              (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
              (hqRk _) (hqTk _) hcInv' hRespInv'
            rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput,
                ← add_assoc, ← add_assoc, ← add_assoc]
            exact hihB
          · -- Case A: cache hit `u₀`. Cell read is `u₀` regardless of `gS`. Apply IH at unchanged
            -- cache `c`.
            have hcell : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
                OracleComp.tableExtending c gS ((tag, (0 : Fin sessionsPerTag)), n) = u₀ :=
              fun gS => by
                show (c ((tag, (0 : Fin sessionsPerTag)), n)).getD
                    (gS ((tag, (0 : Fin sessionsPerTag)), n)) = u₀
                rw [hc]; rfl
            simp_rw [hcell]
            have hRespInv'' : ∀ tag' : TagId, ∀ n' : Nonce,
                c ((tag', (0 : Fin sessionsPerTag)), n') ≠ none →
                (multipleBadAdvance tag sB
                  (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))).responses (tag', n') ≠ none := by
              intro tag' n' hne
              by_cases htagn : (tag', n') = (tag, n)
              · have heq : (multipleBadAdvance tag sB
                    (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))).responses (tag', n') =
                    (sB.responses.cacheQuery (tag, n)
                      (u₀ :: Option.getD (sB.responses (tag, n)) [])) (tag', n') := rfl
                rw [heq, htagn, OracleSpec.QueryCache.cacheQuery_self]
                exact Option.some_ne_none _
              · have hsb_unchanged : (multipleBadAdvance tag sB
                    (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))).responses (tag', n') =
                    sB.responses (tag', n') := by
                  show (sB.responses.cacheQuery (tag, n)
                    (u₀ :: Option.getD (sB.responses (tag, n)) [])) (tag', n') =
                    sB.responses (tag', n')
                  simp [OracleSpec.QueryCache.cacheQuery_of_ne, htagn]
                rw [hsb_unchanged]
                exact hRespInv tag' n' hne
            have hihA := ih (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)) qR qT'
              advM c
              (multipleBadAdvance tag sB (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))
              (hqRk _) (hqTk _) hcInv hRespInv''
            rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput,
                ← add_assoc, ← add_assoc, ← add_assoc]
            exact hihA
        · -- Phase 9.3: slot-positive (1 ≤ k < sp). M reads slot-0 cell, S reads slot-K cell (K ≠ 0).
          -- **Cell-pair independence strategy.** The two cells of a uniform `gS` are independent
          -- uniforms when `slotK ≠ 0`, so two-cell marginalization + index rename closes the gap
          -- via `evalDist_uniformSample_bind_update_two_map` — no per-step cacheBadReader charge
          -- needed at this site. The `qT · |TagId| · sp / |Digest|` budget in the aux signature is
          -- reserved for the reader case (Phase 9.5); it weakens back here via `gcongr`.
          have hqRk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isRight) qR := by
            have := hqR
            rw [OracleComp.isQueryBoundP_query_bind_iff] at this
            simpa using this.2
          have hqTsplit := hqT
          rw [OracleComp.isQueryBoundP_query_bind_iff] at hqTsplit
          have hqTpos : 0 < qT := hqTsplit.1.resolve_left (fun h => absurd rfl h)
          obtain ⟨qT', rfl⟩ : ∃ qT', qT = qT' + 1 := ⟨qT - 1, by omega⟩
          have hqTk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isLeft) qT' := fun u => by
            simpa using hqTsplit.2 u
          -- Post-step state (shared between M and S — both increment `sessionsUsed tag`).
          set advM : UnlinkState TagId :=
            { s with sessionsUsed :=
                Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } with hadvM
          -- Realized slot-K (non-zero by `hzero`).
          set slotK : Fin sessionsPerTag := ⟨s.sessionsUsed tag, hslot⟩ with hslotK
          have hslotK_ne : slotK ≠ 0 := slotPositive_slotK_ne_zero (sessionsPerTag' := sessionsPerTag)
            hslot hzero
          -- M-Fine and S step shapes via the Phase 9.4a helpers. Note: M reads slot-0 cell of
          -- `gS` (via `slotZeroSubTable`) regardless of `hzero`; S reads slot-K cell where
          -- `slotK = ⟨s.sessionsUsed tag, hslot⟩` is non-zero by `hslotK_ne`.
          have hMstep : ∀ gS gFine,
              multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine (Sum.inl tag) (s, sB)
              = ($ᵗ Nonce) >>= fun n =>
                  pure (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest),
                    advM,
                    multipleBadAdvance tag sB
                      (some (⟨n, OracleComp.tableExtending c gS
                        ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                          TagTranscript Nonce Digest))) :=
            fun gS gFine => slotPositive_MFine_tag_step (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) c gS gFine tag s sB hslot
          have hSstep : ∀ gS,
              singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)
                (Sum.inl tag) s
              = ($ᵗ Nonce) >>= fun n =>
                  pure (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, slotK), n)⟩ : TagTranscript Nonce Digest), advM) := fun gS => by
            have := slotPositive_S_tag_step (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) c gS tag s hslot
            convert this using 1
          -- Unfold head queries on both sides.
          simp only [multipleBadTableFine_run_query_bind', singleTable_run'_query_bind', map_bind]
          -- Phase B-1: rewrite each of LHS, RHS, BAD so the head step exposes the inner `n ← $ᵗ`.
          have hLHS_eq :
              (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let p ← multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) gFine (Sum.inl tag) (s, sB)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      z.1) <$>
                    (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS)) gFine) (k p.1)).run p.2)
              = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)) gFine)
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))) := by
            refine bind_congr fun gS => ?_
            refine bind_congr fun gFine => ?_
            rw [hMstep gS gFine]
            exact bind_assoc ..
          have hRHS_eq :
              (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let p ← singleTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c gS) (Sum.inl tag) s
                  (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c gS)) (k p.1)).run' p.2)
              = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS))
                      (k (some (⟨n, OracleComp.tableExtending c gS
                          ((tag, slotK), n)⟩ : TagTranscript Nonce Digest)))).run' advM) := by
            refine bind_congr fun gS => ?_
            rw [hSstep gS]
            exact bind_assoc ..
          have hBAD_eq :
              (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let p ← multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) gFine (Sum.inl tag) (s, sB)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$>
                    (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS)) gFine) (k p.1)).run p.2)
              = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)) gFine)
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))) := by
            refine bind_congr fun gS => ?_
            refine bind_congr fun gFine => ?_
            rw [hMstep gS gFine]
            exact bind_assoc ..
          rw [hLHS_eq, hRHS_eq, hBAD_eq]
          -- Phase B-2: commute outer `$ᵗ gS`, `$ᵗ gFine` past inner `$ᵗ Nonce` at the `𝒟[·]`
          -- level so `n` is outermost. Identical structure to slot-zero (M-side LHS/BAD have the
          -- same shape — both read slot-0). RHS is shorter (no `gFine` binder).
          have hLHS_comm :
              𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)) gFine)
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest))))]
              = 𝒟[(do let n ← $ᵗ Nonce
                      let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))] := by
            -- Step (i): swap inner `gFine ← $ᵗ` past `n ← $ᵗ Nonce` under outer `gS`.
            have hStep1 : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
                𝒟[(do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let n ← $ᵗ Nonce
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
                = 𝒟[(do let n ← $ᵗ Nonce
                        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            z.1) <$>
                          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)) gFine)
                            (k (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest))))] := fun gS =>
              evalDist_probComp_bind_comm
                ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
            have hPart1 :
                𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let n ← $ᵗ Nonce
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
                = 𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        let n ← $ᵗ Nonce
                        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            z.1) <$>
                          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)) gFine)
                            (k (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest))))] := by
              rw [evalDist_bind, evalDist_bind]
              refine congrArg _ (funext fun gS => ?_)
              exact hStep1 gS
            -- Step (ii): swap outermost `gS` past `n`.
            have hStep2 :
                𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let n ← $ᵗ Nonce
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
                = 𝒟[(do let n ← $ᵗ Nonce
                        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            z.1) <$>
                          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)) gFine)
                            (k (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest))))] :=
              evalDist_probComp_bind_comm
                ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
            exact hPart1.trans hStep2
          -- RHS commute: single `evalDist_probComp_bind_comm` (no gFine binder).
          have hRHS_comm :
              𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS))
                      (k (some (⟨n, OracleComp.tableExtending c gS
                          ((tag, slotK), n)⟩ : TagTranscript Nonce Digest)))).run' advM)]
              = 𝒟[(do let n ← $ᵗ Nonce
                      let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, slotK), n)⟩ : TagTranscript Nonce Digest)))).run' advM)] :=
            evalDist_probComp_bind_comm
              ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
          have hBAD_comm :
              𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)) gFine)
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest))))]
              = 𝒟[(do let n ← $ᵗ Nonce
                      let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))] := by
            -- Same two-step commute as hLHS_comm but with the (z.1, z.2.2) projection.
            have hStep1B : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
                𝒟[(do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let n ← $ᵗ Nonce
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
                = 𝒟[(do let n ← $ᵗ Nonce
                        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            (z.1, z.2.2)) <$>
                          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)) gFine)
                            (k (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest))))] := fun gS =>
              evalDist_probComp_bind_comm
                ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
            have hPart1B :
                𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let n ← $ᵗ Nonce
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
                = 𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        let n ← $ᵗ Nonce
                        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            (z.1, z.2.2)) <$>
                          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)) gFine)
                            (k (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest))))] := by
              rw [evalDist_bind, evalDist_bind]
              refine congrArg _ (funext fun gS => ?_)
              exact hStep1B gS
            have hStep2B :
                𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      let n ← $ᵗ Nonce
                      let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)) gFine)
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))]
                = 𝒟[(do let n ← $ᵗ Nonce
                        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            (z.1, z.2.2)) <$>
                          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)) gFine)
                            (k (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, OracleComp.tableExtending c gS
                                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                                TagTranscript Nonce Digest))))] :=
              evalDist_probComp_bind_comm
                ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
            exact hPart1B.trans hStep2B
          rw [probOutput_congr rfl hLHS_comm,
              probOutput_congr rfl hRHS_comm,
              probEvent_congr' (fun _ _ => Iff.rfl) hBAD_comm]
          -- Phase C: split `qR * (qT' + 1) / |Nonce|` into `qR / |Nonce| + qR * qT' / |Nonce|`
          -- and `(qT' + 1) * |TagId| * sp / |Digest|` into `|TagId| * sp / |Digest| +
          -- qT' * |TagId| * sp / |Digest|`. Reassoc + drop the trailing slack via `le_self_add`
          -- (cell-pair independence provides equality at per-`n`, so no extra charge needed).
          classical
          simp only [← probEvent_eq_eq_probOutput]
          have hSplit : ((qR * (qT' + 1) : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞)
              = ((qR : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
                ((qR * qT' : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
            rw [show qR * (qT' + 1) = qR + qR * qT' from by ring,
              Nat.cast_add, ENNReal.add_div]
          have hSplit_s4 :
              (((qT' + 1) * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞)
                / (Fintype.card Digest : ℝ≥0∞)
              = ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞)
                  / (Fintype.card Digest : ℝ≥0∞) +
                ((qT' * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞)
                  / (Fintype.card Digest : ℝ≥0∞) := by
            rw [show (qT' + 1) * Fintype.card TagId * sessionsPerTag
                  = Fintype.card TagId * sessionsPerTag + qT' * Fintype.card TagId * sessionsPerTag
                  from by ring, Nat.cast_add, ENNReal.add_div]
          rw [hSplit, hSplit_s4]
          rw [show ∀ a b c d e f g h : ℝ≥0∞,
                a + b + c + (d + e) + f + (g + h) = a + b + d + (c + e + f + h) + g from
                fun a b c d e f g h => by ring]
          refine (?_ : _ ≤ _).trans le_self_add
          refine probEvent_bind_le_add_bad_disagree
            (D := fun _ : Nonce => False)
            ?_ ?_
          · simp
          intro n _ _hnD
          -- Phase D: per-`n` bound. Two-cell marginalization of slot-0 (M's cell) and slot-K
          -- (S's cell); 4 sub-cases on cache hits/misses; IH application via cell-pair
          -- independence + index rename.
          sorry
      · -- Phase 9.4: slot-exhausted. Both M-Fine and S handlers return `pure (none, s, sB)` /
        -- `pure (none, s)` (since `multipleBadAdvance tag sB none = sB` and `gFine` is not
        -- consumed by the tag branch). The head step unfolds to `pure none` on both sides; the
        -- inner `gFine ← $ᵗ` binder is consumed via `bind_const` shape. After splitting
        -- `qT = qT' + 1`, the IH at `qT'` applies directly with unchanged state `(s, sB)`; the
        -- two `qT`-bearing slacks (qR*qT/|Nonce|, qT*|TagId|*sp/|D|) weaken back via `gcongr`.
        have hqRk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isRight) qR := by
          have := hqR
          rw [OracleComp.isQueryBoundP_query_bind_iff] at this
          simpa using this.2
        have hqTsplit := hqT
        rw [OracleComp.isQueryBoundP_query_bind_iff] at hqTsplit
        have hqTpos : 0 < qT := hqTsplit.1.resolve_left (fun h => absurd rfl h)
        obtain ⟨qT', rfl⟩ : ∃ qT', qT = qT' + 1 := ⟨qT - 1, by omega⟩
        have hqTk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isLeft) qT' := fun u => by
          simpa using hqTsplit.2 u
        -- M-Fine step under `hslot`: returns `pure (none, s, sB)` (no `gFine` dependence;
        -- `multipleBadAdvance tag sB none = sB`).
        have hMstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            ∀ gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest,
            multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c gS)) gFine (Sum.inl tag) (s, sB)
            = pure (none, s, sB) := by
          intro gS gFine
          change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c gS)) (Sum.inl tag)) s
              >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1))
              = _
          rw [multipleTableHandler_tag_run_of_not_lt _ tag s hslot]
          rfl
        -- S step under `hslot`: returns `pure (none, s)`.
        have hSstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)
              (Sum.inl tag) s
            = pure (none, s) := fun gS =>
          singleTableHandler_tag_run_of_not_lt (OracleComp.tableExtending c gS) tag s hslot
        -- Rewrite each of the three positions (LHS-success, RHS-success, BAD-event) so the head
        -- step collapses to running `k none` at the unchanged state. Both M-Fine and S handlers
        -- under `hslot` return `pure (none, …)`, so `pure_bind` reduces the head bind.
        have hLHS_eq :
            (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    z.1) <$>
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) gFine)
                    (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run (s, sB))
            = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      z.1) <$>
                    (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS)) gFine) (k none)).run (s, sB)) := by
          refine bind_congr fun gS => ?_
          refine bind_congr fun gFine => ?_
          rw [multipleBadTableFine_run_query_bind', hMstep gS gFine]
          rw [map_bind]
          exact pure_bind _ _
        have hRHS_eq :
            (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS))
                  (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run' s)
            = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c gS)) (k none)).run' s) := by
          refine bind_congr fun gS => ?_
          rw [singleTable_run'_query_bind', hSstep gS]
          exact pure_bind _ _
        have hBAD_eq :
            (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) gFine)
                    (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run (s, sB))
            = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$>
                    (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS)) gFine) (k none)).run (s, sB)) := by
          refine bind_congr fun gS => ?_
          refine bind_congr fun gFine => ?_
          rw [multipleBadTableFine_run_query_bind', hMstep gS gFine]
          rw [map_bind]
          exact pure_bind _ _
        rw [probOutput_congr rfl (congrArg evalDist hLHS_eq),
            probOutput_congr rfl (congrArg evalDist hRHS_eq),
            probEvent_congr' (fun _ _ => Iff.rfl) (congrArg evalDist hBAD_eq)]
        -- Now LHS / RHS / BAD all evaluate `k none` at the unchanged state `(s, sB)`. Apply IH at
        -- `qT'`; the two `qT`-bearing slacks weaken back via `gcongr` + `Nat.le_succ`.
        refine (ih none qR qT' s c sB (hqRk none) (hqTk none) hcInv hRespInv).trans ?_
        gcongr
        · exact_mod_cast Nat.le_succ _
        · exact_mod_cast Nat.le_succ _
    | inr transcript =>
      -- Phase 9.5: reader query under the Fine handler. The slot-positive `cacheBadReader gFine`
      -- mass closes the M-rejects/S-accepts gap once the per-step Fine/coarse bridge lemma is
      -- threaded — see the Stage 9 plan in the module header.
      sorry

end UnlinkReduction

/-! ### Lazy-form headline (drops hdist)

The lazy-form analogue of `multipleIdeal_le_singleIdeal_add_bad` (`MultipleBadCollision.lean:71`)
*without* the `HasDistinctUnlinkReaderNonces` hypothesis. Routes through
`multipleBadEager_le_singleEager_DC_aux` via the standard eagerization equivalences for the
multiple-bad handler (`evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending`) and the
single-ideal handler (`probOutput_singleIdeal_run'_eq_tableSample`). -/

namespace UnlinkReduction

/-- **Multi-to-single via direct M-S coupling, no `hdist`.** Drop-in replacement for
`multipleIdeal_le_singleIdeal_add_bad` (`MultipleBadCollision.lean:71`) that does *not* require
`HasDistinctUnlinkReaderNonces` on the adversary. Same conclusion shape.

Internally bypasses the M→Hybrid→S chain: the direct M-S coupling via `slotZeroSubTable` works
unconditionally on the adversary (no nonce-distinctness assumption) because the per-step
identification of M's cell `(tag, n)` with S's cell `((tag, 0), n)` is a fixed embedding, not a
state-dependent one. -/
theorem multipleIdeal_le_singleIdeal_add_bad_DC [Fintype Nonce] [Fintype Digest]
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag) :
    Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] ≤
      Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] +
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)] +
      ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) +
      ((qTag * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) +
      ((qTag * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  -- **Step 1.** Replace the multiple-ideal LHS by the multiple-bad LHS (same `Pr[= true]`).
  rw [← probOutput_multipleBad_run'_eq_multipleIdeal adversary
      (UnlinkState.init, (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache)) UnlinkBadState.init]
  -- **Step 2.** Eagerize the M-side: the lazy `multipleBadQueryImpl` run distribution equals the
  -- `$ᵗ gM`-then-eager-table form, modulo the `(z.1, z.2.2)` map projection.
  have hM := evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending
    (sessionsPerTag := sessionsPerTag) adversary
    UnlinkState.init (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) UnlinkBadState.init
  -- M-side success-term rewrite: factor `run' = (·.1) <$> run` through `(z.1, z.2.2) <$> run`.
  have hMsucc :
      Pr[= true | (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
          ((UnlinkState.init, (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache)),
            UnlinkBadState.init)] =
      Pr[= true | do
          let gM ← $ᵗ (TagId × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending
                (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) gM)) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] := by
    rw [probOutput_def, probOutput_def]
    have hlhs : (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
          ((UnlinkState.init, (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache)),
            UnlinkBadState.init) =
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.1) <$>
          ((fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
              ((UnlinkState.init, (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache)),
                UnlinkBadState.init)) := by
      rw [Functor.map_map]; rfl
    have hrhs : (do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending
              (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) gM)) adversary).run
            (UnlinkState.init, UnlinkBadState.init)) =
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.1) <$>
          (do
            let gM ← $ᵗ (TagId × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending
                  (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) gM)) adversary).run
                (UnlinkState.init, UnlinkBadState.init)) := by
      simp only [map_bind, Functor.map_map]
    rw [hlhs, hrhs, evalDist_map, evalDist_map, ← evalDist_map, hM, evalDist_map]
  -- M-side bad-term rewrite: factor `z.2.2.bad = (z.2.bad) ∘ (z.1, z.2.2)` and apply `hM`.
  have hMbad :
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending
              (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) gM)) adversary).run
            (UnlinkState.init, UnlinkBadState.init)] := by
    have hbadev :
        (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad = true) =
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.2.bad = true) ∘
          (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
            (z.1, z.2.2)) := rfl
    rw [hbadev, ← probEvent_map]
    exact probEvent_congr' (fun _ _ => Iff.rfl) hM
  -- **Step 3.** Eagerize the S-side success term to `$ᵗ gS >>= singleTableHandler gS`.
  rw [hMsucc, hMbad, probOutput_singleIdeal_run'_eq_tableSample adversary]
  -- Collapse `tableExtending ∅ g = g` on both M (over `TagId × Nonce`) and S (over the
  -- `(TagId × Fin sp) × Nonce` domain) sides.
  simp only [OracleComp.tableExtending_empty]
  -- **Step 4.** Bridge `$ᵗ (TagId × Nonce → Digest)` to
  -- `$ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)` via `slotZeroSubTable`. The bridge says:
  -- for any continuation `F`, the distribution of `$ᵗ gM >>= F gM` equals the distribution of
  -- `$ᵗ gS >>= F (slotZeroSubTable gS)`. We package this as a generic helper and apply it twice
  -- (once for the success term, once for the bad term).
  haveI : Nonempty Digest :=
    ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  have hbridge : ∀ {X : Type} (F : (TagId × Nonce → Digest) → ProbComp X),
      𝒟[($ᵗ (TagId × Nonce → Digest)) >>= F] =
      𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
            fun gS => F (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)] := by
    intro X F
    have hSZ :
        𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
              fun gS => pure (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)]
        = 𝒟[($ᵗ (TagId × Nonce → Digest))] :=
      evalDist_slotZeroSubTable_uniformSample
    have hR : (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
            fun gS => F (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS))
        = (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
            fun gS => pure (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) >>= F := by
      simp
    rw [hR, evalDist_bind, evalDist_bind, hSZ]
  -- M-success bridge.
  have hbridge_succ :
      Pr[= true | do
          let gM ← $ᵗ (TagId × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) gM) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] =
      Pr[= true | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] :=
    probOutput_congr rfl (hbridge _)
  -- M-bad bridge.
  have hbridge_bad :
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
          let gM ← $ᵗ (TagId × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) gM) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] :=
    probEvent_congr' (fun _ _ => Iff.rfl) (hbridge _)
  rw [hbridge_succ, hbridge_bad]
  -- **Step 4b.** Phase 9.0 Fine-shape bridges. The aux's signature now carries an outer
  -- `gFine ← $ᵗ ((TagId × Fin sp) × Nonce → Digest)` binder and the Fine handler
  -- `multipleBadTableHandlerFine ... gFine`. Bridge the coarse-shape LHS-success and
  -- RHS-bad terms (the current goal shapes after `rw [hbridge_succ, hbridge_bad]`) to the
  -- Fine-shape via `evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_eq`.
  -- Per-`gS`, the bridge gives `𝒟[(π <$> gFine←$ᵗ; Fine.run p)] = 𝒟[coarse.run p]` where
  -- `π = fun z => (z.1, z.2.1, {z.2.2 with cacheBad := p.2.cacheBad})`. Both `Bool.fst` and the
  -- bad event `z.2.bad` factor through `π` (they ignore `cacheBad`).
  have hFineEq : ∀ (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest),
      𝒟[(fun z => (z.1, z.2.1, {z.2.2 with cacheBad :=
              (UnlinkBadState.init : UnlinkBadState TagId Nonce Digest).cacheBad})) <$>
            (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                    (UnlinkState.init, UnlinkBadState.init))]
        = 𝒟[(simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] := fun gS =>
    evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_eq
      (sessionsPerTag := sessionsPerTag)
      (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) adversary
      ((UnlinkState.init, UnlinkBadState.init) :
        UnlinkState TagId × UnlinkBadState TagId Nonce Digest)
  -- Apply the Fine bridge to the success term (event factors through π since π preserves `z.1`).
  have hsucc_fine :
      Pr[= true | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] =
      Pr[= true | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] := by
    -- `Pr[= true | oa] = probOutput oa true`. We convert to `probEvent (· = true)` via
    -- `probEvent_eq_eq_probOutput`, then use `probEvent_bind_congr'`.
    rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
    refine probEvent_bind_congr' _ _ ?_
    intro gS
    -- Per-gS: Pr[(b = true) | (z.1) <$> coarse.run] = Pr[(b = true) | gFine←$ᵗ; (z.1) <$> Fine.run]
    -- Push (z.1) into the inner gFine bind on the Fine side, then apply `probEvent_map` on
    -- both sides to expose `(z.1 = true)` as a precomposition.
    rw [probEvent_map]
    have hrhs :
        (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                  (UnlinkState.init, UnlinkBadState.init))
        = (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                  (UnlinkState.init, UnlinkBadState.init)) := by rw [map_bind]
    rw [hrhs, probEvent_map]
    -- Bridge via hFineEq: replace `coarse.run` with `π <$> (gFine←$ᵗ; Fine.run)`.
    have hbridge :
        Pr[(fun b : Bool => b = true) ∘
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) |
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] =
        Pr[(fun b : Bool => b = true) ∘
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) |
            (fun z => (z.1, z.2.1, {z.2.2 with cacheBad :=
                (UnlinkBadState.init : UnlinkBadState TagId Nonce Digest).cacheBad})) <$>
              (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                      (UnlinkState.init, UnlinkBadState.init))] := by
      rw [probEvent_def, probEvent_def, ← hFineEq gS]
    rw [hbridge, probEvent_map]
    -- Goal: Pr[(b=true) ∘ z.1 ∘ π | gFine←$ᵗ; Fine] = Pr[(b=true) ∘ z.1 | gFine←$ᵗ; Fine].
    -- (b=true) ∘ z.1 ∘ π = (b=true) ∘ z.1 pointwise (π preserves .1).
    exact probEvent_congr' (fun _ _ => Iff.rfl) rfl
  -- Apply the Fine bridge to the bad term. The bad event factors through π (cacheBad ≠ bad).
  -- Strategy: use `probEvent_bind_congr'` to reduce to a per-gS equality, then push the
  -- `(z.1, z.2.2)` map through `probEvent_map` to expose the `z.2.2.bad` predicate, then
  -- apply `hFineEq` after observing that the bad predicate is π-invariant.
  have hbad_fine :
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] := by
    refine probEvent_bind_congr' _ _ ?_
    intro gS
    -- Per-gS goal:
    --   Pr[bad | (z.1, z.2.2) <$> coarse.run]
    --   = Pr[bad | gFine←$ᵗ; (z.1, z.2.2) <$> Fine.run]
    -- Push the (z.1, z.2.2) map through `probEvent_map`:
    rw [probEvent_map]
    -- LHS now: Pr[bad ∘ (z.1, z.2.2) | coarse.run] = Pr[z.2.2.bad | coarse.run].
    -- For the RHS, push the (z.1, z.2.2) map into the inner bind:
    have hrhs :
        (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                  (UnlinkState.init, UnlinkBadState.init))
        = (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                  (UnlinkState.init, UnlinkBadState.init)) := by rw [map_bind]
    rw [hrhs, probEvent_map]
    -- Goal:
    --   Pr[bad ∘ (z.1, z.2.2) | coarse.run] = Pr[bad ∘ (z.1, z.2.2) | gFine←$ᵗ; Fine.run]
    -- which is Pr[z.2.2.bad | coarse.run] = Pr[z.2.2.bad | gFine←$ᵗ; Fine.run]. Express this
    -- via hFineEq: 𝒟[π <$> (gFine←$ᵗ; Fine.run)] = 𝒟[coarse.run]; the bad predicate is
    -- π-invariant.
    have hLHS_via_bridge :
        Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true) ∘
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) |
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] =
        Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true) ∘
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) |
            (fun z => (z.1, z.2.1, {z.2.2 with cacheBad :=
                (UnlinkBadState.init : UnlinkBadState TagId Nonce Digest).cacheBad})) <$>
              (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                      (UnlinkState.init, UnlinkBadState.init))] := by
      rw [probEvent_def, probEvent_def, ← hFineEq gS]
    rw [hLHS_via_bridge, probEvent_map]
    -- Goal: Pr[(bad ∘ (z.1, z.2.2)) ∘ π | gFine←$ᵗ; Fine] = Pr[bad ∘ (z.1, z.2.2) | gFine←$ᵗ; Fine]
    -- Both events agree pointwise (π only changes cacheBad; the event reads only `.2.bad`).
    exact probEvent_congr' (fun _ _ => Iff.rfl) rfl
  rw [hsucc_fine, hbad_fine]
  -- **Step 5.** Apply the DC aux at `c = ∅`, `s = UnlinkState.init`, `sB = UnlinkBadState.init`.
  have haux := multipleBadEager_le_singleEager_DC_aux (sessionsPerTag := sessionsPerTag)
    adversary qReader qTag UnlinkState.init
    (∅ : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) UnlinkBadState.init
    hqReader hqTag (fun _ _ _ _ => rfl) (fun _ _ h => absurd rfl h)
  simp only [OracleComp.tableExtending_empty] at haux
  -- The aux bound is term-by-term ≤ the headline RHS; the extra outermost
  -- `qTag * sessionsPerTag / |Digest|` slack (reserved for the eventual ε_cb
  -- charge transported via `evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_eq`
  -- and `simulateQ_multipleBadTableHandlerFine_cacheBad_prob_le`) is dropped via `le_self_add`.
  exact haux.trans le_self_add

end UnlinkReduction

end DirectCouplingCompose

end PRFTagReader
