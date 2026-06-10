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

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest]
    [NeZero sessionsPerTag] in
/-- `cellSwap a b` sends `b` to `a`. -/
@[simp] lemma cellSwap_right {D : Type} [DecidableEq D] (a b : D) : cellSwap a b b = a := by
  unfold cellSwap
  by_cases hab : b = a <;> simp [hab]

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest]
    [NeZero sessionsPerTag] in
/-- `cellSwap a b` fixes any element distinct from both `a` and `b`. -/
lemma cellSwap_of_ne {D : Type} [DecidableEq D] (a b : D) {x : D} (hxa : x ≠ a) (hxb : x ≠ b) :
    cellSwap a b x = x := by
  simp [cellSwap, hxa, hxb]

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

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- **Bind-level measure-preservation via `cellSwap`.** For any continuation
`F : (table) → ProbComp α`, drawing a uniform `gS` and applying `F` to `gS` has the same
distribution as drawing a uniform `gS` and applying `F` to `gS ∘ cellSwap a b`. Direct
consequence of `evalDist_uniformSample_comp_cellSwap` combined with `map_bind`. -/
lemma evalDist_uniformSample_bind_cellSwap [Fintype Nonce] [Fintype Digest]
    {α : Type} (a b : (TagId × Fin sessionsPerTag) × Nonce)
    (F : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp α) :
    𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest); F gS)] =
      𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest);
            F (gS ∘ cellSwap a b))] := by
  classical
  have hMapBind :
      ((fun gS : (TagId × Fin sessionsPerTag) × Nonce → Digest => gS ∘ cellSwap a b) <$>
            ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))) >>= F =
      (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest);
          F (gS ∘ cellSwap a b)) := by
    simp [map_eq_bind_pure_comp, bind_assoc, Function.comp]
  rw [← hMapBind, evalDist_bind, evalDist_bind,
      evalDist_uniformSample_comp_cellSwap (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) a b]

/-! ### Region-swap exchange of two uniform tables

Where `cellSwap` permutes two individual cells of a single table, `regionSwap P` exchanges the
values of *two* tables `g, h : D → R` on the region `{x | P x}` while keeping them in place on the
complement. The M-side of the direct coupling reads the shared table only through slot-`0` cells
and reads the fine-grained table only through slot-positive cells; exchanging the slot-positive
regions of the two tables is a measure-preserving involution of the joint uniform draw that leaves
the M-world's distribution unchanged while relocating the `cacheBad`-read cells onto the shared
table. -/

/-- Exchange the values of two tables `g, h : D → R` on the region `{x | P x}`, leaving them in
place on the complement. The first component reads `h` on `P` and `g` off `P`; the second reads
`g` on `P` and `h` off `P`. With `P` everywhere false this is the identity pair `(g, h)`; with `P`
everywhere true it is the swap `(h, g)`. -/
def regionSwap {D R : Type} (P : D → Prop) [DecidablePred P]
    (g h : D → R) : (D → R) × (D → R) :=
  (fun x => if P x then h x else g x, fun x => if P x then g x else h x)

/-- `regionSwap P` is an involution on the pair: applying the underlying map twice returns the
original pair `(g, h)`. -/
lemma regionSwap_involution {D R : Type} (P : D → Prop) [DecidablePred P] (g h : D → R) :
    regionSwap P (regionSwap P g h).1 (regionSwap P g h).2 = (g, h) := by
  unfold regionSwap
  ext x <;> simp <;> by_cases hx : P x <;> simp [hx]

/-- On the region `P`, the first component of `regionSwap P g h` reads `h`. -/
@[simp] lemma regionSwap_fst_of_pos {D R : Type} (P : D → Prop) [DecidablePred P]
    (g h : D → R) {x : D} (hx : P x) : (regionSwap P g h).1 x = h x := by
  simp [regionSwap, hx]

/-- Off the region `P`, the first component of `regionSwap P g h` reads `g`. -/
@[simp] lemma regionSwap_fst_of_neg {D R : Type} (P : D → Prop) [DecidablePred P]
    (g h : D → R) {x : D} (hx : ¬ P x) : (regionSwap P g h).1 x = g x := by
  simp [regionSwap, hx]

/-- On the region `P`, the second component of `regionSwap P g h` reads `g`. -/
@[simp] lemma regionSwap_snd_of_pos {D R : Type} (P : D → Prop) [DecidablePred P]
    (g h : D → R) {x : D} (hx : P x) : (regionSwap P g h).2 x = g x := by
  simp [regionSwap, hx]

/-- Off the region `P`, the second component of `regionSwap P g h` reads `h`. -/
@[simp] lemma regionSwap_snd_of_neg {D R : Type} (P : D → Prop) [DecidablePred P]
    (g h : D → R) {x : D} (hx : ¬ P x) : (regionSwap P g h).2 x = h x := by
  simp [regionSwap, hx]

/-- The uncurried region-swap map `(g, h) ↦ regionSwap P g h` is bijective, being its own
inverse by `regionSwap_involution`. The measure-preserving bijection underlying
`evalDist_uniformSample_pair_regionSwap`. -/
lemma regionSwap_uncurry_bijective {D R : Type} (P : D → Prop) [DecidablePred P] :
    Function.Bijective (fun gh : (D → R) × (D → R) => regionSwap P gh.1 gh.2) := by
  refine ⟨fun x y h => ?_, fun y => ⟨_, regionSwap_involution P y.1 y.2⟩⟩
  have hx := regionSwap_involution P x.1 x.2
  rw [(show regionSwap P x.1 x.2 = regionSwap P y.1 y.2 from h),
      regionSwap_involution P y.1 y.2] at hx
  exact (Prod.ext (congrArg Prod.fst hx) (congrArg Prod.snd hx)).symm

/-- The uncurried region-swap map packaged as an `Equiv`, with itself as inverse. -/
noncomputable def regionSwapEquiv {D R : Type} (P : D → Prop) [DecidablePred P] :
    ((D → R) × (D → R)) ≃ ((D → R) × (D → R)) where
  toFun p := regionSwap P p.1 p.2
  invFun p := regionSwap P p.1 p.2
  left_inv p := by have := regionSwap_involution P p.1 p.2; simpa using this
  right_inv p := by have := regionSwap_involution P p.1 p.2; simpa using this

@[simp] lemma regionSwapEquiv_apply {D R : Type} (P : D → Prop) [DecidablePred P]
    (p : (D → R) × (D → R)) : regionSwapEquiv P p = regionSwap P p.1 p.2 := rfl

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- **Joint measure-preservation of region-swap.** Drawing two independent uniform tables `gS` and
`gFine` and exchanging their values on the region `P` (via `regionSwap P`) yields the same joint
distribution as drawing them directly, as observed by any continuation `F`. The joint uniform draw
on the table pair is invariant under the involution `(gS, gFine) ↦ regionSwap P gS gFine`, which is
a bijection on the product `(D → Digest) × (D → Digest)`. -/
lemma evalDist_uniformSample_pair_regionSwap [Fintype Nonce] [Finite Digest] {α : Type}
    (P : ((TagId × Fin sessionsPerTag) × Nonce) → Prop) [DecidablePred P]
    (F : (((TagId × Fin sessionsPerTag) × Nonce) → Digest) →
         (((TagId × Fin sessionsPerTag) × Nonce) → Digest) → ProbComp α) :
    𝒟[(do let gS ← $ᵗ (((TagId × Fin sessionsPerTag) × Nonce) → Digest)
          let gFine ← $ᵗ (((TagId × Fin sessionsPerTag) × Nonce) → Digest)
          F (regionSwap P gS gFine).1 (regionSwap P gS gFine).2)]
    = 𝒟[(do let gS ← $ᵗ (((TagId × Fin sessionsPerTag) × Nonce) → Digest)
            let gFine ← $ᵗ (((TagId × Fin sessionsPerTag) × Nonce) → Digest)
            F gS gFine)] := by
  classical
  letI := Fintype.ofFinite Digest
  refine evalDist_ext fun z => ?_
  have hexpand : ∀ G : (((TagId × Fin sessionsPerTag) × Nonce) → Digest) →
        (((TagId × Fin sessionsPerTag) × Nonce) → Digest) → ProbComp α,
      Pr[= z | (do let gS ← $ᵗ (((TagId × Fin sessionsPerTag) × Nonce) → Digest)
                   let gFine ← $ᵗ (((TagId × Fin sessionsPerTag) × Nonce) → Digest); G gS gFine)]
      = ∑' p : (((TagId × Fin sessionsPerTag) × Nonce) → Digest) ×
              (((TagId × Fin sessionsPerTag) × Nonce) → Digest),
          (Fintype.card (((TagId × Fin sessionsPerTag) × Nonce) → Digest) : ℝ≥0∞)⁻¹ *
          ((Fintype.card (((TagId × Fin sessionsPerTag) × Nonce) → Digest) : ℝ≥0∞)⁻¹ *
            Pr[= z | G p.1 p.2]) := by
    intro G
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_prod']
    refine tsum_congr fun gS => ?_
    rw [probOutput_uniformSample _ gS, probOutput_bind_eq_tsum, ENNReal.tsum_mul_left]
    refine congrArg _ (tsum_congr fun gFine => ?_)
    rw [probOutput_uniformSample _ gFine]
  rw [hexpand (fun gS gFine => F (regionSwap P gS gFine).1 (regionSwap P gS gFine).2), hexpand F]
  rw [← Equiv.tsum_eq (regionSwapEquiv (R := Digest) P)]
  refine tsum_congr fun p => ?_
  rw [regionSwapEquiv_apply, regionSwap_involution]

/-! ### Slot-positive region and M-world congruences

`slotPositiveCell` is the slot-positive region of the fine table domain: the cells `((T, sid), n)`
with `sid ≠ 0`. The M-world reads the shared table `gS` only through slot-`0` cells (via
`slotZeroSubTable (tableExtending c gS)`) and reads `gFine` only through slot-positive cells (via
`cacheBadReader` inside `multipleBadTableHandlerFine`). The three congruence lemmas below record
that each of these reads depends only on the relevant region, which is what makes the region-swap
exchange leave the M-world distribution unchanged. -/

/-- The slot-positive region of the fine-table domain: cells `((T, sid), n)` with `sid ≠ 0`. -/
def slotPositiveCell : ((TagId × Fin sessionsPerTag) × Nonce) → Prop := fun x => x.1.2 ≠ 0

instance : DecidablePred (slotPositiveCell (TagId := TagId) (Nonce := Nonce)
    (sessionsPerTag := sessionsPerTag)) := fun x => by unfold slotPositiveCell; infer_instance

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
    [SampleableType Nonce] in
/-- `slotPositiveCell` holds at `((T, sid), n)` exactly when `sid ≠ 0`. -/
@[simp] lemma slotPositiveCell_apply (T : TagId) (sid : Fin sessionsPerTag) (n : Nonce) :
    slotPositiveCell (TagId := TagId) (Nonce := Nonce) (sessionsPerTag := sessionsPerTag)
      ((T, sid), n) ↔ sid ≠ 0 := Iff.rfl

omit [Fintype TagId] [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
    [DecidableEq Digest] [SampleableType Digest] in
/-- **Slot-`0` agreement determines the M sub-table.** If `gS` and `gS'` agree on all slot-`0`
cells then their slot-`0` sub-tables (after overlaying the cache `c`) coincide, because
`slotZeroSubTable` reads each table only at slot `0`. -/
lemma slotZeroSubTable_tableExtending_eq_of_agree_zero
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (gS gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (h : ∀ (T : TagId) (n : Nonce),
        gS ((T, (0 : Fin sessionsPerTag)), n) = gS' ((T, 0), n)) :
    slotZeroSubTable (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)
    = slotZeroSubTable (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS') := by
  funext p
  obtain ⟨T, n⟩ := p
  simp only [slotZeroSubTable, Function.comp, slotZeroEmbed, OracleComp.tableExtending, h T n]

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
    [SampleableType Digest] in
/-- **Slot-positive agreement determines `cacheBadReader`.** If `gFine` and `gFine'` agree on all
slot-positive cells then `cacheBadReader` reads the same value at every transcript, since its
existential witness ranges only over slot-positive cells. -/
lemma cacheBadReader_eq_of_agree_pos
    (gFine gFine' : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (h : ∀ (T : TagId) (sid : Fin sessionsPerTag), sid ≠ 0 → ∀ n : Nonce,
        gFine ((T, sid), n) = gFine' ((T, sid), n))
    (t : TagTranscript Nonce Digest) :
    cacheBadReader (sessionsPerTag := sessionsPerTag) gFine t
    = cacheBadReader (sessionsPerTag := sessionsPerTag) gFine' t := by
  unfold cacheBadReader
  rw [decide_eq_decide]
  exact ⟨fun ⟨tag, sid, hsid, heq⟩ => ⟨tag, sid, hsid, (h tag sid hsid t.nonce) ▸ heq⟩,
    fun ⟨tag, sid, hsid, heq⟩ => ⟨tag, sid, hsid, (h tag sid hsid t.nonce).symm ▸ heq⟩⟩

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Slot-positive congruence of the fine handler.** If `gFine` and `gFine'` agree on all
slot-positive cells then `multipleBadTableHandlerFine g gFine` and `… g gFine'` are equal as
`QueryImpl`s: the tag branch ignores `gFine`, and the reader branch reaches it only through
`cacheBadReader`, which agrees by `cacheBadReader_eq_of_agree_pos`. As a function equality this
transports through `simulateQ`-runs by `congrArg`/`rw`, so no separate induction lemma is needed. -/
lemma multipleBadTableHandlerFine_congr_pos
    (g : TagId × Nonce → Digest)
    (gFine gFine' : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (h : ∀ (T : TagId) (sid : Fin sessionsPerTag), sid ≠ 0 → ∀ n : Nonce,
        gFine ((T, sid), n) = gFine' ((T, sid), n)) :
    multipleBadTableHandlerFine (sessionsPerTag := sessionsPerTag) g gFine
    = multipleBadTableHandlerFine (sessionsPerTag := sessionsPerTag) g gFine' := by
  funext q p
  cases q with
  | inl tag => rfl
  | inr transcript =>
    unfold multipleBadTableHandlerFine
    simp only [multipleBadReaderAdvance, cacheBadReader_eq_of_agree_pos gFine gFine' h transcript]

/-! ### M-world exchange invariance

Combining the joint measure-preservation `evalDist_uniformSample_pair_regionSwap` with the
slot-`0` congruence yields the M-world exchange identity: replacing `gFine` by the slot-positive
half of `gS` (the second component of `regionSwap slotPositiveCell gS gFine`) leaves the
distribution of the fine M-run unchanged. -/

omit [Nonempty TagId] in
/-- **M-world region-swap invariance.** Drawing `gS, gFine` and running the fine M-handler over the
slot-`0` sub-table of `gS` against `gFine` has the same distribution as running it against the
slot-positive half of `gS` (the `regionSwap`-relocated table `(regionSwap slotPositiveCell gS
gFine).2`), which agrees with `gS` on every slot-positive cell.

Intended Phase 9.5 use: after this exchange, the reader-step `cacheBad` flag reads the same
slot-positive cells of `gS` that the single-session reader existential reads, so the M-side
`cacheBad`-mass can be matched against the S-side reader gap on the shared table. -/
lemma evalDist_MFineRun_regionSwap_invariant [Fintype Nonce] [Fintype Digest] {β : Type}
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) β)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    𝒟[(do let gS ← $ᵗ (((TagId × Fin sessionsPerTag) × Nonce) → Digest)
          let gFine ← $ᵗ (((TagId × Fin sessionsPerTag) × Nonce) → Digest)
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine) oa).run p)]
    = 𝒟[(do let gS ← $ᵗ (((TagId × Fin sessionsPerTag) × Nonce) → Digest)
            let gFine ← $ᵗ (((TagId × Fin sessionsPerTag) × Nonce) → Digest)
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c gS))
              (regionSwap slotPositiveCell gS gFine).2) oa).run p)] := by
  rw [← evalDist_uniformSample_pair_regionSwap (Digest := Digest) slotPositiveCell
      (fun gS gFine =>
        (simulateQ (multipleBadTableHandlerFine (sessionsPerTag := sessionsPerTag)
          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending c gS)) gFine) oa).run p)]
  have hbody : ∀ gS gFine : (((TagId × Fin sessionsPerTag) × Nonce) → Digest),
      (simulateQ (multipleBadTableHandlerFine (sessionsPerTag := sessionsPerTag)
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c (regionSwap slotPositiveCell gS gFine).1))
        (regionSwap slotPositiveCell gS gFine).2) oa).run p
      = (simulateQ (multipleBadTableHandlerFine (sessionsPerTag := sessionsPerTag)
          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending c gS))
          (regionSwap slotPositiveCell gS gFine).2) oa).run p := by
    intro gS gFine
    rw [slotZeroSubTable_tableExtending_eq_of_agree_zero c
          (regionSwap slotPositiveCell gS gFine).1 gS
          (fun T n => regionSwap_fst_of_neg slotPositiveCell gS gFine
            (by rw [slotPositiveCell_apply]; simp))]
  simp only [hbody]

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

omit [Nonempty TagId] [SampleableType Digest] in
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
      -- Case-split on whether T's session budget is available.
      by_cases hslot : s.sessionsUsed T < sessionsPerTag
      · -- Free slot: step samples nonce, reads cell, advances state.
        rw [singleTableHandler_tag_run_of_lt _ T s hslot,
            singleTableHandler_tag_run_of_lt _ T s hslot]
        -- Cell read is `((T, ⟨sessionsUsed T, hslot⟩), nonce)`. Show this is NOT in the swap pair.
        have hcell_ne : ∀ nonce : Nonce,
            ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce)
              ≠ ((tag, (0 : Fin sessionsPerTag)), n) ∧
            ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce)
              ≠ ((tag, slotK), n) := by
          intro nonce
          refine ⟨?_, ?_⟩
          · -- Differs from (tag, 0, n): either T ≠ tag, or sid > 0.
            intro h
            by_cases hT : T = tag
            · -- T = tag: by hAdv, sessionsUsed tag > slotK > 0, so sid > 0 ≠ 0.
              subst hT
              have hsidpos : 0 < s.sessionsUsed T := by
                have : (slotK : ℕ) < s.sessionsUsed T := hAdv
                exact Nat.lt_of_le_of_lt (Nat.zero_le _) this
              have hsid : s.sessionsUsed T = 0 := by
                have := congrArg (fun p => (p.1.2 : Fin sessionsPerTag).val) h
                simpa using this
              omega
            · -- T ≠ tag: first components differ.
              exact hT (congrArg (fun p => p.1.1) h)
          · -- Differs from (tag, slotK, n): either T ≠ tag, or sid ≠ slotK.
            intro h
            by_cases hT : T = tag
            · subst hT
              have : (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag) = slotK := by
                exact (congrArg (fun p => (p.1.2 : Fin sessionsPerTag)) h)
              have hsid : s.sessionsUsed T = slotK.val := by
                exact congrArg Fin.val this
              omega
            · exact hT (congrArg (fun p => p.1.1) h)
        have hcell_eq : ∀ nonce : Nonce,
            g₁ ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce)
            = g₂ ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce) := by
          intro nonce
          exact heq _ (hcell_ne nonce).1 (hcell_ne nonce).2
        -- The bind structure is `(do { let p ← do { ... }; cont p })`. Flatten via bind_assoc
        -- with explicit OracleComp namespace, then bind_congr on the outer `$ᵗ Nonce`.
        show ($ᵗ Nonce >>= fun nonce => pure _) >>= _ =
             ($ᵗ Nonce >>= fun nonce => pure _) >>= _
        rw [bind_assoc, bind_assoc]
        refine bind_congr fun nonce => ?_
        rw [pure_bind, pure_bind, hcell_eq nonce]
        refine ih _ _ ?_
        -- Post-step state preserves hAdv: sessionsUsed tag either unchanged (T ≠ tag) or
        -- increased by 1 (T = tag); in either case ≥ s.sessionsUsed tag > slotK.
        by_cases hT : T = tag
        · subst hT
          show (slotK : ℕ) < (Function.update s.sessionsUsed T (s.sessionsUsed T + 1)) T
          simp
          omega
        · show (slotK : ℕ) < (Function.update s.sessionsUsed T (s.sessionsUsed T + 1)) tag
          rw [Function.update_of_ne (Ne.symm hT)]
          exact hAdv
      · -- Slot exhausted: both sides return `pure (none, s)`. IH on `k none` at state `s` closes.
        rw [singleTableHandler_tag_run_of_not_lt _ T s hslot,
            singleTableHandler_tag_run_of_not_lt _ T s hslot]
        change (simulateQ (singleTableHandler g₁) (k _)).run' s
             = (simulateQ (singleTableHandler g₂) (k _)).run' s
        exact ih _ s hAdv
    | inr transcript =>
      -- Reader query: handler returns `pure (ReaderReply.ofBool (unlinkReaderAccepts ...), s)`.
      rw [singleTableHandler_reader_run, singleTableHandler_reader_run]
      -- Goal: `pure (ofBool h₁, s) >>= cont_g₁ = pure (ofBool h₂, s) >>= cont_g₂`
      -- where h_i = unlinkReaderAccepts (fun slot nc => g_i (slot, nc)) singlePattern transcript.
      by_cases hn : transcript.nonce = n
      · -- Sub-case `transcript.nonce = n`: existential reads cells at `n`, including the swap
        -- pair. Multiset-invariance: `∃ (T', sid'), g((T', sid'), n) = V` is the same for g₁ and
        -- g₂ because the SET of values present at nonce `n` is identical (swap of positions
        -- doesn't change the multiset).
        subst hn
        -- Key claim: `unlinkReaderAccepts` is equal between g₁ and g₂ at this nonce, via the
        -- existential iff: each side can witness the existential by relocating to the other
        -- cached cell when needed.
        have hresp_eq : unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nc => g₁ (slot, nc)) (singlePattern sessionsPerTag) transcript
            = unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nc => g₂ (slot, nc)) (singlePattern sessionsPerTag) transcript := by
          -- Alias the outer `tag` to avoid name shadowing with the existential's bound variable.
          set tagOut : TagId := tag with htag_def
          unfold unlinkReaderAccepts tagAccepts
          rw [decide_eq_decide]
          simp only [decide_eq_true_iff, singlePattern]
          constructor
          · rintro ⟨T', sid', hsid'⟩
            by_cases hCase0 : (T', sid') = (tagOut, (0 : Fin sessionsPerTag))
            · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = 0 := Prod.mk.inj hCase0
              exact ⟨tagOut, slotK, hswap_0 ▸ hsid'⟩
            · by_cases hCaseK : (T', sid') = (tagOut, slotK)
              · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = slotK := Prod.mk.inj hCaseK
                exact ⟨tagOut, 0, hswap_K ▸ hsid'⟩
              · refine ⟨T', sid', ?_⟩
                have h_g_eq : g₁ ((T', sid'), transcript.nonce) =
                    g₂ ((T', sid'), transcript.nonce) := by
                  refine heq ((T', sid'), transcript.nonce) ?_ ?_
                  · intro h
                    exact hCase0 (congrArg (fun p => p.1) h)
                  · intro h
                    exact hCaseK (congrArg (fun p => p.1) h)
                exact h_g_eq ▸ hsid'
          · rintro ⟨T', sid', hsid'⟩
            by_cases hCase0 : (T', sid') = (tagOut, (0 : Fin sessionsPerTag))
            · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = 0 := Prod.mk.inj hCase0
              exact ⟨tagOut, slotK, hswap_K ▸ hsid'⟩
            · by_cases hCaseK : (T', sid') = (tagOut, slotK)
              · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = slotK := Prod.mk.inj hCaseK
                exact ⟨tagOut, 0, hswap_0 ▸ hsid'⟩
              · refine ⟨T', sid', ?_⟩
                have h_g_eq : g₁ ((T', sid'), transcript.nonce) =
                    g₂ ((T', sid'), transcript.nonce) := by
                  refine heq ((T', sid'), transcript.nonce) ?_ ?_
                  · intro h
                    exact hCase0 (congrArg (fun p => p.1) h)
                  · intro h
                    exact hCaseK (congrArg (fun p => p.1) h)
                exact h_g_eq.symm ▸ hsid'
        rw [hresp_eq]
        change (simulateQ (singleTableHandler g₁) (k _)).run' s
             = (simulateQ (singleTableHandler g₂) (k _)).run' s
        exact ih _ s hAdv
      · -- Sub-case `transcript.nonce ≠ n`: cells at `transcript.nonce` are not in swap pair,
        -- so `g₁` and `g₂` agree pointwise there. `unlinkReaderAccepts` value equal.
        -- Pointwise cell-value equality at every cell at `transcript.nonce`:
        have hg_eq : ∀ T' : TagId, ∀ sid' : Fin sessionsPerTag,
            g₁ ((T', sid'), transcript.nonce) = g₂ ((T', sid'), transcript.nonce) := by
          intro T' sid'
          refine heq ((T', sid'), transcript.nonce) ?_ ?_ <;>
            intro h <;> exact hn (congrArg (fun p => p.2) h)
        have hresp_eq : unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nc => g₁ (slot, nc)) (singlePattern sessionsPerTag) transcript
            = unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nc => g₂ (slot, nc)) (singlePattern sessionsPerTag) transcript := by
          unfold unlinkReaderAccepts tagAccepts
          simp only [hg_eq]
        rw [hresp_eq]
        -- Pure-bind: `pure (response, s) >>= cont = cont (response, s)`. Apply IH.
        change (simulateQ (singleTableHandler g₁) (k _)).run' s
             = (simulateQ (singleTableHandler g₂) (k _)).run' s
        exact ih _ s hAdv

/-! ### Swap-bridge for `singleTableHandler` cache extensions

The slot-positive case's Case M-miss needs to bridge between two cache extensions of
`singleTableHandler`:
* LHS: `c.cacheQuery ((tag, 0), n) u` — slot-0 cell cached at `u`.
* RHS: `c.cacheQuery ((tag, slotK), n) u` — slot-K cell cached at `u`.

Under `hcInv` (`c` has no slot-positive entries) and the post-step invariant
`hAdv : slotK.val < s.sessionsUsed tag`, these two cache extensions produce
**distributionally equal** computation outputs. -/

omit [Nonempty TagId] in
/-- **Swap-bridge for `singleTableHandler`.** Under `hcInv` (no slot-positive cache entries),
`hc0` (slot-0 cell of `c` at `n` uncached), and `hAdv` (`sessionsUsed tag` advanced past `slotK`),
the cache extensions at `(tag, 0)` and `(tag, slotK)` produce the same distribution of `oa`
outputs when run through `singleTableHandler` over a uniform `gS`. This is the workhorse for the
slot-positive Case M-miss closure.

**Hypothesis `hc0`.** The slot-0 cell `((tag, 0), n)` must be uncached in `c`. Otherwise a residual
slot-0 entry survives on the right-hand side (the slot-K `cacheQuery` leaves it untouched) while it
is overwritten by `u` on the left, and a reader query at that residual digest separates the two
distributions. The intended call site (Case M-miss) always has this cell fresh.

**Proof structure.** Single measure-preserving permutation argument: let
`φ = cellSwap ((tag, 0), n) ((tag, slotK), n)`. Apply `evalDist_uniformSample_bind_cellSwap` to
rewrite the LHS via `gS ↦ gS ∘ φ`. Then `singleTableHandler_simulateQ_swap_invariant` gives
POINTWISE equality between the rewritten LHS body and the RHS body, because:
* Cells off the swap pair: `gS ∘ φ` and `gS` agree (φ identity outside the pair).
* `((tag, 0), n)`: both tables cache `u`.
* `((tag, slotK), n)`: T_L(gS ∘ φ) exposes `gS((tag, 0), n)` (φ swaps these); T_R(gS) exposes
  `gS((tag, 0), n)` (uncached by `hc0`). -/
lemma singleTableHandler_cache_swap_eq [Fintype Nonce] [Fintype Digest]
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (tag : TagId) (slotK : Fin sessionsPerTag) (hslotK : slotK ≠ 0)
    (n : Nonce) (u : Digest)
    (hcInv : ∀ tag' : TagId, ∀ sid' : Fin sessionsPerTag, sid' ≠ 0 →
        ∀ n' : Nonce, c ((tag', sid'), n') = none)
    (hc0 : c ((tag, (0 : Fin sessionsPerTag)), n) = none)
    (hAdv : slotK.val < s.sessionsUsed tag)
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
  -- **Permutation argument**: let `φ := cellSwap ((tag, 0), n) ((tag, slotK), n)`. φ is
  -- measure-preserving on uniform `$ᵗ gS`. We rewrite the LHS via `gS → gS ∘ φ` and show that
  -- `T_L(gS ∘ φ)` and `T_R(gS)` give pointwise equal `singleTableHandler` outputs via the
  -- swap-invariance lemma.
  set φ : (TagId × Fin sessionsPerTag) × Nonce → (TagId × Fin sessionsPerTag) × Nonce :=
    cellSwap ((tag, (0 : Fin sessionsPerTag)), n) ((tag, slotK), n) with hφ
  -- Step 1: apply `evalDist_uniformSample_bind_cellSwap` to rewrite LHS with `gS ↦ gS ∘ φ`.
  rw [evalDist_uniformSample_bind_cellSwap (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) ((tag, (0 : Fin sessionsPerTag)), n) ((tag, slotK), n)]
  -- Step 2: pointwise — show the bodies are equal as functions of gS.
  refine congrArg evalDist (bind_congr fun gS => ?_)
  -- For each fixed `gS`, apply the swap-invariance lemma with the two tables.
  apply singleTableHandler_simulateQ_swap_invariant tag slotK hslotK n oa s hAdv
  · -- heq: agreement off the swap pair.
    intro x hx0 hxK
    -- T_L(gS ∘ φ) at x = tableExtending (cacheQuery c slot-0 u) (gS ∘ φ) at x.
    -- T_R(gS) at x = tableExtending (cacheQuery c slot-K u) gS at x.
    rw [OracleComp.tableExtending_cacheQuery, OracleComp.tableExtending_cacheQuery,
        Function.update_of_ne hx0, Function.update_of_ne hxK]
    -- Both reduce to tableExtending c (·) at x; `gS` and `gS ∘ φ` agree at x since x not in swap pair.
    show OracleComp.tableExtending c (gS ∘ φ) x = OracleComp.tableExtending c gS x
    unfold OracleComp.tableExtending
    have hφx : φ x = x := by
      rw [hφ]; exact cellSwap_of_ne _ _ hx0 hxK
    show (c x).getD ((gS ∘ φ) x) = (c x).getD (gS x)
    rw [Function.comp_apply, hφx]
  · -- hswap_0: T_L(gS ∘ φ) at ((tag, 0), n) = u = T_R(gS) at ((tag, slotK), n).
    rw [OracleComp.tableExtending_cacheQuery, OracleComp.tableExtending_cacheQuery,
        Function.update_self, Function.update_self]
  · -- hswap_K: T_L(gS ∘ φ) at ((tag, slotK), n) = gS((tag, 0), n) = T_R(gS) at ((tag, 0), n).
    rw [OracleComp.tableExtending_cacheQuery, OracleComp.tableExtending_cacheQuery]
    have hslotK_ne_0 : ((tag, slotK), n) ≠ ((tag, (0 : Fin sessionsPerTag)), n) := by
      intro h
      exact hslotK (congrArg (fun p => p.1.2) h)
    have h0_ne_slotK : ((tag, (0 : Fin sessionsPerTag)), n) ≠ ((tag, slotK), n) :=
      Ne.symm hslotK_ne_0
    rw [Function.update_of_ne hslotK_ne_0, Function.update_of_ne h0_ne_slotK]
    -- Goal: tableExtending c (gS ∘ φ) ((tag, slotK), n) = tableExtending c gS ((tag, 0), n).
    unfold OracleComp.tableExtending
    -- c at ((tag, slotK), n) = none by hcInv; c at ((tag, 0), n) = none by hc0.
    rw [hcInv tag slotK hslotK n, hc0]
    show gS (φ ((tag, slotK), n)) = gS ((tag, (0 : Fin sessionsPerTag)), n)
    have : φ ((tag, slotK), n) = ((tag, (0 : Fin sessionsPerTag)), n) := by
      rw [hφ, cellSwap_right]
    rw [this]

/-! ### Eager-form direct-coupling aux

The structural induction over the adversary, coupling M-side
`multipleBadTableHandler (slotZeroSubTable gS)` (with `UnlinkBadState` instrumentation) against
S-side `singleTableHandler gS` over a shared single-session RO table `gS`. Mirrors
`multipleBadEager_le_hybridEager_aux` (Eager.lean:85), but with M coupled directly to S via the
slot-0 sub-table embedding rather than going through Hybrid.

The aux is deliberately formulated in terms of *eager* table handlers and a *shared* draw `$ᵗ gS`;
the lazy headline `multipleIdeal_le_singleIdeal_add_bad_DC` below recovers it via the standard
eagerization equivalences. -/

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Fine handler is `cacheBad`-irrelevant.** Two initial bad states agreeing off `cacheBad`
produce identical Fine-run distributions after the projection `with cacheBad := cb`. Composes the
pointwise Fine→original bridge (`…_forget_cacheBad_pointwise_eq`) with the original-handler
irrelevance (`…_multipleBadTableHandler_cacheBad_irrelevant`). Used in the reader case to discard
the per-step `multipleBadReaderAdvance` perturbation of the initial state before applying the IH. -/
lemma evalDist_simulateQ_multipleBadTableHandlerFine_cacheBad_irrelevant
    {α : Type} (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : UnlinkState TagId) (sB sB' : UnlinkBadState TagId Nonce Digest) (cb : Bool)
    (hSU : sB.sessionsUsed = sB'.sessionsUsed)
    (hR : sB.responses = sB'.responses) (hB : sB.bad = sB'.bad) :
    𝒟[(fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g gFine) oa).run (s, sB)]
      = 𝒟[(fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g gFine) oa).run (s, sB')] := by
  rw [evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_pointwise_eq g gFine oa (s, sB),
      evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_pointwise_eq g gFine oa (s, sB')]
  exact evalDist_simulateQ_multipleBadTableHandler_cacheBad_irrelevant g oa s sB sB' cb hSU hR hB

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
  memory).

**Privacy.** Kept `private` while the reader case (Phase 9.5) is open, so downstream callers
cannot depend on the unverified bound. Will be exported once the reader case closes. -/
private lemma multipleBadEager_le_singleEager_DC_aux [Fintype Nonce] [Fintype Digest]
    (oa : UnlinkAdversary TagId Nonce Digest) (qR qT qRInit : ℕ)
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (R : Finset Nonce)
    (hqR : OracleComp.IsQueryBoundP oa (·.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP oa (·.isLeft) qT)
    (hqRle : qR + R.card ≤ qRInit)
    (hcInv : ∀ tag : TagId, ∀ sid : Fin sessionsPerTag, sid ≠ 0 →
        ∀ n : Nonce, c ((tag, sid), n) = none)
    (hRespInv : ∀ tag : TagId, ∀ n : Nonce, n ∉ R →
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
      ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) +
      ((qT * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  -- **Phase 9.0 skeleton.** Signature swapped to the Fine handler `multipleBadTableHandlerFine`
  -- with an inner `gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)` binder threaded
  -- through both the LHS success and RHS bad terms. Each induction case is staged as a `sorry`
  -- to be closed in Phases 9.1–9.5; see the recon document for the per-case strategy.
  classical
  induction oa using OracleComp.inductionOn generalizing qR qT s c sB R hqRle hcInv hRespInv with
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
          have hSplit : ((qRInit * (qT' + 1) : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞)
              = ((qRInit : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
                ((qRInit * qT' : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
            rw [show qRInit * (qT' + 1) = qRInit + qRInit * qT' from by ring,
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
            have hRespInv' : ∀ tag' : TagId, ∀ n' : Nonce, n' ∉ R →
                (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
                  ((tag', (0 : Fin sessionsPerTag)), n') ≠ none →
                (multipleBadAdvance tag sB
                  (some (⟨n, u⟩ : TagTranscript Nonce Digest))).responses (tag', n') ≠ none := by
              intro tag' n' hn'R hne
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
                exact hRespInv tag' n' hn'R hne
            have hihB := ih (some (⟨n, u⟩ : TagTranscript Nonce Digest)) qR qT'
              advM (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
              (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest))) R
              (hqRk _) (hqTk _) hqRle hcInv' hRespInv'
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
            have hRespInv'' : ∀ tag' : TagId, ∀ n' : Nonce, n' ∉ R →
                c ((tag', (0 : Fin sessionsPerTag)), n') ≠ none →
                (multipleBadAdvance tag sB
                  (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))).responses (tag', n') ≠ none := by
              intro tag' n' hn'R hne
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
                exact hRespInv tag' n' hn'R hne
            have hihA := ih (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)) qR qT'
              advM c
              (multipleBadAdvance tag sB (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))) R
              (hqRk _) (hqTk _) hqRle hcInv hRespInv''
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
          have hSplit : ((qRInit * (qT' + 1) : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞)
              = ((qRInit : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
                ((qRInit * qT' : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
            rw [show qRInit * (qT' + 1) = qRInit + qRInit * qT' from by ring,
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
            (D := fun n : Nonce => n ∈ R)
            ?_ ?_
          · -- The reader-touched set `R` has uniform-sample probability `R.card / |Nonce|`, which
            -- is at most the `qRInit / |Nonce|` headroom carved out of slack₂.
            rw [probEvent_uniformSample]
            have hcard : (Finset.univ.filter (· ∈ R)).card ≤ qRInit := by
              calc (Finset.univ.filter (· ∈ R)).card
                  = R.card := by
                    rw [Finset.filter_univ_mem]
                _ ≤ qRInit := le_trans (Nat.le_add_left _ _) hqRle
            gcongr
          intro n _ hnD
          -- `hnD : ¬ (n ∈ R)`, i.e. `n ∉ R`: off the reader-touched set, the v2 invariant applies.
          replace hnD : n ∉ R := hnD
          -- Phase D: per-`n` bound. Case-split on `c ((tag, 0), n)`:
          -- * Case M-hit: M reads cached value `u₀`; `hRespInv` triggers `multipleBadAdvance`
          --   to fire `bad := true`. By bad monotonicity, LHS ≤ Pr[bad] (the bad term in RHS).
          -- * Case M-miss: marginalize M's slot-0 cell + S's slot-K cell, apply IH at u_0,
          --   then `singleTableHandler_cache_swap_eq` (swap-bridge) closes the cache-extension
          --   asymmetry; rename u_0 ↔ u_K via the two-cell marginalization.
          rcases hc0 : c ((tag, (0 : Fin sessionsPerTag)), n) with _ | u₀
          · -- Case M-miss: c slot-0 = none. Marginalize slot-0 → IH → swap-bridge → re-marginalize.
            haveI : Nonempty Digest :=
              ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
            -- Step 1: marginalize gS over slot-0 cell (same pattern as slot-zero Case B).
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
              have h1 := OracleComp.tableExtending_update_of_none c gS' hc0 u
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
            -- Step 2: marginalize LHS-success event over slot-0 (same as slot-zero Case B).
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
            -- Step 3: marginalize RHS S-event over slot-K cell (uncached by hcInv).
            have hmarg_K : ∀ {β : Type}
                (Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp β),
                𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest); Mψ gS)] =
                𝒟[(do let u ← $ᵗ Digest
                      let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      Mψ (Function.update gS' ((tag, slotK), n) u))] := by
              intro β Mψ
              have hbase :
                  𝒟[(do let u ← $ᵗ Digest
                        let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        pure (Function.update gS' ((tag, slotK), n) u))]
                  = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] :=
                evalDist_uniformSample_bind_update ((tag, slotK), n)
              have hL : (do let u ← $ᵗ Digest
                            let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                            Mψ (Function.update gS' ((tag, slotK), n) u))
                  = (do let u ← $ᵗ Digest
                        let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        pure (Function.update gS' ((tag, slotK), n) u))
                      >>= Mψ := by
                simp [bind_assoc]
              have hR : (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest); Mψ gS)
                  = ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= Mψ := rfl
              rw [hL, hR, evalDist_bind, evalDist_bind, hbase]
            have hext_K_eq : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
                (u : Digest),
                OracleComp.tableExtending c
                    (Function.update gS' ((tag, slotK), n) u) =
                  OracleComp.tableExtending (c.cacheQuery ((tag, slotK), n) u) gS' :=
              fun gS' u => by
                have h1 := OracleComp.tableExtending_update_of_none c gS'
                  (hcInv tag slotK hslotK_ne n) u
                have h2 := OracleComp.tableExtending_cacheQuery c gS' ((tag, slotK), n) u
                exact h1.symm.trans h2.symm
            have hcell_K_u : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
                (u : Digest),
                OracleComp.tableExtending (c.cacheQuery ((tag, slotK), n) u) gS'
                    ((tag, slotK), n) = u := fun gS' u => by
              rw [OracleComp.tableExtending_cacheQuery]
              simp [Function.update_self]
            have hRHS_marg :
                Pr[(· = true) |
                  (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, slotK), n)⟩ : TagTranscript Nonce Digest)))).run' advM)]
              = Pr[(· = true) |
                  (do let u ← $ᵗ Digest
                      let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending (c.cacheQuery ((tag, slotK), n) u) gS'))
                        (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' advM)] := by
              refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
              rw [hmarg_K _]
              refine congrArg evalDist ?_
              refine bind_congr fun u => ?_
              refine bind_congr fun gS' => ?_
              rw [hext_K_eq gS' u, hcell_K_u gS' u]
            -- Step 4: rewrite the marginalizations and apply probEvent_bind_le_add_bad_disagree.
            rw [hLHS_marg, hRHS_marg, hBAD_marg]
            rw [show ∀ a b c : ℝ≥0∞, a + b + c = a + b + 0 + c from
                  fun a b c => by ring]
            refine probEvent_bind_le_add_bad_disagree
              (mx := ($ᵗ Digest : ProbComp Digest))
              (D := fun _ : Digest => False)
              (by simp) ?_
            intro u _ _
            -- Step 5: per-`u`. Build new invariants for IH call at cache `c.cacheQuery slot-0 u`.
            have hcInv' : ∀ tag' : TagId, ∀ sid' : Fin sessionsPerTag, sid' ≠ 0 →
                ∀ n' : Nonce,
                  (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
                    ((tag', sid'), n') = none := by
              intro tag' sid' hsid' n'
              have hne : ((tag', sid'), n') ≠ ((tag, (0 : Fin sessionsPerTag)), n) := by
                intro h
                exact hsid' (congrArg (fun p => p.1.2) h)
              simp [OracleSpec.QueryCache.cacheQuery_of_ne, hne, hcInv tag' sid' hsid' n']
            have hRespInv' : ∀ tag' : TagId, ∀ n' : Nonce, n' ∉ R →
                (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
                  ((tag', (0 : Fin sessionsPerTag)), n') ≠ none →
                (multipleBadAdvance tag sB
                  (some (⟨n, u⟩ : TagTranscript Nonce Digest))).responses (tag', n') ≠ none := by
              intro tag' n' hn'R hne
              by_cases htagn : (tag', n') = (tag, n)
              · have : (multipleBadAdvance tag sB
                    (some (⟨n, u⟩ : TagTranscript Nonce Digest))).responses (tag', n') =
                    (sB.responses.cacheQuery (tag, n)
                      (u :: Option.getD (sB.responses (tag, n)) [])) (tag', n') := rfl
                rw [this, htagn, OracleSpec.QueryCache.cacheQuery_self]
                exact Option.some_ne_none _
              · have hne_cell : ((tag', (0 : Fin sessionsPerTag)), n') ≠
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
                exact hRespInv tag' n' hn'R hne
            -- IH at transcript ⟨n, u⟩, cache c+u@slot-0, qT'.
            have hihB := ih (some (⟨n, u⟩ : TagTranscript Nonce Digest)) qR qT'
              advM (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
              (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest))) R
              (hqRk _) (hqTk _) hqRle hcInv' hRespInv'
            -- Bridge S-side from c+u@slot-0 to c+u@slot-K via the swap-bridge.
            -- The swap-bridge requires `slotK.val < advM.sessionsUsed tag`, which holds
            -- because advM = (s with sessionsUsed tag ↦ s.sessionsUsed tag + 1)
            -- = slotK.val + 1 > slotK.val.
            have hAdv_advM : slotK.val < advM.sessionsUsed tag := by
              show slotK.val <
                (Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)) tag
              rw [Function.update_self]
              show s.sessionsUsed tag < s.sessionsUsed tag + 1
              omega
            have hbridge :=
              singleTableHandler_cache_swap_eq (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                advM c tag slotK hslotK_ne n u hcInv hc0 hAdv_advM
                (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
            -- The bridge says distributions over uniform gS are equal between the two caches.
            -- Use this to rewrite the S-side of hihB.
            -- Rewrite hihB's S-side from c+u@slot-0 to c+u@slot-K via hbridge.
            have hS_eq : Pr[= true |
                  (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending
                          (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS))
                        (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' advM)]
                = Pr[= true |
                  (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending
                          (c.cacheQuery ((tag, slotK), n) u) gS))
                        (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' advM)] :=
              probOutput_congr rfl hbridge
            rw [hS_eq] at hihB
            rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput,
                ← add_assoc, ← add_assoc, ← add_assoc]
            exact hihB
          · -- Case M-hit: c slot-0 = some u₀.
            -- Step 1: M's transcript becomes constant ⟨n, u₀⟩.
            have hcell : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
                OracleComp.tableExtending c gS ((tag, (0 : Fin sessionsPerTag)), n) = u₀ :=
              fun gS => by
                show (c ((tag, (0 : Fin sessionsPerTag)), n)).getD
                    (gS ((tag, (0 : Fin sessionsPerTag)), n)) = u₀
                rw [hc0]; rfl
            simp_rw [hcell]
            -- Step 2: hRespInv → responses (tag, n) ≠ none → multipleBadAdvance flips bad := true.
            have hresp_some : sB.responses (tag, n) ≠ none :=
              hRespInv tag n hnD (by rw [hc0]; exact Option.some_ne_none _)
            have hbad_init : (multipleBadAdvance tag sB
                (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))).bad = true := by
              show (sB.bad || (sB.responses (tag, n)).isSome) = true
              rw [Option.isSome_iff_ne_none.mpr hresp_some]
              simp
            -- Step 3: By preserves_bad, every reachable output has z.2.2.bad = true.
            -- So LHS-success event (z.1 = true) is dominated by BAD event (z.2.2.bad = true).
            have hLHS_le_BAD :
                probEvent (do
                    let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)) gFine)
                        (k (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))))
                  (fun x => x = true)
                ≤ probEvent (do
                    let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)) gFine)
                        (k (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))))
                  (fun z => z.2.bad = true) := by
              -- Both events come from the same underlying do-block via different `<$>`
              -- projections; factor out the projections via `probEvent_map`, then use
              -- `probEvent_mono` with the implication that preserves_bad makes unconditional.
              simp only [probEvent_bind_eq_tsum, probEvent_map]
              refine ENNReal.tsum_le_tsum fun gS => ?_
              refine mul_le_mul_right ?_ _
              refine ENNReal.tsum_le_tsum fun gFine => ?_
              refine mul_le_mul_right ?_ _
              refine probEvent_mono ?_
              intro z hz_mem _
              -- z is in support of the simQ run starting at state with bad = true.
              -- By preserves_bad, z.2.2.bad = true.
              exact multipleBadTableHandlerFine_run_preserves_bad
                (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine _
                (advM, multipleBadAdvance tag sB
                  (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))) hbad_init z hz_mem
            -- Step 4: BAD ≤ (S + BAD) + slacks. Chain: `le_add_self` then `le_self_add`.
            refine hLHS_le_BAD.trans ?_
            exact le_add_self.trans le_self_add
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
        refine (ih none qR qT' s c sB R (hqRk none) (hqTk none) hqRle hcInv hRespInv).trans ?_
        gcongr
        · exact Nat.le_succ _
        · exact Nat.le_succ _
    | inr transcript =>
      -- Phase 9.5: reader query — the asymmetric-discard argument. Slot-0 column lazification
      -- on both sides makes M's reader bit a constant `m` of the extended cache `c₀′`; on `m = true`
      -- the IH closes directly, on `m = false` the slot-positive acceptance event `E gS` is the
      -- whole gap and is charged to one slack₃ unit via `cacheBadReader`.
      -- **Budget splits.** The head reader query is right-not-left, so `qR = qR' + 1` and `qT`
      -- is unchanged. `R` grows to `insert transcript.nonce R`.
      have hqTk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isLeft) qT := by
        intro u
        have h := hqT
        rw [OracleComp.isQueryBoundP_query_bind_iff] at h
        simpa using h.2 u
      have hqRsplit := hqR
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hqRsplit
      have hqRpos : 0 < qR := hqRsplit.1.resolve_left (fun h => absurd rfl h)
      obtain ⟨qR', rfl⟩ : ∃ qR', qR = qR' + 1 := ⟨qR - 1, by omega⟩
      have hqRk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isRight) qR' := fun u => by
        simpa using hqRsplit.2 u
      -- Abbreviation for the M-side reader acceptance bit at a sub-table.
      set mAcc : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → Bool := fun gS =>
        unlinkReaderAccepts (Slot := TagId)
          (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending c gS) (tag, nonce))
          (multiplePattern (TagId := TagId) sessionsPerTag) transcript with hmAcc
      set sAcc : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → Bool := fun gS =>
        unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun slot nonce => OracleComp.tableExtending c gS (slot, nonce))
          (singlePattern (TagId := TagId) sessionsPerTag) transcript with hsAcc
      -- M-Fine reader head step: pure reply, state untouched, `cacheBad` advances by `gFine`.
      have hMstep : ∀ gS gFine,
          multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine (Sum.inr transcript) (s, sB)
          = pure (ReaderReply.ofBool (mAcc gS), s,
              multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB) := by
        intro gS gFine
        show (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) (Sum.inr transcript)) s
            >>= (fun r => pure (r.1, r.2,
              multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB))
            = _
        rw [multipleTableHandler_reader_run_slotZeroSubTable]
        rfl
      -- S reader head step: pure reply, state untouched.
      have hSstep : ∀ gS,
          singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)
            (Sum.inr transcript) s
          = pure (ReaderReply.ofBool (sAcc gS), s) := fun gS =>
        singleTableHandler_reader_run (OracleComp.tableExtending c gS) transcript s
      -- Collapse the head reader query on all three positions.
      simp only [multipleBadTableFine_run_query_bind', singleTable_run'_query_bind', map_bind]
      have hLHS_eq :
          (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let p ← multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine (Sum.inr transcript) (s, sB)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
                (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c gS)) gFine) (k p.1)).run p.2)
          = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) gFine)
                    (k (ReaderReply.ofBool (mAcc gS)))).run
                    (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                      gFine transcript sB)) := by
        refine bind_congr fun gS => ?_
        refine bind_congr fun gFine => ?_
        rw [hMstep gS gFine]; rfl
      have hRHS_eq :
          (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let p ← singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)
                (Sum.inr transcript) s
              (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
                (k p.1)).run' p.2)
          = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
                  (k (ReaderReply.ofBool (sAcc gS)))).run' s) := by
        refine bind_congr fun gS => ?_
        rw [hSstep gS]; rfl
      have hBAD_eq :
          (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let p ← multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine (Sum.inr transcript) (s, sB)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c gS)) gFine) (k p.1)).run p.2)
          = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) gFine)
                    (k (ReaderReply.ofBool (mAcc gS)))).run
                    (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                      gFine transcript sB)) := by
        refine bind_congr fun gS => ?_
        refine bind_congr fun gFine => ?_
        rw [hMstep gS gFine]; rfl
      rw [probOutput_congr rfl (congrArg evalDist hLHS_eq),
          probOutput_congr rfl (congrArg evalDist hRHS_eq),
          probEvent_congr' (fun _ _ => Iff.rfl) (congrArg evalDist hBAD_eq)]
      classical
      haveI : Nonempty Digest :=
        ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
      -- **C1: slot-0 column lazification.** Cache every slot-0 cell of the queried column.
      set cells : List ((TagId × Fin sessionsPerTag) × Nonce) :=
        (Finset.univ.toList).map
          (fun T : TagId => ((T, (0 : Fin sessionsPerTag)), transcript.nonce)) with hcells
      -- The three terms (LHS-success, RHS-success, BAD) all have the shape
      -- `$ᵗ gS >>= fun gS => Mψ (tableExtending c gS)` for the continuations below; the
      -- lazification lemma rewrites `tableExtending c gS` to `idealCacheMapM cells c >>= …`.
      -- LHS continuation: absorbs the inner `$ᵗ gFine` binder.
      have hLHS_lazify :
          𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) gFine)
                    (k (ReaderReply.ofBool (mAcc gS)))).run
                    (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                      gFine transcript sB))]
          = 𝒟[(do let rs ← idealCacheMapM (Digest := Digest) cells c
                  let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      z.1) <$>
                    (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending rs.2 gS)) gFine)
                      (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
                        (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending rs.2 gS) (tag, nonce))
                        (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
                      (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                        gFine transcript sB))] := by
        rw [hmAcc]
        exact (evalDist_idealCacheMapM_bind_uniformTable_comp cells c
          (fun T => do
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) T) gFine)
                (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
                  (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    T (tag, nonce))
                  (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
                (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript sB))).symm
      -- RHS continuation (no `gFine`).
      have hRHS_lazify :
          𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
                  (k (ReaderReply.ofBool (sAcc gS)))).run' s)]
          = 𝒟[(do let rs ← idealCacheMapM (Digest := Digest) cells c
                  let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending rs.2 gS))
                    (k (ReaderReply.ofBool (unlinkReaderAccepts
                      (Slot := TagId × Fin sessionsPerTag)
                      (fun slot nonce => OracleComp.tableExtending rs.2 gS (slot, nonce))
                      (singlePattern (TagId := TagId) sessionsPerTag) transcript)))).run' s)] := by
        rw [hsAcc]
        exact (evalDist_idealCacheMapM_bind_uniformTable_comp cells c
          (fun T => (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) T)
            (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nonce => T (slot, nonce))
              (singlePattern (TagId := TagId) sessionsPerTag) transcript)))).run' s)).symm
      -- BAD continuation: same as LHS but with the `(z.1, z.2.2)` projection.
      have hBAD_lazify :
          𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) gFine)
                    (k (ReaderReply.ofBool (mAcc gS)))).run
                    (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                      gFine transcript sB))]
          = 𝒟[(do let rs ← idealCacheMapM (Digest := Digest) cells c
                  let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$>
                    (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending rs.2 gS)) gFine)
                      (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
                        (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending rs.2 gS) (tag, nonce))
                        (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
                      (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                        gFine transcript sB))] := by
        rw [hmAcc]
        exact (evalDist_idealCacheMapM_bind_uniformTable_comp cells c
          (fun T => do
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag) T) gFine)
                (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
                  (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    T (tag, nonce))
                  (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
                (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript sB))).symm
      -- Rewrite all three terms to their lazified forms.
      rw [probOutput_congr rfl hLHS_lazify, probOutput_congr rfl hRHS_lazify,
          probEvent_congr' (fun _ _ => Iff.rfl) hBAD_lazify]
      -- **Per-rs coupling.** All three terms now share the `idealCacheMapM cells c` head; couple
      -- them via the empty-`D` disagreement bound (mirroring the tag cases' `$ᵗ Nonce` coupling).
      -- The slacks are charged entirely in the per-rs obligation (closed in C2/C3); here `ε₁ = 0`,
      -- `ε₂ = slack₁ + slack₂ + slack₃ + slack₄`.
      simp only [← probEvent_eq_eq_probOutput]
      -- Regroup the RHS so the four slacks become a single trailing `ε₂` and insert `ε₁ = 0`.
      rw [show ∀ a b c d e f : ℝ≥0∞, a + b + c + d + e + f = a + b + 0 + (c + d + e + f) from
            fun a b c d e f => by ring]
      refine probEvent_bind_le_add_bad_disagree
        (mx := idealCacheMapM (Digest := Digest) cells c)
        (D := fun _ => False) (by simp) ?_
      intro rs hrs _
      -- **C2: per-rs facts.** Set `c₀′ := rs.2`, the cache with the slot-0 column cached.
      set c₀ := rs.2 with hc₀
      -- (a) hcInv for `c₀`: slot-positive cells are never in `cells`, so unchanged from `c`.
      have hc₀Inv : ∀ tag : TagId, ∀ sid : Fin sessionsPerTag, sid ≠ 0 →
          ∀ n : Nonce, c₀ ((tag, sid), n) = none := by
        intro tag sid hsid n
        have hnotmem : ((tag, sid), n) ∉ cells := by
          rw [hcells]
          simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
          rintro ⟨T, hT⟩
          exact hsid (congrArg (fun p => p.1.2) hT).symm
        rw [hc₀, idealCacheMapM_cache_not_mem cells c rs hrs ((tag, sid), n) hnotmem]
        exact hcInv tag sid hsid n
      -- (b) Every slot-0 cell at column `transcript.nonce` is cached in `c₀`.
      have hc₀cached : ∀ tag : TagId, (c₀ ((tag, (0 : Fin sessionsPerTag)), transcript.nonce)).isSome := by
        intro tag
        have hmem : ((tag, (0 : Fin sessionsPerTag)), transcript.nonce) ∈ cells := by
          rw [hcells]
          exact List.mem_map.mpr ⟨tag, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩
        rw [hc₀]
        exact idealCacheMapM_cache_isSome_of_mem cells c rs hrs _ hmem
      -- (c) The slot-0 cell read is independent of `gS` (it is the cached value).
      have hcellConst : ∀ tag : TagId, ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
          OracleComp.tableExtending c₀ gS ((tag, (0 : Fin sessionsPerTag)), transcript.nonce) =
            (c₀ ((tag, (0 : Fin sessionsPerTag)), transcript.nonce)).getD
              (transcript.auth) := fun tag gS => by
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hc₀cached tag)
        show (c₀ ((tag, (0 : Fin sessionsPerTag)), transcript.nonce)).getD
            (gS ((tag, (0 : Fin sessionsPerTag)), transcript.nonce)) = _
        rw [hu]; rfl
      -- (d) The M reader bit is therefore a constant `m` independent of `gS`.
      set m : Bool := unlinkReaderAccepts (Slot := TagId)
        (fun tag _nonce => (c₀ ((tag, (0 : Fin sessionsPerTag)), transcript.nonce)).getD
          (transcript.auth))
        (multiplePattern (TagId := TagId) sessionsPerTag) transcript with hm
      have hmConst : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
          unlinkReaderAccepts (Slot := TagId)
            (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c₀ gS) (tag, nonce))
            (multiplePattern (TagId := TagId) sessionsPerTag) transcript = m := by
        intro gS
        rw [hm]
        unfold unlinkReaderAccepts tagAccepts multiplePattern
        simp only [decide_eq_decide]
        refine exists_congr fun tag => ?_
        simp only [slotZeroSubTable_apply, hcellConst tag gS]
      -- (e) Per-rs bookkeeping: `R′ := insert transcript.nonce R`.
      set R' : Finset Nonce := insert transcript.nonce R with hR'
      have hqRle' : qR' + R'.card ≤ qRInit := by
        calc qR' + R'.card ≤ qR' + (R.card + 1) :=
              Nat.add_le_add_left (Finset.card_insert_le _ _) _
          _ = qR' + 1 + R.card := by ring
          _ ≤ qRInit := hqRle
      -- (f) hRespInv-v2 for `c₀` at `R'`: off `R'` we have `n' ≠ transcript.nonce`, so the cell is
      -- not in `cells`, hence `c₀` agrees with `c` there and `sB` is unchanged by the reader step.
      have hRespInv' : ∀ tag' : TagId, ∀ n' : Nonce, n' ∉ R' →
          c₀ ((tag', (0 : Fin sessionsPerTag)), n') ≠ none →
          sB.responses (tag', n') ≠ none := by
        intro tag' n' hn'R' hne
        rw [hR', Finset.mem_insert, not_or] at hn'R'
        obtain ⟨hn'ne, hn'R⟩ := hn'R'
        have hnotmem : ((tag', (0 : Fin sessionsPerTag)), n') ∉ cells := by
          rw [hcells]
          simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
          rintro ⟨T, hT⟩
          exact hn'ne (congrArg (fun p => p.2) hT).symm
        rw [hc₀, idealCacheMapM_cache_not_mem cells c rs hrs _ hnotmem] at hne
        exact hRespInv tag' n' hn'R hne
      -- Rewrite the M reader bit (in LHS and BAD) to the constant `m`.
      simp only [hmConst]
      -- **m-split.**
      by_cases hmb : m = true
      · -- **Case m = true.** The S reader also accepts (slot-0 witness lifts), so for every `gS` the
        -- S bit is `true`; both sides run `k (ReaderReply.ofBool true)` at the same state, and the
        -- IH at `(c₀, qR', R')` closes it.
        have hsTrue : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nonce => OracleComp.tableExtending c₀ gS (slot, nonce))
              (singlePattern (TagId := TagId) sessionsPerTag) transcript = true := by
          intro gS
          refine mReader_accepts_imp_sReader_accepts
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c₀ gS) transcript ?_
          rw [hmConst gS]; exact hmb
        -- Rewrite the M bit (LHS/BAD) and the S bit (RHS) to `true`.
        rw [hmb]
        simp only [hsTrue]
        -- Discard the `multipleBadReaderAdvance` perturbation of the initial state: the success
        -- bool and the bad flag both ignore `cacheBad`, so per-`gS,gFine` the run distribution is
        -- unchanged when starting from `(s, sB)` instead of `(s, advBad gFine)`.
        have hLHS_irr :
            probEvent (do
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
                (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool true))).run
                  (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                    gFine transcript sB)) (fun x => x = true)
            = probEvent (do
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
                (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool true))).run
                  (s, sB)) (fun x => x = true) := by
          refine probEvent_bind_congr' _ _ fun gS => ?_
          refine probEvent_bind_congr' _ _ fun gFine => ?_
          refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
          -- `(z.1) <$> run = (z.1) <$> (proj <$> run)`; apply irrelevance under the outer map.
          have hirr := evalDist_simulateQ_multipleBadTableHandlerFine_cacheBad_irrelevant
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c₀ gS)) gFine (k (ReaderReply.ofBool true)) s
            (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB) sB
            sB.cacheBad rfl rfl rfl
          calc 𝒟[(fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    z.1) <$>
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c₀ gS)) gFine)
                    (k (ReaderReply.ofBool true))).run
                    (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                      gFine transcript sB)]
              = 𝒟[(fun z => z.1) <$> ((fun z => (z.1, z.2.1, {z.2.2 with
                    cacheBad := (sB.cacheBad : Bool)})) <$>
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c₀ gS)) gFine)
                    (k (ReaderReply.ofBool true))).run
                    (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                      gFine transcript sB))] := by rw [Functor.map_map]
            _ = 𝒟[(fun z => z.1) <$> ((fun z => (z.1, z.2.1, {z.2.2 with
                    cacheBad := (sB.cacheBad : Bool)})) <$>
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c₀ gS)) gFine)
                    (k (ReaderReply.ofBool true))).run (s, sB))] := by
                  rw [evalDist_map, hirr, ← evalDist_map]
            _ = 𝒟[(fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    z.1) <$>
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c₀ gS)) gFine)
                    (k (ReaderReply.ofBool true))).run (s, sB)] := by
                  rw [Functor.map_map]
        have hBAD_irr :
            probEvent (do
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool true))).run
                  (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                    gFine transcript sB)) (fun z => z.2.bad = true)
            = probEvent (do
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool true))).run
                  (s, sB)) (fun z => z.2.bad = true) := by
          refine probEvent_bind_congr' _ _ fun gS => ?_
          refine probEvent_bind_congr' _ _ fun gFine => ?_
          have hirr := evalDist_simulateQ_multipleBadTableHandlerFine_cacheBad_irrelevant
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c₀ gS)) gFine (k (ReaderReply.ofBool true)) s
            (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB) sB
            sB.cacheBad rfl rfl rfl
          -- `Pr[bad | (z.1,z.2.2) <$> run]` equals `Pr[bad | proj <$> run]` since `proj` preserves
          -- the `bad` field; then apply `hirr`.
          set proj : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) →
              Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :=
            fun z => (z.1, z.2.1, {z.2.2 with cacheBad := (sB.cacheBad : Bool)}) with hproj
          set Eb : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) → Prop :=
            (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.2.bad = true) ∘
              (fun w => (w.1, w.2.2)) with hEb
          have hElaz : ∀ X : ProbComp (Bool × (UnlinkState TagId ×
                UnlinkBadState TagId Nonce Digest)),
              Pr[Eb | X] = Pr[Eb | proj <$> X] := fun X => by
            rw [probEvent_map]
            exact probEvent_congr' (fun _ _ => Iff.rfl) rfl
          rw [probEvent_map, probEvent_map,
              hElaz ((simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool true))).run
                (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript sB)),
              hElaz ((simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool true))).run
                (s, sB))]
          exact probEvent_congr' (fun _ _ => Iff.rfl) hirr
        -- Rewrite LHS-success and BAD to the unperturbed `(s, sB)` state, then apply the IH.
        rw [hLHS_irr, hBAD_irr, probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput]
        refine (ih (ReaderReply.ofBool true) qR' qT s c₀ sB R'
          (hqRk _) (hqTk _) hqRle' hc₀Inv hRespInv').trans ?_
        rw [show ∀ a b c d e : ℝ≥0∞, a + (b + c + d + e) = a + b + c + d + e from
              fun a b c d e => by ring]
        gcongr <;> exact Nat.le_succ _
      · -- **Case m = false** (closed in C3).
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
state-dependent one.

**Privacy.** Kept `private` while the reader case of the underlying aux is open, so downstream
callers cannot depend on the unverified bound. Will be exported once the aux closes. -/
private theorem multipleIdeal_le_singleIdeal_add_bad_DC [Fintype Nonce] [Fintype Digest]
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
    adversary qReader qTag qReader UnlinkState.init
    (∅ : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) UnlinkBadState.init ∅
    hqReader hqTag (by simp) (fun _ _ _ _ => rfl) (fun _ _ _ h => absurd rfl h)
  simp only [OracleComp.tableExtending_empty] at haux
  -- The aux bound is term-by-term ≤ the headline RHS; the extra outermost
  -- `qTag * sessionsPerTag / |Digest|` slack (reserved for the eventual ε_cb
  -- charge transported via `evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_eq`
  -- and `simulateQ_multipleBadTableHandlerFine_cacheBad_prob_le`) is dropped via `le_self_add`.
  exact haux.trans le_self_add

end UnlinkReduction

end DirectCouplingCompose

end PRFTagReader
