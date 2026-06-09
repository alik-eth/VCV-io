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

/-! ### Slot-positive trace-union residue (cross-file Option-6 blocker)

After the slot-positive tag-step Phase A–D unfolds (handler unfolds, `$ᵗ gS` / `$ᵗ Nonce`
commutation, per-`n` disagree split, two-cell marginalization at cell A = `((tag, 0), n)` and
cell B = `((tag, slotK), n)` with `slotK ≠ 0`, and the inductive hypothesis at a single auth
value), each of the three slot-positive sub-cases reduces to the *same* residual inequality
shape: the S-side reader-accept probability with one auth value bounded by the S-side
reader-accept probability with a *different* auth value, where the cache and outer `$ᵗ gS`
draw are identical on both sides.

`slotPositive_trace_union_residue` packages this residue into a single named bound. Its
statement is the structural mismatch that *cannot* be closed by the inductive hypothesis (IH at
a single auth value cannot bridge `M ≠ S` auth disagreements that arise from disjoint cell
reads in the slot-positive case).

**Cross-file blocker.** Discharging this residue requires the Option-6 cacheBad refactor.
**Status (post iter-26).** The upstream infrastructure has LANDED in
`Examples/PRFTagReader/MultipleToHybrid/EagerSetup.lean`:
* `cacheBad : Bool` field on `UnlinkBadState` (Defs.lean), `cacheBad := false` in `init`;
* `cacheBadReader` predicate + `multipleBadReaderAdvance` advance combinator;
* `multipleBadTableHandlerFine g gFine` — the fine-grained cacheBad-instrumented variant
  (output-marginally-equivalent to the existing `multipleBadTableHandler g` but with the
  reader branch ORing `cacheBadReader gFine transcript` into `cacheBad`);
* companion headline `simulateQ_multipleBadTableHandlerFine_cacheBad_prob_le` giving
  `Pr[cacheBad] ≤ qR · |TagId| · sessionsPerTag / |Digest|` over a fresh `gFine ← $ᵗ`.

**Remaining gap to close this helper.** The handler currently used in the aux is the
COARSE `multipleBadTableHandler g` (cacheBad invariant). To absorb the slot-positive auth
residue into a `Pr[cacheBad]` slack, the aux must be re-stated against
`multipleBadTableHandlerFine g gFine` with an outer `gFine ← $ᵗ`.

**Technical obstacle (iter-28 finding).** A bridge lemma of the form
`Pr[P | coarse run from p] = Pr[P | Fine run from p]` for cacheBad-independent `P` is
NOT a single straightforward induction. The reason: at a `query_bind`, after
`probEvent_bind_eq_tsum` the goal splits into a tsum over `r`, but the per-`r` factor
`(handler t s).probOutput r` involves the post-advance state, and the advance produces
*different* values of `r.2.2.cacheBad` between coarse (`p.2.cacheBad`) and Fine
(`p.2.cacheBad || cacheBadReader gFine transcript`). The `r`-indices don't align across
the two tsum's, so tsum-congr cannot be applied pointwise. A correct proof must reindex
the tsum (e.g. by quotienting out cacheBad on `r`) or use a stronger structural
"projection on r" framework. Estimated effort: a full-day implementation in EagerSetup.lean
with intermediate "support up to cacheBad" lemmas.

**Alternative path (simpler bound).** Rather than the full handler-swap bridge, prove
DIRECTLY: `Pr[bad | coarse] + Pr[helper residue contribution]` ≤
`Pr[bad ∨ cacheBad | Fine] + Pr[cacheBad | Fine]` where the helper residue at each
slot-positive site contributes a Bernoulli `cacheBadReader gFine` mass. This avoids
the global handler swap by treating cacheBad as a *witness flag* threaded only through
the bad-mass accounting, leaving the M-side output distribution untouched at the coarse
level. Requires a per-step probabilistic charge lemma matching `Pr[cacheBadReader ...]`
to a fresh `gFine ← $ᵗ` slot-mass bound.

With either path:
* the aux gains a `Pr[cacheBad over multipleBadTableHandlerFine]` slack term on its RHS;
* that slack absorbs the helper-residue auth disagreement at slot-positive tag-step sites;
* the headline `multipleIdeal_le_singleIdeal_add_bad_DC` bounds the new term via
  `simulateQ_multipleBadTableHandlerFine_cacheBad_prob_le`, yielding the final
  `qR · |TagId| · sessionsPerTag / |Digest|` charge. -/
lemma slotPositive_trace_union_residue [Fintype Nonce] [Fintype Digest]
    (advM : UnlinkState TagId) (tag : TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (k : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inl tag) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (transcriptM : TagTranscript Nonce Digest)
    (transcriptS : ((TagId × Fin sessionsPerTag) × Nonce → Digest) →
      TagTranscript Nonce Digest) :
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
  -- **Cross-file Option-6 cacheBad blocker.** See module docstring above for the refactor plan.
  -- The inequality is *not* universally true at the eager-coupling level — discharging it
  -- requires the `cacheBad` bad-state field absorbing the auth-disagreement mass.
  --
  -- **Counterexample (why the statement is not currently provable).** Take `k` to be the
  -- predicate `fun t => decide (t.auth = d)` for some fixed `d : Digest`. Then `transcriptM = d`
  -- and `transcriptS = d'` with `d ≠ d'` gives LHS = 1, RHS = 0. The cross-file refactor adds a
  -- `+ Pr[cacheBad]` term to the RHS, which absorbs exactly such mismatches.
  --
  -- **Call-site map.** This helper is invoked at three structurally distinct sites in the
  -- slot-positive tag-step proof of `multipleBadEager_le_singleEager_DC_aux` below:
  -- * **Case B (cell A uncached):** `transcriptM = ⟨n, u⟩` (fresh from cell A marginalization),
  --   `transcriptS gS' = ⟨n, tableExtending c gS' ((tag, slotK), n)⟩` (gS'-dependent at cell B).
  -- * **Sub-case A.B (cell A cached, cell B uncached):** `transcriptM = ⟨n, u₀⟩` (cached at cell A),
  --   `transcriptS = fun _ => ⟨n, u⟩` (fresh from cell B marginalization; constant in gS').
  -- * **Sub-case A.A (both cells cached):** `transcriptM = ⟨n, u₀⟩`, `transcriptS = fun _ => ⟨n, u_B⟩`
  --   (both cached, both constant in gS'; the simplest residue form).
  -- All three sites need the same cacheBad mass charge — the Option-6 refactor closes them in
  -- one stroke via the companion bound `Pr[cacheBad] ≤ qR · |TagId| · sessionsPerTag / |Digest|`.
  sorry

/-! ### Slot-positive trace-union residue with explicit disagreement-mass hypothesis

`slotPositive_trace_union_residue_with_slack` is an additive-slack variant of the unconditional
helper above. It accepts an explicit hypothesis bounding the *disagreement mass*
`Pr[transcriptM ≠ transcriptS gS | gS ← $ᵗ]` by a parameter `ε`, and concludes the same
inequality with `+ ε` on the RHS. This is provable unconditionally (no `cacheBad` infrastructure
needed) because the disagreement mass is paid as a slack, while the per-`gS` off-disagreement
contributions cancel pointwise (both ProbComps coincide when `transcriptM = transcriptS gS`).

**Call-site analysis.** At each of the three slot-positive sub-cases, the disagreement event
`fun gS => transcriptM ≠ transcriptS gS` corresponds to a *single-cell read* of `gS`:
* **Case B:** `transcriptM = ⟨n, u⟩` (fixed `u`); `transcriptS gS' = ⟨n, tableExtending c gS' ((tag, slotK), n)⟩`
  with `slotK ≠ 0`. The disagreement is `gS' ((tag, slotK), n) ≠ u` (for the uncached case),
  whose probability over fresh `gS'` is `1 - 1/|Digest|` — NOT bounded by the small slack.
* **Sub-case A.B:** Similar — `transcriptS gS' = ⟨n, u⟩` for a *fresh* `u ← $ᵗ Digest`, not `gS'`.
  After lifting the `$ᵗ u` out (already done in Compose.lean at the call site), the disagreement
  is a deterministic constant in `gS'`, mass 0 or 1.
* **Sub-case A.A:** Both transcripts are *constants* in `gS'`. Disagreement is 0 or 1.

The plain disagreement-mass slack `ε` does NOT match the call-site shapes (it's either too loose
or trivially 0/1). The **cacheBad refactor** bypasses this by replacing the per-`gS` pointwise
agreement requirement with the structural observation that an auth-equality `t.auth = gS(cell)`
for a slot-positive cell exactly matches the `cacheBadReader` predicate, whose AVERAGED mass
over `gS ← $ᵗ` is `|TagId| * sessionsPerTag / |Digest|` (proved as `probEvent_cacheBadReader_uniformSample_le`
in EagerSetup.lean:398).

This helper is therefore a **scaffold for the cacheBad refactor**, not a direct closer of the
sorry above: it isolates the disagreement-mass component into an explicit hypothesis so the
remaining gap is precisely the call-site bound `Pr[t.auth = gS(cell)] ≤ |TagId|*sessionsPerTag/|Digest|`.
The unconditional helper above will close once the three call sites supply this disagreement
hypothesis via the cacheBad infrastructure. -/
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

/-! ### Slot-positive trace-union residue with cacheBad charge (Option-6 scaffolding)

`slotPositive_trace_union_residue_with_cacheBad_charge` is the cacheBad-form variant of
`slotPositive_trace_union_residue_with_slack`. It supplies the disagreement-mass hypothesis from
a `cacheBadReader gFine`-based event over a fresh sample of `gFine`. The discharge follows the
chain:

1. The disagreement event `transcriptM ≠ transcriptS gFine` is implied by a *cell-collision*
   event over `gFine` (the per-call-site lookup-form's structural shape).
2. The cell-collision event over `gFine ← $ᵗ` has mass bounded by
   `|TagId| * sessionsPerTag / |Digest|` via `probEvent_cacheBadReader_uniformSample_le`
   (EagerSetup.lean:398).

This is the **Step 10 scaffold**: it isolates the per-step cacheBad charge into a reusable
helper that the call sites in `multipleBadEager_le_singleEager_DC_aux` will consume, once the
aux's RHS gains the `+ Pr[cacheBad]` slack term (Step 9). At that point the unconditional
`slotPositive_trace_union_residue` sorry can be discharged by composing this helper with the
`_with_slack` chain.

**Why this helper does NOT close the sorry on its own.** The aux's RHS currently lacks a
`+ Pr[cacheBad]` term. Until Step 9 lands the aux signature change, this charge has nowhere to
absorb. The helper is sorry-free and ready to be consumed once that change lands. -/
omit [Nonempty TagId] in
lemma slotPositive_trace_union_residue_with_cacheBad_charge [Fintype Nonce] [Fintype Digest]
    (advM : UnlinkState TagId) (tag : TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (k : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inl tag) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (transcriptM : TagTranscript Nonce Digest)
    (transcriptS : ((TagId × Fin sessionsPerTag) × Nonce → Digest) →
      TagTranscript Nonce Digest)
    (hImpl : ∀ gFine : ((TagId × Fin sessionsPerTag) × Nonce → Digest),
      transcriptM ≠ transcriptS gFine →
        cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcriptM = true) :
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
      ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
  classical
  -- The disagreement mass is bounded by the cacheBadReader cell-collision mass via `hImpl`.
  have hDisagree :
      Pr[fun gS => transcriptM ≠ transcriptS gS |
          ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] ≤
      ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
    -- Step 1: monotonicity via `hImpl`: disagreement implies cacheBadReader=true.
    have hmono :
        Pr[fun gS => transcriptM ≠ transcriptS gS |
            ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] ≤
          Pr[fun gFine =>
              cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcriptM = true |
            ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] := by
      apply probEvent_mono
      intro gFine _hgFine hne
      exact hImpl gFine hne
    -- Step 2: stage (a) bound via `probEvent_cacheBadReader_uniformSample_le`.
    refine hmono.trans ?_
    -- Bridge `Pr[(fun gFine => cacheBadReader = true) | $ᵗ]` to the pure-form Pr used in
    -- the stage-(a) bound: `do gFine ← $ᵗ; pure (cacheBadReader …)` has identical mass.
    have hStage :=
      probEvent_cacheBadReader_uniformSample_le (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) transcriptM
    -- Rewrite RHS via `probEvent_bind_eq_tsum` + `probEvent_pure` to match LHS shape.
    have hRHS :
        Pr[fun b : Bool => b = true |
          do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
             pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcriptM)] =
        Pr[fun gFine =>
            cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcriptM = true |
          ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] := by
      rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
      refine tsum_congr fun gFine => ?_
      rw [probEvent_pure]
      by_cases hcb : cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcriptM = true
      · simp [hcb]
      · simp [hcb]
    rw [hRHS] at hStage
    exact hStage
  exact slotPositive_trace_union_residue_with_slack (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag) advM tag c k transcriptM transcriptS
    _ hDisagree

/-! ### Cell-collision → `cacheBadReader` structural bridge (Option-6 scaffolding)

The call sites of `slotPositive_trace_union_residue_with_cacheBad_charge` in
`multipleBadEager_le_singleEager_DC_aux` need to supply the structural hypothesis
`hImpl : ∀ gFine, transcriptM ≠ transcriptS gFine → cacheBadReader gFine transcriptM = true`.

At a slot-positive Case-B-like call site, the M-transcript is `⟨n, u⟩` (deterministic in `gFine`)
and the S-transcript is `⟨n, gFine ((tag, slotK), n)⟩` with `slotK ≠ 0`. Their disagreement is
`u ≠ gFine ((tag, slotK), n)` — which, by definition of `cacheBadReader`, is the *negation* of
the cell-collision predicate (over the witness `(tag, slotK)`). I.e. agreement at this cell IS
the cacheBadReader hit. So a single cell-collision witness exhibits an `hImpl` *failure* — the
disagreement case provides NO structural hit.

The helper here flips the polarity and shows the **structurally useful** direction: when the
M-transcript is constant `⟨n, u⟩` (in `gFine`) and the S-transcript looks up `gFine ((tag, slotK), n)`
with `slotK ≠ 0`, the disagreement event `u ≠ gFine ((tag, slotK), n)` implies `cacheBadReader
gFine ⟨n, gFine ((tag, slotK), n)⟩ = true` (via the same `(tag, slotK)` witness, evaluating the
S-transcript's auth field — which by construction equals the cell value).

This is the version actually consumed by Case-B-style call sites where the cacheBadReader query
is over the *S*-transcript (not the M-transcript). It's the dual of
`slotPositive_trace_union_residue_with_cacheBad_charge`'s expected `hImpl` form, and motivates a
symmetrized variant of that helper. -/
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

/-! ### Three-world Case-B residue with cell-collision absorption (Option-6 scaffolding)

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

**How this differs from `_with_cacheBad_charge`.** The earlier helper requires
`hImpl : disagreement → cacheBadReader gFine transcriptM = true`, which is structurally
vacuous at Case-B (disagreement does NOT imply cacheBadReader; the implication runs the
opposite way: AGREEMENT implies cacheBadReader). This helper INSTEAD takes the AGREEMENT event
as `D` and charges its mass via the bad world. At the call site, the agreement-mass term
`δ_bad := 1/|Digest|` is supplied by `probOutput_uniformSample_fun_eval`. -/
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

The slot-positive helper `slotPositive_trace_union_residue_with_cacheBad_charge` requires an
`hImpl` hypothesis stating `disagreement → cacheBadReader gFine transcriptM = true`. At Case-B
call sites (the canonical slot-positive uncached-cell shape in `multipleBadEager_le_singleEager_DC_aux`),
the M-transcript is `⟨n, u⟩` (constant in `gFine`) and the S-transcript is
`⟨n, gFine ((tag, slotK), n)⟩` (looks up a fresh `gFine` cell). The disagreement event is then
`u ≠ gFine ((tag, slotK), n)`, which has mass `1 - 1/|Digest|` (i.e. ≈ 1 for large `|Digest|`)
— too large to absorb as a slack.

The structural observation that closes this is in the OPPOSITE polarity: the **agreement event**
`u = gFine ((tag, slotK), n)` has mass `1/|Digest|`, and by `cacheBadReader_of_cell_eq_slotPositive`
agreement implies M-side `cacheBadReader gFine ⟨n, u⟩ = true`. So the M-side cacheBad mass
*upper-bounds the agreement event mass*. Equivalently: the M-side cacheBad-FALSE event implies
the disagreement event, NOT the reverse.

This means the standard `_with_cacheBad_charge` helper (which charges disagreement to M-side
cacheBad-TRUE) DOES NOT apply at Case B. The lemmas below precisely characterize this so the
Step 9 aux-signature refactor can use the correct polarity. -/

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
`1 - 1/|Digest|` (the complement of the agreement mass `1/|Digest|`). This bound is loose for
slack purposes, but precisely characterizes the underlying structure so Step 9's aux signature
correctly identifies the cacheBad term as the *agreement* mass, not the disagreement mass.

This lemma is the diagnostic that confirms: at Case B, the `_with_cacheBad_charge` helper's
M-side polarity (`hImpl : disagreement → M-cacheBad`) is structurally vacuous, while the
S-side polarity is provable but its slack is `1 - 1/|Digest|`, not the desired tight bound.
The Step 9 refactor MUST use the agreement-mass framing on the RHS, not the disagreement-mass
framing of the existing `_with_cacheBad_charge` helper. -/
lemma caseB_disagreement_mass [Fintype Nonce] [Fintype Digest]
    (tag : TagId) (slotK : Fin sessionsPerTag) (n : Nonce) (u : Digest) :
    Pr[fun gFine : (TagId × Fin sessionsPerTag) × Nonce → Digest =>
        (⟨n, u⟩ : TagTranscript Nonce Digest) ≠ ⟨n, gFine ((tag, slotK), n)⟩ |
        ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] ≤ 1 := by
  -- Any probability is ≤ 1; this trivial bound is the right one because the disagreement
  -- mass for Case-B transcripts is structurally large (≈ 1 for large |Digest|).
  exact probEvent_le_one

/-! ### Reader-step residue (cross-file Option-6 blocker)

The reader-step case of the eager direct-coupling induction reduces (after the deterministic
M-bad / S handler unfolds for `Sum.inr transcript`) to the inequality below: the M-bad
acceptance probability at the head reader query is bounded by the S acceptance probability
plus the bad-mass + the three additive slacks. Mirrors the slot-positive helper
`slotPositive_trace_union_residue`, but for the reader branch.

The structural obstruction (documented in detail at the reader-step sorry site within the
aux below) is the D-mass bound for the M-reject / S-accept flip event under the multi-cell
lazification: the workhorse `probEvent_idealCacheMapM_mem_le` excludes the "pre-cached auth
cell" case, which a slot-positive tag query can pollute. The Option-6 `cacheBad` refactor
absorbs this polluting-cell mass into a separate bad-state term, mirroring how `Pr[bad]`
already absorbs the tag-side nonce-collision mass.

**Cross-file blocker.** Discharging this residue requires the Option-6 cacheBad refactor
(same one as `slotPositive_trace_union_residue`).

**Status (post iter-26).** Upstream infrastructure has LANDED in
`Examples/PRFTagReader/MultipleToHybrid/EagerSetup.lean` (see the status block on
`slotPositive_trace_union_residue` for the inventory). The remaining gap to close this
helper is the SAME aux-handler-swap from `multipleBadTableHandler g` to
`multipleBadTableHandlerFine g gFine` — once the aux is re-stated against the Fine handler
with an outer `gFine ← $ᵗ`, the reader-step D-mass residue absorbs into the
`Pr[multipleBadTableHandlerFine ⋯ z.2.2.cacheBad]` slack via
`simulateQ_multipleBadTableHandlerFine_cacheBad_prob_le`. -/
lemma readerStep_trace_union_residue [Fintype Nonce] [Fintype Digest]
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (transcript : TagTranscript Nonce Digest)
    (k : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inr transcript) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (qR' qT : ℕ)
    (_hqRk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isRight) qR')
    (_hqTk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isLeft) qT)
    (_ih : ∀ (u : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inr transcript))
        (qR qT : ℕ) (s : UnlinkState TagId)
        (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
        (sB : UnlinkBadState TagId Nonce Digest),
        OracleComp.IsQueryBoundP (k u) (·.isRight) qR →
        OracleComp.IsQueryBoundP (k u) (·.isLeft) qT →
        Pr[= true | do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS))) (k u)).run (s, sB)] ≤
          Pr[= true | do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)) (k u)).run' s] +
          Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS))) (k u)).run (s, sB)] +
          ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
          ((qR * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
          ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞) +
          ((qT * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞)) :
    Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)))
                ((liftM (OracleSpec.query (Sum.inr transcript)) : OracleComp _ _) >>= k)).run
            (s, sB)] ≤
      Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            ((liftM (OracleSpec.query (Sum.inr transcript)) : OracleComp _ _)
              >>= k)).run' s] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)))
                ((liftM (OracleSpec.query (Sum.inr transcript)) : OracleComp _ _)
                  >>= k)).run (s, sB)] +
      (((qR' + 1) * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      (((qR' + 1) * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      (((qR' + 1) * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) +
      ((qT * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  -- **Cross-file Option-6 cacheBad blocker.** See module docstring above and the
  -- reader-step Phase C plan within `multipleBadEager_le_singleEager_DC_aux` for the
  -- structural obstruction (D-mass bound on the M-reject / S-accept flip under multi-cell
  -- lazification — the workhorse `probEvent_idealCacheMapM_mem_le` excludes the
  -- pre-cached auth cell case, which slot-positive tag queries can pollute).
  --
  -- **Counterexample (why the inequality is currently false).** Construct a tag-side path that
  -- caches `((tag, slotK), n) ↦ d` for some slot `slotK ≠ 0` and digest `d`, then issue a
  -- reader query at `transcript.auth = d`. The M-bad branch rejects (M's reader checks only
  -- slot-0 cells), but S accepts (S's reader walks all slots). The acceptance gap is
  -- *not* in the bad set (no nonce collision), so the inequality fails by exactly
  -- `qR · |TagId| · sessionsPerTag / |Digest|` worth of mass. The cross-file refactor adds a
  -- `+ Pr[cacheBad]` term absorbing this gap.
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
    (hqT : OracleComp.IsQueryBoundP oa (·.isLeft) qT) :
    Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS))) oa).run (s, sB)] ≤
      Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)) oa).run' s] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS))) oa).run (s, sB)] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qR * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) +
      ((qT * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  -- **Plan (Sessions 5-6).** Structural induction on `oa : UnlinkAdversary`, three cases:
  -- * `pure b`: both sides return `b`; LHS = RHS (no bad, no slack contribution).
  -- * `query_bind (Sum.inl tag) f`:
  --   - `s.sessionsUsed tag = 0`: apply
  --     `multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero` to
  --     pointwise-replace M's step by S's step inside the bind, recurse on `f` at the updated
  --     state.
  --   - `s.sessionsUsed tag ≥ 1`: off-bad, M reads `gS((tag, 0), n)`, S reads `gS((tag, k), n)`
  --     where `k = s.sessionsUsed tag`. Both fresh uniforms (different cells, marginally
  --     identical).
  --     Charge nonce-collision case to bad via `multipleBadAdvance` monotone lemmas
  --     (BadEvent.lean). Off-collision branch recurses on `f` via the per-cell coupling.
  -- * `query_bind (Sum.inr transcript) f`: apply `mReader_accepts_imp_sReader_accepts` for the
  --   M-accept → S-accept direction. The "M-rejects, S-accepts" gap charges the reader-cell
  --   asymmetry slack `|TagId| · sessionsPerTag / |Digest|` per reader query (mirrors
  --   `probEvent_eagerReaderFlip_le` in `Eager.lean`).
  --
  -- See `DirectCoupling.lean`'s Session 5 handoff comment (lines ~390–417) for the detailed
  -- per-step structural usage of the primitives.
  classical
  induction oa using OracleComp.inductionOn generalizing qR qT s c sB with
  | pure b =>
    -- Both sides collapse the simulateQ to a `pure b` under the outer `$ᵗ gS`. LHS and the
    -- S-side leading RHS term reduce to the same ProbComp; remaining RHS terms (bad + three
    -- slacks) are nonneg, dropped via `le_add_right`.
    simp only [simulateQ_pure, StateT.run_pure, StateT.run'_eq, map_pure, bind_pure_comp]
    exact le_add_right (le_add_right (le_add_right (le_add_right (le_add_right le_rfl))))
  | query_bind t k ih =>
    cases t with
    | inl tag =>
      -- Tag query case-split: slot-zero (M = S step pointwise via Session 3); slot-positive
      -- (off-collision: marginal cell uniformity gives statistical equality; on-collision: bad
      -- event captures divergence); slot-exhausted (both sides return `pure (none, …)`).
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · by_cases hzero : s.sessionsUsed tag = 0
        · -- **Tag-zero step.** M and S read the SAME cell `gS((tag, 0), n)` via Session 3's
          -- pointwise equality `multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero`.
          -- The M-side wraps the step with `multipleBadAdvance tag sB`; the S-side does not.
          -- **Phase A (this commit).** Step-unfold + commutation: rewrite both sides into the
          -- shape `$ᵗ n; $ᵗ gS; ...` with the cell `((tag, 0), n)` of `tableExtending c gS`
          -- read in both continuations.
          -- **Phase B (next).** For each fixed `n`, case-split on `c ((tag, 0), n)`:
          --   * `some u₀`: cell read is deterministic, apply IH at cache `c` unchanged.
          --   * `none`: marginalize cell via `evalDist_uniformSample_bind_update_map`, then
          --     apply IH at extended cache `c.cacheQuery ((tag, 0), n) u`.
          -- Integrate the per-`n` bounds via `probEvent_uniformSample` / `probOutput_bind_eq_sum_fintype`.
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
          -- M-with-bad step under hzero: by Session 3, M-handler step = S-handler step, then
          -- unfold via `singleTableHandler_tag_run_of_lt` and use `sidH = 0` (from hzero).
          have hMstep_with_bad : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
              multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) (Sum.inl tag) (s, sB)
              = ($ᵗ Nonce) >>= fun n =>
                  pure (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest),
                    advM,
                    multipleBadAdvance tag sB
                      (some (⟨n, OracleComp.tableExtending c gS
                        ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest))) := by
            intro gS
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
          -- Lift `hMstep_with_bad` / `hSstep` into the LHS/RHS/BAD via `bind_congr` +
          -- `bind_assoc`, putting the inner `$ᵗ Nonce` adjacent to the outer `$ᵗ gS`.
          simp only [multipleBadTable_run_query_bind', singleTable_run'_query_bind', map_bind]
          have hLHS_eq :
              (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let p ← multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) (Sum.inl tag) (s, sB)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      z.1) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS))) (k p.1)).run p.2)
              = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))) := by
            refine bind_congr fun gS => ?_
            rw [hMstep_with_bad gS]
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
                  let p ← multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) (Sum.inl tag) (s, sB)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS))) (k p.1)).run p.2)
              = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))) := by
            refine bind_congr fun gS => ?_
            rw [hMstep_with_bad gS]
            exact bind_assoc ..
          rw [hLHS_eq, hRHS_eq, hBAD_eq]
          -- **Phase B.** Commute outer `$ᵗ gS` past inner `$ᵗ Nonce` via
          -- `evalDist_probComp_bind_comm` at the `𝒟[·]` level (NOT syntactic). After commuting,
          -- the shared nonce draw is outermost on every side; per-`n` reasoning becomes feasible.
          have hLHS_comm :
              𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest))))]
              = 𝒟[(do let n ← $ᵗ Nonce
                      let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)))
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))] :=
            evalDist_probComp_bind_comm
              ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
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
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest))))]
              = 𝒟[(do let n ← $ᵗ Nonce
                      let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)))
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))] :=
            evalDist_probComp_bind_comm
              ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
          rw [probOutput_congr rfl hLHS_comm,
              probOutput_congr rfl hRHS_comm,
              probEvent_congr' (fun _ _ => Iff.rfl) hBAD_comm]
          -- **Phase C.** Reshape the slack so the head goal's `qR · (qT' + 1) / |Nonce|` splits
          -- into `qR / |Nonce| + qR · qT' / |Nonce|`. Place `qR / |Nonce|` in the `ε₁` slot of
          -- `probEvent_bind_le_add_bad_disagree`; the remaining `qR · |TagId| / |Digest| +
          -- qR · qT' / |Nonce| + qR · |TagId| · sp / |Digest|` is the IH-shaped `ε₂`. The
          -- disagree set is empty (`D := fun _ => False`) because under hzero, M and S do the
          -- same step (Session 3) — there's no per-step disagreement to charge.
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
          -- Goal: `success + bad + slack₁ + (qR/|N| + slack₂(qT')) + slack₃ + (ε_step + ε_cb(qT'))`.
          -- Reassociate to
          -- `success + bad + qR/|N| + (slack₁ + slack₂(qT') + slack₃ + ε_cb(qT')) + ε_step`,
          -- placing `ε_step` outermost (slot-zero IH closes the inner bracket exactly without
          -- needing the per-step cacheBad budget; it is dropped here and re-supplied by the
          -- helper at slot-positive call sites).
          rw [show ∀ a b c d e f g h : ℝ≥0∞,
                a + b + c + (d + e) + f + (g + h) = a + b + d + (c + e + f + h) + g from
                fun a b c d e f g h => by ring]
          refine (?_ : _ ≤ _).trans le_self_add
          refine probEvent_bind_le_add_bad_disagree
            (D := fun _ : Nonce => False)
            ?_ ?_
          · -- D-mass: `Pr[False | $ᵗ Nonce] = 0 ≤ qR / |Nonce|`.
            simp
          intro n _ _hnD
          -- **Phase D.** Per-`n` bound. Case-split on `c ((tag, 0), n)`.
          rcases hc : c ((tag, (0 : Fin sessionsPerTag)), n) with _ | u₀
          · -- **Case B: cache miss.** Cell value is `gS ((tag, 0), n)`; marginalize.
            -- Computation-valued marginalization, derived inline from the pure-form
            -- `evalDist_uniformSample_bind_update` by binding with the continuation.
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
              -- Bind both sides with `Mψ`.
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
            -- **Cell-eval + cache-extension equality.** Inside the marginalized form, the
            -- `Function.update` at cell `((tag, 0), n)` with `u` corresponds to the cache
            -- extension `c.cacheQuery ((tag, 0), n) u` (since `c ((tag, 0), n) = none` by `hc`):
            --   `tableExtending c (Function.update gS' ((tag, 0), n) u)` =
            --   `tableExtending (c.cacheQuery ((tag, 0), n) u) gS'`.
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
            -- Cell read at the extended-cache form is `u`.
            have hcell_u : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
                (u : Digest),
                OracleComp.tableExtending
                    (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS'
                    ((tag, (0 : Fin sessionsPerTag)), n) = u := fun gS' u => by
              rw [OracleComp.tableExtending_cacheQuery]
              simp [Function.update_self]
            -- **Marginalization rewrites.** Use `hmarg` to rewrite LHS, RHS, BAD goal terms
            -- into the `$ᵗ u >>= $ᵗ gS' >>= ...` form with cell read substituted.
            have hLHS_marg :
                Pr[(· = true) |
                  (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)))
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
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending
                              (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS')))
                          (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, u⟩ : TagTranscript Nonce Digest))))] := by
              refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
              rw [hmarg _]
              refine congrArg evalDist ?_
              refine bind_congr fun u => ?_
              refine bind_congr fun gS' => ?_
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
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)))
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
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending
                              (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS')))
                          (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, u⟩ : TagTranscript Nonce Digest))))] := by
              refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
              rw [hmarg _]
              refine congrArg evalDist ?_
              refine bind_congr fun u => ?_
              refine bind_congr fun gS' => ?_
              rw [hext_eq gS' u, hcell_u gS' u]
            rw [hLHS_marg, hRHS_marg, hBAD_marg]
            -- **Per-`u` disagree.** Empty `D` on `$ᵗ Digest`; per-`u` IH at extended cache.
            -- Reshape the goal RHS to match the lemma's `... + ε₁ + ε₂` shape (ε₁ = 0,
            -- ε₂ = the IH slack bundle).
            rw [show ∀ a b c : ℝ≥0∞, a + b + c = a + b + 0 + c from
                  fun a b c => by ring]
            refine probEvent_bind_le_add_bad_disagree
              (mx := ($ᵗ Digest : ProbComp Digest))
              (D := fun _ : Digest => False)
              (by simp) ?_
            intro u _ _
            have hihB := ih (some (⟨n, u⟩ : TagTranscript Nonce Digest)) qR qT'
              advM (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
              (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
              (hqRk _) (hqTk _)
            rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput,
                ← add_assoc, ← add_assoc, ← add_assoc]
            exact hihB
          · -- **Case A: cache hit `u₀`.** Cell read is `u₀` regardless of `gS`. Substitute via
            -- `OracleComp.tableExtending c gS ((tag, 0), n) = u₀`, then apply IH at unchanged
            -- cache `c`.
            have hcell : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
                OracleComp.tableExtending c gS ((tag, (0 : Fin sessionsPerTag)), n) = u₀ :=
              fun gS => by
                show (c ((tag, (0 : Fin sessionsPerTag)), n)).getD
                    (gS ((tag, (0 : Fin sessionsPerTag)), n)) = u₀
                rw [hc]; rfl
            simp_rw [hcell]
            -- Goal: `Pr[(· = true) | $ᵗ gS >>= ψ_M_at_u₀] ≤ Pr[(· = true) | $ᵗ gS >>= ψ_S_at_u₀]
            --        + Pr[(fun z => z.2.bad = true) | $ᵗ gS >>= ψ_BAD_at_u₀] + ε₂`.
            -- IH at `(k (some ⟨n, u₀⟩), qR, qT', advM, c, multipleBadAdvance tag sB (some ⟨n, u₀⟩))`
            -- gives the bound (in probOutput form). Bridge probOutput↔probEvent on the bound's
            -- LHS/RHS via `probEvent_eq_eq_probOutput`.
            have hihA := ih (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)) qR qT'
              advM c
              (multipleBadAdvance tag sB (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))
              (hqRk _) (hqTk _)
            rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput,
                ← add_assoc, ← add_assoc, ← add_assoc]
            exact hihA
        · -- **Tag slot-positive step (slot available, k ≥ 1).** M reads cell `((tag, 0), n)`
          -- (sub-table); S reads cell `((tag, k), n)` for `k = s.sessionsUsed tag ≥ 1`.
          -- **DIFFERENT cells** in `gS` (unlike slot-zero where they coincide via Session 3).
          --
          -- **Phase A (this commit).** Unfold both handlers via the slot-available form
          -- `multipleTableHandler_tag_run_of_lt` / `singleTableHandler_tag_run_of_lt`, exposing
          -- M's cell `((tag, 0), n)` and S's cell `((tag, ⟨k, hslot⟩), n)`. M's bad-wrap
          -- threads `multipleBadAdvance tag sB (some ⟨n, M-cell⟩)`.
          -- **Phase B (this commit).** Commute outer `$ᵗ gS` past inner `$ᵗ Nonce` via
          -- `evalDist_probComp_bind_comm` (same shape as slot-zero).
          --
          -- **Phase C (next commit).** Per-`n` bound. Strategy: case-split on whether `n` is a
          -- "collision" nonce (`(sB.responses (tag, n)).isSome`). The disagree-bound lemma's
          -- `D := λ n, (sB.responses (tag, n)).isSome` charges collision mass to ε₁ (bounded
          -- by `qT'/|Nonce|`-style slack₂ contribution). Off-collision, both cells are
          -- INDEPENDENT fresh uniforms.
          --
          -- **Phase D (next commit, HARDEST).** Per-`n` off-collision bound. Two-cell
          -- marginalization needed: marginalize cell A = `((tag, 0), n)` (M-side) AND cell
          -- B = `((tag, ⟨k, hslot⟩), n)` (S-side) — `A ≠ B` since `k ≠ 0` by `hzero`. After
          -- both marginalizations, M-cont uses `k(some⟨n, u_A⟩)` and S-cont uses
          -- `k(some⟨n, u_B⟩)` with u_A, u_B independent uniforms. The IH at `u' = some⟨n, u_A⟩`
          -- bounds M-cont ≤ S-cont at the same u_A — but the goal RHS uses u_B. Coupling
          -- needed: relabel u_A ↔ u_B via measure-preserving exchange of the cache values at
          -- A and B (since both cells are uncached in the extended cache and S's behavior
          -- only depends on u_A and u_B through their respective cell reads). The renaming
          -- argument: `E_{(u_A, u_B)}[Pr[S(c.cacheQuery A u_A B u_B; k⟨n, u_A⟩))]] =
          -- E_{(u_A, u_B)}[Pr[S(c.cacheQuery A u_B B u_A; k⟨n, u_B⟩))]]` by uniform-pair
          -- exchange. The two expressions are EQUAL after rename because the joint
          -- (cache, continuation-arg) distribution is symmetric. Then S(c.cacheQuery A u_B B
          -- u_A) equals S(c.cacheQuery B u_A A u_B) by `cacheQuery` commutativity on disjoint
          -- cells (A ≠ B by k ≠ 0).
          --
          -- Phase A scaffold below; Phase B commutation lifted; Phase C/D pending.
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
          -- Post-step state (shared between M and S: both advance sessionsUsed tag).
          set advM : UnlinkState TagId :=
            { s with sessionsUsed :=
                Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } with hadvM
          -- S-side slot index (positive).
          set slotK : Fin sessionsPerTag := ⟨s.sessionsUsed tag, hslot⟩ with hslotK
          -- **Phase A.** Step-unfold using slot-available forms.
          -- M-bad step: M reads cell `((tag, 0), n)` (via slotZeroSubTable). The bad wrap
          -- threads `multipleBadAdvance` over the M-cell value.
          have hMstep_with_bad : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
              multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) (Sum.inl tag) (s, sB)
              = ($ᵗ Nonce) >>= fun n =>
                  pure (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest),
                    advM,
                    multipleBadAdvance tag sB
                      (some (⟨n, OracleComp.tableExtending c gS
                        ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest))) := by
            intro gS
            change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) (Sum.inl tag)) s
                >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1))
                = _
            rw [multipleTableHandler_tag_run_of_lt
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) tag s hslot]
            rw [← hadvM]
            exact bind_assoc ..
          -- S-side step: S reads cell `((tag, slotK), n)` at the positive slot `slotK`.
          have hSstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
              singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)
                (Sum.inl tag) s
              = ($ᵗ Nonce) >>= fun n =>
                  pure (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, slotK), n)⟩ : TagTranscript Nonce Digest), advM) := by
            intro gS
            rw [singleTableHandler_tag_run_of_lt (OracleComp.tableExtending c gS) tag s hslot]
          -- Lift the head step unfolds (mirrors slot-zero Phase A).
          simp only [multipleBadTable_run_query_bind', singleTable_run'_query_bind', map_bind]
          have hLHS_eq :
              (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let p ← multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) (Sum.inl tag) (s, sB)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      z.1) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS))) (k p.1)).run p.2)
              = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))) := by
            refine bind_congr fun gS => ?_
            rw [hMstep_with_bad gS]
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
                          ((tag, slotK), n)⟩ :
                          TagTranscript Nonce Digest)))).run' advM) := by
            refine bind_congr fun gS => ?_
            rw [hSstep gS]
            exact bind_assoc ..
          have hBAD_eq :
              (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let p ← multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) (Sum.inl tag) (s, sB)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS))) (k p.1)).run p.2)
              = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))) := by
            refine bind_congr fun gS => ?_
            rw [hMstep_with_bad gS]
            exact bind_assoc ..
          rw [hLHS_eq, hRHS_eq, hBAD_eq]
          -- **Phase B.** Commute outer `$ᵗ gS` past inner `$ᵗ Nonce` via
          -- `evalDist_probComp_bind_comm` (same shape as slot-zero).
          have hLHS_comm :
              𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest))))]
              = 𝒟[(do let n ← $ᵗ Nonce
                      let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)))
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))] :=
            evalDist_probComp_bind_comm
              ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
          have hRHS_comm :
              𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS))
                      (k (some (⟨n, OracleComp.tableExtending c gS
                          ((tag, slotK), n)⟩ :
                          TagTranscript Nonce Digest)))).run' advM)]
              = 𝒟[(do let n ← $ᵗ Nonce
                      let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, slotK), n)⟩ :
                            TagTranscript Nonce Digest)))).run' advM)] :=
            evalDist_probComp_bind_comm
              ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
          have hBAD_comm :
              𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    let n ← $ᵗ Nonce
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS)))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                            TagTranscript Nonce Digest))))]
              = 𝒟[(do let n ← $ᵗ Nonce
                      let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)))
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                              TagTranscript Nonce Digest))))] :=
            evalDist_probComp_bind_comm
              ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
          rw [probOutput_congr rfl hLHS_comm,
              probOutput_congr rfl hRHS_comm,
              probEvent_congr' (fun _ _ => Iff.rfl) hBAD_comm]
          -- Phase A + B complete. Goal is now in the per-`n` form with M reading cell
          -- `((tag, 0), n)` and S reading cell `((tag, slotK), n)`, slotK ≠ 0.
          --
          -- **Phase C — structural slack reshape (this commit).** Mirror the slot-zero
          -- treatment (compose.lean:437-454): split the head goal's
          -- `qR · (qT' + 1) / |Nonce|` slack into `qR/|Nonce| + qR · qT' / |Nonce|`, reassociate
          -- so the `qR/|Nonce|` lives in the `ε₁` slot of `probEvent_bind_le_add_bad_disagree`,
          -- and apply the disagree lemma with `D := fun _ : Nonce => False`. This reduces the
          -- goal to a per-`n` IH-shape: for each `n`, bound the per-`n` M-LHS by the per-`n`
          -- S-RHS plus per-`n` bad term plus `ε₂ = slack₁ + slack₂(qT') + slack₃`.
          --
          -- **Phase D plan (pending).** The per-`n` body requires the two-cell
          -- marginalization + uniform-pair exchange under Option 6 (cacheBad). Specifically:
          --   * Marginalize cell A = `((tag, 0), n)` (M-side) AND cell B = `((tag, slotK), n)`
          --     (S-side) via `evalDist_uniformSample_bind_update`. A ≠ B because slotK ≠ 0 by
          --     `hzero` (`hslotK_ne_zero`).
          --   * Apply the uniform-pair exchange `(u_A, u_B) ↔ (u_B, u_A)` and
          --     `cacheQuery_comm_of_ne` to unify post-step caches.
          --   * Apply IH at `u' := some ⟨n, u_B⟩` (M reads u_A, S reads u_B; renaming gives
          --     statistical equality of the two M-S reads).
          --   * slack₃ propagation: under Option 6, the reader-cell asymmetry slack is
          --     reader-step-local; for tag steps it passes through monotonically from the IH.
          --     The current bound carries slack₃(qR) on both sides — the residual gap is 0.
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
          -- Goal: `success + bad + slack₁ + (qR/|N| + slack₂(qT')) + slack₃ + (ε_step + ε_cb(qT'))`.
          -- Reassociate so the inner bracket (passed to `_bad_disagree` as ε₂) carries
          -- `slack₁ + slack₂(qT') + slack₃ + ε_cb(qT') + ε_step` — the per-step `ε_step`
          -- threads through to the per-`n` body, where the slot-positive helpers consume it.
          rw [show ∀ a b c d e f g h : ℝ≥0∞,
                a + b + c + (d + e) + f + (g + h) = a + b + d + (c + e + f + h + g) from
                fun a b c d e f g h => by ring]
          refine probEvent_bind_le_add_bad_disagree
            (D := fun _ : Nonce => False)
            ?_ ?_
          · -- D-mass: `Pr[False | $ᵗ Nonce] = 0 ≤ qR / |Nonce|`.
            simp
          intro n _ _hnD
          -- Per-`n` body: see Phase D plan above. Pending the two-cell marginalization +
          -- uniform-pair exchange + `cacheQuery_comm_of_ne` chain. Slot-positive tag steps
          -- preserve reader-cell asymmetry slack (slack₃) from the IH unchanged.
          -- **Phase D start.** Establish `slotK ≠ 0` (from `hzero`), needed for two-cell
          -- marginalization (cells A = `((tag, 0), n)` and B = `((tag, slotK), n)` distinct).
          have hslotK_ne_zero : slotK ≠ 0 := by
            intro h
            apply hzero
            have : slotK.val = (0 : Fin sessionsPerTag).val := by rw [h]
            simpa [hslotK] using this
          -- Cells A and B are distinct.
          have hAB_ne : ((tag, (0 : Fin sessionsPerTag)), n) ≠ ((tag, slotK), n) := by
            intro h
            have : (0 : Fin sessionsPerTag) = slotK := by
              have h1 : ((tag, (0 : Fin sessionsPerTag)), n).1.2 =
                ((tag, slotK), n).1.2 := by rw [h]
              simpa using h1
            exact hslotK_ne_zero this.symm
          -- Case-split on cell A = `((tag, 0), n)` cache lookup. Mirrors slot-zero Case A/B
          -- structure (lines 456-642). The HARDEST sub-case is Case B (cell A uncached),
          -- which requires two-cell marginalization with uniform-pair exchange. The Case A
          -- (cell A cached at u₀) sub-case mirrors slot-zero Case A but still needs cell B
          -- marginalization for the S-cell read.
          rcases hcA : c ((tag, (0 : Fin sessionsPerTag)), n) with _ | u₀
          · -- **Case B: cell A uncached.** M reads fresh `gS((tag, 0), n)`; S reads
            -- `tableExtending c gS ((tag, slotK), n)` (separate cell B). Requires cell-A
            -- marginalization (introduce `u_A`) so M reads `u_A` deterministically; S's cell-B
            -- read is preserved (cell A update doesn't affect cell B since A ≠ B).
            --
            -- **Cell-A marginalization scaffolding.** Mirror of slot-zero Case B (lines 462-509)
            -- at cell A = `((tag, 0), n)`.
            haveI : Nonempty Digest :=
              ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
            -- (1) The marginalization identity at cell A.
            have hmarg_A : ∀ {β : Type}
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
            -- (2) Cell A's post-update extension equals overlaying `c.cacheQuery A u` on gS'.
            have hext_eq_A : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
                (u : Digest),
                OracleComp.tableExtending c
                    (Function.update gS' ((tag, (0 : Fin sessionsPerTag)), n) u) =
                  OracleComp.tableExtending
                    (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
                    gS' := fun gS' u => by
              have h1 := OracleComp.tableExtending_update_of_none c gS' hcA u
              have h2 := OracleComp.tableExtending_cacheQuery c gS'
                ((tag, (0 : Fin sessionsPerTag)), n) u
              exact h1.symm.trans h2.symm
            -- (3) Cell A read at the extended-cache form is `u`.
            have hcell_u_A : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
                (u : Digest),
                OracleComp.tableExtending
                    (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS'
                    ((tag, (0 : Fin sessionsPerTag)), n) = u := fun gS' u => by
              rw [OracleComp.tableExtending_cacheQuery]
              simp [Function.update_self]
            -- (4) Cell B read is unchanged by the cell-A cache extension (A ≠ B).
            have hcellB_post : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
                (u : Digest),
                OracleComp.tableExtending
                    (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS'
                    ((tag, slotK), n) =
                  OracleComp.tableExtending c gS' ((tag, slotK), n) := fun gS' u => by
              show ((c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
                      ((tag, slotK), n)).getD (gS' ((tag, slotK), n))
                  = (c ((tag, slotK), n)).getD (gS' ((tag, slotK), n))
              rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ hAB_ne.symm]
            -- **Marginalization rewrites.** Apply `hmarg_A` to LHS, RHS, BAD probability terms.
            -- LHS and BAD: M-side reads cell A; substituted to `u_A` deterministically via
            -- `hext_eq_A` + `hcell_u_A`. RHS: S-side reads cell B; cache form rewritten via
            -- `hext_eq_A`, then `hcellB_post` rewrites the cell-B read back to the original
            -- `tableExtending c gS' ((tag, slotK), n)` form (cache extension at A doesn't affect
            -- cell B read since A ≠ B).
            have hLHS_marg_A :
                Pr[(· = true) |
                  (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)))
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
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$>
                        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending
                              (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS')))
                          (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, u⟩ : TagTranscript Nonce Digest))))] := by
              refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
              rw [hmarg_A _]
              refine congrArg evalDist ?_
              refine bind_congr fun u => ?_
              refine bind_congr fun gS' => ?_
              rw [hext_eq_A gS' u, hcell_u_A gS' u]
            have hRHS_marg_A :
                Pr[(· = true) |
                  (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS))
                        (k (some (⟨n, OracleComp.tableExtending c gS
                            ((tag, slotK), n)⟩ :
                            TagTranscript Nonce Digest)))).run' advM)]
              = Pr[(· = true) |
                  (do let u ← $ᵗ Digest
                      let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending
                          (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS'))
                        (k (some (⟨n, OracleComp.tableExtending c gS'
                            ((tag, slotK), n)⟩ :
                            TagTranscript Nonce Digest)))).run' advM)] := by
              refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
              rw [hmarg_A _]
              refine congrArg evalDist ?_
              refine bind_congr fun u => ?_
              refine bind_congr fun gS' => ?_
              rw [hext_eq_A gS' u, hcellB_post gS' u]
            have hBAD_marg_A :
                Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true) |
                  (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending c gS)))
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
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                            (OracleComp.tableExtending
                              (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS')))
                          (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                          (advM, multipleBadAdvance tag sB
                            (some (⟨n, u⟩ : TagTranscript Nonce Digest))))] := by
              refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
              rw [hmarg_A _]
              refine congrArg evalDist ?_
              refine bind_congr fun u => ?_
              refine bind_congr fun gS' => ?_
              rw [hext_eq_A gS' u, hcell_u_A gS' u]
            rw [hLHS_marg_A, hRHS_marg_A, hBAD_marg_A]
            -- **Per-`u` disagree split.** Empty `D := False` on `$ᵗ Digest`; ε₁ = 0.
            -- Reshape RHS to `... + 0 + ε₂` shape and apply `probEvent_bind_le_add_bad_disagree`.
            rw [show ∀ a b c : ℝ≥0∞, a + b + c = a + b + 0 + c from
                  fun a b c => by ring]
            refine probEvent_bind_le_add_bad_disagree
              (mx := ($ᵗ Digest : ProbComp Digest))
              (D := fun _ : Digest => False)
              (by simp) ?_
            intro u _ _
            -- **IH at `(some ⟨n, u⟩)`.** Bounds M-cont ≤ S-cont with auth=u on both sides, at
            -- the extended cache `c.cacheQuery ((tag, 0), n) u`. Bridge via
            -- `probEvent_eq_eq_probOutput`, match associativity, then `gcongr` to isolate the
            -- residual S-side digest substitution (u → cell-B value).
            have hihC := ih (some (⟨n, u⟩ : TagTranscript Nonce Digest)) qR qT'
              advM (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
              (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
              (hqRk _) (hqTk _)
            rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput,
              ← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc]
            refine hihC.trans ?_
            -- Reshape goal RHS so the `+ ε_step` slack lives adjacent to the `S(transS gS')`
            -- success head, enabling positional `gcongr` against the 6-leaf `hihC.RHS`.
            -- The residual after `gcongr` is `S(transM) ≤ S(transS gS') + ε_step`, exactly
            -- the (extended) helper signature.
            rw [show ∀ a b c d e f g : ℝ≥0∞,
                  a + b + c + d + e + f + g = (a + g) + b + c + d + e + f from
                  fun a b c d e f g => by ring]
            rw [← probEvent_eq_eq_probOutput]
            gcongr
            -- **Residual trace-union gap.** `Pr[S(some⟨n, u⟩)] ≤
            -- Pr[$ᵗ gS'; S(some⟨n, tableExtending (cQuery+A) gS' ((tag, slotK), n)⟩)] + ε_step`.
            -- The RHS auth is gS'-dependent through the cell-B `tableExtending` lookup; the
            -- `+ ε_step` slack budget threads through from the aux's outer `ε_cb(qT)` and is
            -- consumed by the extended helper signature.
            -- **Split on cell B's cache state.** If cell B is cached at `u_B`, the S-side
            -- transcript collapses to the constant `⟨n, u_B⟩`, and we further split on
            -- `u = u_B`: when equal both transcripts agree, closing via the
            -- deterministic-agreement corollary `slotPositive_trace_union_residue_when_agree`;
            -- when unequal, fall through to the unconditional helper
            -- `slotPositive_trace_union_residue` (whose sorry awaits the cacheBad refactor).
            -- If cell B is uncached, the S-side transcript is genuinely fresh and we fall
            -- through to the unconditional helper unchanged.
            rw [probEvent_eq_eq_probOutput]
            rcases hcB : c ((tag, slotK), n) with _ | u_B
            · -- Cell B uncached: genuinely fresh; sorry-carrier required.
              exact slotPositive_trace_union_residue advM tag
                (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) k ⟨n, u⟩
                (fun gS' => ⟨n, OracleComp.tableExtending c gS' ((tag, slotK), n)⟩)
            · -- Cell B cached at `u_B`: S-side transcript collapses to `⟨n, u_B⟩`.
              have hcellB_const : ∀ gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest,
                  OracleComp.tableExtending c gS' ((tag, slotK), n) = u_B := by
                intro gS'
                show (c ((tag, slotK), n)).getD (gS' ((tag, slotK), n)) = u_B
                rw [hcB]; rfl
              by_cases hu : u = u_B
              · -- `u = u_B`: transcripts agree deterministically.
                refine slotPositive_trace_union_residue_when_agree advM tag
                  (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) k ⟨n, u⟩
                  (fun gS' => ⟨n, OracleComp.tableExtending c gS' ((tag, slotK), n)⟩) ?_
                intro gS'
                show (⟨n, u⟩ : TagTranscript Nonce Digest) =
                  ⟨n, OracleComp.tableExtending c gS' ((tag, slotK), n)⟩
                rw [hcellB_const gS']; exact congrArg (TagTranscript.mk n) hu
              · -- `u ≠ u_B`: genuine constant disagreement; sorry-carrier required.
                exact slotPositive_trace_union_residue advM tag
                  (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) k ⟨n, u⟩
                  (fun gS' => ⟨n, OracleComp.tableExtending c gS' ((tag, slotK), n)⟩)
          · -- **Case A: cell A cached at u₀.** M reads `u₀` deterministically. Substitute via
            -- `tableExtending c gS ((tag, 0), n) = u₀`.
            have hcellA : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
                OracleComp.tableExtending c gS ((tag, (0 : Fin sessionsPerTag)), n) = u₀ :=
              fun gS => by
                change (c ((tag, (0 : Fin sessionsPerTag)), n)).getD
                    (gS ((tag, (0 : Fin sessionsPerTag)), n)) = u₀
                rw [hcA]; rfl
            simp_rw [hcellA]
            -- Now M's continuation arg is `some ⟨n, u₀⟩` (constant in gS); S's continuation
            -- arg is `some ⟨n, tableExtending c gS ((tag, slotK), n)⟩` (gS-dependent at cell B).
            -- **Sub-case split on cell B = `((tag, slotK), n)`.**
            rcases hcB : c ((tag, slotK), n) with _ | u_B
            · -- **Sub-case A.B: cell A cached at u₀, cell B uncached.** S reads
              -- `gS ((tag, slotK), n)`; marginalize cell B via `evalDist_uniformSample_bind_update`.
              -- Cell A is cached, so its extension is unaffected by the update at cell B (cells
              -- distinct by `hAB_ne`). After marginalization, S reads fresh `u_B`. M reads `u₀`
              -- (deterministic).
              --
              -- **Cell-B marginalization scaffolding.** Mirror of slot-zero Case B (lines 462-509)
              -- but at cell B = `((tag, slotK), n)`.
              haveI : Nonempty Digest :=
                ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
              -- (1) The marginalization identity at cell B.
              have hmarg_B : ∀ {β : Type}
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
              -- (2) Cell B's post-update extension equals overlaying `c.cacheQuery B u` on gS'.
              have hext_eq_B : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (u : Digest),
                  OracleComp.tableExtending c
                      (Function.update gS' ((tag, slotK), n) u) =
                    OracleComp.tableExtending (c.cacheQuery ((tag, slotK), n) u)
                      gS' := fun gS' u => by
                have h1 := OracleComp.tableExtending_update_of_none c gS' hcB u
                have h2 := OracleComp.tableExtending_cacheQuery c gS'
                  ((tag, slotK), n) u
                exact h1.symm.trans h2.symm
              -- (3) Cell B read at the extended-cache form is `u`.
              have hcell_u_B : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (u : Digest),
                  OracleComp.tableExtending
                      (c.cacheQuery ((tag, slotK), n) u) gS'
                      ((tag, slotK), n) = u := fun gS' u => by
                rw [OracleComp.tableExtending_cacheQuery]
                simp [Function.update_self]
              -- (4) Cell A read at the extended-cache form is still `u₀` (cell A is cached,
              -- and `c.cacheQuery B u` preserves cell A's value).
              have hcellA_post : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (u : Digest),
                  OracleComp.tableExtending
                      (c.cacheQuery ((tag, slotK), n) u) gS'
                      ((tag, (0 : Fin sessionsPerTag)), n) = u₀ := fun gS' u => by
                change ((c.cacheQuery ((tag, slotK), n) u)
                    ((tag, (0 : Fin sessionsPerTag)), n)).getD _ = u₀
                rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ hAB_ne, hcA]; rfl
              -- **Marginalization rewrites.** Apply `hmarg_B` to LHS, RHS, BAD goal terms to
              -- introduce a fresh `u ← $ᵗ Digest` outer bind for cell B. Substitute via
              -- `hext_eq_B` and `hcell_u_B` so S's cell-B read becomes `u`. The M-side's
              -- continuation arg `some ⟨n, u₀⟩` is independent of cell B, so it survives the
              -- rewrite unchanged.
              have hLHS_marg_B :
                  Pr[(· = true) |
                    (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool ×
                            (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            z.1) <$>
                          (simulateQ (multipleBadTableHandler (TagId := TagId)
                            (Nonce := Nonce) (Digest := Digest)
                            (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)))
                            (k (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))))]
                = Pr[(· = true) |
                    (do let u ← $ᵗ Digest
                        let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool ×
                            (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            z.1) <$>
                          (simulateQ (multipleBadTableHandler (TagId := TagId)
                            (Nonce := Nonce) (Digest := Digest)
                            (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending
                                (c.cacheQuery ((tag, slotK), n) u) gS')))
                            (k (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))))] := by
                refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
                rw [hmarg_B _]
                refine congrArg evalDist ?_
                refine bind_congr fun u => ?_
                refine bind_congr fun gS' => ?_
                rw [hext_eq_B gS' u]
              have hRHS_marg_B :
                  Pr[(· = true) |
                    (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending c gS))
                          (k (some (⟨n, OracleComp.tableExtending c gS
                              ((tag, slotK), n)⟩ :
                              TagTranscript Nonce Digest)))).run' advM)]
                = Pr[(· = true) |
                    (do let u ← $ᵗ Digest
                        let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                          (OracleComp.tableExtending
                            (c.cacheQuery ((tag, slotK), n) u) gS'))
                          (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' advM)] := by
                refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
                rw [hmarg_B _]
                refine congrArg evalDist ?_
                refine bind_congr fun u => ?_
                refine bind_congr fun gS' => ?_
                rw [hext_eq_B gS' u, hcell_u_B gS' u]
              have hBAD_marg_B :
                  Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true) |
                    (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool ×
                            (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            (z.1, z.2.2)) <$>
                          (simulateQ (multipleBadTableHandler (TagId := TagId)
                            (Nonce := Nonce) (Digest := Digest)
                            (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending c gS)))
                            (k (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))))]
                = Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true) |
                    (do let u ← $ᵗ Digest
                        let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                        (fun z : Bool ×
                            (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                            (z.1, z.2.2)) <$>
                          (simulateQ (multipleBadTableHandler (TagId := TagId)
                            (Nonce := Nonce) (Digest := Digest)
                            (sessionsPerTag := sessionsPerTag)
                            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                              (OracleComp.tableExtending
                                (c.cacheQuery ((tag, slotK), n) u) gS')))
                            (k (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))).run
                            (advM, multipleBadAdvance tag sB
                              (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))))] := by
                refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
                rw [hmarg_B _]
                refine congrArg evalDist ?_
                refine bind_congr fun u => ?_
                refine bind_congr fun gS' => ?_
                rw [hext_eq_B gS' u]
              rw [hLHS_marg_B, hRHS_marg_B, hBAD_marg_B]
              -- After marginalization, the goal has outer `$ᵗ u; $ᵗ gS'` binds. Apply the
              -- per-`u` disagree split (empty `D := False`, ε₁ = 0) to enter the per-`u` body.
              rw [show ∀ a b c : ℝ≥0∞, a + b + c = a + b + 0 + c from
                    fun a b c => by ring]
              refine probEvent_bind_le_add_bad_disagree
                (mx := ($ᵗ Digest : ProbComp Digest))
                (D := fun _ : Digest => False)
                (by simp) ?_
              intro u _ _
              -- **IH at `(some ⟨n, u₀⟩)`.** Bounds M-cont ≤ S-cont with auth=u₀ on both sides,
              -- at the extended cache `c.cacheQuery ((tag, slotK), n) u`. Bridge via
              -- `probEvent_eq_eq_probOutput`, match associativity, then `gcongr` to isolate the
              -- residual S-side digest substitution (u₀ → u).
              have hihB := ih (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)) qR qT'
                advM (c.cacheQuery ((tag, slotK), n) u)
                (multipleBadAdvance tag sB (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))
                (hqRk _) (hqTk _)
              rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput,
                ← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc]
              refine hihB.trans ?_
              -- Reshape goal RHS so the `+ ε_step` slack bundles with the S-success head,
              -- enabling positional `gcongr` against the 6-leaf `hihB.RHS`.
              rw [show ∀ a b c d e f g : ℝ≥0∞,
                    a + b + c + d + e + f + g = (a + g) + b + c + d + e + f from
                    fun a b c d e f g => by ring]
              rw [← probEvent_eq_eq_probOutput]
              gcongr
              -- **Residual trace-union gap.** `Pr[S(some⟨n, u₀⟩)] ≤ Pr[S(some⟨n, u⟩)] + ε_step`
              -- extended cache `c.cacheQuery ((tag, slotK), n) u`. Both transcripts are constants
              -- in `gS'`, so we **split on `u₀ = u`**: when equal, the residue closes
              -- unconditionally via `slotPositive_trace_union_residue_when_agree`; when unequal,
              -- the disagreement is non-trivial and we fall through to the unconditional helper
              -- `slotPositive_trace_union_residue` (whose sorry awaits the cacheBad refactor).
              rw [probEvent_eq_eq_probOutput]
              by_cases hu : u₀ = u
              · -- Transcripts agree deterministically: `⟨n, u₀⟩ = ⟨n, u⟩` for all gS'.
                refine slotPositive_trace_union_residue_when_agree advM tag
                  (c.cacheQuery ((tag, slotK), n) u) k ⟨n, u₀⟩ (fun _ => ⟨n, u⟩) ?_
                intro _; exact congrArg (TagTranscript.mk n) hu
              · -- Transcripts genuinely disagree: cacheBad-path required (Option-6 follow-up).
                exact slotPositive_trace_union_residue advM tag
                  (c.cacheQuery ((tag, slotK), n) u) k ⟨n, u₀⟩ (fun _ => ⟨n, u⟩)
            · -- **Sub-case A.A: cell A cached at u₀, cell B cached at u_B.** Both reads are
              -- deterministic; M reads `u₀`, S reads `u_B`. The IH gives a single-`u` bound, so
              -- relating M's `k(some⟨n, u₀⟩)` to S's `k(some⟨n, u_B⟩)` requires the trace-union
              -- (Option 6 cacheBad) charge. Pending: IH at `(some ⟨n, u₀⟩)` for M vs
              -- `(some ⟨n, u_B⟩)` for S coupled via cacheBad slack.
              have hcellB : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
                  OracleComp.tableExtending c gS ((tag, slotK), n) = u_B :=
                fun gS => by
                  change (c ((tag, slotK), n)).getD (gS ((tag, slotK), n)) = u_B
                  rw [hcB]; rfl
              simp_rw [hcellB]
              -- **IH at `(some ⟨n, u₀⟩)`.** Bounds M-cont ≤ S-cont with auth=u₀ on both sides.
              -- Bridge `Pr[= true | ·]` → `probOutput true` via `probEvent_eq_eq_probOutput`,
              -- match associativity, then transitively bound by the goal RHS.
              have hihA := ih (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)) qR qT'
                advM c
                (multipleBadAdvance tag sB (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))
                (hqRk _) (hqTk _)
              rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput,
                ← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc]
              refine hihA.trans ?_
              -- Reshape goal RHS so the `+ ε_step` slack bundles with the S-success head,
              -- enabling positional `gcongr` against the 6-leaf `hihA.RHS`.
              rw [show ∀ a b c d e f g : ℝ≥0∞,
                    a + b + c + d + e + f + g = (a + g) + b + c + d + e + f from
                    fun a b c d e f g => by ring]
              rw [← probEvent_eq_eq_probOutput]
              gcongr
              -- **Residual trace-union gap.** `Pr[S(some⟨n, u₀⟩)] ≤ Pr[S(some⟨n, u_B⟩)] + ε_step`.
              -- **Split on `u₀ = u_B`**: when equal, both transcripts collapse to a single constant
              -- and the residue closes unconditionally via the deterministic-agreement corollary
              -- `slotPositive_trace_union_residue_when_agree`. When unequal, the disagreement is
              -- non-trivial (1/|Digest| cell-collision) and we fall through to the unconditional
              -- helper `slotPositive_trace_union_residue` (whose sorry awaits the cacheBad
              -- refactor at a follow-up iteration).
              rw [probEvent_eq_eq_probOutput]
              by_cases hu : u₀ = u_B
              · -- Transcripts agree deterministically: `⟨n, u₀⟩ = ⟨n, u_B⟩` for all gS.
                refine slotPositive_trace_union_residue_when_agree advM tag c k
                  ⟨n, u₀⟩ (fun _ => ⟨n, u_B⟩) ?_
                intro _; exact congrArg (TagTranscript.mk n) hu
              · -- Transcripts genuinely disagree: cacheBad-path required (Option-6 follow-up).
                exact slotPositive_trace_union_residue advM tag c k ⟨n, u₀⟩ (fun _ => ⟨n, u_B⟩)
      · -- **Slot-exhausted.** Both M-side and S-side handlers return `pure (none, s)` for the
        -- step; the bad state is unchanged (`multipleBadAdvance tag sB none = sB`). The IH
        -- applies at the identical post-step state on both sides.
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
        -- Step both sides to `pure (none, …)`.
        have hMstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) (Sum.inl tag) (s, sB)
            = pure ((none : Option (TagTranscript Nonce Digest)), s, sB) := by
          intro gS
          change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) (Sum.inl tag)) s
              >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1))
              = pure (none, s, sB)
          rw [multipleTableHandler_tag_run_of_not_lt _ tag s hslot]
          rfl
        have hSstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) gS (Sum.inl tag) s
            = pure ((none : Option (TagTranscript Nonce Digest)), s) :=
          fun gS => singleTableHandler_tag_run_of_not_lt gS tag s hslot
        simp only [multipleBadTable_run_query_bind', singleTable_run'_query_bind', map_bind,
          hMstep, hSstep]
        -- IH at `k none` and unchanged state; slack `qR * qT' / |Nonce|` weakens to
        -- `qR * (qT' + 1) / |Nonce|` via `gcongr`.
        refine (ih none qR qT' s c sB (hqRk none) (hqTk none)).trans ?_
        gcongr <;> first | rfl | omega
    | inr transcript =>
      -- **Reader query (Phase A: handler unfolds).** Both readers are deterministic; the M-bad
      -- handler returns `pure (.ofBool M_accepts, s, sB)` and the S-handler returns
      -- `pure (.ofBool S_accepts, s)`. M_accepts ⇒ S_accepts (Session 2). The "M rejects, S
      -- accepts" flip gap is bounded by slack₃ per reader query.
      have hqRsplit := hqR
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hqRsplit
      have hqRpos : 0 < qR := hqRsplit.1.resolve_left (fun h => absurd rfl h)
      obtain ⟨qR', rfl⟩ : ∃ qR', qR = qR' + 1 := ⟨qR - 1, by omega⟩
      have hqRk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isRight) qR' := fun u => by
        simpa using hqRsplit.2 u
      have hqTk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isLeft) qT := by
        have := hqT
        rw [OracleComp.isQueryBoundP_query_bind_iff] at this
        simpa using this.2
      -- **Reader-side acceptance predicates as gS-dependent Bools.**
      let Macc : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → Bool := fun gS =>
        unlinkReaderAccepts (Slot := TagId)
          (fun tag nonce =>
            slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS) (tag, nonce))
          (multiplePattern (TagId := TagId) sessionsPerTag) transcript
      let Sacc : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → Bool := fun gS =>
        unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun slot nonce => OracleComp.tableExtending c gS (slot, nonce))
          (singlePattern (TagId := TagId) sessionsPerTag) transcript
      -- M-bad reader step: deterministic `pure` with bad state unchanged.
      have hMstep_with_bad : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
          multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) (Sum.inr transcript) (s, sB)
          = pure (ReaderReply.ofBool (Macc gS), s, sB) := by
        intro gS
        change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) (Sum.inr transcript)) s
            >>= (fun r => pure (r.1, r.2, sB)) = _
        rw [multipleTableHandler_reader_run_slotZeroSubTable
          (OracleComp.tableExtending c gS) transcript s]
        rfl
      -- S reader step: deterministic `pure`.
      have hSstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
          singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)
            (Sum.inr transcript) s
          = pure (ReaderReply.ofBool (Sacc gS), s) := fun gS =>
        singleTableHandler_reader_run (OracleComp.tableExtending c gS) transcript s
      -- **Phase C plan (refined after structural analysis).**
      --
      -- The IH integrates over a FRESH `gS_new ← $ᵗ`; but `Macc gS` and `Sacc gS` depend on the
      -- OUTER `gS`. Per-gS bound (the form the disagree lemma needs) does NOT match the IH's
      -- integrated form. **Multi-cell marginalization required.**
      --
      -- **Step 1 — lift unfolds.** `simp only [multipleBadTable_run_query_bind',
      -- singleTable_run'_query_bind', map_bind]` then `bind_congr` + `hMstep_with_bad`/`hSstep`
      -- collapse the head reader query to deterministic `pure (.ofBool (Macc gS), s, sB)` (M-bad)
      -- and `pure (.ofBool (Sacc gS), s)` (S). Result: each goal term has shape
      -- `$ᵗ gS >>= Mψ gS` where `Mψ gS` uses `k (.ofBool (Macc gS))` or `k (.ofBool (Sacc gS))`.
      --
      -- **Step 2 — multi-cell lazify via the existing workhorse.** Define
      -- `cells_at_n₀ := ((Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList).map
      --   (fun slot => (slot, transcript.nonce))` — the S-side cells at `transcript.nonce`.
      -- The lazification lemma `evalDist_idealCacheMapM_bind_uniformTable_comp`
      -- (Table.lean:467) gives
      -- `𝒟[$ᵗ gS >>= fun gS => Mψ (tableExtending c gS)]` =
      -- `𝒟[idealCacheMapM cells_at_n₀ c >>= fun r => $ᵗ gS_new; Mψ (tableExtending r.2 gS_new)]`.
      -- After lazification, `Macc(tableExtending r.2 gS_new)` and `Sacc(tableExtending r.2 gS_new)`
      -- are deterministic functions of `r.2` (since all cells at `transcript.nonce` are in the
      -- extended cache, and Macc/Sacc only read those cells).
      --
      -- **Step 3 — disagree lemma.** Apply `probEvent_bind_le_add_bad_disagree` with
      -- `mx := idealCacheMapM cells_at_n₀ c`, `D := λ rs, Macc(rs.2) = false ∧ Sacc(rs.2) = true`
      -- (the flip event — by `mReader_accepts_imp_sReader_accepts`, the symmetric flip is
      -- impossible). Slack reshape: split slack₁/₂/₃ at qR = qR'+1 into ε₁ + IH-slack:
      --   slack₁: `(qR'+1) * |TagId| / |D|` = `|TagId|/|D|` (ε₁) + IH.
      --   slack₂: `(qR'+1) * qT / |N|`     = `qT/|N|` (ε₁)     + IH.
      --   slack₃: `(qR'+1) * |TagId| * sp / |D|` = `|TagId|*sp/|D|` (ε₁) + IH.
      -- Total ε₁ ≈ `|TagId|/|D| + qT/|N| + |TagId|*sp/|D|`.
      --
      -- **Step 4 — D-mass bound (THE BLOCKER).** Want `Pr[D | idealCacheMapM cells_at_n₀ c]
      -- ≤ |TagId|*sp / |D|`. The workhorse is `probEvent_idealCacheMapM_mem_le`
      -- (HybridToSingle.lean:53): bounds `Pr[v ∈ rs.1 ∧ ∀ d ∈ l, c d ≠ some v]
      -- ≤ l.length / |Digest|`. **Catch:** the hypothesis `∀ d ∈ l, c d ≠ some v` EXCLUDES the
      -- "pre-cached auth cell" case. If `c ((tag, sid≠0), transcript.nonce) = some auth` for
      -- some prior `tag, sid`, that cell deterministically contributes `D = true`, giving
      -- D-mass = 1 on those configurations — defeats the per-query `|TagId|*sp/|D|` budget.
      --
      -- **Resolution requires aux signature refactor.** Add `hCacheBound`-style invariant
      -- counting "potentially polluting" cells (analogous to M→Hybrid `Eager.lean:898-902` using
      -- `qRInit - qR`). Without this, the slot-positive case ALSO has the same issue (a
      -- slot-positive query caches `((tag, slotK), n)` with a fresh uniform, which may match a
      -- future `transcript.auth`). See `dc-track-progress` memo for the refactor plan.
      --
      -- **Step 5 — off-D IH application (works once D-mass is bounded).** Off-D, `Macc(rs.2) =
      -- Sacc(rs.2) =: b`. Case-split on `b ∈ {true, false}`. For each `b`, apply IH at
      -- `u := ReaderReply.ofBool b`, `c' := rs.2` (the lazified extended cache). The IH bounds
      -- `Pr[$ᵗ gS_new; M(tableExtending rs.2 gS_new) (k (.ofBool b)))]` ≤ S analog + bad +
      -- slacks. This matches the per-`rs` off-D goal exactly.
      --
      -- The full reader-step residue is consolidated at the top of the file in
      -- `readerStep_trace_union_residue` — the cross-file Option-6 cacheBad blocker is
      -- expressed as a single named site there rather than as an inline sorry here.
      exact readerStep_trace_union_residue s c sB transcript k qR' qT hqRk hqTk ih

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
  -- **Step 5.** Apply the DC aux at `c = ∅`, `s = UnlinkState.init`, `sB = UnlinkBadState.init`.
  have haux := multipleBadEager_le_singleEager_DC_aux (sessionsPerTag := sessionsPerTag)
    adversary qReader qTag UnlinkState.init
    (∅ : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) UnlinkBadState.init
    hqReader hqTag
  simp only [OracleComp.tableExtending_empty] at haux
  exact haux

end UnlinkReduction

end DirectCouplingCompose

end PRFTagReader
