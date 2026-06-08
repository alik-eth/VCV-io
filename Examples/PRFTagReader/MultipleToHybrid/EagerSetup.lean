/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.MultipleToHybrid.Setup

/-!
# PRF Tag/Reader Protocol — Multiple-to-hybrid eager coupling, shared setup

Shared definitions and helpers for the eager-table multiple-vs-hybrid coupling proof. This
module hosts:

* the deterministic-table instrumented multiple-session handler `multipleBadTableHandler` and its
  per-step / per-run bad-flag monotonicity lemmas
  (`multipleBadTable_run_query_bind'`, `multipleBadTableHandler_step_preserves_bad`,
  `multipleBadTableHandler_run_preserves_bad`);
* the eager equivalence
  `evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending` lifting the lazy-vs-eager
  equivalence to the instrumented handler;
* the multiple-to-hybrid cell embedding `couplingEmbed` built from `chooseSid`, with its
  injectivity lemma and the table-projection distribution lemma
  `evalDist_couplingProject_uniformSample`.

The headline aux lemma `multipleBadEager_le_hybridEager_aux` and its two large sub-branches live
in the sibling modules `MultipleToHybrid.Eager` and `MultipleToHybrid.EagerReader`.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-! ### Reader-side cell-collision predicate (Option 6 scaffolding)

`cacheBadReader T transcript` is the deterministic Boolean predicate that holds at the queried
reader transcript `⟨nonce, auth⟩` against an eager fine-grained table `T` exactly when *some*
slot-positive cell at the queried nonce already carries the queried auth. Under the slot-zero
embedding, only slot-zero cells are M-reachable; a slot-positive collision is an
M-rejects / S-accepts witness — the structural origin of the trace-union residue blockers in
`DirectCoupling/Compose.lean`.

This is the deterministic per-reader-step indicator that, in the Option 6 (cacheBad) refactor,
is OR-accumulated into a `cacheBad` flag in the bad state via `multipleBadReaderAdvance`. With
the bad-state field in place, `Pr[cacheBad]` absorbs the reader-cell asymmetry slack
`qR · |TagId| * sessionsPerTag / |Digest|` as a separate bad-mass term, mirroring how
`Pr[bad]` already absorbs the tag-side nonce-collision mass.

Lives in this module (rather than `DirectCoupling.Compose`) so that the instrumented fine handler
`multipleBadTableHandlerFine` defined below can reach it without inducing an import cycle. -/
def cacheBadReader [Fintype TagId]
    (T : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (t : TagTranscript Nonce Digest) : Bool :=
  decide (∃ tag : TagId, ∃ sid : Fin sessionsPerTag, sid ≠ 0 ∧ T ((tag, sid), t.nonce) = t.auth)

/-- Reader-step bad-state advance: OR `cacheBadReader gFine transcript` into the `cacheBad`
flag, leaving every other field of the bad state untouched. This is the reader-side analogue of
`multipleBadAdvance`, but mutating `cacheBad` instead of `bad`. The two flags are independent:
reader steps never touch `bad`, tag steps never touch `cacheBad`. -/
def multipleBadReaderAdvance [Fintype TagId]
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) : UnlinkBadState TagId Nonce Digest :=
  { sB with cacheBad := sB.cacheBad ||
      cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript }

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] in
/-- `multipleBadReaderAdvance` preserves the tag-side `bad` flag (it only ORs into `cacheBad`). -/
@[simp] lemma multipleBadReaderAdvance_bad
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB).bad =
      sB.bad := rfl

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] in
/-- `multipleBadReaderAdvance` preserves `sessionsUsed`. -/
@[simp] lemma multipleBadReaderAdvance_sessionsUsed
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB).sessionsUsed =
      sB.sessionsUsed := rfl

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] in
/-- `multipleBadReaderAdvance` preserves `responses`. -/
@[simp] lemma multipleBadReaderAdvance_responses
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB).responses =
      sB.responses := rfl

/-! ### Multiple-to-hybrid: the eager-table instrumented multiple handler

The `MultipleHybridCoupling`-`inductionOn` route for the coupling bound is a proven dead end: a
`Prop`-valued state coupling cannot encode the run-determined session index that a later tag query
reads back. The eager route fixes this by sampling the random-oracle table up front.

`multipleBadTableHandler g` is the deterministic-table instrumented multiple handler: it runs the
deterministic real handler `multipleTableHandler g` on the multiple-ideal component and threads the
bad-world `UnlinkBadState` via `multipleBadAdvance` exactly as `multipleBadQueryImpl` does. The
eager equivalence `evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending` lifts the
lazy-vs-eager equivalence to the instrumented handler, threading the bad state. -/

/-- Deterministic-table instrumented multiple-session handler: runs `multipleTableHandler g` on the
multiple-ideal component (now just `UnlinkState`) and, on a tag query, advances the bad-world
component via `multipleBadAdvance`. The eager-table analogue of `multipleBadQueryImpl`. -/
noncomputable def multipleBadTableHandler (g : TagId × Nonce → Digest) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) ProbComp) :=
  fun q => fun p => match q with
    | Sum.inl tag =>
        (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1 >>= fun r =>
          pure (r.1, r.2, multipleBadAdvance tag p.2 r.1)
    | Sum.inr transcript =>
        (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1 >>= fun r =>
          pure (r.1, r.2, p.2)

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `simulateQ multipleBadTableHandler` of a `query_bind`, run from a state and projected to its
full output. -/
lemma multipleBadTable_run_query_bind' {α : Type} (g : TagId × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g) (liftM (OracleSpec.query t) >>= f)).run s =
      (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g t s) >>= fun p =>
        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g) (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Eager-table single-step bad monotonicity.** If the bad flag is already set in the
multiple-bad state `p.2`, then every reachable output of `multipleBadTableHandler g t p` keeps
`bad = true`. The eager-table analogue of `multipleBadQueryImpl_step_preserves_bad`; the proof
case-splits on tag vs. reader and unfolds `multipleBadAdvance`. -/
lemma multipleBadTableHandler_step_preserves_bad (g : TagId × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbad : p.2.bad = true) :
    ∀ z ∈ support (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g t p), z.2.2.bad = true := by
  cases t with
  | inl tag =>
    intro z hz
    change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1
        >>= fun r => pure (r.1, r.2, multipleBadAdvance tag p.2 r.1)) at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    cases hr : r.1 <;> simp [multipleBadAdvance, hbad]
  | inr transcript =>
    intro z hz
    change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1
        >>= fun r => pure (r.1, r.2, p.2)) at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    exact hbad

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Eager-table full-run bad monotonicity.** Starting `simulateQ multipleBadTableHandler` from a
state whose bad flag is set, every reachable output keeps `bad = true`. The eager-table analogue of
`multipleBadQueryImpl_run_preserves_bad`. -/
lemma multipleBadTableHandler_run_preserves_bad {α : Type} (g : TagId × Nonce → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbad : p.2.bad = true) :
    ∀ z ∈ support ((simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) oa).run p), z.2.2.bad = true := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure b =>
    intro z hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz; exact hbad
  | query_bind t f ih =>
    intro z hz
    rw [multipleBadTable_run_query_bind', mem_support_bind_iff] at hz
    obtain ⟨q, hq, hz⟩ := hz
    exact ih q.1 q.2 (multipleBadTableHandler_step_preserves_bad g t p hbad q hq) z hz

/-! ### Fine-grained eager handler (Option-6 scaffolding)

`multipleBadTableHandlerFine g gFine` is a *parallel* eager handler that runs identical M-side
dynamics to `multipleBadTableHandler g` (same coarse table `g : TagId × Nonce → Digest` for the
multiple-ideal output computation, so output-distribution-equivalent) but additionally threads a
fine-grained eager table `gFine : (TagId × Fin sessionsPerTag) × Nonce → Digest` through the
reader branch to advance the `cacheBad` flag via `multipleBadReaderAdvance`.

This is the Option-6 instrumented variant: invariant on the `bad` flag, on the multiple-ideal
output, and on `sessionsUsed` / `responses`; it only differs from `multipleBadTableHandler` in
the `cacheBad` field of the bad state on the reader branch.

The companion bound `Pr[cacheBad] ≤ qR · |TagId| * sessionsPerTag / |Digest|` (Step 8 of the
Option-6 plan) is stated against this handler. -/
noncomputable def multipleBadTableHandlerFine
    (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) ProbComp) :=
  fun q => fun p => match q with
    | Sum.inl tag =>
        (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1 >>= fun r =>
          pure (r.1, r.2, multipleBadAdvance tag p.2 r.1)
    | Sum.inr transcript =>
        (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1 >>= fun r =>
          pure (r.1, r.2,
            multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript p.2)

omit [Nonempty TagId] [SampleableType Digest] in
/-- `simulateQ multipleBadTableHandlerFine` of a `query_bind`, run from a state. Analogue of
`multipleBadTable_run_query_bind'`. -/
lemma multipleBadTableFine_run_query_bind' {α : Type} (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g gFine) (liftM (OracleSpec.query t) >>= f)).run s =
      (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g gFine t s) >>= fun p =>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g gFine) (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Fine eager-table single-step bad monotonicity.** If `bad` is set in the multiple-bad state
`p.2`, every reachable output of `multipleBadTableHandlerFine g gFine t p` keeps `bad = true`. The
reader branch ORs into `cacheBad` but never touches `bad`. -/
lemma multipleBadTableHandlerFine_step_preserves_bad (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbad : p.2.bad = true) :
    ∀ z ∈ support (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g gFine t p), z.2.2.bad = true := by
  cases t with
  | inl tag =>
    intro z hz
    change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1
        >>= fun r => pure (r.1, r.2, multipleBadAdvance tag p.2 r.1)) at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    show (multipleBadAdvance tag p.2 r.1).bad = true
    rcases r.1 with _ | tr
    · exact hbad
    · show (p.2.bad || _ : Bool) = true
      rw [hbad, Bool.true_or]
  | inr transcript =>
    intro z hz
    change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1
        >>= fun r => pure (r.1, r.2,
          multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript p.2)) at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    show (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
      gFine transcript p.2).bad = true
    rw [multipleBadReaderAdvance_bad]; exact hbad

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Fine eager-table full-run bad monotonicity.** Starting `simulateQ multipleBadTableHandlerFine`
from a state whose `bad` flag is set, every reachable output keeps `bad = true`. -/
lemma multipleBadTableHandlerFine_run_preserves_bad {α : Type} (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbad : p.2.bad = true) :
    ∀ z ∈ support ((simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run p),
        z.2.2.bad = true := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure b =>
    intro z hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz; exact hbad
  | query_bind t f ih =>
    intro z hz
    rw [multipleBadTableFine_run_query_bind', mem_support_bind_iff] at hz
    obtain ⟨q, hq, hz⟩ := hz
    exact ih q.1 q.2 (multipleBadTableHandlerFine_step_preserves_bad g gFine t p hbad q hq) z hz

/-! ### Per-step uniform-table cacheBadReader bound (Step 8 stage (a)) -/

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- **Single-cell marginal at a uniform function.** Drawing a uniform function `gFine` and
reading off its value at a fixed cell `x` produces a uniform digest, so any specific value `v`
appears with probability `1 / |Digest|`.

This is a consequence of the marginalization lemma
`OracleComp.evalDist_uniformSample_bind_update_map`: rewriting a uniform function as the
post-composition of a fresh uniform value at `x` with a uniform function at the remaining cells. -/
lemma probOutput_uniformSample_fun_eval [Fintype Nonce] [Fintype Digest] [Nonempty Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (x : (TagId × Fin sessionsPerTag) × Nonce) (v : Digest) :
    Pr[= v | do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
                pure (gFine x)] =
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  classical
  -- Bridge via `evalDist_uniformSample_bind_update_map` at the cell `x`, with `ψ = fun g => g x`.
  have hbridge :=
    OracleComp.evalDist_uniformSample_bind_update_map
      (D := (TagId × Fin sessionsPerTag) × Nonce) (R := Digest) x (fun g => g x)
  have hLHS :
      (do let u ← ($ᵗ Digest); let g ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
          pure ((Function.update g x u) x))
        = (do let u ← ($ᵗ Digest); let _g ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
              pure u) := by
    refine bind_congr fun u => bind_congr fun g => ?_
    rw [Function.update_self]
  rw [hLHS] at hbridge
  -- Use the equivalence on `Pr[= v |...]` to convert the target to `Pr[= v | $ᵗ Digest]`.
  have htarget : Pr[= v | do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
                              pure (gFine x)] =
                 Pr[= v | do let u ← ($ᵗ Digest);
                              let _g ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
                              pure u] := probOutput_congr rfl hbridge.symm
  rw [htarget]
  -- Eliminate the unused `_g` bind: probability factors as `Pr[= v | $ᵗ Digest] * 1`.
  rw [probOutput_bind_eq_tsum]
  have hinner : ∀ u : Digest,
      Pr[= v | (do let _g ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)); pure u)]
        = Pr[= v | (pure u : ProbComp Digest)] := fun u => by
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  simp_rw [hinner]
  -- ∑' u, Pr[= u | $ᵗ Digest] * Pr[= v | pure u] = Pr[= v | $ᵗ Digest]
  rw [show (∑' u : Digest, Pr[= u | ($ᵗ Digest)] * Pr[= v | (pure u : ProbComp Digest)]) =
        Pr[= v | (do let u ← ($ᵗ Digest); pure u : ProbComp Digest)]
      from (probOutput_bind_eq_tsum _ _ _).symm]
  rw [bind_pure, probOutput_uniformSample]

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce] in
/-- **Per-step uniform-table bound on `cacheBadReader`.** Sampling a uniform fine-grained
table `gFine` and checking `cacheBadReader gFine transcript`, the probability of a hit is
bounded by `|TagId| * sessionsPerTag / |Digest|`.

The proof is a union bound over the cell set `TagId × Fin sessionsPerTag` (existence in a
finset), where each summand is the single-cell marginal `1 / |Digest|` from
`probOutput_uniformSample_fun_eval`. The `sid ≠ 0` filter is dropped by monotonicity, giving
the slightly loose `|TagId| * sessionsPerTag` bound (rather than the tight
`|TagId| * (sessionsPerTag - 1)`). -/
lemma probEvent_cacheBadReader_uniformSample_le [Fintype Nonce] [Fintype Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (transcript : TagTranscript Nonce Digest) :
    Pr[fun b : Bool => b = true |
        do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
           pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript)] ≤
      ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  haveI : Nonempty Digest := ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  -- Step 1: expand the predicate. `cacheBadReader g t = true` is `∃ tag sid, sid ≠ 0 ∧
  -- g((tag,sid), t.nonce) = t.auth`; drop the `sid ≠ 0` filter by monotonicity.
  set P : (((TagId × Fin sessionsPerTag) × Nonce) → Digest) → Prop :=
    fun gFine => ∃ slot : TagId × Fin sessionsPerTag, slot ∈
      (Finset.univ : Finset (TagId × Fin sessionsPerTag)) ∧
      gFine (slot, transcript.nonce) = transcript.auth with hP
  have hmono :
      Pr[fun b : Bool => b = true |
          do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
             pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript)] ≤
        Pr[fun gFine => P gFine |
          ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] := by
    -- Direct via `probEvent_mono` once we rewrite the LHS into a `Pr[.. | $ᵗ]` form.
    rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite (p := fun gFine => P gFine)]
    refine ENNReal.tsum_le_tsum fun gFine => ?_
    -- Inner factor: `Pr[(b=true) | pure (cacheBadReader gFine t)] = if cacheBadReader gFine t then 1 else 0`
    have hinner :
        Pr[fun b : Bool => b = true |
            (pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript)
              : ProbComp Bool)] =
          (if cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript = true
            then (1 : ℝ≥0∞) else 0) := by
      simp
    rw [hinner]
    by_cases hcb : cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript = true
    · rw [if_pos hcb, mul_one, if_pos]
      unfold cacheBadReader at hcb
      rw [decide_eq_true_eq] at hcb
      obtain ⟨tag, sid, _, hg⟩ := hcb
      exact ⟨(tag, sid), Finset.mem_univ _, hg⟩
    · rw [if_neg hcb, mul_zero]; exact zero_le _
  refine hmono.trans ?_
  -- Step 2: union bound over the slot set.
  have hsum :
      Pr[fun gFine => P gFine |
          ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] ≤
        ∑ slot ∈ (Finset.univ : Finset (TagId × Fin sessionsPerTag)),
          Pr[fun gFine => gFine (slot, transcript.nonce) = transcript.auth |
            ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] := by
    simpa [P] using probEvent_exists_finset_le_sum
      (s := (Finset.univ : Finset (TagId × Fin sessionsPerTag)))
      (mx := ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)))
      (E := fun slot gFine => gFine (slot, transcript.nonce) = transcript.auth)
  refine hsum.trans ?_
  -- Step 3: each summand equals `1 / |Digest|` via the single-cell marginal.
  have hcell : ∀ slot : TagId × Fin sessionsPerTag,
      Pr[fun gFine => gFine (slot, transcript.nonce) = transcript.auth |
          ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))]
        = (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
    intro slot
    -- Rewrite the probEvent as `Pr[= transcript.auth | g ←$ᵗ; pure (g (slot, nonce))]`
    -- via the bind/map bridge, then apply the single-cell marginal.
    have hkey :
        Pr[fun gFine => gFine (slot, transcript.nonce) = transcript.auth |
            ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))]
          = Pr[= transcript.auth |
              do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
                 pure (gFine (slot, transcript.nonce))] := by
      rw [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite]
      refine tsum_congr fun gFine => ?_
      by_cases h : gFine (slot, transcript.nonce) = transcript.auth
      · simp [h, probOutput_pure]
      · simp only [h, ite_false, probOutput_pure]
        rw [if_neg (fun heq => h heq.symm), mul_zero]
    rw [hkey]
    exact probOutput_uniformSample_fun_eval (slot, transcript.nonce) transcript.auth
  rw [Finset.sum_congr rfl (fun slot _ => hcell slot)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [nsmul_eq_mul]
  rw [ENNReal.div_eq_inv_mul, Nat.cast_mul]
  rw [show (((Fintype.card Digest : ℝ≥0∞)⁻¹ *
    ((Fintype.card TagId : ℝ≥0∞) * (sessionsPerTag : ℝ≥0∞))))
      = ((Fintype.card TagId : ℝ≥0∞) * (sessionsPerTag : ℝ≥0∞) *
          (Fintype.card Digest : ℝ≥0∞)⁻¹) by ring]

/-! ### Step 8 stage (b) preservation helpers

The two single-step state-shape lemmas used by the full-run cacheBad bound (Step 8 stage (b),
landing in a follow-up iteration). They make the per-step state-transition transparent so the
inductive proof of the cacheBad bound can apply the IH directly on the continuation, threading
the (possibly-flipped) `cacheBad` field through the step.

* `multipleBadTableHandlerFine_tag_preserves_cacheBad`: tag-step does not touch `cacheBad`.
* `multipleBadTableHandlerFine_reader_state_eq`: reader-step advances `p.2` to
  `multipleBadReaderAdvance gFine transcript p.2`, leaving the `UnlinkState` (`p.1`) untouched
  modulo the deterministic table read.

Both are pure-add scaffolding — they leave the existing stage (a) bound and downstream
consumers untouched. -/

omit [Nonempty TagId] [SampleableType Digest] in
/-- Tag-step `cacheBad`-preservation observation: `multipleBadTableHandlerFine` on a tag query
keeps `p.2.cacheBad` unchanged across every reachable output. This is the deterministic
companion to `multipleBadAdvance` preserving `cacheBad` (only the `bad` field is touched). -/
lemma multipleBadTableHandlerFine_tag_preserves_cacheBad (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest) (tag : TagId)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    ∀ z ∈ support (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g gFine (Sum.inl tag) p),
        z.2.2.cacheBad = p.2.cacheBad := by
  intro z hz
  change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1
      >>= fun r => pure (r.1, r.2, multipleBadAdvance tag p.2 r.1)) at hz
  obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [mem_support_pure_iff] at hz
  subst hz
  show (multipleBadAdvance tag p.2 r.1).cacheBad = p.2.cacheBad
  cases r.1 <;> simp [multipleBadAdvance]

omit [Nonempty TagId] [SampleableType Digest] in
/-- Reader-step state shape: every reachable output of `multipleBadTableHandlerFine` on a reader
query has bad-state component exactly `multipleBadReaderAdvance gFine transcript p.2`. The
`UnlinkState` (`p.1`) advances exactly as the deterministic reader handler dictates. -/
lemma multipleBadTableHandlerFine_reader_state_eq (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (transcript : TagTranscript Nonce Digest)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    ∀ z ∈ support (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g gFine (Sum.inr transcript) p),
        z.2.2 =
          multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript p.2 := by
  intro z hz
  change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1
      >>= fun r => pure (r.1, r.2,
        multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript p.2)) at hz
  obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [mem_support_pure_iff] at hz
  subst hz
  rfl

/-- **Eager-table equivalence for the instrumented multiple handler.** Running the instrumented
multiple handler `multipleBadQueryImpl` from `((s, c), sB)` has the same *full-output* distribution
(output bit, multiple-ideal state and bad-world state) as sampling a full random-oracle table `g`,
overlaying the cache `c`, and running the deterministic instrumented table handler
`multipleBadTableHandler (tableExtending c g)` from `(s, sB)`.

Proved by induction on the adversary, generalized over the state. It mirrors
`evalDist_simulateQ_multipleIdealQueryImpl_run'_eq_tableExtending`, threading the bad-world
component (which `multipleBadAdvance` advances deterministically from the realized transcript). -/
lemma evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending
    [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId) (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) :
    𝒟[(fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => (z.1, z.2.2)) <$>
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) oa).run ((s, c), sB)] =
      𝒟[do let g ← $ᵗ (TagId × Nonce → Digest);
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c g)) oa).run (s, sB)] := by
  classical
  induction oa using OracleComp.inductionOn generalizing s c sB with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    refine (evalDist_ext fun x => ?_).symm
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  | query_bind t f ih =>
    rw [multipleBad_run_query_bind', map_bind]
    have hrhs : 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c g))
              (liftM (OracleSpec.query t) >>= f)).run (s, sB)]
        = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
            (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g) t (s, sB))
              >>= fun p =>
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g)) (f p.1)).run p.2] := by
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [multipleBadTable_run_query_bind', map_bind]
    rw [hrhs]
    cases t with
    | inl tag =>
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · -- tag query, slot available
        rw [multipleBadQueryImpl_tag_run tag ((s, c), sB)]
        dsimp only
        rw [multipleIdealQueryImpl_tag_run_of_lt tag s c hslot]
        set advU := ({ s with sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } : UnlinkState TagId) with hadvU
        -- Normalise the LHS: pull the nonce/cell binds to the top.
        have hlhs_norm :
            ((((($ᵗ Nonce) >>= fun nonce => idealCacheStep c (tag, nonce) >>= fun r =>
              pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest), advU, r.2))) >>=
              fun r => pure (r.1, (r.2.1, r.2.2), multipleBadAdvance tag sB r.1)) >>=
              fun p => (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                (z.1, z.2.2)) <$>
                (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run p.2)
            = (($ᵗ Nonce) >>= fun nonce => idealCacheStep c (tag, nonce) >>= fun r =>
                (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest)))).run
                    ((advU, r.2), multipleBadAdvance tag sB
                      (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest)))) := by
          simp only [bind_assoc, pure_bind]
        refine (congrArg evalDist hlhs_norm).trans ?_
        -- per-nonce eager equivalence under the inner idealCacheStep
        have hlhs_inner : ∀ (n : Nonce),
            𝒟[idealCacheStep c (tag, n) >>= fun r =>
                (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))).run
                    ((advU, r.2), multipleBadAdvance tag sB
                      (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))]
            = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c g))
                      (f (some (⟨n, OracleComp.tableExtending c g (tag, n)⟩ :
                        TagTranscript Nonce Digest)))).run
                      (advU, multipleBadAdvance tag sB (some (⟨n,
                        OracleComp.tableExtending c g (tag, n)⟩ :
                        TagTranscript Nonce Digest)))] := by
          intro n
          set Mψ : (TagId × Nonce → Digest) → ProbComp (Bool × UnlinkBadState TagId Nonce Digest) :=
            fun g' =>
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) g')
                (f (some (⟨n, g' (tag, n)⟩ : TagTranscript Nonce Digest)))).run
                (advU, multipleBadAdvance tag sB
                  (some (⟨n, g' (tag, n)⟩ : TagTranscript Nonce Digest)))
            with hMψ
          refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable_comp c (tag, n) Mψ)
          refine evalDist_bind_congr_of_support _ _ _ fun r hr => ?_
          rw [ih (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)) advU r.2
            (multipleBadAdvance tag sB (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))]
          refine congrArg _ (congrArg _ (funext fun g => ?_))
          have hcell : OracleComp.tableExtending r.2 g (tag, n) = r.1 := by
            simp only [OracleComp.tableExtending,
              idealCacheStep_cache_self c (tag, n) r hr, Option.getD_some]
          rw [hMψ]
          simp only [hcell]
        -- RHS: collapse the table-handler tag query and swap the two samples.
        have hrhs_swap :
            (($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
              (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)
                (Sum.inl tag) (s, sB)) >>= fun p =>
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c g)) (f p.1)).run p.2)
            = (($ᵗ (TagId × Nonce → Digest)) >>= fun g => ($ᵗ Nonce) >>= fun n =>
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c g))
                    (f (some (⟨n, OracleComp.tableExtending c g (tag, n)⟩ :
                      TagTranscript Nonce Digest)))).run
                    (advU, multipleBadAdvance tag sB (some (⟨n,
                      OracleComp.tableExtending c g (tag, n)⟩ :
                      TagTranscript Nonce Digest)))) := by
          refine bind_congr fun g => ?_
          show ((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)
              (Sum.inl tag)) s >>= (fun r => pure (r.1, r.2,
                multipleBadAdvance tag sB r.1))) >>= _ = _
          rw [multipleTableHandler_tag_run_of_lt _ tag s hslot, ← hadvU]
          simp only [bind_assoc, pure_bind]
          exact bind_assoc ..
        refine Eq.trans ?_ (congrArg evalDist hrhs_swap).symm
        rw [evalDist_probComp_bind_comm ($ᵗ (TagId × Nonce → Digest)) ($ᵗ Nonce)]
        refine evalDist_bind_congr_of_support _ _ _ fun n _ => ?_
        exact hlhs_inner n
      · -- tag query, slot exhausted
        rw [multipleBadQueryImpl_tag_run tag ((s, c), sB)]
        dsimp only
        rw [multipleIdealQueryImpl_tag_run_of_not_lt tag s c hslot]
        show 𝒟[(fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
            (z.1, z.2.2)) <$>
            (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f none)).run
              ((s, c), multipleBadAdvance tag sB none)] = _
        rw [ih none s c (multipleBadAdvance tag sB none)]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        show _ = ((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)
            (Sum.inl tag)) s >>= (fun r => pure (r.1, r.2,
              multipleBadAdvance tag sB r.1))) >>= _
        rw [multipleTableHandler_tag_run_of_not_lt _ tag s hslot]
        rfl
    | inr transcript =>
      rw [multipleBadQueryImpl_reader_run transcript ((s, c), sB)]
      dsimp only
      rw [multipleIdealQueryImpl_reader_run transcript s c]
      set cells := (Finset.univ : Finset TagId).toList.map
        (fun tag => (tag, transcript.nonce)) with hcells
      -- Normalise the LHS: pull all binds outward, projection at the leaf.
      have hlhs_norm :
          (((idealCacheMapM cells c >>= fun rs =>
                pure (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s, rs.2))
              >>= fun r => pure (r.1, (r.2.1, r.2.2), sB)) >>= fun p =>
              (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run p.2)
          = (idealCacheMapM cells c >>= fun rs =>
              (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run
                  ((s, rs.2), sB)) := by
        simp only [bind_assoc]; rfl
      refine (congrArg evalDist hlhs_norm).trans ?_
      -- eager equivalence under idealCacheMapM
      set Mψ : (TagId × Nonce → Digest) → ProbComp (Bool × UnlinkBadState TagId Nonce Digest) :=
        fun g' =>
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) g')
            (f (ReaderReply.ofBool (decide (∃ d ∈ cells.map g', d = transcript.auth))))).run
            (s, sB)
        with hMψ
      have hstep1 :
          𝒟[idealCacheMapM cells c >>= fun rs =>
              (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run
                ((s, rs.2), sB)]
          = 𝒟[idealCacheMapM cells c >>= fun rs =>
              ($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
                Mψ (OracleComp.tableExtending rs.2 g)] := by
        refine evalDist_bind_congr_of_support _ _ _ fun rs hrs => ?_
        rw [ih (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))) s rs.2 sB]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [hMψ]
        simp only [idealCacheMapM_support cells c rs hrs g]
      rw [hstep1, evalDist_idealCacheMapM_bind_uniformTable_comp cells c Mψ]
      -- RHS: collapse the table-handler reader query
      refine (evalDist_bind_congr_of_support _ _ _ fun g _ => ?_).symm
      have hrhs_reader : (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c g) (Sum.inr transcript) (s, sB))
          = pure (ReaderReply.ofBool (unlinkReaderAccepts (TagId := TagId) (Slot := TagId)
              (Nonce := Nonce) (Digest := Digest)
              (fun tag nonce => OracleComp.tableExtending c g (tag, nonce))
              (multiplePattern (TagId := TagId) sessionsPerTag) transcript), s, sB) := by
        change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)
            (Sum.inr transcript)) s >>= _ = _
        rw [multipleTableHandler_reader_run _ transcript s]; rfl
      rw [hrhs_reader, hMψ]
      have hAccept : decide (∃ d ∈ cells.map (OracleComp.tableExtending c g),
            d = transcript.auth)
          = unlinkReaderAccepts (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
            (fun tag nonce => OracleComp.tableExtending c g (tag, nonce))
            (multiplePattern (TagId := TagId) sessionsPerTag) transcript := by
        unfold unlinkReaderAccepts tagAccepts
        rw [hcells]
        simp only [List.map_map, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
          multiplePattern, decide_eq_decide, decide_eq_true_eq, Function.comp]
        constructor
        · rintro ⟨d, ⟨a, rfl⟩, hd⟩
          exact ⟨a, ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne sessionsPerTag)⟩, hd⟩⟩
        · rintro ⟨tag, _, hd⟩
          exact ⟨_, ⟨tag, rfl⟩, hd⟩
      rw [← hAccept]
      rfl

/-- The session index chosen to couple a multiple-world cell `(tag, n)` to a hybrid-world cell:
the (off-collision unique) session of `tag` that drew nonce `n`, defaulting to slot `0` when no
session drew it. -/
noncomputable def chooseSid
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag) (tag : TagId) (n : Nonce) :
    Fin sessionsPerTag :=
  if h : ∃ sid : Fin sessionsPerTag, sn (tag, sid) = some n then h.choose else 0

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [SampleableType Digest] in
/-- When some session of `tag` drew `n`, `chooseSid` returns a witness session. -/
lemma chooseSid_spec (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (tag : TagId) (n : Nonce) (h : ∃ sid : Fin sessionsPerTag, sn (tag, sid) = some n) :
    sn (tag, chooseSid (sessionsPerTag := sessionsPerTag) sn tag n) = some n := by
  rw [chooseSid, dif_pos h]; exact h.choose_spec

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [SampleableType Digest] in
/-- Off-collision (`hcf`), `chooseSid sn tag n` is *the* session that drew `n`. -/
lemma chooseSid_eq (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (hcf : ∀ tag sid₁ sid₂ n, sn (tag, sid₁) = some n → sn (tag, sid₂) = some n → sid₁ = sid₂)
    (tag : TagId) (sid : Fin sessionsPerTag) (n : Nonce) (hsn : sn (tag, sid) = some n) :
    chooseSid (sessionsPerTag := sessionsPerTag) sn tag n = sid :=
  hcf tag _ sid n (chooseSid_spec sn tag n ⟨sid, hsn⟩) hsn

/-- The coupling injection from multiple-world cells to hybrid-world cells induced by a
session-nonce map `sn`: send `(tag, n)` to the cell `((tag, chooseSid sn tag n), n)`. -/
noncomputable def couplingEmbed
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag) :
    TagId × Nonce → (TagId × Fin sessionsPerTag) × Nonce :=
  fun p => ((p.1, chooseSid (sessionsPerTag := sessionsPerTag) sn p.1 p.2), p.2)

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [SampleableType Digest] in
/-- The coupling embedding is injective: it preserves the tag and the nonce coordinates. -/
lemma couplingEmbed_injective
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag) :
    Function.Injective (couplingEmbed (sessionsPerTag := sessionsPerTag) sn) := by
  intro p q h
  simp only [couplingEmbed, Prod.mk.injEq] at h
  exact Prod.ext h.1.1 h.2

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest] in
/-- **State-dependent table coupling.** Drawing a uniform hybrid (fine) table `gH` and projecting
it along the coupling embedding yields the uniform distribution on multiple (coarse) tables. This
is the marginalization step underlying the hop-A coupled-table comparison: it lets a multiple-world
table draw be replaced by a projection of a single hybrid-world draw. -/
lemma evalDist_couplingProject_uniformSample [Fintype Nonce] [Finite Digest]
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag) :
    𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
        fun gH => pure (gH ∘ couplingEmbed (sessionsPerTag := sessionsPerTag) sn)] =
      𝒟[$ᵗ (TagId × Nonce → Digest)] := by
  haveI : Nonempty Digest := ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  exact evalDist_uniformSample_map_comp_injective (R := Digest)
    (couplingEmbed_injective (sessionsPerTag := sessionsPerTag) sn)

/-! ### Per-query fresh-table handler (Step 8 stage (b), fresh variant)

`multipleBadTableHandlerFineFresh g` is an alternative instrumented eager handler that, instead of
threading a *single* externally-sampled fine-grained table `gFine` across the whole run, samples a
*fresh* `gFine` per reader query. The tag branch is identical to `multipleBadTableHandlerFine` (no
`gFine` use). The reader branch first samples a fresh `gFine`, then ORs `cacheBadReader gFine
transcript` into `cacheBad`.

Why this variant: the full-run cacheBad bound on `multipleBadTableHandlerFine` runs into a coupling
obstruction — the inductive hypothesis would sample a fresh `gFine` inside the continuation, but
the outer handler reuses the SAME `gFine` across reader steps. With per-query-fresh sampling, the
induction goes through cleanly: each reader step independently pays
`|TagId| * sessionsPerTag / |Digest|` via the stage (a) bound, and the total over a
`qR`-bounded adversary is `qR * |TagId| * sessionsPerTag / |Digest|`.

This is purely additive scaffolding for the Option-6 (cacheBad) refactor: the bound on the
*shared-table* `multipleBadTableHandlerFine` will be derived from the fresh-variant bound via a
Fubini-style marginalization step in a follow-up iteration. -/
noncomputable def multipleBadTableHandlerFineFresh [Fintype Nonce] [Fintype Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (g : TagId × Nonce → Digest) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) ProbComp) :=
  fun q => fun p => match q with
    | Sum.inl tag =>
        (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1 >>= fun r =>
          pure (r.1, r.2, multipleBadAdvance tag p.2 r.1)
    | Sum.inr transcript =>
        (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1 >>= fun r => do
          let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
          pure (r.1, r.2,
            multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript p.2)

omit [Nonempty TagId] [SampleableType Digest] in
/-- `simulateQ multipleBadTableHandlerFineFresh` of a `query_bind`, run from a state. Analogue of
`multipleBadTableFine_run_query_bind'`. -/
lemma multipleBadTableFineFresh_run_query_bind' {α : Type} [Fintype Nonce] [Fintype Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (g : TagId × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    (simulateQ (multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g)
        (liftM (OracleSpec.query t) >>= f)).run s =
      (multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g t s) >>= fun p =>
        (simulateQ (multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Tag-step cacheBad preservation for the fresh-variant handler.** Tag queries never touch
`cacheBad` (only `bad` and `responses` / `sessionsUsed`), so every reachable output keeps
`cacheBad = p.2.cacheBad`. Identical proof shape to
`multipleBadTableHandlerFine_tag_preserves_cacheBad`. -/
lemma multipleBadTableHandlerFineFresh_tag_preserves_cacheBad [Fintype Nonce] [Fintype Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (g : TagId × Nonce → Digest) (tag : TagId)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    ∀ z ∈ support (multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) p),
        z.2.2.cacheBad = p.2.cacheBad := by
  intro z hz
  change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1
      >>= fun r => pure (r.1, r.2, multipleBadAdvance tag p.2 r.1)) at hz
  obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [mem_support_pure_iff] at hz
  subst hz
  show (multipleBadAdvance tag p.2 r.1).cacheBad = p.2.cacheBad
  cases r.1 <;> simp [multipleBadAdvance]

omit [Nonempty TagId] in
/-- **Per-reader-step cacheBad bound for the fresh-variant handler.** A single reader step samples
a fresh `gFine` and ORs `cacheBadReader gFine transcript` into `cacheBad`. Conditional on
`p.2.cacheBad = false` going in, the probability `cacheBad` becomes `true` is the same as
`Pr[cacheBadReader gFine transcript = true | gFine ← $ᵗ]`, which the stage (a) bound covers. -/
lemma multipleBadTableHandlerFineFresh_reader_step_cacheBad_le [Fintype Nonce] [Fintype Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (g : TagId × Nonce → Digest) (transcript : TagTranscript Nonce Digest)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest)
    (hcb : p.2.cacheBad = false) :
    Pr[fun z : ReaderReply × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          z.2.2.cacheBad = true |
        multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript) p] ≤
      ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  -- Unfold the reader branch.
  change Pr[fun z : ReaderReply × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
        z.2.2.cacheBad = true |
      ((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1 >>= fun r => do
        let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
        pure (r.1, r.2,
          multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript p.2))] ≤ _
  -- Pull the outer bind / inner bind.
  rw [probEvent_bind_eq_tsum]
  -- For each `r`, the inner is `gFine ← $ᵗ; pure (..., advance gFine transcript p.2)`, whose
  -- cacheBad-true probability is `Pr[cacheBadReader gFine transcript = true | $ᵗ]` (since `hcb`
  -- gives `(false || x) = x`).
  have hinner : ∀ r : ReaderReply × UnlinkState TagId,
      Pr[fun z : ReaderReply × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            z.2.2.cacheBad = true |
          (do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
              pure (r.1, r.2,
                multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine
                  transcript p.2)
                : ProbComp (ReaderReply × (UnlinkState TagId ×
                    UnlinkBadState TagId Nonce Digest)))] =
        Pr[fun b : Bool => b = true |
          do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
             pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript)] := by
    intro r
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun gFine => ?_
    congr 1
    rw [probEvent_pure, probEvent_pure]
    -- `(multipleBadReaderAdvance ... p.2).cacheBad = p.2.cacheBad || cacheBadReader ... = cacheBadReader ...`
    simp only [multipleBadReaderAdvance, hcb, Bool.false_or]
  -- Bound each summand by `step_a := |TagId| * sessionsPerTag / |Digest|` and sum.
  have hStep := probEvent_cacheBadReader_uniformSample_le (TagId := TagId)
    (sessionsPerTag := sessionsPerTag) (Nonce := Nonce) (Digest := Digest) transcript
  calc ∑' r, Pr[= r | (multipleTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1] *
          Pr[fun z : ReaderReply × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              z.2.2.cacheBad = true |
            (do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
                pure (r.1, r.2,
                  multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine
                    transcript p.2)
                  : ProbComp (ReaderReply × (UnlinkState TagId ×
                      UnlinkBadState TagId Nonce Digest)))]
      = ∑' r, Pr[= r | (multipleTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1] *
          Pr[fun b : Bool => b = true |
            do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
               pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript)] := by
          refine tsum_congr fun r => ?_; rw [hinner]
    _ = (∑' r, Pr[= r | (multipleTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1]) *
          Pr[fun b : Bool => b = true |
            do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
               pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript)] := by
          rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * Pr[fun b : Bool => b = true |
            do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
               pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript)] := by
          gcongr; exact tsum_probOutput_le_one
    _ ≤ ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
          (Fintype.card Digest : ℝ≥0∞) := by rw [one_mul]; exact hStep

omit [Nonempty TagId] in
/-- **Per-step cacheBad monotonicity for the fresh-variant handler.** If `cacheBad` is set in the
state going into a `multipleBadTableHandlerFineFresh` step, every reachable output keeps
`cacheBad = true`. The tag branch leaves `cacheBad` unchanged; the reader branch ORs into it. -/
lemma multipleBadTableHandlerFineFresh_step_preserves_cacheBad [Fintype Nonce] [Fintype Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (g : TagId × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hcb : p.2.cacheBad = true) :
    ∀ z ∈ support (multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g t p), z.2.2.cacheBad = true := by
  cases t with
  | inl tag =>
    intro z hz
    have h := multipleBadTableHandlerFineFresh_tag_preserves_cacheBad
      (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) g tag p z hz
    rw [h]; exact hcb
  | inr transcript =>
    intro z hz
    change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1
        >>= fun r => do
          let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
          pure (r.1, r.2,
            multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine
              transcript p.2)) at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    obtain ⟨gFine, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    show (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
      gFine transcript p.2).cacheBad = true
    show (p.2.cacheBad || _ : Bool) = true
    rw [hcb, Bool.true_or]

omit [Nonempty TagId] in
/-- **Full-run cacheBad bound for the fresh-variant handler.** Running `simulateQ` of the
per-reader-step fresh-sampling handler against an adversary making at most `qR` reader queries,
starting from a state with `cacheBad = false`, the probability that `cacheBad` ends up set is at
most `qR * |TagId| * sessionsPerTag / |Digest|`.

The induction is clean because each reader step samples a fresh `gFine`, so the inductive
hypothesis at the continuation has no coupling with earlier draws. Tag steps are transparent (they
don't touch `cacheBad`); reader steps charge one per-step bound via the stage (a) lemma. -/
lemma simulateQ_multipleBadTableHandlerFineFresh_cacheBad_prob_le
    [Fintype Nonce] [Fintype Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (g : TagId × Nonce → Digest)
    (qR : ℕ) (hqR : OracleComp.IsQueryBoundP adversary (·.isRight) qR)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest)
    (hcb : p.2.cacheBad = false) :
    Pr[fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          z.2.2.cacheBad = true |
        (simulateQ (multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) adversary).run p] ≤
      (qR : ℝ≥0∞) *
        (((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
          (Fintype.card Digest : ℝ≥0∞)) := by
  classical
  induction adversary using OracleComp.inductionOn generalizing p qR with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, hcb, Bool.false_eq_true,
      ite_false]
    exact zero_le _
  | query_bind t oa ih =>
    rw [multipleBadTableFineFresh_run_query_bind' g t (fun r => oa r) p]
    rw [isQueryBoundP_query_bind_iff] at hqR
    obtain ⟨hpos, hcont⟩ := hqR
    cases t with
    | inl tag =>
      -- Tag branch: cacheBad preserved; recurse on the continuation with the same qR budget.
      -- (`if p t then qR-1 else qR` reduces to `qR` because `(·.isRight)` is false on `inl`.)
      have hsimp : ∀ u, IsQueryBoundP (oa u) (·.isRight) qR := by
        intro u; have := hcont u; simpa using this
      rw [probEvent_bind_eq_tsum]
      calc ∑' z,
              Pr[= z | multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) p] *
              Pr[fun y : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  y.2.2.cacheBad = true |
                (simulateQ (multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) (oa z.1)).run z.2]
          ≤ ∑' z,
              Pr[= z | multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) p] *
              ((qR : ℝ≥0∞) *
                (((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
                  (Fintype.card Digest : ℝ≥0∞))) := by
            refine ENNReal.tsum_le_tsum fun z => ?_
            by_cases hmem : z ∈ support (multipleBadTableHandlerFineFresh (TagId := TagId)
                (Nonce := Nonce) (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                g (Sum.inl tag) p)
            · have hzcb := multipleBadTableHandlerFineFresh_tag_preserves_cacheBad
                (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) g tag p z hmem
              refine mul_le_mul' le_rfl ?_
              exact ih z.1 qR (hsimp z.1) z.2 (by rw [hzcb]; exact hcb)
            · rw [probOutput_eq_zero_of_not_mem_support hmem]; simp
        _ = (∑' z,
              Pr[= z | multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) p]) *
              ((qR : ℝ≥0∞) *
                (((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
                  (Fintype.card Digest : ℝ≥0∞))) := by rw [ENNReal.tsum_mul_right]
        _ ≤ 1 * ((qR : ℝ≥0∞) *
              (((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
                (Fintype.card Digest : ℝ≥0∞))) := by
            gcongr; exact tsum_probOutput_le_one
        _ = (qR : ℝ≥0∞) *
              (((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
                (Fintype.card Digest : ℝ≥0∞)) := one_mul _
    | inr transcript =>
      -- Reader branch: charge one per-step bound, then recurse on (qR - 1).
      -- `hpos` gives `0 < qR`. The continuation gets budget `qR - 1`.
      have hqRpos : 0 < qR := by
        rcases hpos with h | h
        · exact absurd (by rfl : (Sum.inr transcript : TagId ⊕ TagTranscript Nonce Digest).isRight = true) h
        · exact h
      have hcont' : ∀ u, IsQueryBoundP (oa u) (·.isRight) (qR - 1) := by
        intro u; have := hcont u; simpa using this
      -- Step bound: `Pr[¬ cacheBad = false] = Pr[cacheBad = true] ≤ |TagId|*sessionsPerTag/|Digest|`.
      have hstepBound :
          Pr[fun z : ReaderReply × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                ¬ z.2.2.cacheBad = false |
            multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript) p] ≤
          ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞) := by
        have :
            (fun z : ReaderReply × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                ¬ z.2.2.cacheBad = false) =
              (fun z => z.2.2.cacheBad = true) := by
          ext z; cases z.2.2.cacheBad <;> simp
        rw [this]
        exact multipleBadTableHandlerFineFresh_reader_step_cacheBad_le
          (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g transcript p hcb
      -- Continuation bound: when `cacheBad = false` persists into the continuation, the IH at
      -- budget `qR-1` applies.
      have hcontBound :
          ∀ z ∈ support (multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript) p),
            z.2.2.cacheBad = false →
            Pr[fun y : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                ¬ y.2.2.cacheBad = false |
              (simulateQ (multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) (oa z.1)).run z.2] ≤
            ((qR - 1 : ℕ) : ℝ≥0∞) *
              (((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
                (Fintype.card Digest : ℝ≥0∞)) := by
        intro z _ hzcb
        have hih := ih z.1 (qR - 1) (hcont' z.1) z.2 hzcb
        -- Rewrite the goal from `¬ = false` to `= true`.
        have hrw :
            (fun y : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                ¬ y.2.2.cacheBad = false) =
              (fun y => y.2.2.cacheBad = true) := by
          ext y; cases y.2.2.cacheBad <;> simp
        rw [hrw]; exact hih
      have hcombine := probEvent_bind_le_add
        (mx := multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript) p)
        (my := fun z => (simulateQ (multipleBadTableHandlerFineFresh (TagId := TagId)
          (Nonce := Nonce) (Digest := Digest) (sessionsPerTag := sessionsPerTag) g)
          (oa z.1)).run z.2)
        (p := fun z : ReaderReply × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          z.2.2.cacheBad = false)
        (q := fun y : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          y.2.2.cacheBad = false)
        (ε₁ := ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
          (Fintype.card Digest : ℝ≥0∞))
        (ε₂ := ((qR - 1 : ℕ) : ℝ≥0∞) *
          (((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞)))
        hstepBound hcontBound
      -- Rewrite the target into `Pr[¬ = false]` form and bound by hcombine.
      have htgt :
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              z.2.2.cacheBad = true) =
            (fun z => ¬ z.2.2.cacheBad = false) := by
        ext z; cases z.2.2.cacheBad <;> simp
      rw [htgt]
      refine hcombine.trans ?_
      -- Combine: `step + (qR-1) * step = qR * step`.
      have hbase : (1 : ℝ≥0∞) + ((qR - 1 : ℕ) : ℝ≥0∞) = (qR : ℝ≥0∞) := by
        have : (1 : ℕ) + (qR - 1) = qR := Nat.add_sub_cancel' (Nat.one_le_iff_ne_zero.mpr
          (Nat.pos_iff_ne_zero.mp hqRpos))
        exact_mod_cast this
      have heq :
          ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
              (Fintype.card Digest : ℝ≥0∞) +
            ((qR - 1 : ℕ) : ℝ≥0∞) *
              (((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
                (Fintype.card Digest : ℝ≥0∞)) =
          (qR : ℝ≥0∞) *
              (((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
                (Fintype.card Digest : ℝ≥0∞)) := by
        rw [show ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
              (Fintype.card Digest : ℝ≥0∞) +
            ((qR - 1 : ℕ) : ℝ≥0∞) *
              (((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
                (Fintype.card Digest : ℝ≥0∞)) =
            (1 + ((qR - 1 : ℕ) : ℝ≥0∞)) *
              (((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
                (Fintype.card Digest : ℝ≥0∞)) from by ring]
        rw [hbase]
      exact le_of_eq heq

/-! ### Per-step shared-table cacheBad bound (Step 8 stage (b) bridge) -/

omit [Nonempty TagId] in
/-- **Per-reader-step cacheBad bound for the shared-table handler, averaged over `gFine ← $ᵗ`.**

For the shared-table `multipleBadTableHandlerFine g gFine`, the gFine parameter is read only at
the reader-step OR into cacheBad. Sampling `gFine ← $ᵗ` outside one reader step and asking for
`cacheBad = true` after the step gives the same marginal as the FineFresh per-step bound,
because the only gFine-dependence in a single reader step is the final OR. The intermediate
state advance (sessionsUsed, responses, bad) is gFine-independent.

Conditional on `p.2.cacheBad = false` going in, this probability is bounded by the stage (a)
uniform-table bound `|TagId| * sessionsPerTag / |Digest|`.

The proof commutes the outer `gFine ← $ᵗ` past the gFine-independent table-handler step using
`evalDist_probComp_bind_comm`. After the commutation, the computation is the exact shape of the
FineFresh reader-step, and the FineFresh per-step bound applies. -/
lemma multipleBadTableHandlerFine_reader_step_cacheBad_avg_le
    [Fintype Nonce] [Fintype Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (g : TagId × Nonce → Digest) (transcript : TagTranscript Nonce Digest)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest)
    (hcb : p.2.cacheBad = false) :
    Pr[fun z : ReaderReply × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
          z.2.2.cacheBad = true |
        do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
           multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
             (sessionsPerTag := sessionsPerTag) g gFine (Sum.inr transcript) p] ≤
      ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  -- Unfold the reader branch of `multipleBadTableHandlerFine`.
  change Pr[fun z : ReaderReply × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
        z.2.2.cacheBad = true |
      do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
         (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1 >>= fun r =>
            pure (r.1, r.2,
              multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                gFine transcript p.2)] ≤ _
  -- Commute the outer `gFine` sample past the gFine-independent inner step at the `𝒟[·]` level.
  -- After the commutation, the computation is the exact shape of the FineFresh reader-step.
  have hcomm :
      𝒟[(do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
            (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1 >>= fun r =>
              pure (r.1, r.2,
                multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript p.2) :
            ProbComp (ReaderReply × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest)))] =
        𝒟[((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1 >>= fun r => do
            let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
            pure (r.1, r.2,
              multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                gFine transcript p.2))] := by
    exact evalDist_probComp_bind_comm ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
      ((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1)
      (fun gFine r => pure (r.1, r.2,
        multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript p.2))
  -- Transport via the evalDist equality and then apply the FineFresh bound.
  have heq :
      Pr[fun z : ReaderReply × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            z.2.2.cacheBad = true |
          (do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
              (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1 >>= fun r =>
              pure (r.1, r.2,
                multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript p.2) :
              ProbComp _)] =
        Pr[fun z : ReaderReply × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            z.2.2.cacheBad = true |
          multipleBadTableHandlerFineFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript) p] :=
    probEvent_congr' (fun _ _ => Iff.rfl) hcomm
  -- Apply the equality and then the FineFresh bound.
  refine heq.trans_le ?_
  exact multipleBadTableHandlerFineFresh_reader_step_cacheBad_le
    (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) g transcript p hcb

/-! ### Tag-step gFine-commutation for the shared-table full run (Step 8 stage (b) bridge) -/

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Tag-step gFine commutation for the shared-table full run.** A tag step of
`multipleBadTableHandlerFine g gFine` is gFine-independent (the bad-state advance is
`multipleBadAdvance tag p.2 r.1`, which doesn't read `gFine`). Sampling `gFine ← $ᵗ` outside a
tag-headed adversary `liftM (OracleSpec.query (Sum.inl tag)) >>= oa` is equivalent to running the
tag step first and *then* sampling `gFine` afresh for the continuation, even though both share
the same gFine sample at the source.

This is the key structural lemma the full-run shared-table cacheBad bound consumes at the tag-step
case of its induction: after the commutation, the IH applies directly at the same query budget
because tag steps don't consume reader-query budget.

Proved by combining `multipleBadTableFine_run_query_bind'` (unfolding `simulateQ` over the
`query_bind` of a tag query) with `evalDist_probComp_bind_comm` (commuting the outer
`gFine ← $ᵗ` past the gFine-independent inner step). -/
lemma multipleBadTableHandlerFine_full_run_tag_step_commute
    [Fintype Nonce] [Fintype Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (g : TagId × Nonce → Digest) (tag : TagId)
    (oa : Option (TagTranscript Nonce Digest) → UnlinkAdversary TagId Nonce Digest)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    𝒟[(($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gFine =>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine)
              ((liftM (OracleSpec.query (spec := UnlinkOracleSpec TagId Nonce Digest)
                  (Sum.inl tag))) >>= oa)).run p :
          ProbComp (Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest)))] =
        𝒟[((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1 >>= fun r =>
            ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gFine =>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine)
                (oa r.1)).run (r.2, multipleBadAdvance tag p.2 r.1))] := by
  classical
  -- Unfold the inner simulateQ over the query_bind, then commute the outer gFine past the
  -- gFine-independent step.
  have hstep_eq : ∀ gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest,
      (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine)
          ((liftM (OracleSpec.query (spec := UnlinkOracleSpec TagId Nonce Digest)
              (Sum.inl tag))) >>= oa)).run p =
        ((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1 >>= fun r =>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine)
              (oa r.1)).run (r.2, multipleBadAdvance tag p.2 r.1)) := by
    intro gFine
    rw [multipleBadTableFine_run_query_bind' g gFine (Sum.inl tag) oa p]
    simp [multipleBadTableHandlerFine]
  have hunfold :
      (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gFine =>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine)
                ((liftM (OracleSpec.query (spec := UnlinkOracleSpec TagId Nonce Digest)
                    (Sum.inl tag))) >>= oa)).run p :
            ProbComp (Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest))) =
        (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gFine =>
            (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1 >>= fun r =>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine)
                (oa r.1)).run (r.2, multipleBadAdvance tag p.2 r.1)) := by
    refine bind_congr fun gFine => ?_
    exact hstep_eq gFine
  rw [show 𝒟[_] = 𝒟[_] from congrArg _ hunfold]
  exact evalDist_probComp_bind_comm
    ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
    ((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1)
    (fun gFine r => (simulateQ (multipleBadTableHandlerFine (TagId := TagId)
        (Nonce := Nonce) (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine)
        (oa r.1)).run (r.2, multipleBadAdvance tag p.2 r.1))

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Tag-step cacheBad preservation, averaged over `gFine ← $ᵗ`.** The shared-table tag step
does not touch `cacheBad`, so for every reachable output the `cacheBad` flag matches the input.
This is the tag-side averaged companion to `multipleBadTableHandlerFine_reader_step_cacheBad_avg_le`
— trivial because the tag branch ignores `gFine` entirely, so the averaging over `gFine ← $ᵗ`
contributes nothing. -/
lemma multipleBadTableHandlerFine_tag_step_cacheBad_avg_preserves
    [Fintype Nonce] [Fintype Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (g : TagId × Nonce → Digest) (tag : TagId)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    ∀ z ∈ support
        (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gFine =>
          multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g gFine (Sum.inl tag) p),
        z.2.2.cacheBad = p.2.cacheBad := by
  intro z hz
  obtain ⟨gFine, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  exact multipleBadTableHandlerFine_tag_preserves_cacheBad
    (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) g gFine tag p z hz

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Per-step cacheBad monotonicity for the shared-table Fine handler.** If `cacheBad` is set in
the input state, every reachable output of `multipleBadTableHandlerFine g gFine t p` keeps
`cacheBad = true`. The tag branch leaves `cacheBad` unchanged (proved via
`multipleBadTableHandlerFine_tag_preserves_cacheBad`); the reader branch ORs into it (proved via
`multipleBadTableHandlerFine_reader_state_eq` and idempotence of OR on `true`).

Shared-table analogue of `multipleBadTableHandlerFineFresh_step_preserves_cacheBad`. Used by the
upcoming full-run shared-table cacheBad bound at the tag-step IH application site (we need
preservation in BOTH directions: false-stays-false for the per-step charge to fire, and
true-stays-true so the IH can be applied at the post-step state). -/
lemma multipleBadTableHandlerFine_step_preserves_cacheBad
    (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hcb : p.2.cacheBad = true) :
    ∀ z ∈ support (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g gFine t p), z.2.2.cacheBad = true := by
  cases t with
  | inl tag =>
    intro z hz
    have h := multipleBadTableHandlerFine_tag_preserves_cacheBad
      (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) g gFine tag p z hz
    rw [h]; exact hcb
  | inr transcript =>
    intro z hz
    have h := multipleBadTableHandlerFine_reader_state_eq
      (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) g gFine transcript p z hz
    rw [h]
    show (p.2.cacheBad || _ : Bool) = true
    rw [hcb, Bool.true_or]

/-! ### Full-run shared-table cacheBad bound (Step 8 stage (b))

The headline bound the Option-6 plan calls for: starting from a state with `cacheBad = false` and
sampling a single shared `gFine ← $ᵗ` outside the run, the probability that the shared-table
`multipleBadTableHandlerFine g gFine` handler leaves `cacheBad = true` after running an
adversary that makes at most `qR` reader queries is bounded by
`qR * |TagId| * sessionsPerTag / |Digest|`.

This is the bound that `simulateQ_multipleBadTableHandlerFineFresh_cacheBad_prob_le` provides for
the **fresh-per-step** variant. The shared-table variant requires bridging across the gFine
coupling at the reader step: a shared `gFine` is reused across all reader queries, so the
inductive proof's continuation must operate at the *same* `gFine` as the current step rather than
sampling a fresh one.

**Status (Iteration 12).** The full-run shared-table bound below is the remaining open target of
Step 8 stage (b). Iterations 9-11 attempted three different bridge strategies — per-step
`bind_comm` lift, tag-step gFine commutation, and reader-step stochastic dominance — and
documented their structural obstructions (the reader-step gFine sharing forces a coupling between
the per-step OR and the continuation's gFine reads).

The cleanest path forward — to be executed in the next iteration — is one of:
1. **Direct Fubini decomposition.** Express `cacheBad_end` after a shared-`gFine` run as the
   union over reader queries `i = 1..qR` of `cacheBadReader gFine T_i`, where `T_i` is the
   `i`-th reader-query transcript. The transcripts `T_i` are gFine-independent (the
   `multipleTableHandler` reads only `g`, not `gFine`). Union bound + the stage (a) per-cell
   marginal closes the bound at `qR * |TagId| * sessionsPerTag / |Digest|`.
2. **Reduction to FineFresh via marginal-distribution equality.** Show that the marginal
   distribution of `(state, cacheBad)` after a shared-`gFine` Fine run agrees with the marginal
   after a per-step-fresh FineFresh run. Then transport the FineFresh bound.
3. **Per-cell coupling.** Identify the finite set of `((TagId × Fin sessionsPerTag) × Nonce)`
   cells the shared `gFine` is read at across the full run, and decompose the bound across these
   cells using the marginal lemma `probOutput_uniformSample_fun_eval`.

For Iteration 12 we leave the full-run shared-table bound as the named open target, with the
per-step / preservation / commutation scaffolding from Iterations 9-11 + this iteration's
`multipleBadTableHandlerFine_step_preserves_cacheBad` in place. Steps 9-12 of the Option-6 plan
(the two `sorry`s in `DirectCoupling/Compose.lean`) consume this bound; until it lands, those
sorries remain. -/

end UnlinkReduction

end PRFTagReader
