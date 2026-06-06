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

/-- Path-A variant of the eager-table multi handler. Identical to `multipleBadTableHandler` on
tag queries and on the output bit; on a reader query it advances the bad-world component via
`multipleBadReaderAdvanceEager`, which flips `badReader` when the queried nonce has been visited
before (`sB.readerTouched transcript.nonce`) AND some `g`-cell at that nonce matches
`transcript.auth` while not being session-recorded.

This is the eager-table analogue of `multipleBadQueryImplPathA`. The pair will satisfy the
Path-A eager-equivalence
(`evalDist_simulateQ_multipleBadQueryImplPathA_run_eq_tableExtending`, added in a follow-up
commit) under an extended coupling invariant linking the lazy stale-cell condition to
`readerTouched`. -/
noncomputable def multipleBadTableHandlerPathA (g : TagId × Nonce → Digest) :
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
          pure (r.1, r.2, multipleBadReaderAdvanceEager transcript g p.2)

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

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Path-A `simulateQ` query-bind unfolding. Same shape as `multipleBadTable_run_query_bind'`. -/
lemma multipleBadTablePathA_run_query_bind' {α : Type} (g : TagId × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    (simulateQ (multipleBadTableHandlerPathA (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g) (liftM (OracleSpec.query t) >>= f)).run s =
      (multipleBadTableHandlerPathA (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g t s) >>= fun p =>
        (simulateQ (multipleBadTableHandlerPathA (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g) (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Path-A eager-table single-step bad monotonicity.** -/
lemma multipleBadTableHandlerPathA_step_preserves_bad (g : TagId × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbad : p.2.bad = true) :
    ∀ z ∈ support (multipleBadTableHandlerPathA (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
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
        >>= fun r => pure (r.1, r.2, multipleBadReaderAdvanceEager transcript g p.2)) at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    rw [multipleBadReaderAdvanceEager_bad]; exact hbad

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Path-A eager-table single-step badReader monotonicity.** -/
lemma multipleBadTableHandlerPathA_step_preserves_badReader (g : TagId × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbR : p.2.badReader = true) :
    ∀ z ∈ support (multipleBadTableHandlerPathA (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g t p), z.2.2.badReader = true := by
  cases t with
  | inl tag =>
    intro z hz
    change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1
        >>= fun r => pure (r.1, r.2, multipleBadAdvance tag p.2 r.1)) at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    cases hr : r.1 <;> simp [multipleBadAdvance, hbR]
  | inr transcript =>
    intro z hz
    change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1
        >>= fun r => pure (r.1, r.2, multipleBadReaderAdvanceEager transcript g p.2)) at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    exact multipleBadReaderAdvanceEager_badReader_of_set transcript g p.2 hbR

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Path-A eager-table full-run bad monotonicity.** -/
lemma multipleBadTableHandlerPathA_run_preserves_bad {α : Type} (g : TagId × Nonce → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbad : p.2.bad = true) :
    ∀ z ∈ support ((simulateQ (multipleBadTableHandlerPathA (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) oa).run p), z.2.2.bad = true := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure b =>
    intro z hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz; exact hbad
  | query_bind t f ih =>
    intro z hz
    rw [multipleBadTablePathA_run_query_bind', mem_support_bind_iff] at hz
    obtain ⟨q, hq, hz⟩ := hz
    exact ih q.1 q.2 (multipleBadTableHandlerPathA_step_preserves_bad g t p hbad q hq) z hz

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Path-A eager-table full-run badReader monotonicity.** -/
lemma multipleBadTableHandlerPathA_run_preserves_badReader {α : Type} (g : TagId × Nonce → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbR : p.2.badReader = true) :
    ∀ z ∈ support ((simulateQ (multipleBadTableHandlerPathA (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) oa).run p),
      z.2.2.badReader = true := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure b =>
    intro z hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz; exact hbR
  | query_bind t f ih =>
    intro z hz
    rw [multipleBadTablePathA_run_query_bind', mem_support_bind_iff] at hz
    obtain ⟨q, hq, hz⟩ := hz
    exact ih q.1 q.2 (multipleBadTableHandlerPathA_step_preserves_badReader g t p hbR q hq) z hz

/-! ### Path-A coupling invariant linking the lazy cache and `readerTouched`

For the Path-A eager equivalence to hold, the lazy cache `c` and the shadow `sB.readerTouched`
must agree on which `(tag, n)` cells are "reader-written" (cached but not session-recorded). The
predicate `MultipleBadPathACoupling c sB` packages the two directions of this agreement:

* `Q`: every nonce in `readerTouched` has the full column cached in `c` (a reader query at `n`
  writes all `|TagId|` cells `(tag, n)`);
* `(a)`: every cached non-session cell `(tag, n)` has `readerTouched n = true` (the cell was
  written by the reader query that marked `n`).

The pair `(Q, (a))` is preserved by all per-query steps of the Path-A lazy handler and is what
makes the lazy `multipleBadReaderAdvance transcript c sB` and the eager
`multipleBadReaderAdvanceEager transcript (tableExtending c g) sB` produce the same bad-state
update pointwise (independent of the eager-table draw `g`). -/

/-- Path-A coupling invariant on the lazy cache `c` and the bad state `sB`. -/
def MultipleBadPathACoupling
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) : Prop :=
  (∀ n : Nonce, sB.readerTouched n = true → ∀ tag : TagId, (c (tag, n)).isSome) ∧
  (∀ (tag : TagId) (n : Nonce),
    (c (tag, n)).isSome → sB.responses (tag, n) = none → sB.readerTouched n = true)

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
lemma MultipleBadPathACoupling_init :
    MultipleBadPathACoupling (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) UnlinkBadState.init := by
  refine ⟨?_, ?_⟩
  · intro n hRT _; simp [UnlinkBadState.init] at hRT
  · intro _ _ h1 _; simp at h1

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The Path-A coupling invariant survives the off-collision tag step: the new cell
`(tag, tr.nonce)` is added to BOTH the cache and `sB.responses`, so `(a)`'s
`responses = none` hypothesis fails for it; and `readerTouched` is preserved unchanged, so `Q`'s
column condition is unchanged at every previously-touched nonce. -/
lemma MultipleBadPathACoupling_tag_advance_some
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (h : MultipleBadPathACoupling (TagId := TagId) (Nonce := Nonce) (Digest := Digest) c sB)
    (tag : TagId) (tr : TagTranscript Nonce Digest) :
    MultipleBadPathACoupling (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (c.cacheQuery (tag, tr.nonce) tr.auth) (multipleBadAdvance tag sB (some tr)) := by
  obtain ⟨hQ, ha⟩ := h
  refine ⟨?_, ?_⟩
  · intro n hRT tag'
    -- multipleBadAdvance for `some tr` preserves readerTouched
    have hRT' : sB.readerTouched n = true := by
      simpa [multipleBadAdvance] using hRT
    have hcprev := hQ n hRT' tag'
    -- `cacheQuery` only adds; preserves `isSome` at all other cells.
    by_cases hkey : (tag', n) = (tag, tr.nonce)
    · rw [hkey, QueryCache.cacheQuery_self]; rfl
    · rwa [QueryCache.cacheQuery_of_ne _ _ hkey]
  · intro tag' n h1 h2
    -- multipleBadAdvance for `some tr`: responses' = responses.cacheQuery (tag, tr.nonce) (...)
    by_cases hkey : (tag', n) = (tag, tr.nonce)
    · -- new cell — responses' at this key is `some _`, contradicting `h2 : responses' = none`
      exfalso
      have hsome : (multipleBadAdvance tag sB (some tr)).responses (tag', n)
          = some (tr.auth :: Option.getD (sB.responses (tag, tr.nonce)) []) := by
        rw [hkey]
        show (sB.responses.cacheQuery (tag, tr.nonce) _) (tag, tr.nonce) = _
        rw [QueryCache.cacheQuery_self]
      rw [hsome] at h2; cases h2
    · -- old cell — both `c` and `responses` are unchanged at this key
      have hc_eq : c.cacheQuery (tag, tr.nonce) tr.auth (tag', n) = c (tag', n) :=
        QueryCache.cacheQuery_of_ne _ _ hkey
      have hresp_eq : (sB.responses.cacheQuery (tag, tr.nonce)
          (tr.auth :: Option.getD (sB.responses (tag, tr.nonce)) [])) (tag', n) =
            sB.responses (tag', n) := QueryCache.cacheQuery_of_ne _ _ hkey
      rw [hc_eq] at h1
      have hresp_none : sB.responses (tag', n) = none := by
        change (sB.responses.cacheQuery (tag, tr.nonce) _) (tag', n) = none at h2
        rw [hresp_eq] at h2; exact h2
      -- readerTouched on multipleBadAdvance preserves; apply (a) and rewrite back
      change sB.readerTouched n = true
      exact ha tag' n h1 hresp_none

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The Path-A coupling invariant is trivially preserved by the slot-exhausted tag step
(`r.1 = none`): the cache is unchanged and `multipleBadAdvance tag sB none = sB`. -/
lemma MultipleBadPathACoupling_tag_advance_none
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (h : MultipleBadPathACoupling (TagId := TagId) (Nonce := Nonce) (Digest := Digest) c sB)
    (tag : TagId) :
    MultipleBadPathACoupling (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      c (multipleBadAdvance tag sB none) := h

/-- **Path-A flip-event matching.** Under the coupling invariant `MultipleBadPathACoupling c sB`,
the LAZY stale-match condition over `c` and the EAGER stale-match condition over
`tableExtending c g` (gated by `readerTouched`) are equivalent — that is, the boolean OR-ed into
`badReader` is the same on both sides. This is the load-bearing identity that lets the Path-A
eager equivalence hold pointwise (not just in distribution). -/
lemma multipleBadReaderAdvance_eq_Eager_of_coupling
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (h : MultipleBadPathACoupling (TagId := TagId) (Nonce := Nonce) (Digest := Digest) c sB)
    (transcript : TagTranscript Nonce Digest)
    (g : TagId × Nonce → Digest) :
    multipleBadReaderAdvance transcript c sB =
      multipleBadReaderAdvanceEager transcript (OracleComp.tableExtending c g) sB := by
  classical
  obtain ⟨hQ, ha⟩ := h
  unfold multipleBadReaderAdvance multipleBadReaderAdvanceEager
  congr 1
  -- only the `badReader` and `readerTouched` fields differ structurally; show the lazy and eager
  -- flip booleans agree.
  refine Bool.eq_iff_iff.mpr ?_
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨tag, hcv, hresp⟩
    refine ⟨ha tag transcript.nonce ?_ hresp, tag, ?_, hresp⟩
    · rw [hcv]; rfl
    · simp [OracleComp.tableExtending, hcv]
  · rintro ⟨hRT, tag, hgv, hresp⟩
    have hcsome := hQ transcript.nonce hRT tag
    obtain ⟨v, hcv⟩ := Option.isSome_iff_exists.mp hcsome
    have hg_eq : OracleComp.tableExtending c g (tag, transcript.nonce) = v := by
      simp [OracleComp.tableExtending, hcv]
    rw [hg_eq] at hgv
    exact ⟨tag, hcv.trans (by rw [hgv]), hresp⟩

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

end UnlinkReduction

end PRFTagReader
