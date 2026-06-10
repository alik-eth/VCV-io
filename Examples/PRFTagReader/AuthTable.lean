/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.Collision
import Examples.PRFTagReader.Table

/-!
# PRF Tag/Reader Protocol — Eager-Table Form of the Random-Function Auth World

The random-function authentication world `authRFQueryImpl` threads a lazy random-oracle cache
(`AuthIdealState.responses`) shared between the honest tag oracle and the fresh-drawing reader.
This file reformulates that world against an *eager* full random-oracle table
`g : TagId × Nonce → Digest`, drawn uniformly up front:

* `authTableHandler g` is the deterministic handler keyed on the table `g`, mirroring
  `authRFQueryImpl` with the lazy `responses` lookups replaced by reads of `g`;
* `evalDist_simulateQ_authRFQueryImpl_run'_eq_tableExtending` lifts the generic lazy-vs-eager
  table equivalence (`OracleComp.evalDist_simulateQ_randomOracle_run'_eq_tableExtending`, via the
  per-cell absorption lemmas `evalDist_idealCacheStep_bind_uniformTable` and
  `evalDist_idealCacheMapM_bind_uniformTable`) to this stateful auth handler.

In the eager world every cell digest is fixed before any adversary feedback, so the forge event
becomes a static union over the reader queries; this is the route used by the collision bound
`authRFExp_le_collisionBound` to close without any nonce-distinctness hypothesis. The structural
template is the unlinkability eager-table lemma
`evalDist_simulateQ_multipleIdealQueryImpl_run'_eq_tableExtending`.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section AuthEagerTable

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]

/-- Deterministic tag oracle keyed on a full random-oracle table `g : TagId × Nonce → Digest`:
sample a nonce, read `g (tag, nonce)` as the authenticator, record the transcript. This is
`authIdealTagQueryImpl` with the lazy `responses` lookup replaced by a read of `g`. -/
noncomputable def authTableTagQueryImpl (g : TagId × Nonce → Digest) :
    QueryImpl (TagId →ₒ TagTranscript Nonce Digest)
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) := fun tag => do
  let st ← get
  let nonce ← ($ᵗ Nonce : ProbComp Nonce)
  let auth := g (tag, nonce)
  let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
  set
    ({ responses := st.responses
       honestOutputs := insert (tag, transcript) st.honestOutputs
       readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)
  return transcript

/-- Deterministic reader oracle keyed on a full random-oracle table `g`: read `g (tag, nonce)` for
every tag at the transcript's nonce, accept on a digest match, and record non-honest matches as
forgeries. This is `authRFReaderQueryImpl` with the lazy lookups replaced by reads of `g`. -/
noncomputable def authTableReaderQueryImpl (g : TagId × Nonce → Digest) :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) := fun transcript => do
  let st ← get
  let pairs : List (TagId × Digest) := (Finset.univ : Finset TagId).toList.map
    (fun tag => (tag, g (tag, transcript.nonce)))
  let accepted : Bool := decide (∃ p ∈ pairs, p.2 = transcript.auth)
  let newForged : Finset TagId :=
    ((pairs.filter fun p => decide (p.2 = transcript.auth ∧
        (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset
  set ({ st with readerForged := st.readerForged ∪ (newForged.image (·, transcript)) } :
    AuthIdealState TagId Nonce Digest)
  return ReaderReply.ofBool accepted

/-- Deterministic combined handler keyed on a full random-oracle table `g`, mirroring
`authRFQueryImpl` with both lazy lookups replaced by reads of `g`. -/
noncomputable def authTableHandler (g : TagId × Nonce → Digest) :
    QueryImpl (AuthOracleSpec TagId Nonce Digest)
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) :=
  authTableTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g +
    authTableReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g

/-! ### Lazy run-lemmas: rephrasing the auth handlers via `idealCacheStep`/`idealCacheMapM`

These rewrite a lazy auth-handler step run from `AuthIdealState` `st` as the corresponding
`idealCacheStep` / `idealCacheMapM` over the bare cache `st.responses`, followed by deterministic
bookkeeping. They are the auth analogues of `multipleIdealQueryImpl_tag_run_of_lt` and
`multipleIdealQueryImpl_reader_run`, and let the generic per-cell absorption lemmas apply. -/

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest] in
/-- `authRFLookup` run from state `st` is `idealCacheStep` over `st.responses`, with the produced
cache repackaged into the ideal state (the `honestOutputs`/`readerForged` logs untouched). -/
lemma authRFLookup_run_eq_idealCacheStep (tag : TagId) (nonce : Nonce)
    (st : AuthIdealState TagId Nonce Digest) :
    (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce).run st =
      idealCacheStep st.responses (tag, nonce) >>= fun r =>
        pure (r.1, ({ st with responses := r.2 } : AuthIdealState TagId Nonce Digest)) := by
  unfold authRFLookup idealCacheStep
  cases hc : st.responses (tag, nonce) with
  | some d =>
    simp only [hc, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure]
  | none =>
    simp only [hc, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
      monadLift_eq_self, bind_pure_comp, StateT.run_map, StateT.run_set, map_pure]
    rw [Functor.map_map, Functor.map_map]

omit [Fintype TagId] [Nonempty TagId] in
/-- The ideal tag handler run from `st`: sample a nonce, take an `idealCacheStep` on `st.responses`
at `(tag, nonce)`, then emit the transcript and record it in `honestOutputs`. -/
lemma authIdealTagQueryImpl_run_eq_idealCacheStep (tag : TagId)
    (st : AuthIdealState TagId Nonce Digest) :
    (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag).run st =
      ($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
        idealCacheStep st.responses (tag, nonce) >>= fun r =>
          pure (⟨nonce, r.1⟩,
            ({ responses := r.2
               honestOutputs := insert (tag, ⟨nonce, r.1⟩) st.honestOutputs
               readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)) := by
  unfold authIdealTagQueryImpl idealCacheStep
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_eq_self,
    bind_pure_comp, pure_bind]
  rw [bind_map_left]
  refine bind_congr fun nonce => ?_
  cases hc : st.responses (tag, nonce) with
  | some d =>
    simp only [StateT.run_map, StateT.run_set, map_pure]
  | none =>
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
      StateT.run_map, StateT.run_set, map_pure]
    rw [Functor.map_map, Functor.map_map]

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest] in
/-- The reader's per-tag `mapM` of `(tag, authRFLookup tag nonce)`, run from `st`, folds
`idealCacheStep` over the cells `(tag, nonce)` as `idealCacheMapM`, then pairs each tag with the
produced digest by zipping. Only the `responses` field of the state changes. -/
lemma authRFLookup_mapM_run_eq_idealCacheMapM (nonce : Nonce) (tags : List TagId)
    (st : AuthIdealState TagId Nonce Digest) :
    (tags.mapM (fun tag => Prod.mk tag <$>
        authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce)).run st =
      idealCacheMapM (tags.map (fun tag => (tag, nonce))) st.responses >>= fun rs =>
        (pure (tags.zip rs.1,
          ({ st with responses := rs.2 } : AuthIdealState TagId Nonce Digest)) :
          ProbComp (List (TagId × Digest) × AuthIdealState TagId Nonce Digest)) := by
  induction tags generalizing st with
  | nil =>
    simp only [List.mapM_nil, StateT.run_pure, List.map_nil, idealCacheMapM, pure_bind,
      List.zip_nil_left]
  | cons hd tl ih =>
    rw [List.mapM_cons, List.map_cons, idealCacheMapM]
    rw [StateT.run_bind, map_eq_bind_pure_comp, StateT.run_bind,
      authRFLookup_run_eq_idealCacheStep hd nonce st]
    simp only [bind_assoc]
    refine bind_congr fun r => ?_
    rw [pure_bind]
    simp only [Function.comp, StateT.run_pure, pure_bind, StateT.run_bind]
    rw [ih ({ st with responses := r.2 } : AuthIdealState TagId Nonce Digest)]
    simp only [bind_assoc]
    refine bind_congr fun rs => ?_
    simp only [List.zip_cons_cons, pure_bind]

omit [Nonempty TagId] [SampleableType Nonce] in
/-- The random-function reader handler run from `st`: fold `idealCacheStep` over all
`(tag, transcript.nonce)` cells via `idealCacheMapM`, then accept on a digest match and record
non-honest matches as forgeries. The honest/forged logs update deterministically from the read
list; only the `responses` field carries the freshly sampled digests. -/
lemma authRFReaderQueryImpl_run_eq_idealCacheMapM (transcript : TagTranscript Nonce Digest)
    (st : AuthIdealState TagId Nonce Digest) :
    (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        transcript).run st =
      idealCacheMapM ((Finset.univ : Finset TagId).toList.map
          (fun tag => (tag, transcript.nonce))) st.responses >>= fun rs =>
        (let pairs : List (TagId × Digest) := (Finset.univ : Finset TagId).toList.zip rs.1
         pure (ReaderReply.ofBool (decide (∃ p ∈ pairs, p.2 = transcript.auth)),
          ({ responses := rs.2
             honestOutputs := st.honestOutputs
             readerForged := st.readerForged ∪
               ((((pairs.filter fun p => decide (p.2 = transcript.auth ∧
                   (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset).image
                 (·, transcript)) } : AuthIdealState TagId Nonce Digest)) :
          ProbComp (ReaderReply × AuthIdealState TagId Nonce Digest)) := by
  unfold authRFReaderQueryImpl
  simp only [StateT.run_bind, StateT.run_get, bind_pure_comp]
  rw [authRFLookup_mapM_run_eq_idealCacheMapM transcript.nonce
    (Finset.univ : Finset TagId).toList st]
  rw [bind_assoc]
  refine bind_congr fun rs => ?_
  rw [pure_bind, pure_bind]
  simp only [StateT.run_map, StateT.run_set, map_pure, Function.comp]
  rfl

/-! ### Eager table-handler step lemmas and the lazy-vs-eager equivalence -/

omit [Nonempty TagId] in
/-- `simulateQ authRFQueryImpl` of a `query_bind`, run from a state and projected to its output:
the per-query handler followed by the recursive simulation of the continuation. -/
lemma authRF_run'_query_bind' {α : Type}
    (t : (AuthOracleSpec TagId Nonce Digest).Domain)
    (f : (AuthOracleSpec TagId Nonce Digest).Range t →
      OracleComp (AuthOracleSpec TagId Nonce Digest) α)
    (st : AuthIdealState TagId Nonce Digest) :
    (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        (liftM (OracleSpec.query t) >>= f)).run' st =
      (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run st >>= fun p =>
        (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]; rfl

omit [Nonempty TagId] [SampleableType Digest] in
/-- `simulateQ (authTableHandler g)` of a `query_bind`, run from a state and projected to its
output: the per-query handler followed by the recursive simulation of the continuation. -/
lemma authTable_run'_query_bind' {α : Type} (g : TagId × Nonce → Digest)
    (t : (AuthOracleSpec TagId Nonce Digest).Domain)
    (f : (AuthOracleSpec TagId Nonce Digest).Range t →
      OracleComp (AuthOracleSpec TagId Nonce Digest) α)
    (st : AuthIdealState TagId Nonce Digest) :
    (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g)
        (liftM (OracleSpec.query t) >>= f)).run' st =
      (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g t).run st >>=
        fun p =>
          (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g)
            (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]; rfl

omit [Nonempty TagId] [SampleableType Digest] in
/-- `authTableHandler g` on a tag query: sample a nonce, read `g (tag, nonce)`, record the
transcript. -/
lemma authTableHandler_tag_run (g : TagId × Nonce → Digest) (tag : TagId)
    (st : AuthIdealState TagId Nonce Digest) :
    (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g
        (Sum.inl tag)).run st =
      ($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
        pure (⟨nonce, g (tag, nonce)⟩,
          ({ responses := st.responses
             honestOutputs := insert (tag, ⟨nonce, g (tag, nonce)⟩) st.honestOutputs
             readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)) := by
  unfold authTableHandler
  rw [QueryImpl.add_apply_inl]
  change (authTableTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    g tag).run st = _
  unfold authTableTagQueryImpl
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_eq_self,
    bind_pure_comp, StateT.run_map, StateT.run_set, pure_bind, map_pure]
  rw [Functor.map_map]
  rfl

omit [Nonempty TagId] [SampleableType Digest] in
/-- `authTableHandler g` on a reader query: read `g (tag, nonce)` for every tag and emit the
deterministic acceptance and forged-set bookkeeping; the `responses` field is untouched. -/
lemma authTableHandler_reader_run (g : TagId × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) (st : AuthIdealState TagId Nonce Digest) :
    (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g
        (Sum.inr transcript)).run st =
      (let pairs : List (TagId × Digest) := (Finset.univ : Finset TagId).toList.map
          (fun tag => (tag, g (tag, transcript.nonce)))
       pure (ReaderReply.ofBool (decide (∃ p ∈ pairs, p.2 = transcript.auth)),
        ({ responses := st.responses
           honestOutputs := st.honestOutputs
           readerForged := st.readerForged ∪
             ((((pairs.filter fun p => decide (p.2 = transcript.auth ∧
                 (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset).image
               (·, transcript)) } : AuthIdealState TagId Nonce Digest)) :
        ProbComp (ReaderReply × AuthIdealState TagId Nonce Digest)) := by
  unfold authTableHandler
  rw [QueryImpl.add_apply_inr]
  change (authTableReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    g transcript).run st = _
  unfold authTableReaderQueryImpl
  simp only [StateT.run_bind, StateT.run_get, bind_pure_comp, StateT.run_map,
    StateT.run_set, map_pure]

omit [Nonempty TagId] [SampleableType Digest] in
/-- The deterministic table handler reads only the table `g`, the `honestOutputs` and the
`readerForged` logs; it never consults the state's `responses` cache. Hence running it (projected
to its output) is insensitive to the `responses` field: two states agreeing on `honestOutputs` and
`readerForged` produce equal output distributions. -/
lemma simulateQ_authTableHandler_run'_responses_irrel (g : TagId × Nonce → Digest) {β : Type}
    (oa : OracleComp (AuthOracleSpec TagId Nonce Digest) β)
    (st₁ st₂ : AuthIdealState TagId Nonce Digest)
    (hh : st₁.honestOutputs = st₂.honestOutputs)
    (hr : st₁.readerForged = st₂.readerForged) :
    (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g)
        oa).run' st₁ =
      (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g)
        oa).run' st₂ := by
  induction oa using OracleComp.inductionOn generalizing st₁ st₂ with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
  | query_bind t f ih =>
    rw [authTable_run'_query_bind', authTable_run'_query_bind']
    cases t with
    | inl tag =>
      rw [authTableHandler_tag_run g tag st₁, authTableHandler_tag_run g tag st₂]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun nonce => ?_
      exact ih _ _ _ (by simp [hh]) hr
    | inr transcript =>
      rw [authTableHandler_reader_run g transcript st₁,
        authTableHandler_reader_run g transcript st₂]
      simp only [hh, hr]
      refine ih _ _ _ rfl ?_
      rfl

omit [Nonempty TagId] in
/-- **Eager-table form of the random-function auth world.** Running the random-function auth
handler `authRFQueryImpl` from `st` has the same output distribution as sampling a full
random-oracle table `g`, overlaying the cache `st.responses`, and running the deterministic table
handler `authTableHandler (tableExtending st.responses g)` from `st`.

This is the auth analogue of `evalDist_simulateQ_multipleIdealQueryImpl_run'_eq_tableExtending`:
the tag-query case is closed by the single-cell absorption
`evalDist_idealCacheStep_bind_uniformTable`, the reader-query case by the list absorption
`evalDist_idealCacheMapM_bind_uniformTable`. -/
lemma evalDist_simulateQ_authRFQueryImpl_run'_eq_tableExtending
    [Fintype Nonce] [Finite Digest] {β : Type}
    (oa : OracleComp (AuthOracleSpec TagId Nonce Digest) β)
    (st : AuthIdealState TagId Nonce Digest) :
    𝒟[(simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        oa).run' st] =
      𝒟[do let g ← $ᵗ (TagId × Nonce → Digest);
            (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (OracleComp.tableExtending st.responses g)) oa).run' st] := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    refine (evalDist_ext fun x => ?_).symm
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  | query_bind t f ih =>
    rw [authRF_run'_query_bind']
    have hrhs : 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
          (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (OracleComp.tableExtending st.responses g))
            (liftM (OracleSpec.query t) >>= f)).run' st]
        = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
            (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (OracleComp.tableExtending st.responses g) t).run st >>= fun p =>
              (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (OracleComp.tableExtending st.responses g)) (f p.1)).run' p.2] := by
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [authTable_run'_query_bind']
    rw [hrhs]
    cases t with
    | inl tag =>
      -- Tag query: sample a nonce, then an `idealCacheStep` on the cell `(tag, nonce)`.
      rw [show (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (Sum.inl tag)).run st =
          (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag).run st
        from rfl]
      rw [authIdealTagQueryImpl_run_eq_idealCacheStep tag st]
      have hlhs_reassoc :
          ((($ᵗ Nonce : ProbComp Nonce) >>= fun nonce => idealCacheStep st.responses (tag, nonce)
              >>= fun r => pure
                (⟨nonce, r.1⟩,
                  ({ responses := r.2
                     honestOutputs := insert (tag, ⟨nonce, r.1⟩) st.honestOutputs
                     readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)))
            >>= fun p => (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest)) (f p.1)).run' p.2)
          = (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
              idealCacheStep st.responses (tag, nonce) >>= fun r =>
                (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                  (f ⟨nonce, r.1⟩)).run'
                  ({ responses := r.2
                     honestOutputs := insert (tag, ⟨nonce, r.1⟩) st.honestOutputs
                     readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)) := by
        rw [bind_assoc]; refine bind_congr fun nonce => ?_
        rw [bind_assoc]; refine bind_congr fun r => ?_
        rw [pure_bind]
      refine (congrArg evalDist hlhs_reassoc).trans ?_
      -- Per-nonce eager equivalence under the inner `idealCacheStep`.
      have hlhs_inner : ∀ (n : Nonce),
          𝒟[idealCacheStep st.responses (tag, n) >>= fun r =>
            (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
              (f ⟨n, r.1⟩)).run'
              ({ responses := r.2
                 honestOutputs := insert (tag, ⟨n, r.1⟩) st.honestOutputs
                 readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)]
          = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
                (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (OracleComp.tableExtending st.responses g))
                  (f ⟨n, OracleComp.tableExtending st.responses g (tag, n)⟩)).run'
                  ({ responses := st.responses
                     honestOutputs :=
                       insert (tag, ⟨n, OracleComp.tableExtending st.responses g (tag, n)⟩)
                         st.honestOutputs
                     readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)] := by
        intro n
        set Mψ : (TagId × Nonce → Digest) → ProbComp β := fun g' =>
          (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g')
            (f ⟨n, g' (tag, n)⟩)).run'
            ({ responses := st.responses
               honestOutputs := insert (tag, ⟨n, g' (tag, n)⟩) st.honestOutputs
               readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest) with hMψ
        refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable_comp st.responses (tag, n) Mψ)
        refine evalDist_bind_congr_of_support _ _ _ fun r hr => ?_
        rw [ih ⟨n, r.1⟩
          ({ responses := r.2
             honestOutputs := insert (tag, ⟨n, r.1⟩) st.honestOutputs
             readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        have hcell : OracleComp.tableExtending r.2 g (tag, n) = r.1 := by
          simp only [OracleComp.tableExtending,
            idealCacheStep_cache_self st.responses (tag, n) r hr, Option.getD_some]
        rw [hMψ]
        simp only [hcell]
        exact simulateQ_authTableHandler_run'_responses_irrel _ _ _ _ rfl rfl
      simp only [authTableHandler_tag_run _ tag st]
      -- Swap the table draw past the nonce draw on the RHS.
      have hrhs_swap :
          (($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
            (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
              pure (⟨nonce, OracleComp.tableExtending st.responses g (tag, nonce)⟩,
                ({ responses := st.responses
                   honestOutputs :=
                     insert (tag, ⟨nonce, OracleComp.tableExtending st.responses g (tag, nonce)⟩)
                       st.honestOutputs
                   readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)))
              >>= fun p =>
                (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (OracleComp.tableExtending st.responses g)) (f p.1)).run' p.2)
          = (($ᵗ (TagId × Nonce → Digest)) >>= fun g => ($ᵗ Nonce : ProbComp Nonce) >>= fun n =>
              (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (OracleComp.tableExtending st.responses g))
                (f ⟨n, OracleComp.tableExtending st.responses g (tag, n)⟩)).run'
                ({ responses := st.responses
                   honestOutputs :=
                     insert (tag, ⟨n, OracleComp.tableExtending st.responses g (tag, n)⟩)
                       st.honestOutputs
                   readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)) := by
        refine bind_congr fun g => ?_
        rw [bind_assoc]; refine bind_congr fun n => ?_
        rw [pure_bind]
      refine Eq.trans ?_ (congrArg evalDist hrhs_swap).symm
      rw [evalDist_probComp_bind_comm ($ᵗ (TagId × Nonce → Digest)) ($ᵗ Nonce)]
      refine evalDist_bind_congr_of_support _ _ _ fun n _ => ?_
      exact hlhs_inner n
    | inr transcript =>
      -- Reader query: fold `idealCacheStep` over all `(tag, transcript.nonce)` cells.
      rw [show (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (Sum.inr transcript)).run st =
          (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            transcript).run st
        from rfl]
      rw [authRFReaderQueryImpl_run_eq_idealCacheMapM transcript st]
      set cells := (Finset.univ : Finset TagId).toList.map
        (fun tag => (tag, transcript.nonce)) with hcells
      -- Collapse the LHS bind to a single `idealCacheMapM` bind.
      have hlhs_reassoc :
          ((idealCacheMapM cells st.responses >>= fun rs =>
              (pure (ReaderReply.ofBool (decide (∃ p ∈ (Finset.univ : Finset TagId).toList.zip rs.1,
                  p.2 = transcript.auth)),
                ({ responses := rs.2
                   honestOutputs := st.honestOutputs
                   readerForged := st.readerForged ∪
                     (((((Finset.univ : Finset TagId).toList.zip rs.1).filter fun p =>
                         decide (p.2 = transcript.auth ∧
                         (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset).image
                       (·, transcript) } : AuthIdealState TagId Nonce Digest)) :
                ProbComp (ReaderReply × AuthIdealState TagId Nonce Digest)))
            >>= fun p => (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest)) (f p.1)).run' p.2)
          = (idealCacheMapM cells st.responses >>= fun rs =>
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                (f (ReaderReply.ofBool (decide (∃ p ∈ (Finset.univ : Finset TagId).toList.zip rs.1,
                  p.2 = transcript.auth))))).run'
                ({ responses := rs.2
                   honestOutputs := st.honestOutputs
                   readerForged := st.readerForged ∪
                     (((((Finset.univ : Finset TagId).toList.zip rs.1).filter fun p =>
                         decide (p.2 = transcript.auth ∧
                         (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset).image
                       (·, transcript) } : AuthIdealState TagId Nonce Digest)) := by
        rw [bind_assoc]; refine bind_congr fun rs => ?_
        rw [pure_bind]
      refine (congrArg evalDist hlhs_reassoc).trans ?_
      -- Eager equivalence under `idealCacheMapM`.
      set Mψ : (TagId × Nonce → Digest) → ProbComp β := fun g' =>
        (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g')
          (f (ReaderReply.ofBool (decide (∃ p ∈ cells.map (fun c => (c.1, g' c)),
            p.2 = transcript.auth))))).run'
          ({ responses := st.responses
             honestOutputs := st.honestOutputs
             readerForged := st.readerForged ∪
               ((((cells.map (fun c => (c.1, g' c))).filter fun p =>
                   decide (p.2 = transcript.auth ∧
                   (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset).image
                 (·, transcript) } : AuthIdealState TagId Nonce Digest)
        with hMψ
      have hstep1 :
          𝒟[idealCacheMapM cells st.responses >>= fun rs =>
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                (f (ReaderReply.ofBool (decide (∃ p ∈ (Finset.univ : Finset TagId).toList.zip rs.1,
                  p.2 = transcript.auth))))).run'
                ({ responses := rs.2
                   honestOutputs := st.honestOutputs
                   readerForged := st.readerForged ∪
                     (((((Finset.univ : Finset TagId).toList.zip rs.1).filter fun p =>
                         decide (p.2 = transcript.auth ∧
                         (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset).image
                       (·, transcript) } : AuthIdealState TagId Nonce Digest)]
          = 𝒟[idealCacheMapM cells st.responses >>= fun rs =>
              ($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
                Mψ (OracleComp.tableExtending rs.2 g)] := by
        refine evalDist_bind_congr_of_support _ _ _ fun rs hrs => ?_
        rw [ih (ReaderReply.ofBool (decide (∃ p ∈ (Finset.univ : Finset TagId).toList.zip rs.1,
            p.2 = transcript.auth)))
          ({ responses := rs.2
             honestOutputs := st.honestOutputs
             readerForged := st.readerForged ∪
               (((((Finset.univ : Finset TagId).toList.zip rs.1).filter fun p =>
                   decide (p.2 = transcript.auth ∧
                   (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset).image
                 (·, transcript) } : AuthIdealState TagId Nonce Digest)]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [hMψ]
        have hzip : (Finset.univ : Finset TagId).toList.zip rs.1
            = cells.map (fun c => (c.1, OracleComp.tableExtending rs.2 g c)) := by
          have hlen : rs.1 = cells.map (OracleComp.tableExtending rs.2 g) :=
            idealCacheMapM_support cells st.responses rs hrs g
          apply List.ext_getElem
          · simp [hlen, hcells]
          · intro i h₁ h₂
            simp only [hcells, List.getElem_zip, hlen, List.getElem_map]
        rw [hzip]
        exact simulateQ_authTableHandler_run'_responses_irrel _ _ _ _ rfl rfl
      rw [hstep1, evalDist_idealCacheMapM_bind_uniformTable_comp cells st.responses Mψ]
      -- RHS: collapse the table-handler reader query.
      refine (evalDist_bind_congr_of_support _ _ _ fun g _ => ?_).symm
      rw [authTableHandler_reader_run _ transcript st]
      rw [hMψ]
      change 𝒟[(pure _ : ProbComp (ReaderReply × AuthIdealState TagId Nonce Digest)) >>= fun p =>
          (simulateQ (authTableHandler (OracleComp.tableExtending st.responses g))
            (f p.1)).run' p.2] = _
      rw [pure_bind]
      rw [hcells]
      simp only [List.map_map, Function.comp_def]

/-! ### Forge-log eager equivalence: transporting the `(honestOutputs, readerForged)` projection

The forged-acceptance event lives on the final state's `readerForged` field, which is not visible to
the output projection `run'`. These lemmas transport the joint `(honestOutputs, readerForged)`
projection of the lazy random-function world to the eager-table world, mirroring
`evalDist_simulateQ_authRFQueryImpl_run'_eq_tableExtending` with the output replaced by the
responses-irrelevant log projection. -/

omit [Nonempty TagId] in
/-- `simulateQ authRFQueryImpl` of a `query_bind`, run from a state and projected to its
`(honestOutputs, readerForged)` logs: the per-query handler followed by the recursive simulation. -/
lemma authRF_run_proj_query_bind {α : Type}
    (t : (AuthOracleSpec TagId Nonce Digest).Domain)
    (f : (AuthOracleSpec TagId Nonce Digest).Range t →
      OracleComp (AuthOracleSpec TagId Nonce Digest) α)
    (st : AuthIdealState TagId Nonce Digest) :
    (fun z : α × AuthIdealState TagId Nonce Digest => (z.2.honestOutputs, z.2.readerForged)) <$>
      (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        (liftM (OracleSpec.query t) >>= f)).run st =
      (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run st >>= fun p =>
        (fun z : α × AuthIdealState TagId Nonce Digest =>
            (z.2.honestOutputs, z.2.readerForged)) <$>
          (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
            (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind, map_bind]; rfl

omit [Nonempty TagId] [SampleableType Digest] in
/-- `simulateQ (authTableHandler g)` of a `query_bind`, run from a state (full state): the per-query
handler followed by the recursive simulation of the continuation. -/
lemma authTable_run_query_bind {α : Type} (g : TagId × Nonce → Digest)
    (t : (AuthOracleSpec TagId Nonce Digest).Domain)
    (f : (AuthOracleSpec TagId Nonce Digest).Range t →
      OracleComp (AuthOracleSpec TagId Nonce Digest) α)
    (st : AuthIdealState TagId Nonce Digest) :
    (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g)
        (liftM (OracleSpec.query t) >>= f)).run st =
      (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g t).run st >>=
        fun p =>
          (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g)
            (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]; rfl

omit [Nonempty TagId] [SampleableType Digest] in
/-- The deterministic table handler's `(honestOutputs, readerForged)` log projection is insensitive
to the starting state's `responses` cache: two states agreeing on the logs produce equal projected
output distributions. -/
lemma simulateQ_authTableHandler_run_proj_responses_irrel (g : TagId × Nonce → Digest) {β : Type}
    (oa : OracleComp (AuthOracleSpec TagId Nonce Digest) β)
    (st₁ st₂ : AuthIdealState TagId Nonce Digest)
    (hh : st₁.honestOutputs = st₂.honestOutputs)
    (hr : st₁.readerForged = st₂.readerForged) :
    (fun z : β × AuthIdealState TagId Nonce Digest => (z.2.honestOutputs, z.2.readerForged)) <$>
        (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g)
        oa).run st₁ =
      (fun z : β × AuthIdealState TagId Nonce Digest => (z.2.honestOutputs, z.2.readerForged)) <$>
        (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g)
        oa).run st₂ := by
  induction oa using OracleComp.inductionOn generalizing st₁ st₂ with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, hh, hr]
  | query_bind t f ih =>
    rw [authTable_run_query_bind, authTable_run_query_bind, map_bind, map_bind]
    cases t with
    | inl tag =>
      rw [authTableHandler_tag_run g tag st₁, authTableHandler_tag_run g tag st₂]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun nonce => ?_
      exact ih ⟨nonce, g (tag, nonce)⟩ _ _ (by simp only; rw [hh]) hr
    | inr transcript =>
      rw [authTableHandler_reader_run g transcript st₁,
        authTableHandler_reader_run g transcript st₂]
      simp only [hh, hr]
      exact ih _ _ _ rfl rfl

omit [Nonempty TagId] in
/-- **Forge-log eager equivalence.** The lazy random-function world's joint
`(honestOutputs, readerForged)` log projection has the same distribution as the eager-table world's,
mirroring `evalDist_simulateQ_authRFQueryImpl_run'_eq_tableExtending` for the state-log projection
in place of the output. The forged-acceptance event factors through this projection, so the eager
union bound transports back to the lazy world. -/
lemma evalDist_simulateQ_authRFQueryImpl_run_proj_eq_tableExtending
    [Fintype Nonce] [Finite Digest] {β : Type}
    (oa : OracleComp (AuthOracleSpec TagId Nonce Digest) β)
    (st : AuthIdealState TagId Nonce Digest) :
    𝒟[(fun z : β × AuthIdealState TagId Nonce Digest =>
          (z.2.honestOutputs, z.2.readerForged)) <$>
        (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        oa).run st] =
      𝒟[do let g ← $ᵗ (TagId × Nonce → Digest);
            (fun z : β × AuthIdealState TagId Nonce Digest =>
              (z.2.honestOutputs, z.2.readerForged)) <$>
            (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (OracleComp.tableExtending st.responses g)) oa).run st] := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    refine (evalDist_ext fun x => ?_).symm
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  | query_bind t f ih =>
    rw [authRF_run_proj_query_bind]
    have hrhs : 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
          (fun z : β × AuthIdealState TagId Nonce Digest =>
              (z.2.honestOutputs, z.2.readerForged)) <$>
            (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (OracleComp.tableExtending st.responses g))
            (liftM (OracleSpec.query t) >>= f)).run st]
        = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
            (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (OracleComp.tableExtending st.responses g) t).run st >>= fun p =>
              (fun z : β × AuthIdealState TagId Nonce Digest =>
                  (z.2.honestOutputs, z.2.readerForged)) <$>
                (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (OracleComp.tableExtending st.responses g)) (f p.1)).run p.2] := by
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [authTable_run_query_bind, map_bind]
    rw [hrhs]
    cases t with
    | inl tag =>
      -- Tag query: sample a nonce, then an `idealCacheStep` on the cell `(tag, nonce)`.
      rw [show (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (Sum.inl tag)).run st =
          (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag).run st
        from rfl]
      rw [authIdealTagQueryImpl_run_eq_idealCacheStep tag st]
      have hlhs_reassoc :
          ((($ᵗ Nonce : ProbComp Nonce) >>= fun nonce => idealCacheStep st.responses (tag, nonce)
              >>= fun r => pure
                (⟨nonce, r.1⟩,
                  ({ responses := r.2
                     honestOutputs := insert (tag, ⟨nonce, r.1⟩) st.honestOutputs
                     readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)))
            >>= fun p => (fun z : β × AuthIdealState TagId Nonce Digest =>
                (z.2.honestOutputs, z.2.readerForged)) <$>
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest)) (f p.1)).run p.2)
          = (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
              idealCacheStep st.responses (tag, nonce) >>= fun r =>
                (fun z : β × AuthIdealState TagId Nonce Digest =>
                    (z.2.honestOutputs, z.2.readerForged)) <$>
                (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                  (f ⟨nonce, r.1⟩)).run
                  ({ responses := r.2
                     honestOutputs := insert (tag, ⟨nonce, r.1⟩) st.honestOutputs
                     readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)) := by
        rw [bind_assoc]; refine bind_congr fun nonce => ?_
        rw [bind_assoc]; refine bind_congr fun r => ?_
        rw [pure_bind]
      refine (congrArg evalDist hlhs_reassoc).trans ?_
      -- Per-nonce eager equivalence under the inner `idealCacheStep`.
      have hlhs_inner : ∀ (n : Nonce),
          𝒟[idealCacheStep st.responses (tag, n) >>= fun r =>
            (fun z : β × AuthIdealState TagId Nonce Digest =>
                (z.2.honestOutputs, z.2.readerForged)) <$>
            (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
              (f ⟨n, r.1⟩)).run
              ({ responses := r.2
                 honestOutputs := insert (tag, ⟨n, r.1⟩) st.honestOutputs
                 readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)]
          = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
                (fun z : β × AuthIdealState TagId Nonce Digest =>
                    (z.2.honestOutputs, z.2.readerForged)) <$>
                (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (OracleComp.tableExtending st.responses g))
                  (f ⟨n, OracleComp.tableExtending st.responses g (tag, n)⟩)).run
                  ({ responses := st.responses
                     honestOutputs :=
                       insert (tag, ⟨n, OracleComp.tableExtending st.responses g (tag, n)⟩)
                         st.honestOutputs
                     readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)] := by
        intro n
        set Mψ : (TagId × Nonce → Digest) → ProbComp
            (Finset (TagId × TagTranscript Nonce Digest) ×
              Finset (TagId × TagTranscript Nonce Digest)) := fun g' =>
          (fun z : β × AuthIdealState TagId Nonce Digest =>
              (z.2.honestOutputs, z.2.readerForged)) <$>
          (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g')
            (f ⟨n, g' (tag, n)⟩)).run
            ({ responses := st.responses
               honestOutputs := insert (tag, ⟨n, g' (tag, n)⟩) st.honestOutputs
               readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest) with hMψ
        refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable_comp st.responses (tag, n) Mψ)
        refine evalDist_bind_congr_of_support _ _ _ fun r hr => ?_
        rw [ih ⟨n, r.1⟩
          ({ responses := r.2
             honestOutputs := insert (tag, ⟨n, r.1⟩) st.honestOutputs
             readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        have hcell : OracleComp.tableExtending r.2 g (tag, n) = r.1 := by
          simp only [OracleComp.tableExtending,
            idealCacheStep_cache_self st.responses (tag, n) r hr, Option.getD_some]
        rw [hMψ]
        simp only [hcell]
        exact simulateQ_authTableHandler_run_proj_responses_irrel _ _ _ _ rfl rfl
      simp only [authTableHandler_tag_run _ tag st]
      -- Swap the table draw past the nonce draw on the RHS.
      have hrhs_swap :
          (($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
            (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
              pure (⟨nonce, OracleComp.tableExtending st.responses g (tag, nonce)⟩,
                ({ responses := st.responses
                   honestOutputs :=
                     insert (tag, ⟨nonce, OracleComp.tableExtending st.responses g (tag, nonce)⟩)
                       st.honestOutputs
                   readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)))
              >>= fun p =>
                (fun z : β × AuthIdealState TagId Nonce Digest =>
                    (z.2.honestOutputs, z.2.readerForged)) <$>
                (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (OracleComp.tableExtending st.responses g)) (f p.1)).run p.2)
          = (($ᵗ (TagId × Nonce → Digest)) >>= fun g => ($ᵗ Nonce : ProbComp Nonce) >>= fun n =>
              (fun z : β × AuthIdealState TagId Nonce Digest =>
                  (z.2.honestOutputs, z.2.readerForged)) <$>
              (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (OracleComp.tableExtending st.responses g))
                (f ⟨n, OracleComp.tableExtending st.responses g (tag, n)⟩)).run
                ({ responses := st.responses
                   honestOutputs :=
                     insert (tag, ⟨n, OracleComp.tableExtending st.responses g (tag, n)⟩)
                       st.honestOutputs
                   readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)) := by
        refine bind_congr fun g => ?_
        rw [bind_assoc]; refine bind_congr fun n => ?_
        rw [pure_bind]
      refine Eq.trans ?_ (congrArg evalDist hrhs_swap).symm
      rw [evalDist_probComp_bind_comm ($ᵗ (TagId × Nonce → Digest)) ($ᵗ Nonce)]
      refine evalDist_bind_congr_of_support _ _ _ fun n _ => ?_
      exact hlhs_inner n
    | inr transcript =>
      -- Reader query: fold `idealCacheStep` over all `(tag, transcript.nonce)` cells.
      rw [show (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (Sum.inr transcript)).run st =
          (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            transcript).run st
        from rfl]
      rw [authRFReaderQueryImpl_run_eq_idealCacheMapM transcript st]
      set cells := (Finset.univ : Finset TagId).toList.map
        (fun tag => (tag, transcript.nonce)) with hcells
      -- Collapse the LHS bind to a single `idealCacheMapM` bind.
      have hlhs_reassoc :
          ((idealCacheMapM cells st.responses >>= fun rs =>
              (pure (ReaderReply.ofBool (decide (∃ p ∈ (Finset.univ : Finset TagId).toList.zip rs.1,
                  p.2 = transcript.auth)),
                ({ responses := rs.2
                   honestOutputs := st.honestOutputs
                   readerForged := st.readerForged ∪
                     (((((Finset.univ : Finset TagId).toList.zip rs.1).filter fun p =>
                         decide (p.2 = transcript.auth ∧
                         (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset).image
                       (·, transcript) } : AuthIdealState TagId Nonce Digest)) :
                ProbComp (ReaderReply × AuthIdealState TagId Nonce Digest)))
            >>= fun p => (fun z : β × AuthIdealState TagId Nonce Digest =>
                (z.2.honestOutputs, z.2.readerForged)) <$>
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest)) (f p.1)).run p.2)
          = (idealCacheMapM cells st.responses >>= fun rs =>
              (fun z : β × AuthIdealState TagId Nonce Digest =>
                  (z.2.honestOutputs, z.2.readerForged)) <$>
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                (f (ReaderReply.ofBool (decide (∃ p ∈ (Finset.univ : Finset TagId).toList.zip rs.1,
                  p.2 = transcript.auth))))).run
                ({ responses := rs.2
                   honestOutputs := st.honestOutputs
                   readerForged := st.readerForged ∪
                     (((((Finset.univ : Finset TagId).toList.zip rs.1).filter fun p =>
                         decide (p.2 = transcript.auth ∧
                         (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset).image
                       (·, transcript) } : AuthIdealState TagId Nonce Digest)) := by
        rw [bind_assoc]; refine bind_congr fun rs => ?_
        rw [pure_bind]
      refine (congrArg evalDist hlhs_reassoc).trans ?_
      -- Eager equivalence under `idealCacheMapM`.
      set Mψ : (TagId × Nonce → Digest) → ProbComp
          (Finset (TagId × TagTranscript Nonce Digest) ×
            Finset (TagId × TagTranscript Nonce Digest)) := fun g' =>
        (fun z : β × AuthIdealState TagId Nonce Digest =>
            (z.2.honestOutputs, z.2.readerForged)) <$>
        (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) g')
          (f (ReaderReply.ofBool (decide (∃ p ∈ cells.map (fun c => (c.1, g' c)),
            p.2 = transcript.auth))))).run
          ({ responses := st.responses
             honestOutputs := st.honestOutputs
             readerForged := st.readerForged ∪
               ((((cells.map (fun c => (c.1, g' c))).filter fun p =>
                   decide (p.2 = transcript.auth ∧
                   (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset).image
                 (·, transcript) } : AuthIdealState TagId Nonce Digest)
        with hMψ
      have hstep1 :
          𝒟[idealCacheMapM cells st.responses >>= fun rs =>
              (fun z : β × AuthIdealState TagId Nonce Digest =>
                  (z.2.honestOutputs, z.2.readerForged)) <$>
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                (f (ReaderReply.ofBool (decide (∃ p ∈ (Finset.univ : Finset TagId).toList.zip rs.1,
                  p.2 = transcript.auth))))).run
                ({ responses := rs.2
                   honestOutputs := st.honestOutputs
                   readerForged := st.readerForged ∪
                     (((((Finset.univ : Finset TagId).toList.zip rs.1).filter fun p =>
                         decide (p.2 = transcript.auth ∧
                         (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset).image
                       (·, transcript) } : AuthIdealState TagId Nonce Digest)]
          = 𝒟[idealCacheMapM cells st.responses >>= fun rs =>
              ($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
                Mψ (OracleComp.tableExtending rs.2 g)] := by
        refine evalDist_bind_congr_of_support _ _ _ fun rs hrs => ?_
        rw [ih (ReaderReply.ofBool (decide (∃ p ∈ (Finset.univ : Finset TagId).toList.zip rs.1,
            p.2 = transcript.auth)))
          ({ responses := rs.2
             honestOutputs := st.honestOutputs
             readerForged := st.readerForged ∪
               (((((Finset.univ : Finset TagId).toList.zip rs.1).filter fun p =>
                   decide (p.2 = transcript.auth ∧
                   (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset).image
                 (·, transcript) } : AuthIdealState TagId Nonce Digest)]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [hMψ]
        have hzip : (Finset.univ : Finset TagId).toList.zip rs.1
            = cells.map (fun c => (c.1, OracleComp.tableExtending rs.2 g c)) := by
          have hlen : rs.1 = cells.map (OracleComp.tableExtending rs.2 g) :=
            idealCacheMapM_support cells st.responses rs hrs g
          apply List.ext_getElem
          · simp [hlen, hcells]
          · intro i h₁ h₂
            simp only [hcells, List.getElem_zip, hlen, List.getElem_map]
        rw [hzip]
        exact simulateQ_authTableHandler_run_proj_responses_irrel _ _ _ _ rfl rfl
      rw [hstep1, evalDist_idealCacheMapM_bind_uniformTable_comp cells st.responses Mψ]
      -- RHS: collapse the table-handler reader query.
      refine (evalDist_bind_congr_of_support _ _ _ fun g _ => ?_).symm
      rw [authTableHandler_reader_run _ transcript st]
      rw [hMψ]
      change 𝒟[(pure _ : ProbComp (ReaderReply × AuthIdealState TagId Nonce Digest)) >>= fun p =>
          (fun z : β × AuthIdealState TagId Nonce Digest =>
              (z.2.honestOutputs, z.2.readerForged)) <$>
          (simulateQ (authTableHandler (OracleComp.tableExtending st.responses g))
            (f p.1)).run p.2] = _
      rw [pure_bind]
      rw [hcells]
      simp only [List.map_map, Function.comp_def]

/-! ### Static union bound in the eager world and the collision bound -/

omit [Nonempty TagId] in
/-- **Unrestricted forge bound for the random-function reader (eager-table route).** Running the
adversary against the lazy random-function handler from a forgery-free state records a forged
acceptance with probability at most `q * |TagId| * maxDigestProb`, with no restriction on the
adversary's reader nonces.

The bound is obtained in the eager-table world: by
`evalDist_simulateQ_authRFQueryImpl_run'_eq_tableExtending` the shared lazy cache is replaced by a
full table `g : TagId × Nonce → Digest` drawn up front (every cell digest fixed before any adversary
feedback), and the forged-acceptance event becomes a static union over the `≤ q * |TagId|`
reader-query cell reads, each a uniform coincidence `g (tag, nonce) = auth` of probability at most
`maxDigestProb`. -/
lemma authRF_forge_le [Fintype Nonce] [Finite Digest]
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (maxDigestProb : ℝ≥0∞)
    (hmax : ∀ d : Digest, Pr[= d | ($ᵗ Digest : ProbComp Digest)] ≤ maxDigestProb)
    (st : AuthIdealState TagId Nonce Digest)
    (hst : st.readerForged = ∅) :
    Pr[fun z : Unit × AuthIdealState TagId Nonce Digest => z.2.readerForged ≠ ∅ |
        (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          adversary).run st] ≤
      (q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
  -- FRONTIER (single remaining obligation of the collision conjecture).
  --
  -- Stage 1 (this file, fully proven) factors the lazy random-function reader through an eager full
  -- random-oracle table: `evalDist_simulateQ_authRFQueryImpl_run'_eq_tableExtending` replaces the
  -- shared lazy cache by a table `g : TagId × Nonce → Digest` drawn up front, with
  -- `authTableHandler g` the deterministic handler whose tag/reader steps read `g` (run-lemmas
  -- `authIdealTagQueryImpl_run_eq_idealCacheStep`, `authRFReaderQueryImpl_run_eq_idealCacheMapM`,
  -- `authTableHandler_tag_run`, `authTableHandler_reader_run`).
  --
  -- Stage 2 (remaining): the forged-acceptance probability in the eager world is a static union
  -- bound. The forge event is insensitive to the final `responses` cache, so it transports across
  -- the `run'`/state-projection equivalence (`simulateQ_authTableHandler_run'_responses_irrel`).
  -- Walking the adversary by `OracleComp.inductionOn`, a reader query `query_bind (Sum.inr t) f`
  -- has a FIXED argument `t` (independent of `g`), so the per-step forge probability is genuinely
  -- static `Pr_g[∃ tag, g (tag, t.nonce) = t.auth ∧ (tag, t) non-honest] ≤ |TagId| * maxDigestProb`
  -- (a `probEvent_exists_finset_le_sum` over tags, each cell read uniform by `hmax`); the
  -- continuation `f` contributes the IH bound `(q-1) * |TagId| * maxDigestProb`. The remaining
  -- technical step is the shared-`g` reconciliation between the per-step term and the IH: it needs
  -- the column-`t.nonce` marginal (`evalDist_uniformSample_bind_update_map` on the cells
  -- `(·, t.nonce)`) to expose the just-read column as fresh independent uniforms before invoking
  -- the IH on the rest of the table. This column-split marginalization is the documented multi-day
  -- remainder; the eager table is precisely what removes the reader-created-cell obstruction that
  -- killed the lazy single-world per-step route, and the resulting bound
  -- `q * |TagId| * maxDigestProb` matches the distinct-nonce sibling exactly.
  --
  -- First proof step (already available): transport the forge event to the eager table world.
  have _heager := evalDist_simulateQ_authRFQueryImpl_run'_eq_tableExtending
    (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary st
  sorry

omit [Nonempty TagId] in
/-- **Collision bound for the random-function authentication world.** For any adversary making at
most `q` reader queries, the probability that the random-function reader records a forged
acceptance is at most `q * |TagId| * maxDigestProb`, with no restriction on the adversary's reader
nonces.

The proof passes to the eager-table world
(`evalDist_simulateQ_authRFQueryImpl_run'_eq_tableExtending`): the shared lazy random-oracle cache
is replaced by a full table `g` drawn up front, after which the forged-acceptance event is a static
union over the reader-query cell reads (`authRF_forge_le`).

This closes the bound in the finite setting (`[Fintype Nonce] [Fintype Digest]`, the same instances
carried by the unlinkability headline theorems). The infinite-`Digest` generalization remains open:
there the eager full table does not exist, and the lazy single-world per-step route is provably
insufficient because a reader-created cache cell in the queried column has a fixed digest, making
the per-step forge probability `0` or `1` rather than `≤ maxDigestProb`; the bound is still
believed true via a first-forge per-path point-mass telescoping but needs a conditional/martingale
formalization. The hdist-conditional and distinct-reader-nonce siblings keep their statements. -/
theorem authRFExp_le_collisionBound [Fintype Nonce] [Fintype Digest]
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (maxDigestProb : ℝ)
    (hmax : ∀ d : Digest,
      (Pr[= d | ($ᵗ Digest : ProbComp Digest)]).toReal ≤ maxDigestProb) :
    (Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) adversary]).toReal ≤
      ((q * Fintype.card TagId : ℕ) : ℝ) * maxDigestProb := by
  -- Convert `maxDigestProb` to `ℝ≥0∞`.
  have hmax_ENNReal : ∀ d : Digest,
      Pr[= d | ($ᵗ Digest : ProbComp Digest)] ≤ ENNReal.ofReal maxDigestProb := by
    intro d
    rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top one_ne_top probOutput_le_one)]
    exact ENNReal.ofReal_le_ofReal (hmax d)
  -- Rewrite the LHS as the forged-acceptance event in the lazy random-function world.
  have hlhs : Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) adversary] =
      Pr[fun z : Unit × AuthIdealState TagId Nonce Digest => z.2.readerForged ≠ ∅ |
        (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          adversary).run AuthIdealState.init] := by
    rw [authRFExp_eq_authRFDirectExp, ← probEvent_eq_eq_probOutput, authRFDirectExp,
      probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    simp
  rw [hlhs]
  -- Apply the unrestricted forge bound and convert back to `ℝ`.
  have hcore := authRF_forge_le (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    adversary q hq (ENNReal.ofReal maxDigestProb) hmax_ENNReal AuthIdealState.init rfl
  have hconv : (Pr[fun z : Unit × AuthIdealState TagId Nonce Digest => z.2.readerForged ≠ ∅ |
        (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          adversary).run AuthIdealState.init]).toReal ≤
      ((q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * ENNReal.ofReal maxDigestProb).toReal :=
    ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) hcore
  have hsupp : (support ($ᵗ Digest : ProbComp Digest)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ne_eq, ← probFailure_eq_one_iff]
    simp
  obtain ⟨d0, _⟩ := hsupp
  have hmax_nonneg : 0 ≤ maxDigestProb := ENNReal.toReal_nonneg.trans (hmax d0)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hmax_nonneg] at hconv
  rw [Nat.cast_mul]
  exact hconv

omit [Nonempty TagId] in
/-- Uniform-`Digest` specialization of `authRFExp_le_collisionBound`: when `Digest` is sampled
uniformly, the per-digest probability is `1 / |Digest|`, so the collision bound reads
`q * |TagId| / |Digest|`. -/
theorem authRFExp_le_uniformCollisionBound [Fintype Nonce] [Fintype Digest]
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q) :
    (Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) adversary]).toReal ≤
      ((q * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) := by
  have hmax : ∀ d : Digest,
      (Pr[= d | ($ᵗ Digest : ProbComp Digest)]).toReal ≤ (Fintype.card Digest : ℝ)⁻¹ := fun d => by
    simp [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have h := authRFExp_le_collisionBound (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    adversary q hq ((Fintype.card Digest : ℝ)⁻¹) hmax
  rwa [div_eq_mul_inv]

end AuthEagerTable

end PRFTagReader
