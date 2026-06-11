/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.Defs
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeAmbient

/-!
# PRF Tag/Reader Protocol — Probe-Oracle Coupling of the Eager Auth World

This file couples the eager-table authentication world with the first-fire probe oracle of
`VCVio.OracleComp.QueryTracking.RandomOracle.ProbeAmbient`, providing the machinery behind the
collision bound's forge-growth lemma:

* `authTableHandler g` is the deterministic auth handler keyed on a full random-oracle table
  `g : TagId × Nonce → Digest` (tag queries read one cell, reader queries read a column);
* `authProbeTranslator` re-expresses an auth adversary over the combined signature
  `unifSpec + probeSpec (TagId × Nonce) Digest`: a tag query draws its nonce through the ambient
  (left) oracle and *reveals* the cell `(tag, nonce)`, while a reader query *probes* every cell of
  the queried column against the transcript's authenticator;
* `fst_simulateQ_eagerProbeImplWith_translator_run` (faithfulness): against the eager probe
  implementation `eagerProbeImplWith (QueryImpl.id' unifSpec) g`, the translated adversary
  reproduces the auth run `authTableHandler g` exactly on the output/auth-state component, for
  every probe knowledge state and fired flag;
* `simulateQ_eagerProbeImplWith_translator_support_fired` (fired dominance): along the coupled
  run, any growth of the `readerForged` log beyond a baseline forces the probe oracle's fired
  flag, via the knowledge-soundness/provenance invariant on the probe state;
* `isQueryBoundP_run_simulateQ_authProbeTranslator` (query-bound transfer): an adversary making
  at most `q` reader queries translates to at most `q * |TagId|` probe queries.

Together with the cache-extension entry point
`probEvent_uniformSample_tableExtending_bind_eagerProbeImplWith_le`, these reduce the eager
forge-growth probability to the first-fire bound `q * |TagId| / |Digest|`; the assembly lives in
`Examples.PRFTagReader.AuthTable`.
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

/-! ## The probe-oracle translation of the auth adversary

`authProbeTranslator` interprets the auth oracle interface over the combined signature
`unifSpec + probeSpec (TagId × Nonce) Digest`: the random-oracle table is never read directly,
only interrogated through *reveal* operations (tag queries) and *probe* operations (reader
queries), while the nonce draw is delegated to the ambient (left) uniform oracle. The threaded
`AuthIdealState` performs exactly the same `honestOutputs`/`readerForged` bookkeeping as
`authTableHandler`, with the table comparison `decide (g (tag, n) = auth)` replaced by the probe
reply. -/

/-- Probe the whole column `{(tag, nonce)}` of the table at the transcript's nonce against the
transcript's authenticator, collecting the per-tag boolean replies. -/
def probeColumn (transcript : TagTranscript Nonce Digest) :
    List TagId → OracleComp (unifSpec + probeSpec (TagId × Nonce) Digest) (List (TagId × Bool))
  | [] => pure []
  | tag :: tags => do
    let b ← liftM (OracleSpec.query (spec := unifSpec + probeSpec (TagId × Nonce) Digest)
      (Sum.inr (ProbeOp.probe (tag, transcript.nonce) transcript.auth)))
    let rest ← probeColumn transcript tags
    pure ((tag, b) :: rest)

/-- Knowledge-state/fired-flag update performed by `probeColumn` when answered eagerly from the
fixed table `g`: each cell of the column takes one `eagerProbeState` step, and the genuine-fire
indicator of each probe is ORed onto the flag, exactly as in `eagerProbeImplWith`. -/
def probeColumnState (g : TagId × Nonce → Digest) (transcript : TagTranscript Nonce Digest) :
    List TagId → ProbeState (TagId × Nonce) Digest × Bool →
      ProbeState (TagId × Nonce) Digest × Bool
  | [], s => s
  | tag :: tags, s => probeColumnState g transcript tags
      (eagerProbeState g s.1 (tag, transcript.nonce) transcript.auth,
        s.2 || ((s.1 (tag, transcript.nonce)).genuine transcript.auth &&
          decide (g (tag, transcript.nonce) = transcript.auth)))

/-- Probe-oracle translation of the auth oracle interface, over the combined signature
`unifSpec + probeSpec (TagId × Nonce) Digest`. A tag query draws a nonce through the ambient
(left) oracle, *reveals* the cell `(tag, nonce)` to obtain the authenticator, and records the
transcript as honest. A reader query *probes* every cell of the queried column against the
transcript's authenticator, accepts iff some probe replies `true`, and records the accepting
non-honest tags as forgeries — the same bookkeeping as `authTableReaderQueryImpl`, keyed on the
probe replies instead of direct table reads. -/
noncomputable def authProbeTranslator :
    QueryImpl (AuthOracleSpec TagId Nonce Digest)
      (StateT (AuthIdealState TagId Nonce Digest)
        (OracleComp (unifSpec + probeSpec (TagId × Nonce) Digest)))
  | Sum.inl tag => do
    let st ← get
    let nonce ← liftComp ($ᵗ Nonce : ProbComp Nonce)
      (unifSpec + probeSpec (TagId × Nonce) Digest)
    let auth ← liftM (OracleSpec.query (spec := unifSpec + probeSpec (TagId × Nonce) Digest)
      (Sum.inr (ProbeOp.reveal (tag, nonce))))
    let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
    set
      ({ responses := st.responses
         honestOutputs := insert (tag, transcript) st.honestOutputs
         readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)
    return transcript
  | Sum.inr transcript => do
    let st ← get
    let replies ← probeColumn (TagId := TagId) transcript (Finset.univ : Finset TagId).toList
    let accepted : Bool := replies.any (·.2)
    let newForged : Finset TagId :=
      ((replies.filter fun p => p.2 && decide ((p.1, transcript) ∉ st.honestOutputs)).map
        Prod.fst).toFinset
    set ({ st with readerForged := st.readerForged ∪ (newForged.image (·, transcript)) } :
      AuthIdealState TagId Nonce Digest)
    return ReaderReply.ofBool accepted

omit [Nonempty TagId] [SampleableType Digest] in
/-- The translated tag query: an ambient nonce draw, a reveal of the cell `(tag, nonce)`, and the
honest-transcript bookkeeping. -/
lemma authProbeTranslator_tag_run (tag : TagId) (st : AuthIdealState TagId Nonce Digest) :
    (authProbeTranslator (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (Sum.inl tag)).run st =
      liftComp ($ᵗ Nonce : ProbComp Nonce) (unifSpec + probeSpec (TagId × Nonce) Digest) >>=
        fun nonce =>
          (liftM (OracleSpec.query (spec := unifSpec + probeSpec (TagId × Nonce) Digest)
              (Sum.inr (ProbeOp.reveal (tag, nonce)))) :
            OracleComp (unifSpec + probeSpec (TagId × Nonce) Digest) Digest) >>= fun auth =>
            pure (⟨nonce, auth⟩,
              ({ responses := st.responses
                 honestOutputs := insert (tag, ⟨nonce, auth⟩) st.honestOutputs
                 readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)) := by
  unfold authProbeTranslator
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_eq_self,
    bind_pure_comp, StateT.run_map, StateT.run_set, pure_bind, map_pure]
  rw [bind_map_left]
  refine bind_congr fun nonce => ?_
  rw [Functor.map_map]
  rfl

omit [Nonempty TagId] [SampleableType Digest] in
/-- The translated reader query: a column probe followed by the acceptance and forged-set
bookkeeping keyed on the probe replies. -/
lemma authProbeTranslator_reader_run (transcript : TagTranscript Nonce Digest)
    (st : AuthIdealState TagId Nonce Digest) :
    (authProbeTranslator (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (Sum.inr transcript)).run st =
      probeColumn (TagId := TagId) transcript (Finset.univ : Finset TagId).toList >>=
        fun replies =>
          pure (ReaderReply.ofBool (replies.any (·.2)),
            ({ st with readerForged := st.readerForged ∪
                ((((replies.filter fun p => p.2 &&
                    decide ((p.1, transcript) ∉ st.honestOutputs)).map
                  Prod.fst).toFinset).image (·, transcript)) } :
              AuthIdealState TagId Nonce Digest)) := by
  unfold authProbeTranslator
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_eq_self,
    bind_pure_comp, StateT.run_map, StateT.run_set, pure_bind, map_pure]
  rw [Functor.map_map]
  rfl

omit [Nonempty TagId] [SampleableType Digest] in
/-- `simulateQ` of the translated adversary over a `query_bind`, simulated by the eager probe
implementation and run from a joint state: the per-query coupled step followed by the recursive
coupled simulation of the continuation. -/
lemma eager_translator_run_query_bind {α : Type} (g : TagId × Nonce → Digest)
    (t : (AuthOracleSpec TagId Nonce Digest).Domain)
    (f : (AuthOracleSpec TagId Nonce Digest).Range t →
      OracleComp (AuthOracleSpec TagId Nonce Digest) α)
    (st : AuthIdealState TagId Nonce Digest)
    (s : ProbeState (TagId × Nonce) Digest × Bool) :
    (simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g)
        ((simulateQ (authProbeTranslator (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          (liftM (OracleSpec.query t) >>= f)).run st)).run s =
      (simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g)
          ((authProbeTranslator (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run
            st)).run s >>= fun ps =>
        (simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g)
          ((simulateQ (authProbeTranslator (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
            (f ps.1.1)).run ps.1.2)).run ps.2 := by
  rw [simulateQ_query_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  rfl

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] in
/-- Simulating an ambient-lifted `ProbComp` computation with the eager probe implementation
leaves the probe state and fired flag untouched: the run is the lifted computation paired with
the unchanged state. -/
lemma simulateQ_eagerProbeImplWith_liftComp {β : Type} (g : TagId × Nonce → Digest)
    (pc : ProbComp β) (s : ProbeState (TagId × Nonce) Digest × Bool) :
    (simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g)
        (liftComp pc (unifSpec + probeSpec (TagId × Nonce) Digest))).run s =
      (fun u => (u, s)) <$> (liftM pc : OptionT ProbComp β) := by
  induction pc using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map]
    rw [show (liftM (OracleSpec.query t) :
        OracleComp (unifSpec + probeSpec (TagId × Nonce) Digest) (unifSpec.Range t)) =
      (liftM (OracleSpec.query (spec := unifSpec + probeSpec (TagId × Nonce) Digest)
          (Sum.inl t)) :
        OracleComp (unifSpec + probeSpec (TagId × Nonce) Digest) (unifSpec.Range t)) from rfl]
    rw [simulateQ_query_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, monadLift_self,
      eagerProbeImplWith_run_inl, QueryImpl.id'_apply, bind_map_left]
    have hlift : (liftM (liftM (OracleSpec.query t) >>= k) : OptionT ProbComp _) =
        (liftM (liftM (OracleSpec.query t) : ProbComp _) : OptionT ProbComp _) >>=
          fun u => liftM (k u) := by
      simp [monad_norm]
    rw [hlift, map_bind]
    refine bind_congr fun u => ?_
    simpa using ih u s

/-! ## Eager coupled step-run lemmas

The translated adversary, simulated by the eager probe implementation
`eagerProbeImplWith (QueryImpl.id' unifSpec) g`, takes deterministic steps: a tag query reduces
to an ambient nonce draw followed by a `pure` carrying the revealed cell, and a reader query is
a single `pure` carrying the column's table comparisons and the `probeColumnState` update. -/

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] in
/-- `simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g)` of a `query_bind`, run from a
joint probe state: the per-query eager reply followed by the recursive simulation. -/
lemma eager_run_query_bind {α : Type} (g : TagId × Nonce → Digest)
    (t : (unifSpec + probeSpec (TagId × Nonce) Digest).Domain)
    (k : (unifSpec + probeSpec (TagId × Nonce) Digest).Range t →
      OracleComp (unifSpec + probeSpec (TagId × Nonce) Digest) α)
    (s : ProbeState (TagId × Nonce) Digest × Bool) :
    (simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g)
        (liftM (OracleSpec.query t) >>= k)).run s =
      (eagerProbeImplWith (QueryImpl.id' unifSpec) g t).run s >>= fun ps =>
        (simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g) (k ps.1)).run ps.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]; rfl

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] in
/-- `probeColumn` simulated by the eager probe implementation: the replies are the
deterministic table comparisons of the column cells against the transcript's authenticator,
and the joint probe state evolves by `probeColumnState`. -/
lemma simulateQ_eagerProbeImplWith_probeColumn (g : TagId × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) (l : List TagId)
    (s : ProbeState (TagId × Nonce) Digest × Bool) :
    (simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g)
        (probeColumn (TagId := TagId) transcript l)).run s =
      pure (l.map (fun tag => (tag, decide (g (tag, transcript.nonce) = transcript.auth))),
        probeColumnState g transcript l s) := by
  induction l generalizing s with
  | nil =>
    simp only [probeColumn, probeColumnState, List.map_nil, simulateQ_pure, StateT.run_pure]
  | cons tag tags ih =>
    rw [probeColumn, eager_run_query_bind, eagerProbeImplWith_run_probe, pure_bind,
      simulateQ_bind, StateT.run_bind, ih]
    rw [pure_bind, simulateQ_pure, StateT.run_pure, List.map_cons, probeColumnState]

omit [Nonempty TagId] [SampleableType Digest] in
/-- The eager coupled tag step: an ambient nonce draw followed by a `pure` carrying the
revealed authenticator `g (tag, nonce)`, the honest-transcript bookkeeping, and the
`eagerRevealState` knowledge update (the fired flag untouched). -/
lemma simulateQ_eagerProbeImplWith_translator_tag_run (g : TagId × Nonce → Digest)
    (tag : TagId) (st : AuthIdealState TagId Nonce Digest)
    (s : ProbeState (TagId × Nonce) Digest × Bool) :
    (simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g)
        ((authProbeTranslator (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (Sum.inl tag)).run st)).run s =
      (liftM ($ᵗ Nonce : ProbComp Nonce) : OptionT ProbComp Nonce) >>= fun nonce =>
        pure ((⟨nonce, g (tag, nonce)⟩,
          ({ responses := st.responses
             honestOutputs := insert (tag, ⟨nonce, g (tag, nonce)⟩) st.honestOutputs
             readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)),
          (eagerRevealState g s.1 (tag, nonce), s.2)) := by
  rw [authProbeTranslator_tag_run, simulateQ_bind, StateT.run_bind,
    simulateQ_eagerProbeImplWith_liftComp, bind_map_left]
  refine bind_congr fun nonce => ?_
  simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, StateT.run_bind,
    eagerProbeImplWith_run_reveal, pure_bind, simulateQ_pure, StateT.run_pure]
  rfl

omit [Nonempty TagId] [SampleableType Digest] in
/-- The eager coupled reader step: a single `pure` whose reply and forged-set bookkeeping are
keyed on the deterministic column comparisons `decide (g (tag, nonce) = auth)`, and whose
joint probe state advances by `probeColumnState` over the column. -/
lemma simulateQ_eagerProbeImplWith_translator_reader_run (g : TagId × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) (st : AuthIdealState TagId Nonce Digest)
    (s : ProbeState (TagId × Nonce) Digest × Bool) :
    (simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g)
        ((authProbeTranslator (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (Sum.inr transcript)).run st)).run s =
      pure (((ReaderReply.ofBool (((Finset.univ : Finset TagId).toList.map
          (fun tag => (tag, decide (g (tag, transcript.nonce) = transcript.auth)))).any (·.2)) :
            (AuthOracleSpec TagId Nonce Digest).Range (Sum.inr transcript)),
        ({ st with readerForged := st.readerForged ∪
            ((((((Finset.univ : Finset TagId).toList.map
                (fun tag => (tag, decide (g (tag, transcript.nonce) = transcript.auth)))).filter
              fun p => p.2 && decide ((p.1, transcript) ∉ st.honestOutputs)).map
              Prod.fst).toFinset).image (·, transcript)) } : AuthIdealState TagId Nonce Digest)),
        probeColumnState g transcript (Finset.univ : Finset TagId).toList s) := by
  rw [authProbeTranslator_reader_run]
  -- Retype the head bind: the translator's reply type elaborates as the unreduced
  -- `(AuthOracleSpec …).Range (Sum.inr transcript)`, which blocks the `simulateQ_bind` match.
  change (simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g)
      (probeColumn (TagId := TagId) transcript (Finset.univ : Finset TagId).toList >>=
        fun replies =>
          (pure (ReaderReply.ofBool (replies.any (·.2)),
            ({ st with readerForged := st.readerForged ∪
                ((((replies.filter fun p => p.2 &&
                    decide ((p.1, transcript) ∉ st.honestOutputs)).map
                  Prod.fst).toFinset).image (·, transcript)) } :
              AuthIdealState TagId Nonce Digest)) :
            OracleComp (unifSpec + probeSpec (TagId × Nonce) Digest)
              (ReaderReply × AuthIdealState TagId Nonce Digest)))).run s = _
  rw [simulateQ_bind, StateT.run_bind, simulateQ_eagerProbeImplWith_probeColumn, pure_bind,
    simulateQ_pure, StateT.run_pure]

/-! ## Per-table faithfulness

Against the eager probe implementation for a fixed table `g`, the translated adversary
reproduces the auth run `authTableHandler g` exactly on the output/auth-state component: the
probe replies are the table comparisons the auth reader computes itself, and reveal replies
are the table cells the auth tag oracle reads itself. -/

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [SampleableType Digest] [DecidableEq Nonce] in
/-- The translated reader's acceptance bit over the probe replies equals the auth reader's
acceptance bit over the table reads. -/
private lemma probeReplies_any_eq (g : TagId × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) (l : List TagId) :
    (l.map (fun tag => (tag, decide (g (tag, transcript.nonce) = transcript.auth)))).any (·.2)
      = decide (∃ p ∈ l.map (fun tag => (tag, g (tag, transcript.nonce))),
          p.2 = transcript.auth) := by
  induction l with
  | nil => simp
  | cons tag tags ih =>
    simp only [List.map_cons, List.any_cons, List.exists_mem_cons_iff, Bool.decide_or, ih]

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] in
/-- The translated reader's forged-tag list over the probe replies equals the auth reader's
forged-tag list over the table reads. -/
private lemma probeReplies_filter_map_eq (g : TagId × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest)
    (hon : Finset (TagId × TagTranscript Nonce Digest)) (l : List TagId) :
    ((l.map (fun tag => (tag, decide (g (tag, transcript.nonce) = transcript.auth)))).filter
        (fun p => p.2 && decide ((p.1, transcript) ∉ hon))).map Prod.fst
      = ((l.map (fun tag => (tag, g (tag, transcript.nonce)))).filter
        (fun p => decide (p.2 = transcript.auth ∧ (p.1, transcript) ∉ hon))).map Prod.fst := by
  rw [List.filter_map, List.filter_map, List.map_map, List.map_map]
  change List.map (fun tag => tag) (l.filter _) = List.map (fun tag => tag) (l.filter _)
  refine congrArg _ (List.filter_congr fun tag _ => ?_)
  simp only [Function.comp_apply]
  exact (Bool.decide_and _ _).symm

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Per-table faithfulness.** For every fixed table `g`, projecting the coupled eager run to
its output/auth-state component recovers the auth run `authTableHandler g` exactly (lifted into
`OptionT`), for every starting probe knowledge state `K` and fired flag `b`: the eager replies
are independent of `(K, b)`. -/
lemma fst_simulateQ_eagerProbeImplWith_translator_run {α : Type} (g : TagId × Nonce → Digest)
    (oa : OracleComp (AuthOracleSpec TagId Nonce Digest) α)
    (st : AuthIdealState TagId Nonce Digest)
    (K : ProbeState (TagId × Nonce) Digest) (b : Bool) :
    Prod.fst <$> (simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g)
        ((simulateQ (authProbeTranslator (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          oa).run st)).run (K, b) =
      (liftM ((simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          g) oa).run st) : OptionT ProbComp (α × AuthIdealState TagId Nonce Digest)) := by
  induction oa using OracleComp.inductionOn generalizing st K b with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    simp [monad_norm]
  | query_bind t f ih =>
    rw [eager_translator_run_query_bind, map_bind, authTable_run_query_bind]
    cases t with
    | inl tag =>
      rw [simulateQ_eagerProbeImplWith_translator_tag_run, authTableHandler_tag_run,
        bind_assoc, bind_assoc]
      have hlift : (liftM ((($ᵗ Nonce : ProbComp Nonce)) >>= fun nonce =>
            pure (⟨nonce, g (tag, nonce)⟩,
              ({ responses := st.responses
                 honestOutputs := insert (tag, ⟨nonce, g (tag, nonce)⟩) st.honestOutputs
                 readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)) >>=
              fun p => (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) g) (f p.1)).run p.2) : OptionT ProbComp _)
          = (liftM ($ᵗ Nonce : ProbComp Nonce) : OptionT ProbComp Nonce) >>= fun nonce =>
              liftM (pure (⟨nonce, g (tag, nonce)⟩,
                ({ responses := st.responses
                   honestOutputs := insert (tag, ⟨nonce, g (tag, nonce)⟩) st.honestOutputs
                   readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)) >>=
                fun p => (simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) g) (f p.1)).run p.2) := by
        simp [monad_norm]
      rw [hlift]
      refine bind_congr fun nonce => ?_
      rw [pure_bind, pure_bind]
      exact ih _ _ _ _
    | inr transcript =>
      set replies : List (TagId × Bool) := (Finset.univ : Finset TagId).toList.map
        (fun tag => (tag, decide (g (tag, transcript.nonce) = transcript.auth))) with hreplies
      set pairs : List (TagId × Digest) := (Finset.univ : Finset TagId).toList.map
        (fun tag => (tag, g (tag, transcript.nonce))) with hpairs
      calc _ = Prod.fst <$> (simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g)
              ((simulateQ (authProbeTranslator (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest)) (f (ReaderReply.ofBool (replies.any (·.2))))).run
                ({ st with readerForged := st.readerForged ∪
                    ((((replies.filter fun p => p.2 &&
                        decide ((p.1, transcript) ∉ st.honestOutputs)).map
                      Prod.fst).toFinset).image (·, transcript)) } :
                  AuthIdealState TagId Nonce Digest))).run
              (probeColumnState g transcript (Finset.univ : Finset TagId).toList (K, b)) := by
            rw [simulateQ_eagerProbeImplWith_translator_reader_run]
            rfl
        _ = liftM ((simulateQ (authTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) g) (f (ReaderReply.ofBool
                (decide (∃ p ∈ pairs, p.2 = transcript.auth))))).run
              ({ st with readerForged := st.readerForged ∪
                  ((((pairs.filter fun p => decide (p.2 = transcript.auth ∧
                      (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset).image
                    (·, transcript)) } : AuthIdealState TagId Nonce Digest)) := by
            rw [hreplies, hpairs, probeReplies_any_eq g transcript,
              probeReplies_filter_map_eq g transcript st.honestOutputs]
            exact ih _ _
              (probeColumnState g transcript (Finset.univ : Finset TagId).toList (K, b)).1
              (probeColumnState g transcript (Finset.univ : Finset TagId).toList (K, b)).2
        _ = _ := by
            rw [authTableHandler_reader_run]
            rfl

/-! ## Fired dominance

Along the coupled eager run, any growth of the `readerForged` log beyond a baseline forces the
probe oracle's fired flag. The invariant carried by the induction records that the probe
knowledge state is *sound* for the table (`known` cells hold the table value, excluded sets
never contain it) and that every `known` cell has a *provenance*: the flag is already set, or
the cell was revealed to the honest log, or its transcript was already forged at the baseline.
A reader query can then only forge a new transcript through a genuine probe hit, which sets the
flag. -/

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] in
/-- Walking `probeColumnState` over a column preserves knowledge soundness and provenance, the
fired flag is monotone, and every probed tag whose cell matches the authenticator either fires
the flag or was already forged at the baseline (when its transcript is not honest). -/
private lemma probeColumnState_sound (g : TagId × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest)
    (hon forged₀ : Finset (TagId × TagTranscript Nonce Digest)) :
    ∀ (l : List TagId) (K : ProbeState (TagId × Nonce) Digest) (b : Bool),
      (∀ cell v, K cell = .known v → v = g cell) →
      (∀ cell S, K cell = .excluded S → g cell ∉ S) →
      (∀ cell v, K cell = .known v → b = true ∨
        (cell.1, (⟨cell.2, v⟩ : TagTranscript Nonce Digest)) ∈ hon ∨
        (cell.1, (⟨cell.2, v⟩ : TagTranscript Nonce Digest)) ∈ forged₀) →
      (∀ cell v, (probeColumnState g transcript l (K, b)).1 cell = .known v → v = g cell) ∧
      (∀ cell S, (probeColumnState g transcript l (K, b)).1 cell = .excluded S →
        g cell ∉ S) ∧
      (∀ cell v, (probeColumnState g transcript l (K, b)).1 cell = .known v →
        (probeColumnState g transcript l (K, b)).2 = true ∨
        (cell.1, (⟨cell.2, v⟩ : TagTranscript Nonce Digest)) ∈ hon ∨
        (cell.1, (⟨cell.2, v⟩ : TagTranscript Nonce Digest)) ∈ forged₀) ∧
      (b = true → (probeColumnState g transcript l (K, b)).2 = true) ∧
      (∀ tag ∈ l, g (tag, transcript.nonce) = transcript.auth → (tag, transcript) ∉ hon →
        (probeColumnState g transcript l (K, b)).2 = true ∨ (tag, transcript) ∈ forged₀) := by
  intro l
  induction l with
  | nil =>
    intro K b hK hKexcl hprov
    exact ⟨hK, hKexcl, fun cell v h => (hprov cell v h).imp_left fun hb => hb, fun hb => hb,
      fun tag htag => absurd htag (List.not_mem_nil)⟩
  | cons tag tags ih =>
    intro K b hK hKexcl hprov
    rw [probeColumnState]
    rcases hcell : K (tag, transcript.nonce) with v | S
    · -- `known` cell: the step is inert (the probe is not genuine).
      rw [eagerProbeState_known transcript.auth hcell]
      simp only [hcell, CellKnowledge.genuine_known, Bool.false_and, Bool.or_false]
      obtain ⟨q1, q2, q3, q4, q5⟩ := ih K b hK hKexcl hprov
      refine ⟨q1, q2, q3, q4, fun tag' htag' hga hhon => ?_⟩
      rcases List.mem_cons.1 htag' with rfl | htags
      · -- The matched cell is `known`: its provenance decides the disjunction.
        have hv : v = transcript.auth := (hK _ _ hcell).trans hga
        rcases hprov _ _ hcell with hb | hhon' | hforged
        · exact Or.inl (q4 hb)
        · exact absurd (by simpa [hv] using hhon' :
            (tag', transcript) ∈ hon) hhon
        · exact Or.inr (by simpa [hv] using hforged)
      · exact q5 tag' htags hga hhon
    · by_cases ha : transcript.auth ∈ S
      · -- Already-excluded target: the step is inert and the cell cannot match.
        rw [eagerProbeState_excluded_mem hcell ha]
        simp only [hcell, CellKnowledge.genuine_excluded, ha, not_true_eq_false, decide_false,
          Bool.false_and, Bool.or_false]
        obtain ⟨q1, q2, q3, q4, q5⟩ := ih K b hK hKexcl hprov
        refine ⟨q1, q2, q3, q4, fun tag' htag' hga hhon => ?_⟩
        rcases List.mem_cons.1 htag' with rfl | htags
        · exact absurd (hga ▸ ha) (hKexcl _ _ hcell)
        · exact q5 tag' htags hga hhon
      · by_cases hga : g (tag, transcript.nonce) = transcript.auth
        · -- Genuine hit: the flag fires and stays set; everything follows from monotonicity.
          rw [eagerProbeState_excluded_hit hcell ha hga]
          simp only [hcell, CellKnowledge.genuine_excluded, ha, not_false_eq_true, decide_true,
            hga, Bool.true_and, Bool.or_true]
          have hKhit : ∀ cell v,
              Function.update K (tag, transcript.nonce) (.known transcript.auth) cell =
                .known v → v = g cell := by
            intro cell v h
            by_cases hc : cell = (tag, transcript.nonce)
            · subst hc
              rw [Function.update_self] at h
              injection h with h
              rw [← h, hga]
            · rw [Function.update_of_ne hc] at h
              exact hK cell v h
          have hKexclhit : ∀ cell S',
              Function.update K (tag, transcript.nonce) (.known transcript.auth) cell =
                .excluded S' → g cell ∉ S' := by
            intro cell S' h
            by_cases hc : cell = (tag, transcript.nonce)
            · subst hc
              rw [Function.update_self] at h
              exact absurd h (by simp)
            · rw [Function.update_of_ne hc] at h
              exact hKexcl cell S' h
          obtain ⟨q1, q2, q3, q4, q5⟩ :=
            ih (Function.update K (tag, transcript.nonce) (.known transcript.auth)) true
              hKhit hKexclhit (fun _ _ _ => Or.inl rfl)
          refine ⟨q1, q2, q3, fun _ => q4 rfl, fun tag' htag' hga' hhon => ?_⟩
          rcases List.mem_cons.1 htag' with rfl | htags
          · exact Or.inl (q4 rfl)
          · exact q5 tag' htags hga' hhon
        · -- Genuine miss: the target joins the exclusion set; the step is sound and inert.
          rw [eagerProbeState_excluded_miss hcell ha hga]
          simp only [hcell, CellKnowledge.genuine_excluded, ha, not_false_eq_true, decide_true,
            hga, decide_false, Bool.and_false, Bool.or_false]
          have hKmiss : ∀ cell v,
              Function.update K (tag, transcript.nonce)
                (.excluded (insert transcript.auth S)) cell = .known v → v = g cell := by
            intro cell v h
            by_cases hc : cell = (tag, transcript.nonce)
            · subst hc
              rw [Function.update_self] at h
              exact absurd h (by simp)
            · rw [Function.update_of_ne hc] at h
              exact hK cell v h
          have hKexclmiss : ∀ cell S',
              Function.update K (tag, transcript.nonce)
                (.excluded (insert transcript.auth S)) cell = .excluded S' →
                g cell ∉ S' := by
            intro cell S' h
            by_cases hc : cell = (tag, transcript.nonce)
            · subst hc
              rw [Function.update_self] at h
              injection h with h
              rw [← h]
              simp only [Finset.mem_insert, not_or]
              exact ⟨hga, hKexcl _ _ hcell⟩
            · rw [Function.update_of_ne hc] at h
              exact hKexcl cell S' h
          have hprovmiss : ∀ cell v,
              Function.update K (tag, transcript.nonce)
                (.excluded (insert transcript.auth S)) cell = .known v → b = true ∨
                (cell.1, (⟨cell.2, v⟩ : TagTranscript Nonce Digest)) ∈ hon ∨
                (cell.1, (⟨cell.2, v⟩ : TagTranscript Nonce Digest)) ∈ forged₀ := by
            intro cell v h
            by_cases hc : cell = (tag, transcript.nonce)
            · subst hc
              rw [Function.update_self] at h
              exact absurd h (by simp)
            · rw [Function.update_of_ne hc] at h
              exact hprov cell v h
          obtain ⟨q1, q2, q3, q4, q5⟩ :=
            ih (Function.update K (tag, transcript.nonce)
              (.excluded (insert transcript.auth S))) b hKmiss hKexclmiss hprovmiss
          refine ⟨q1, q2, q3, q4, fun tag' htag' hga' hhon => ?_⟩
          rcases List.mem_cons.1 htag' with rfl | htags
          · exact absurd hga' hga
          · exact q5 tag' htags hga' hhon

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] in
/-- The support of a `pure` in `OptionT ProbComp` is the singleton of its value, stated for the
`Alternative`-derived `Pure` instance the coupled step-run lemmas elaborate with. -/
private lemma optionT_support_pure {β : Type} (x : β) :
    support (pure x : OptionT ProbComp β) = {x} := support_pure x

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Fired dominance.** Along the coupled eager run, every support point whose final
`readerForged` log contains a transcript outside the baseline `st₀.readerForged` carries a set
fired flag — provided the starting probe state is sound for the table and every `known` cell
has a provenance (flag set, honest, or baseline-forged). New forgeries can only arise from a
column probe replying `true`, which at a sound knowledge state is either a genuine hit
(setting the flag) or a cell whose provenance already accounts for the transcript. -/
lemma simulateQ_eagerProbeImplWith_translator_support_fired {α : Type}
    (g : TagId × Nonce → Digest) (st₀ : AuthIdealState TagId Nonce Digest)
    (oa : OracleComp (AuthOracleSpec TagId Nonce Digest) α) :
    ∀ (st : AuthIdealState TagId Nonce Digest) (K : ProbeState (TagId × Nonce) Digest)
      (b : Bool),
      (∀ cell v, K cell = .known v → v = g cell) →
      (∀ cell S, K cell = .excluded S → g cell ∉ S) →
      (b = false → st.readerForged ⊆ st₀.readerForged) →
      (∀ cell v, K cell = .known v → b = true ∨
        (cell.1, (⟨cell.2, v⟩ : TagTranscript Nonce Digest)) ∈ st.honestOutputs ∨
        (cell.1, (⟨cell.2, v⟩ : TagTranscript Nonce Digest)) ∈ st₀.readerForged) →
      ∀ z ∈ support ((simulateQ (eagerProbeImplWith (QueryImpl.id' unifSpec) g)
          ((simulateQ (authProbeTranslator (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest)) oa).run st)).run (K, b)),
        (∃ x ∈ z.1.2.readerForged, x ∉ st₀.readerForged) → z.2.2 = true := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro st K b hK hKexcl hb hprov z hz hgrow
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    obtain ⟨y, hy, hy'⟩ := hgrow
    by_contra hbt
    exact hy' (hb (Bool.eq_false_iff.mpr hbt) hy)
  | query_bind t f ihf =>
    intro st K b hK hKexcl hb hprov z hz hgrow
    rw [eager_translator_run_query_bind, mem_support_bind_iff] at hz
    obtain ⟨ps, hps, hz⟩ := hz
    cases t with
    | inl tag =>
      rw [simulateQ_eagerProbeImplWith_translator_tag_run, mem_support_bind_iff] at hps
      obtain ⟨nonce, -, hps⟩ := hps
      rw [optionT_support_pure, Set.mem_singleton_iff] at hps
      subst hps
      refine ihf _ _ _ _ ?_ ?_ ?_ ?_ z hz hgrow
      · -- Knowledge soundness for `known` cells after the reveal.
        intro cell v h
        rcases hc : K (tag, nonce) with w | S
        · rw [eagerRevealState_known hc] at h
          exact hK cell v h
        · rw [eagerRevealState_excluded hc] at h
          by_cases hcc : cell = (tag, nonce)
          · subst hcc
            rw [Function.update_self] at h
            injection h with h
            exact h.symm
          · rw [Function.update_of_ne hcc] at h
            exact hK cell v h
      · -- Exclusion soundness after the reveal.
        intro cell S' h
        rcases hc : K (tag, nonce) with w | S
        · rw [eagerRevealState_known hc] at h
          exact hKexcl cell S' h
        · rw [eagerRevealState_excluded hc] at h
          by_cases hcc : cell = (tag, nonce)
          · subst hcc
            rw [Function.update_self] at h
            exact absurd h (by simp)
          · rw [Function.update_of_ne hcc] at h
            exact hKexcl cell S' h
      · -- Baseline containment: the tag step never touches `readerForged`.
        exact hb
      · -- Provenance after the reveal: the revealed cell is freshly honest.
        intro cell v h
        rcases hc : K (tag, nonce) with w | S
        · rw [eagerRevealState_known hc] at h
          exact (hprov cell v h).imp_right (Or.imp_left Finset.mem_insert_of_mem)
        · rw [eagerRevealState_excluded hc] at h
          by_cases hcc : cell = (tag, nonce)
          · subst hcc
            rw [Function.update_self] at h
            injection h with h
            exact Or.inr (Or.inl (by rw [← h]; exact Finset.mem_insert_self _ _))
          · rw [Function.update_of_ne hcc] at h
            exact (hprov cell v h).imp_right (Or.imp_left Finset.mem_insert_of_mem)
    | inr transcript =>
      rw [simulateQ_eagerProbeImplWith_translator_reader_run] at hps
      have hps' := (mem_support_pure_iff ps _).1 hps
      subst hps'
      obtain ⟨q1, q2, q3, q4, q5⟩ := probeColumnState_sound g transcript st.honestOutputs
        st₀.readerForged (Finset.univ : Finset TagId).toList K b hK hKexcl hprov
      refine ihf _ _ _ _ ?_ ?_ ?_ ?_ z hz hgrow
      · exact q1
      · exact q2
      · -- Baseline containment: an unfired run only re-records baseline forgeries.
        intro hbf x hx
        have hbfalse : b = false := by
          rcases Bool.eq_false_or_eq_true b with hbb | hbb
          · rw [q4 hbb] at hbf
            exact absurd hbf (by simp)
          · exact hbb
        rcases Finset.mem_union.1 hx with hold | hnew
        · exact hb hbfalse hold
        · -- A new forgery comes from a `true` probe reply on a non-honest transcript.
          obtain ⟨tag', htag', rfl⟩ := Finset.mem_image.1 hnew
          rw [List.mem_toFinset] at htag'
          obtain ⟨p, hpmem, hpfst⟩ := List.mem_map.1 htag'
          obtain ⟨hpreplies, hppred⟩ := List.mem_filter.1 hpmem
          obtain ⟨t0, -, ht0⟩ := List.mem_map.1 hpreplies
          have hga : g (tag', transcript.nonce) = transcript.auth := by
            rw [Bool.and_eq_true] at hppred
            have hp2 := hppred.1
            rw [← ht0] at hp2 hpfst
            simp only at hp2 hpfst
            rw [decide_eq_true_eq] at hp2
            rw [← hpfst]
            exact hp2
          have hhon : (tag', transcript) ∉ st.honestOutputs := by
            rw [Bool.and_eq_true] at hppred
            have hp2 := hppred.2
            rw [decide_eq_true_eq] at hp2
            rwa [hpfst] at hp2
          rcases q5 tag' (Finset.mem_toList.2 (Finset.mem_univ _)) hga hhon with hfired | hbase
          · rw [hfired] at hbf
            exact absurd hbf (by simp)
          · exact hbase
      · exact q3

/-! ## Query-bound transfer

A reader-query bound on the auth adversary translates to a probe-query bound on the translated
adversary: a tag query costs no probes (an ambient nonce draw plus a reveal), and a reader
query costs exactly `|TagId|` probes (one per column cell). -/

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest]
  [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest] in
/-- An ambient-lifted `ProbComp` computation makes no probe queries. -/
private lemma isQueryBoundP_liftComp_probe_zero {β : Type} (pc : ProbComp β) :
    OracleComp.IsQueryBoundP (liftComp pc (unifSpec + probeSpec (TagId × Nonce) Digest))
      (fun i => Sum.elim (fun _ => false) ProbeOp.isProbe i = true) 0 := by
  induction pc using OracleComp.inductionOn with
  | pure x =>
    simp only [liftComp_pure]
    exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map]
    rw [show (liftM (OracleSpec.query t) :
        OracleComp (unifSpec + probeSpec (TagId × Nonce) Digest) (unifSpec.Range t)) =
      (liftM (OracleSpec.query (spec := unifSpec + probeSpec (TagId × Nonce) Digest)
          (Sum.inl t)) :
        OracleComp (unifSpec + probeSpec (TagId × Nonce) Digest) (unifSpec.Range t)) from rfl]
    exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr
      ⟨Or.inl (by simp), fun u => by simpa using ih u⟩

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest]
  [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest] in
/-- `probeColumn` makes exactly one probe query per column cell. -/
private lemma isQueryBoundP_probeColumn (transcript : TagTranscript Nonce Digest)
    (l : List TagId) :
    OracleComp.IsQueryBoundP (probeColumn (TagId := TagId) transcript l)
      (fun i => Sum.elim (fun _ => false) ProbeOp.isProbe i = true) l.length := by
  induction l with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons tag tags ih =>
    rw [probeColumn]
    refine (isQueryBoundP_query_bind_iff _ _ _ _).mpr ⟨Or.inr (Nat.succ_pos _), fun u => ?_⟩
    refine (isQueryBoundP_bind (m := 0) ih fun rest _ => isQueryBoundP_pure _ _ _).mono ?_
    simp

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Query-bound transfer.** An auth adversary making at most `q` reader queries translates to
an adversary over the combined signature making at most `q * |TagId|` probe queries: tag
queries contribute no probes, reader queries exactly `|TagId|`. -/
lemma isQueryBoundP_run_simulateQ_authProbeTranslator {α : Type}
    (oa : OracleComp (AuthOracleSpec TagId Nonce Digest) α) (q : ℕ)
    (hq : OracleComp.IsQueryBoundP oa (fun i => i.isRight) q)
    (st : AuthIdealState TagId Nonce Digest) :
    OracleComp.IsQueryBoundP
      ((simulateQ (authProbeTranslator (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        oa).run st)
      (fun i => Sum.elim (fun _ => false) ProbeOp.isProbe i = true)
      (q * Fintype.card TagId) := by
  induction oa using OracleComp.inductionOn generalizing st q with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact isQueryBoundP_pure _ _ _
  | query_bind t f ih =>
    have hrun : (simulateQ (authProbeTranslator (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest)) (liftM (OracleSpec.query t) >>= f)).run st
        = (authProbeTranslator (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run st
            >>= fun p => (simulateQ (authProbeTranslator (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest)) (f p.1)).run p.2 := by
      rw [simulateQ_query_bind, StateT.run_bind]; rfl
    rw [hrun]
    have hqsplit := (isQueryBoundP_query_bind_iff (p := fun i => i.isRight) t f q).mp hq
    cases t with
    | inl tag =>
      have hqcont : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isRight) q := by
        have := hqsplit.2
        simpa using this
      have hhead : OracleComp.IsQueryBoundP
          ((authProbeTranslator (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (Sum.inl tag)).run st)
          (fun i => Sum.elim (fun _ => false) ProbeOp.isProbe i = true) 0 := by
        rw [authProbeTranslator_tag_run]
        refine isQueryBoundP_bind (m := 0)
          (isQueryBoundP_liftComp_probe_zero _) fun nonce _ => ?_
        exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr
          ⟨Or.inl (by simp), fun u => isQueryBoundP_pure _ _ _⟩
      simpa using isQueryBoundP_bind hhead fun p _ => ih p.1 q (hqcont p.1) p.2
    | inr transcript =>
      have hqpos : 0 < q := hqsplit.1.resolve_left (by simp)
      have hqcont : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isRight) (q - 1) := by
        have := hqsplit.2
        simpa using this
      have hhead : OracleComp.IsQueryBoundP
          ((authProbeTranslator (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (Sum.inr transcript)).run st)
          (fun i => Sum.elim (fun _ => false) ProbeOp.isProbe i = true)
          (Fintype.card TagId) := by
        rw [authProbeTranslator_reader_run]
        refine (isQueryBoundP_bind (m := 0) (isQueryBoundP_probeColumn transcript
          (Finset.univ : Finset TagId).toList) fun replies _ =>
            isQueryBoundP_pure _ _ _).mono ?_
        simp [Finset.length_toList]
      have hbind := isQueryBoundP_bind hhead fun p _ => ih p.1 (q - 1) (hqcont p.1) p.2
      refine hbind.mono (le_of_eq ?_)
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hqpos).symm⟩
      rw [Nat.add_sub_cancel, Nat.succ_mul]
      exact Nat.add_comm _ _

end AuthEagerTable

end PRFTagReader
