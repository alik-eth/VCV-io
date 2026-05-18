/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# Unlinkability PRF Reduction

This file builds the PRF reduction for the tag/reader unlinkability game defined in
`Examples.PRFTagReader`. The unlinkability advantage `unlinkabilityAdvantage` is the gap between
the multiple-session world `unlinkMultipleExp` (all sessions of a tag share one secret) and the
single-session world `unlinkSingleExp` (each session uses an independent secret).

The reduction follows a three-hop game-playing argument:

* a PRF hop replacing `prfs.evalMultiple` by a lazy random function turns `unlinkMultipleExp` into
  the ideal-PRF world of `unlinkToMultiplePRFReduction`;
* an identical-until-bad coupling bounds the gap between the two random-function worlds by the
  nonce-collision probability `unlinkBadExp`;
* a second PRF hop replacing `prfs.evalSingle` turns `unlinkSingleExp` into the ideal-PRF world of
  `unlinkToSinglePRFReduction`.

Telescoping the three bounds yields `unlinkabilityAdvantage_le_two_prf_plus_collision`: the
unlinkability advantage is bounded by two PRF advantages plus `Pr[unlinkBadExp]`. Chaining the
proven `unlinkBadExp_le_sessionCollisionBound` then gives the explicit session-collision bounds.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-! ## Multiple-session reduction

The multiple-session world hashes through a single per-tag secret. Replacing that secret by a PRF
oracle on `(TagId × Nonce)` turns the game into a PRF distinguisher. -/

/-- Tag-oracle implementation of the multiple-session reduction: sample a nonce uniformly and
query the PRF oracle on `(tag, nonce)` for the authenticator. Models `unlinkTagQueryImpl` under the
`multiplePattern` with the hash replaced by a PRF oracle call. -/
def unlinkToMultiplePRFTagImpl :
    QueryImpl (TagId →ₒ Option (TagTranscript Nonce Digest))
      (StateT (UnlinkState TagId)
        (OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))) := fun tag => do
  let st ← get
  if _h : st.sessionsUsed tag < sessionsPerTag then
    let nonce ← (OracleComp.liftComp (spec := unifSpec)
      (superSpec := unifSpec + ((TagId × Nonce) →ₒ Digest)) ($ᵗ Nonce) :
      OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Nonce)
    let auth ← ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr (tag, nonce)) :
      OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest)
    set { st with
      sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1) }
    return some (⟨nonce, auth⟩ : TagTranscript Nonce Digest)
  else
    return none

/-- Reader-oracle implementation of the multiple-session reduction: query the PRF oracle on
`(tag, transcript.nonce)` for every tag and accept when some digest matches the submitted
authenticator. Models `unlinkReaderQueryImpl` under the `multiplePattern`. -/
noncomputable def unlinkToMultiplePRFReaderImpl :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (UnlinkState TagId)
        (OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))) := fun transcript => do
  let digests ← (Finset.univ : Finset TagId).toList.mapM
    (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
    (fun tag => ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query
      (Sum.inr (tag, transcript.nonce)) :
      OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest))
  return ReaderReply.ofBool (decide (∃ d ∈ digests, d = transcript.auth))

/-- Combined oracle implementation of the multiple-session reduction. -/
noncomputable def unlinkToMultiplePRFQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId)
        (OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))) :=
  unlinkToMultiplePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) +
    unlinkToMultiplePRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)

/-- PRF distinguisher against `prfs.multiplePRFScheme` derived from an unlinkability adversary.
It runs the unlinkability game with every `prfs.evalMultiple k tag nonce` replaced by a PRF oracle
query on `(tag, nonce)`, and returns the adversary's distinguishing bit. -/
noncomputable def unlinkToMultiplePRFReduction
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    PRFScheme.PRFAdversary (TagId × Nonce) Digest :=
  (simulateQ (unlinkToMultiplePRFQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run' UnlinkState.init

/-! ## Single-session reduction

The single-session world hashes through an independent secret per session. Replacing it by a PRF
oracle on `((TagId × Fin sessionsPerTag) × Nonce)` turns the game into a PRF distinguisher. -/

/-- Tag-oracle implementation of the single-session reduction: sample a nonce uniformly and query
the PRF oracle on `((tag, sid), nonce)` for the authenticator, where `sid` is the current session
index. Models `unlinkTagQueryImpl` under the `singlePattern`. -/
def unlinkToSinglePRFTagImpl :
    QueryImpl (TagId →ₒ Option (TagTranscript Nonce Digest))
      (StateT (UnlinkState TagId)
        (OracleComp (unifSpec +
          (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)))) := fun tag => do
  let st ← get
  if h : st.sessionsUsed tag < sessionsPerTag then
    let sid : Fin sessionsPerTag := ⟨st.sessionsUsed tag, h⟩
    let nonce ← (OracleComp.liftComp (spec := unifSpec)
      (superSpec := unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) ($ᵗ Nonce) :
      OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) Nonce)
    let auth ← ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
      (Sum.inr ((tag, sid), nonce)) :
      OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) Digest)
    set { st with
      sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1) }
    return some (⟨nonce, auth⟩ : TagTranscript Nonce Digest)
  else
    return none

/-- Reader-oracle implementation of the single-session reduction: query the PRF oracle on
`((tag, sid), transcript.nonce)` for every tag/session slot and accept when some digest matches
the submitted authenticator. Models `unlinkReaderQueryImpl` under the `singlePattern`. -/
noncomputable def unlinkToSinglePRFReaderImpl :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (UnlinkState TagId)
        (OracleComp (unifSpec +
          (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)))) := fun transcript => do
  let digests ← (Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.mapM
    (m := OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)))
    (fun slot => ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
      (Sum.inr (slot, transcript.nonce)) :
      OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) Digest))
  return ReaderReply.ofBool (decide (∃ d ∈ digests, d = transcript.auth))

/-- Combined oracle implementation of the single-session reduction. -/
noncomputable def unlinkToSinglePRFQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId)
        (OracleComp (unifSpec +
          (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)))) :=
  unlinkToSinglePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) +
    unlinkToSinglePRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)

/-- PRF distinguisher against `prfs.singlePRFScheme` derived from an unlinkability adversary.
It runs the unlinkability game with every `prfs.evalSingle k tag sid nonce` replaced by a PRF
oracle query on `((tag, sid), nonce)`, and returns the adversary's distinguishing bit. -/
noncomputable def unlinkToSinglePRFReduction
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest :=
  (simulateQ (unlinkToSinglePRFQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run' UnlinkState.init

/-! ## Bridge lemmas

The three lemmas below are the analytic content of the reduction. The first two are PRF-real
faithfulness lemmas (each provable by the same simulation-collapse argument as the auth-side
`prfRealExp_authToPRFReduction_eq_authExp`); the third is the identical-until-bad coupling. -/

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Per-tag-query equivalence, multiple-session world: running the reduction's tag-oracle
implementation through the real PRF simulator produces the same distribution and final state as
the real multiple-session unlinkability tag oracle parameterised by `prfs.evalMultiple k`. -/
private lemma simulateQ_prfReal_unlinkToMultiplePRFTagImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (tag : TagId) (s : UnlinkState TagId) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
        ((unlinkToMultiplePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) tag).run s) =
      (unlinkTagQueryImpl (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
        (fun tag nonce => prfs.evalMultiple k tag nonce)
        (multiplePattern (TagId := TagId) sessionsPerTag) tag).run s := by
  let so : QueryImpl ((TagId × Nonce) →ₒ Digest) ProbComp :=
    fun d => pure (prfs.multiplePRFScheme.eval k d)
  let impl : QueryImpl (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp :=
    HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + so
  have hImplEq : impl = PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k := rfl
  have hleft : ∀ {α : Type} (oa : ProbComp α),
      simulateQ impl (liftComp oa (unifSpec + ((TagId × Nonce) →ₒ Digest))) = oa := by
    intro α oa
    trans simulateQ (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) oa
    · exact QueryImpl.simulateQ_add_liftComp_left
        (impl₁' := HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp))
        (impl₂' := so) oa
    · exact simulateQ_ofLift_eq_self _
  have hquery : ∀ (d : TagId × Nonce),
      simulateQ impl
        (liftM ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr d)) :
          OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) _) =
      (pure (prfs.evalMultiple k d.1 d.2) : ProbComp Digest) := by
    intro d
    rw [simulateQ_spec_query]
    show impl (Sum.inr d) = _
    simp [impl, so, QueryImpl.add_apply_inr, TagReaderPRFs.multiplePRFScheme]
  unfold unlinkToMultiplePRFTagImpl unlinkTagQueryImpl
  rw [← hImplEq]
  by_cases hs : s.sessionsUsed tag < sessionsPerTag
  · simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      bind_pure_comp, pure_bind, dif_pos hs]
    change @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _ impl _ _ = _
    simp only [simulateQ_bind, simulateQ_map, monadLift_eq_self, hleft]
    refine bind_congr fun nonce => ?_
    erw [hquery (tag, nonce.1)]
    rfl
  · simp only [StateT.run_bind, StateT.run_get,
      bind_pure_comp, pure_bind, dif_neg hs]
    change @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _ impl _ _ = _
    simp only [StateT.run_pure, simulateQ_pure]

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] in
/-- Per-reader-query equivalence, multiple-session world: running the reduction's reader-oracle
implementation through the real PRF simulator produces the same distribution and final state as
the real multiple-session unlinkability reader oracle parameterised by `prfs.evalMultiple k`. -/
private lemma simulateQ_prfReal_unlinkToMultiplePRFReaderImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
        ((unlinkToMultiplePRFReaderImpl
            (TagId := TagId) (Nonce := Nonce) (Digest := Digest) transcript).run s) =
      (unlinkReaderQueryImpl (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
        (fun tag nonce => prfs.evalMultiple k tag nonce)
        (multiplePattern (TagId := TagId) sessionsPerTag) transcript).run s := by
  let so : QueryImpl ((TagId × Nonce) →ₒ Digest) ProbComp :=
    fun d => pure (prfs.multiplePRFScheme.eval k d)
  let impl : QueryImpl (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp :=
    HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + so
  have hImplEq : impl = PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k := rfl
  have hquery : ∀ (d : TagId × Nonce),
      simulateQ impl
        (liftM ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr d)) :
          OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) _) =
      (pure (prfs.evalMultiple k d.1 d.2) : ProbComp Digest) := by
    intro d
    rw [simulateQ_spec_query]
    show impl (Sum.inr d) = _
    simp [impl, so, QueryImpl.add_apply_inr, TagReaderPRFs.multiplePRFScheme]
  have hmapM :
      simulateQ impl
        ((Finset.univ : Finset TagId).toList.mapM
          (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
          (fun tag => ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query
            (Sum.inr (tag, transcript.nonce)) :
            OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest))) =
      pure ((Finset.univ : Finset TagId).toList.map
        fun tag => prfs.evalMultiple k tag transcript.nonce) := by
    show @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _ impl _ _ = _
    rw [simulateQ_list_mapM]
    induction (Finset.univ : Finset TagId).toList with
    | nil => rfl
    | cons t ts ih =>
      rw [List.mapM_cons]
      erw [hquery (t, transcript.nonce)]
      rw [pure_bind, ih, pure_bind]
      rfl
  have hAccept :
      decide (∃ d ∈ (Finset.univ : Finset TagId).toList.map
        fun tag => prfs.evalMultiple k tag transcript.nonce, d = transcript.auth) =
      unlinkReaderAccepts (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
        (fun tag nonce => prfs.evalMultiple k tag nonce)
        (multiplePattern (TagId := TagId) sessionsPerTag) transcript := by
    unfold unlinkReaderAccepts tagAccepts
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, multiplePattern,
      decide_eq_decide, decide_eq_true_eq]
    constructor
    · rintro ⟨d, ⟨tag, rfl⟩, hd⟩
      exact ⟨tag, ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne sessionsPerTag)⟩, hd⟩⟩
    · rintro ⟨tag, _, hd⟩
      exact ⟨_, ⟨tag, rfl⟩, hd⟩
  unfold unlinkToMultiplePRFReaderImpl unlinkReaderQueryImpl
  simp only [bind_pure_comp]
  rw [← hImplEq]
  change @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _ impl _ _ = _
  simp only [StateT.run_map, StateT.run_monadLift, simulateQ_bind, simulateQ_map,
    monadLift_eq_self, hmapM, pure_bind, simulateQ_pure, map_pure]
  rw [hAccept]
  rfl

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] in
/-- Inductive helper, multiple-session world: simulating the unlinkability adversary through the
reduction's query implementation and then through the real PRF query implementation is the same,
state-by-state, as simulating it directly through the real multiple-session query implementation
with the hash set to `prfs.evalMultiple k`. -/
private theorem simulateQ_prfReal_unlinkToMultiplePRFQueryImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
        ((simulateQ
          (unlinkToMultiplePRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag))
          adversary).run s) =
      (simulateQ
        (unlinkMultipleQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          prfs k)
        adversary).run s := by
  induction adversary using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    rfl
  | query_bind t f ih =>
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    rcases t with tag | transcript
    · change simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
            ((unlinkToMultiplePRFTagImpl tag).run s >>=
              fun p => (simulateQ unlinkToMultiplePRFQueryImpl (f p.1)).run p.2) =
          (unlinkTagQueryImpl (fun tag nonce => prfs.evalMultiple k tag nonce)
            (multiplePattern sessionsPerTag) tag).run s >>=
            fun p => (simulateQ (unlinkMultipleQueryImpl prfs k) (f p.1)).run p.2
      rw [simulateQ_bind, simulateQ_prfReal_unlinkToMultiplePRFTagImpl_run prfs k tag s]
      refine bind_congr fun p => ?_
      exact ih p.1 p.2
    · change simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
            ((unlinkToMultiplePRFReaderImpl transcript).run s >>=
              fun p => (simulateQ unlinkToMultiplePRFQueryImpl (f p.1)).run p.2) =
          (unlinkReaderQueryImpl (fun tag nonce => prfs.evalMultiple k tag nonce)
            (multiplePattern sessionsPerTag) transcript).run s >>=
            fun p => (simulateQ (unlinkMultipleQueryImpl prfs k) (f p.1)).run p.2
      rw [simulateQ_bind,
        simulateQ_prfReal_unlinkToMultiplePRFReaderImpl_run prfs k transcript s]
      refine bind_congr fun p => ?_
      exact ih p.1 p.2

/-- PRF-real faithfulness, multiple-session world: under the real PRF, each oracle query at
`(tag, nonce)` returns `prfs.evalMultiple k tag nonce`, so the reduction runs exactly the
multiple-session unlinkability game. -/
theorem prfRealExp_unlinkToMultiplePRFReduction_eq_unlinkMultipleExp
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | PRFScheme.prfRealExp prfs.multiplePRFScheme
        (unlinkToMultiplePRFReduction (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary)] =
      Pr[= true | unlinkMultipleExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) prfs adversary] := by
  suffices h : PRFScheme.prfRealExp prfs.multiplePRFScheme
      (unlinkToMultiplePRFReduction adversary) = unlinkMultipleExp prfs adversary by rw [h]
  unfold PRFScheme.prfRealExp unlinkMultipleExp
  refine bind_congr (m := ProbComp) fun k => ?_
  show simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
      (unlinkToMultiplePRFReduction adversary) =
    (simulateQ (unlinkMultipleQueryImpl prfs k) adversary).run' UnlinkState.init
  unfold unlinkToMultiplePRFReduction
  change simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
      ((simulateQ unlinkToMultiplePRFQueryImpl adversary).run UnlinkState.init >>=
        fun p => pure p.1) = _
  rw [simulateQ_bind,
    simulateQ_prfReal_unlinkToMultiplePRFQueryImpl_run prfs k adversary UnlinkState.init]
  rfl

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Per-tag-query equivalence, single-session world: running the reduction's tag-oracle
implementation through the real PRF simulator produces the same distribution and final state as
the real single-session unlinkability tag oracle parameterised by `prfs.evalSingle k`. -/
private lemma simulateQ_prfReal_unlinkToSinglePRFTagImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (tag : TagId) (s : UnlinkState TagId) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k)
        ((unlinkToSinglePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) tag).run s) =
      (unlinkTagQueryImpl (TagId := TagId) (Slot := TagId × Fin sessionsPerTag) (Nonce := Nonce)
        (Digest := Digest)
        (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
        (singlePattern (TagId := TagId) sessionsPerTag) tag).run s := by
  let so : QueryImpl (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest) ProbComp :=
    fun d => pure (prfs.singlePRFScheme.eval k d)
  let impl : QueryImpl (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) ProbComp :=
    HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + so
  have hImplEq : impl = PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k := rfl
  have hleft : ∀ {α : Type} (oa : ProbComp α),
      simulateQ impl
        (liftComp oa (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest))) = oa := by
    intro α oa
    trans simulateQ (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) oa
    · exact QueryImpl.simulateQ_add_liftComp_left
        (impl₁' := HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp))
        (impl₂' := so) oa
    · exact simulateQ_ofLift_eq_self _
  have hquery : ∀ (d : (TagId × Fin sessionsPerTag) × Nonce),
      simulateQ impl
        (liftM ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
            (Sum.inr d)) :
          OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) _) =
      (pure (prfs.evalSingle k d.1.1 d.1.2 d.2) : ProbComp Digest) := by
    intro d
    rw [simulateQ_spec_query]
    show impl (Sum.inr d) = _
    simp [impl, so, QueryImpl.add_apply_inr, TagReaderPRFs.singlePRFScheme]
  unfold unlinkToSinglePRFTagImpl unlinkTagQueryImpl
  rw [← hImplEq]
  by_cases hs : s.sessionsUsed tag < sessionsPerTag
  · simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      bind_pure_comp, pure_bind, dif_pos hs]
    change @simulateQ _ (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest))
      ProbComp _ impl _ _ = _
    simp only [simulateQ_bind, simulateQ_map, monadLift_eq_self, hleft]
    refine bind_congr fun nonce => ?_
    erw [hquery ((tag, ⟨s.sessionsUsed tag, hs⟩), nonce.1)]
    rfl
  · simp only [StateT.run_bind, StateT.run_get,
      bind_pure_comp, pure_bind, dif_neg hs]
    change @simulateQ _ (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest))
      ProbComp _ impl _ _ = _
    simp only [StateT.run_pure, simulateQ_pure]

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Per-reader-query equivalence, single-session world: running the reduction's reader-oracle
implementation through the real PRF simulator produces the same distribution and final state as
the real single-session unlinkability reader oracle parameterised by `prfs.evalSingle k`. -/
private lemma simulateQ_prfReal_unlinkToSinglePRFReaderImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k)
        ((unlinkToSinglePRFReaderImpl
            (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) transcript).run s) =
      (unlinkReaderQueryImpl (TagId := TagId) (Slot := TagId × Fin sessionsPerTag) (Nonce := Nonce)
        (Digest := Digest)
        (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
        (singlePattern (TagId := TagId) sessionsPerTag) transcript).run s := by
  let so : QueryImpl (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest) ProbComp :=
    fun d => pure (prfs.singlePRFScheme.eval k d)
  let impl : QueryImpl (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) ProbComp :=
    HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + so
  have hImplEq : impl = PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k := rfl
  have hquery : ∀ (d : (TagId × Fin sessionsPerTag) × Nonce),
      simulateQ impl
        (liftM ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
            (Sum.inr d)) :
          OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) _) =
      (pure (prfs.evalSingle k d.1.1 d.1.2 d.2) : ProbComp Digest) := by
    intro d
    rw [simulateQ_spec_query]
    show impl (Sum.inr d) = _
    simp [impl, so, QueryImpl.add_apply_inr, TagReaderPRFs.singlePRFScheme]
  have hmapM :
      simulateQ impl
        ((Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.mapM
          (m := OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)))
          (fun slot => ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
            (Sum.inr (slot, transcript.nonce)) :
            OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest))
              Digest))) =
      pure ((Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
        (fun slot : TagId × Fin sessionsPerTag =>
          prfs.evalSingle k slot.1 slot.2 transcript.nonce)) := by
    show @simulateQ _ (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest))
      ProbComp _ impl _ _ = _
    rw [simulateQ_list_mapM]
    induction (Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList with
    | nil => rfl
    | cons t ts ih =>
      rw [List.mapM_cons]
      erw [hquery (t, transcript.nonce)]
      rw [pure_bind, ih, pure_bind]
      rfl
  have hAccept :
      decide (∃ d ∈ (Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
        (fun slot : TagId × Fin sessionsPerTag =>
          prfs.evalSingle k slot.1 slot.2 transcript.nonce), d = transcript.auth) =
      unlinkReaderAccepts (TagId := TagId) (Slot := TagId × Fin sessionsPerTag) (Nonce := Nonce)
        (Digest := Digest)
        (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
        (singlePattern (TagId := TagId) sessionsPerTag) transcript := by
    unfold unlinkReaderAccepts tagAccepts
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, singlePattern,
      decide_eq_decide, decide_eq_true_eq]
    constructor
    · rintro ⟨d, ⟨⟨tag, sid⟩, hslot⟩, hd⟩
      exact ⟨tag, ⟨sid, by rw [hslot]; exact hd⟩⟩
    · rintro ⟨tag, ⟨sid, hd⟩⟩
      exact ⟨_, ⟨(tag, sid), rfl⟩, hd⟩
  unfold unlinkToSinglePRFReaderImpl unlinkReaderQueryImpl
  simp only [bind_pure_comp]
  rw [← hImplEq]
  change @simulateQ _ (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest))
    ProbComp _ impl _ _ = _
  simp only [StateT.run_map, StateT.run_monadLift, simulateQ_bind, simulateQ_map,
    monadLift_eq_self, hmapM, pure_bind, simulateQ_pure, map_pure]
  rw [hAccept]
  rfl

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] in
/-- Inductive helper, single-session world: simulating the unlinkability adversary through the
reduction's query implementation and then through the real PRF query implementation is the same,
state-by-state, as simulating it directly through the real single-session query implementation
with the hash set to `prfs.evalSingle k`. -/
private theorem simulateQ_prfReal_unlinkToSinglePRFQueryImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k)
        ((simulateQ
          (unlinkToSinglePRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag))
          adversary).run s) =
      (simulateQ
        (unlinkSingleQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          prfs k)
        adversary).run s := by
  induction adversary using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    rfl
  | query_bind t f ih =>
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    rcases t with tag | transcript
    · change simulateQ (PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k)
            ((unlinkToSinglePRFTagImpl tag).run s >>=
              fun p => (simulateQ unlinkToSinglePRFQueryImpl (f p.1)).run p.2) =
          (unlinkTagQueryImpl (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
            (singlePattern sessionsPerTag) tag).run s >>=
            fun p => (simulateQ (unlinkSingleQueryImpl prfs k) (f p.1)).run p.2
      rw [simulateQ_bind, simulateQ_prfReal_unlinkToSinglePRFTagImpl_run prfs k tag s]
      refine bind_congr fun p => ?_
      exact ih p.1 p.2
    · change simulateQ (PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k)
            ((unlinkToSinglePRFReaderImpl transcript).run s >>=
              fun p => (simulateQ unlinkToSinglePRFQueryImpl (f p.1)).run p.2) =
          (unlinkReaderQueryImpl (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
            (singlePattern sessionsPerTag) transcript).run s >>=
            fun p => (simulateQ (unlinkSingleQueryImpl prfs k) (f p.1)).run p.2
      rw [simulateQ_bind,
        simulateQ_prfReal_unlinkToSinglePRFReaderImpl_run prfs k transcript s]
      refine bind_congr fun p => ?_
      exact ih p.1 p.2

/-- PRF-real faithfulness, single-session world: under the real PRF, each oracle query at
`((tag, sid), nonce)` returns `prfs.evalSingle k tag sid nonce`, so the reduction runs exactly the
single-session unlinkability game. -/
theorem prfRealExp_unlinkToSinglePRFReduction_eq_unlinkSingleExp
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | PRFScheme.prfRealExp prfs.singlePRFScheme
        (unlinkToSinglePRFReduction (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary)] =
      Pr[= true | unlinkSingleExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) prfs adversary] := by
  suffices h : PRFScheme.prfRealExp prfs.singlePRFScheme
      (unlinkToSinglePRFReduction adversary) = unlinkSingleExp prfs adversary by rw [h]
  unfold PRFScheme.prfRealExp unlinkSingleExp
  refine bind_congr (m := ProbComp) fun k => ?_
  show simulateQ (PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k)
      (unlinkToSinglePRFReduction adversary) =
    (simulateQ (unlinkSingleQueryImpl prfs k) adversary).run' UnlinkState.init
  unfold unlinkToSinglePRFReduction
  change simulateQ (PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k)
      ((simulateQ unlinkToSinglePRFQueryImpl adversary).run UnlinkState.init >>=
        fun p => pure p.1) = _
  rw [simulateQ_bind,
    simulateQ_prfReal_unlinkToSinglePRFQueryImpl_run prfs k adversary UnlinkState.init]
  rfl

/-! ### Composed ideal-world handlers

The two ideal-PRF experiments are each a `simulateQ` of the lazy random oracle applied to the
output of a `simulateQ` of the reduction's query implementation. The `*IdealQueryImpl` definitions
below package that nested simulation as a single stateful handler over the unlinkability oracle
interface, with state `UnlinkState TagId × QueryCache`. The `simulateQ_*Ideal_collapse` lemmas show
that simulating the adversary through the composed handler reproduces the nested simulation up to
the obvious reassociation of the product state. -/

/-- Composed multiple-session ideal handler: run the reduction's query implementation, then
interpret the resulting PRF-oracle queries through the lazy random oracle. -/
noncomputable def multipleIdealQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) ProbComp) :=
  fun q => fun p => do
    let r ← (simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToMultiplePRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) q).run p.1)).run p.2
    return (r.1.1, (r.1.2, r.2))

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The nested simulation defining the multiple-session ideal experiment collapses to a single
`simulateQ` of `multipleIdealQueryImpl`, up to reassociating the product state. -/
private lemma simulateQ_multipleIdeal_collapse
    (adv : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId) (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ PRFScheme.prfIdealQueryImpl
        ((simulateQ (unlinkToMultiplePRFQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run s)).run c =
      (fun r : (Bool × UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) =>
        ((r.1, r.2.1), r.2.2)) <$>
        (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run (s, c) := by
  induction adv using OracleComp.inductionOn generalizing s c with
  | pure x => rw [simulateQ_pure, StateT.run_pure, simulateQ_pure]; rfl
  | query_bind t f ih =>
    rw [simulateQ_bind, StateT.run_bind]
    change (simulateQ PRFScheme.prfIdealQueryImpl
        ((simulateQ unlinkToMultiplePRFQueryImpl (liftM (OracleSpec.query t))).run s >>=
          fun p => (simulateQ unlinkToMultiplePRFQueryImpl (f p.1)).run p.2)).run c = _
    rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, map_bind]
    have hhead : (simulateQ PRFScheme.prfIdealQueryImpl
          ((simulateQ (unlinkToMultiplePRFQueryImpl (sessionsPerTag := sessionsPerTag))
            (liftM (OracleSpec.query t))).run s)).run c =
        (fun r : ((UnlinkOracleSpec TagId Nonce Digest).Range t × UnlinkState TagId ×
            ((TagId × Nonce) →ₒ Digest).QueryCache) => ((r.1, r.2.1), r.2.2)) <$>
          (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag) t).run (s, c) := by
      rw [simulateQ_spec_query]
      change _ = _ <$> (multipleIdealQueryImpl t (s, c))
      simp only [multipleIdealQueryImpl, map_bind, map_pure]
      rw [bind_pure]
    rw [hhead, bind_map_left, simulateQ_spec_query]
    refine bind_congr fun r => ?_
    exact ih r.1 r.2.1 r.2.2

/-- Composed single-session ideal handler: run the reduction's query implementation, then
interpret the resulting PRF-oracle queries through the lazy random oracle. -/
noncomputable def singleIdealQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId ×
        (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) ProbComp) :=
  fun q => fun p => do
    let r ← (simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToSinglePRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) q).run p.1)).run p.2
    return (r.1.1, (r.1.2, r.2))

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The nested simulation defining the single-session ideal experiment collapses to a single
`simulateQ` of `singleIdealQueryImpl`, up to reassociating the product state. -/
private lemma simulateQ_singleIdeal_collapse
    (adv : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ PRFScheme.prfIdealQueryImpl
        ((simulateQ (unlinkToSinglePRFQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run s)).run c =
      (fun r : (Bool × UnlinkState TagId ×
          (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) =>
        ((r.1, r.2.1), r.2.2)) <$>
        (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run (s, c) := by
  induction adv using OracleComp.inductionOn generalizing s c with
  | pure x => rw [simulateQ_pure, StateT.run_pure, simulateQ_pure]; rfl
  | query_bind t f ih =>
    rw [simulateQ_bind, StateT.run_bind]
    change (simulateQ PRFScheme.prfIdealQueryImpl
        ((simulateQ unlinkToSinglePRFQueryImpl (liftM (OracleSpec.query t))).run s >>=
          fun p => (simulateQ unlinkToSinglePRFQueryImpl (f p.1)).run p.2)).run c = _
    rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, map_bind]
    have hhead : (simulateQ PRFScheme.prfIdealQueryImpl
          ((simulateQ (unlinkToSinglePRFQueryImpl (sessionsPerTag := sessionsPerTag))
            (liftM (OracleSpec.query t))).run s)).run c =
        (fun r : ((UnlinkOracleSpec TagId Nonce Digest).Range t × UnlinkState TagId ×
            (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) =>
            ((r.1, r.2.1), r.2.2)) <$>
          (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag) t).run (s, c) := by
      rw [simulateQ_spec_query]
      change _ = _ <$> (singleIdealQueryImpl t (s, c))
      simp only [singleIdealQueryImpl, map_bind, map_pure]
      rw [bind_pure]
    rw [hhead, bind_map_left, simulateQ_spec_query]
    refine bind_congr fun r => ?_
    exact ih r.1 r.2.1 r.2.2

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The multiple-session ideal-PRF experiment is the composed handler `multipleIdealQueryImpl`
simulated over the adversary from the initial state. -/
private lemma prfIdealExp_unlinkToMultiplePRFReduction_eq_run'
    (adv : UnlinkAdversary TagId Nonce Digest) :
    PRFScheme.prfIdealExp (unlinkToMultiplePRFReduction (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) adv) =
      (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run' (UnlinkState.init, ∅) := by
  unfold PRFScheme.prfIdealExp unlinkToMultiplePRFReduction
  rw [StateT.run']
  change (simulateQ PRFScheme.prfIdealQueryImpl
      ((simulateQ unlinkToMultiplePRFQueryImpl adv).run UnlinkState.init >>=
        fun p => pure p.1)).run' ∅ = _
  rw [simulateQ_bind]
  change ((simulateQ PRFScheme.prfIdealQueryImpl
      ((simulateQ unlinkToMultiplePRFQueryImpl adv).run UnlinkState.init) >>=
        fun p => simulateQ PRFScheme.prfIdealQueryImpl (pure p.1))).run' ∅ = _
  rw [StateT.run'_eq, StateT.run_bind]
  rw [simulateQ_multipleIdeal_collapse adv UnlinkState.init ∅]
  rw [StateT.run'_eq, map_bind, bind_map_left]
  refine bind_congr fun r => ?_
  simp only [simulateQ_pure, StateT.run_pure, map_pure, Function.comp]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The single-session ideal-PRF experiment is the composed handler `singleIdealQueryImpl`
simulated over the adversary from the initial state. -/
private lemma prfIdealExp_unlinkToSinglePRFReduction_eq_run'
    (adv : UnlinkAdversary TagId Nonce Digest) :
    PRFScheme.prfIdealExp (unlinkToSinglePRFReduction (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) adv) =
      (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run' (UnlinkState.init, ∅) := by
  unfold PRFScheme.prfIdealExp unlinkToSinglePRFReduction
  rw [StateT.run']
  change (simulateQ PRFScheme.prfIdealQueryImpl
      ((simulateQ unlinkToSinglePRFQueryImpl adv).run UnlinkState.init >>=
        fun p => pure p.1)).run' ∅ = _
  rw [simulateQ_bind]
  change ((simulateQ PRFScheme.prfIdealQueryImpl
      ((simulateQ unlinkToSinglePRFQueryImpl adv).run UnlinkState.init) >>=
        fun p => simulateQ PRFScheme.prfIdealQueryImpl (pure p.1))).run' ∅ = _
  rw [StateT.run'_eq, StateT.run_bind]
  rw [simulateQ_singleIdeal_collapse adv UnlinkState.init ∅]
  rw [StateT.run'_eq, map_bind, bind_map_left]
  refine bind_congr fun r => ?_
  simp only [simulateQ_pure, StateT.run_pure, map_pure, Function.comp]
  rfl

/-! ### Per-query reduction lemmas for the composed ideal handlers

The `*IdealQueryImpl` handlers are `simulateQ`-wrappers; the lemmas below give their explicit
reduced forms on each oracle query, so that a coupling induction can reason about them concretely.
The lazy-random-oracle lookup at a domain point is exposed via `QueryCache` operations. -/

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Reduced form of the multiple-session reduction tag handler when the slot budget is exhausted. -/
private lemma unlinkToMultiplePRFTagImpl_run_of_not_lt (tag : TagId) (s : UnlinkState TagId)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (unlinkToMultiplePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) tag).run s = pure (none, s) := by
  unfold unlinkToMultiplePRFTagImpl
  simp [hslot]

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Reduced form of the multiple-session reduction tag handler when a slot is available: sample a
nonce, query the PRF oracle at `(tag, nonce)`, advance the session counter. -/
private lemma unlinkToMultiplePRFTagImpl_run_of_lt (tag : TagId) (s : UnlinkState TagId)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (unlinkToMultiplePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) tag).run s =
      (OracleComp.liftComp (spec := unifSpec)
          (superSpec := unifSpec + ((TagId × Nonce) →ₒ Digest)) ($ᵗ Nonce)) >>= fun nonce =>
        ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr (tag, nonce))) >>= fun auth =>
          pure (some (⟨nonce, auth⟩ : TagTranscript Nonce Digest),
            { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }) := by
  unfold unlinkToMultiplePRFTagImpl
  simp [hslot, StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set,
    StateT.run_pure, bind_assoc]

/-- The lazy-random-oracle answer to a PRF-oracle query on domain point `d` against cache `c`:
return the cached digest, or sample a fresh one and insert it. -/
private noncomputable def idealCacheStep {D : Type} [DecidableEq D]
    (c : (D →ₒ Digest).QueryCache) (d : D) :
    ProbComp (Digest × (D →ₒ Digest).QueryCache) :=
  match c d with
  | some u => pure (u, c)
  | none => ($ᵗ Digest) >>= fun u => pure (u, c.cacheQuery d u)

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Simulating a left-injected (uniform-sampling) query through `prfIdealQueryImpl` discards the
cache and reduces to the plain probabilistic computation. -/
private lemma simulateQ_prfIdeal_liftComp {D : Type} [DecidableEq D] {α : Type}
    (oa : ProbComp α) (c : (D →ₒ Digest).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Digest))
        (OracleComp.liftComp oa (unifSpec + (D →ₒ Digest)))).run c =
      oa >>= fun a => pure (a, c) := by
  have h := QueryImpl.simulateQ_add_liftComp_left
    ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (D →ₒ Digest).QueryCache ProbComp)) randomOracle oa
  exact (congrArg (StateT.run · c) (h.trans ((simulateQ_liftTarget _ oa).trans
    (congrArg liftM (simulateQ_ofLift_eq_self oa))))).trans (StateT.run_monadLift oa c)

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Simulating a right-injected (PRF-function) query through `prfIdealQueryImpl` consults the
lazy random oracle: `idealCacheStep`. -/
private lemma simulateQ_prfIdeal_query_inr {D : Type} [DecidableEq D]
    (d : D) (c : (D →ₒ Digest).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Digest))
        (liftM ((PRFScheme.PRFOracleSpec D Digest).query (Sum.inr d)) :
          OracleComp (PRFScheme.PRFOracleSpec D Digest) Digest)).run c =
      idealCacheStep c d := by
  rw [simulateQ_query]
  change ((fun x => x) <$> PRFScheme.prfIdealQueryImpl (Sum.inr d)).run c = _
  rw [id_map']
  change (OracleSpec.randomOracle d).run c = _
  unfold idealCacheStep
  cases hc : c d with
  | none =>
    change (uniformSampleImpl.withCaching d).run c = _
    rw [QueryImpl.withCaching_run_none uniformSampleImpl hc]
    rfl
  | some u =>
    change (uniformSampleImpl.withCaching d).run c = _
    rw [QueryImpl.withCaching_run_some uniformSampleImpl hc]

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- `simulateQ prfIdealQueryImpl` distributes over a bind, threaded through the cache state. -/
private lemma simulateQ_prfIdeal_run_bind {D : Type} [DecidableEq D] {α β : Type}
    (mx : OracleComp (PRFScheme.PRFOracleSpec D Digest) α)
    (my : α → OracleComp (PRFScheme.PRFOracleSpec D Digest) β)
    (c : (D →ₒ Digest).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Digest)) (mx >>= my)).run c =
      (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Digest)) mx).run c >>= fun p =>
        (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Digest)) (my p.1)).run p.2 := by
  rw [simulateQ_bind, StateT.run_bind]

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- `simulateQ prfIdealQueryImpl` of a `pure` returns the value paired with the unchanged cache. -/
private lemma simulateQ_prfIdeal_run_pure {D : Type} [DecidableEq D] {α : Type}
    (a : α) (c : (D →ₒ Digest).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Digest))
        (pure a : OracleComp (PRFScheme.PRFOracleSpec D Digest) α)).run c = pure (a, c) := by
  rw [simulateQ_pure, StateT.run_pure]

/-- Folding the lazy-random-oracle lookup `idealCacheStep` over a list of domain points, threading
the cache: this is the reader-oracle's behaviour under `prfIdealQueryImpl`. -/
private noncomputable def idealCacheMapM {D : Type} [DecidableEq D]
    (l : List D) (c : (D →ₒ Digest).QueryCache) :
    ProbComp (List Digest × (D →ₒ Digest).QueryCache) :=
  match l with
  | [] => pure ([], c)
  | d :: ds => idealCacheStep c d >>= fun r =>
      idealCacheMapM ds r.2 >>= fun rs => pure (r.1 :: rs.1, rs.2)

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Simulating a `mapM` of right-injected PRF-oracle queries (with domain points `f a`) through
`prfIdealQueryImpl` folds the lazy random oracle over `l.map f`: `idealCacheMapM`. -/
private lemma simulateQ_prfIdeal_run_mapM {D α : Type} [DecidableEq D]
    (f : α → D) (l : List α) (c : (D →ₒ Digest).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Digest))
        (l.mapM (m := OracleComp (PRFScheme.PRFOracleSpec D Digest))
          (fun a => (liftM ((PRFScheme.PRFOracleSpec D Digest).query (Sum.inr (f a))) :
            OracleComp (PRFScheme.PRFOracleSpec D Digest) Digest)))).run c =
      idealCacheMapM (l.map f) c := by
  induction l generalizing c with
  | nil => simp [idealCacheMapM, simulateQ_pure, StateT.run_pure]
  | cons a as ih =>
    rw [List.mapM_cons, List.map_cons]
    erw [simulateQ_bind, StateT.run_bind, simulateQ_prfIdeal_query_inr]
    rw [idealCacheMapM]
    refine bind_congr fun r => ?_
    erw [simulateQ_bind, StateT.run_bind, ih]
    refine bind_congr fun rs => ?_
    erw [simulateQ_pure, StateT.run_pure]

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Reduced form of the multiple-session reduction reader handler: query the PRF oracle at
`(tag, transcript.nonce)` for every tag, then return acceptance; the state is untouched. -/
private lemma unlinkToMultiplePRFReaderImpl_run
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    (unlinkToMultiplePRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      transcript).run s =
      ((Finset.univ : Finset TagId).toList.mapM
        (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
        (fun tag => ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query
          (Sum.inr (tag, transcript.nonce)) :
          OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest))) >>= fun digests =>
        pure (ReaderReply.ofBool (decide (∃ d ∈ digests, d = transcript.auth)), s) := by
  unfold unlinkToMultiplePRFReaderImpl
  simp [StateT.run_monadLift, bind_pure_comp]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Multiple-session ideal handler on a tag query whose slot budget is exhausted: returns `none`,
state unchanged. -/
private lemma multipleIdealQueryImpl_tag_run_of_not_lt (tag : TagId) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) (s, c) =
      pure ((none, s, c)) := by
  unfold multipleIdealQueryImpl unlinkToMultiplePRFQueryImpl
  rw [QueryImpl.add_apply_inl unlinkToMultiplePRFTagImpl unlinkToMultiplePRFReaderImpl tag]
  change (do let r ← (simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToMultiplePRFTagImpl tag).run s)).run c; pure (r.1.1, r.1.2, r.2)) = _
  rw [unlinkToMultiplePRFTagImpl_run_of_not_lt tag s hslot]
  rfl

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Running the multiple-session reduction tag handler (slot available) through the lazy random
oracle: sample a nonce, consult the cache at `(tag, nonce)` via `idealCacheStep`, and advance the
session counter. The proof uses `erw` to bridge the reducible-defeq gap between the unfolded spec
`unifSpec + ((TagId × Nonce) →ₒ Digest)` and `PRFScheme.PRFOracleSpec (TagId × Nonce) Digest`. -/
private lemma simulateQ_prfIdeal_unlinkToMultiplePRFTagImpl_run_of_lt
    (tag : TagId) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
        ((unlinkToMultiplePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) tag).run s)).run c =
      ($ᵗ Nonce) >>= fun nonce =>
        idealCacheStep c (tag, nonce) >>= fun r =>
          pure ((some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
            { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }), r.2) := by
  rw [unlinkToMultiplePRFTagImpl_run_of_lt tag s hslot]
  erw [simulateQ_bind, StateT.run_bind, simulateQ_prfIdeal_liftComp, bind_assoc]
  refine bind_congr fun nonce => ?_
  rw [pure_bind]
  erw [simulateQ_bind, StateT.run_bind, simulateQ_prfIdeal_query_inr]
  refine bind_congr fun r => ?_
  erw [simulateQ_pure, StateT.run_pure]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Multiple-session ideal handler on a tag query with a free slot: sample a nonce, consult the
random-oracle cache at `(tag, nonce)` via `idealCacheStep`, advance the session counter. -/
private lemma multipleIdealQueryImpl_tag_run_of_lt (tag : TagId) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) (s, c) =
      ($ᵗ Nonce) >>= fun nonce =>
        idealCacheStep c (tag, nonce) >>= fun r =>
          pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
            { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }, r.2) := by
  unfold multipleIdealQueryImpl unlinkToMultiplePRFQueryImpl
  rw [QueryImpl.add_apply_inl unlinkToMultiplePRFTagImpl unlinkToMultiplePRFReaderImpl tag]
  change ((simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToMultiplePRFTagImpl tag).run s)).run c) >>=
      (fun r => pure (r.1.1, r.1.2, r.2)) = _
  rw [simulateQ_prfIdeal_unlinkToMultiplePRFTagImpl_run_of_lt tag s c hslot, bind_assoc]
  refine bind_congr fun nonce => ?_
  rw [bind_assoc]
  refine bind_congr fun r => ?_
  rw [pure_bind]

omit [Nonempty TagId] [SampleableType Nonce] [NeZero sessionsPerTag] in
/-- Running the multiple-session reduction reader handler through the lazy random oracle: fold
`idealCacheStep` over the `(tag, transcript.nonce)` domain points, then return acceptance. -/
private lemma simulateQ_prfIdeal_unlinkToMultiplePRFReaderImpl_run
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
        ((unlinkToMultiplePRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          transcript).run s)).run c =
      idealCacheMapM ((Finset.univ : Finset TagId).toList.map
          (fun tag => (tag, transcript.nonce))) c >>= fun rs =>
        pure ((ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s), rs.2) := by
  rw [unlinkToMultiplePRFReaderImpl_run transcript s]
  erw [simulateQ_bind, StateT.run_bind,
    simulateQ_prfIdeal_run_mapM (fun tag => (tag, transcript.nonce))]
  refine bind_congr fun rs => ?_
  erw [simulateQ_pure, StateT.run_pure]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Multiple-session ideal handler on a reader query: fold `idealCacheStep` over the
`(tag, transcript.nonce)` domain points and return reader acceptance. -/
private lemma multipleIdealQueryImpl_reader_run
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) (s, c) =
      idealCacheMapM ((Finset.univ : Finset TagId).toList.map
          (fun tag => (tag, transcript.nonce))) c >>= fun rs =>
        pure (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s, rs.2) := by
  unfold multipleIdealQueryImpl unlinkToMultiplePRFQueryImpl
  rw [QueryImpl.add_apply_inr unlinkToMultiplePRFTagImpl unlinkToMultiplePRFReaderImpl transcript]
  change ((simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToMultiplePRFReaderImpl transcript).run s)).run c) >>=
      (fun r => pure (r.1.1, r.1.2, r.2)) = _
  rw [simulateQ_prfIdeal_unlinkToMultiplePRFReaderImpl_run transcript s c, bind_assoc]
  refine bind_congr fun rs => ?_
  rw [pure_bind]

/-! ### Per-query reduction lemmas, single-session ideal handler -/

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Reduced form of the single-session reduction tag handler when the slot budget is exhausted. -/
private lemma unlinkToSinglePRFTagImpl_run_of_not_lt (tag : TagId) (s : UnlinkState TagId)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (unlinkToSinglePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) tag).run s = pure (none, s) := by
  unfold unlinkToSinglePRFTagImpl
  simp [hslot]

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Reduced form of the single-session reduction tag handler when a slot is available: sample a
nonce, query the PRF oracle at `((tag, sid), nonce)`, advance the session counter. -/
private lemma unlinkToSinglePRFTagImpl_run_of_lt (tag : TagId) (s : UnlinkState TagId)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (unlinkToSinglePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) tag).run s =
      (OracleComp.liftComp (spec := unifSpec)
          (superSpec := unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest))
          ($ᵗ Nonce)) >>= fun nonce =>
        ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
          (Sum.inr ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce))) >>= fun auth =>
          pure (some (⟨nonce, auth⟩ : TagTranscript Nonce Digest),
            { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }) := by
  unfold unlinkToSinglePRFTagImpl
  simp [hslot, StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set]

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Running the single-session reduction tag handler (slot available) through the lazy random
oracle: sample a nonce, consult the cache at `((tag, sid), nonce)` via `idealCacheStep`, advance
the session counter. -/
private lemma simulateQ_prfIdeal_unlinkToSinglePRFTagImpl_run_of_lt
    (tag : TagId) (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := (TagId × Fin sessionsPerTag) × Nonce)
        (R := Digest))
        ((unlinkToSinglePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) tag).run s)).run c =
      ($ᵗ Nonce) >>= fun nonce =>
        idealCacheStep c ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce) >>= fun r =>
          pure ((some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
            { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }), r.2) := by
  rw [unlinkToSinglePRFTagImpl_run_of_lt tag s hslot]
  erw [simulateQ_bind, StateT.run_bind, simulateQ_prfIdeal_liftComp, bind_assoc]
  refine bind_congr fun nonce => ?_
  rw [pure_bind]
  erw [simulateQ_bind, StateT.run_bind, simulateQ_prfIdeal_query_inr]
  refine bind_congr fun r => ?_
  erw [simulateQ_pure, StateT.run_pure]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Single-session ideal handler on a tag query whose slot budget is exhausted: returns `none`,
state unchanged. -/
private lemma singleIdealQueryImpl_tag_run_of_not_lt (tag : TagId) (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) (s, c) =
      pure ((none, s, c)) := by
  unfold singleIdealQueryImpl unlinkToSinglePRFQueryImpl
  rw [QueryImpl.add_apply_inl unlinkToSinglePRFTagImpl unlinkToSinglePRFReaderImpl tag]
  change (do let r ← (simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToSinglePRFTagImpl tag).run s)).run c; pure (r.1.1, r.1.2, r.2)) = _
  rw [unlinkToSinglePRFTagImpl_run_of_not_lt tag s hslot]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Single-session ideal handler on a tag query with a free slot: sample a nonce, consult the
random-oracle cache at `((tag, sid), nonce)` via `idealCacheStep`, advance the session counter. -/
private lemma singleIdealQueryImpl_tag_run_of_lt (tag : TagId) (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) (s, c) =
      ($ᵗ Nonce) >>= fun nonce =>
        idealCacheStep c ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce) >>= fun r =>
          pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
            { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }, r.2) := by
  unfold singleIdealQueryImpl unlinkToSinglePRFQueryImpl
  rw [QueryImpl.add_apply_inl unlinkToSinglePRFTagImpl unlinkToSinglePRFReaderImpl tag]
  change ((simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToSinglePRFTagImpl tag).run s)).run c) >>=
      (fun r => pure (r.1.1, r.1.2, r.2)) = _
  rw [simulateQ_prfIdeal_unlinkToSinglePRFTagImpl_run_of_lt tag s c hslot, bind_assoc]
  refine bind_congr fun nonce => ?_
  rw [bind_assoc]
  refine bind_congr fun r => ?_
  rw [pure_bind]

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Reduced form of the single-session reduction reader handler: query the PRF oracle at
`(slot, transcript.nonce)` for every tag/session slot, then return acceptance; state untouched. -/
private lemma unlinkToSinglePRFReaderImpl_run
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    (unlinkToSinglePRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) transcript).run s =
      ((Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.mapM
        (m := OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)))
        (fun slot => ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
          (Sum.inr (slot, transcript.nonce)) :
          OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest))
            Digest))) >>= fun digests =>
        pure (ReaderReply.ofBool (decide (∃ d ∈ digests, d = transcript.auth)), s) := by
  unfold unlinkToSinglePRFReaderImpl
  simp [StateT.run_monadLift, bind_pure_comp]

omit [Nonempty TagId] [SampleableType Nonce] [NeZero sessionsPerTag] in
/-- Running the single-session reduction reader handler through the lazy random oracle: fold
`idealCacheStep` over the `(slot, transcript.nonce)` domain points, then return acceptance. -/
private lemma simulateQ_prfIdeal_unlinkToSinglePRFReaderImpl_run
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := (TagId × Fin sessionsPerTag) × Nonce)
        (R := Digest))
        ((unlinkToSinglePRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) transcript).run s)).run c =
      idealCacheMapM ((Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
          (fun slot => (slot, transcript.nonce))) c >>= fun rs =>
        pure ((ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s), rs.2) := by
  rw [unlinkToSinglePRFReaderImpl_run transcript s]
  erw [simulateQ_bind, StateT.run_bind,
    simulateQ_prfIdeal_run_mapM (fun slot => (slot, transcript.nonce))]
  refine bind_congr fun rs => ?_
  erw [simulateQ_pure, StateT.run_pure]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Single-session ideal handler on a reader query: fold `idealCacheStep` over the
`(slot, transcript.nonce)` domain points and return reader acceptance. -/
private lemma singleIdealQueryImpl_reader_run
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) (s, c) =
      idealCacheMapM ((Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
          (fun slot => (slot, transcript.nonce))) c >>= fun rs =>
        pure (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s, rs.2) := by
  unfold singleIdealQueryImpl unlinkToSinglePRFQueryImpl
  rw [QueryImpl.add_apply_inr unlinkToSinglePRFTagImpl unlinkToSinglePRFReaderImpl transcript]
  change ((simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToSinglePRFReaderImpl transcript).run s)).run c) >>=
      (fun r => pure (r.1.1, r.1.2, r.2)) = _
  rw [simulateQ_prfIdeal_unlinkToSinglePRFReaderImpl_run transcript s c, bind_assoc]
  refine bind_congr fun rs => ?_
  rw [pure_bind]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Base case of any coupling induction for `multipleIdeal_le_singleIdeal_add_bad`: on a `pure`
adversary the multiple- and single-session ideal handlers return the same bit, so the
multiple-world success probability is trivially bounded by the single-world one plus the
bad-event probability. Holds for arbitrary (not necessarily coupled) initial states. -/
private lemma multipleIdeal_le_singleIdeal_add_bad_pure (b : Bool)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sS : UnlinkState TagId × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) :
    Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (pure b)).run' sM] ≤
      Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (pure b)).run' sS] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (pure b)).run sB] := by
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
  exact le_add_right (le_refl _)

/-! ### Structural reductions of the composed ideal handlers on a `query_bind`

The next two lemmas expose `simulateQ … (query_bind t f)` run from a state as a single monadic
`bind`: the per-query handler applied to the head, then the recursive `simulateQ` of the
continuation threaded through the resulting state. They are pure rewriting facts (`simulateQ` is a
monad morphism), and they turn the coupling induction into a sequence of `bind`-decomposition
steps that `probEvent_bind_le_add` / `probEvent_bind_congr_le_add` can attack. -/

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ multipleIdealQueryImpl` of a `query_bind`, run from a state and projected to its
output bit, is the per-query handler followed by the recursive simulation of the continuation. -/
private lemma multipleIdeal_run'_query_bind
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t → UnlinkAdversary TagId Nonce Digest)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' sM =
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sM) >>= fun p =>
        (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ singleIdealQueryImpl` of a `query_bind`, run from a state and projected to its
output bit, is the per-query handler followed by the recursive simulation of the continuation. -/
private lemma singleIdeal_run'_query_bind
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t → UnlinkAdversary TagId Nonce Digest)
    (sS : UnlinkState TagId × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' sS =
      (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sS) >>= fun p =>
        (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ unlinkBadQueryImpl` of a `query_bind`, run from a state, is the per-query handler
followed by the recursive simulation of the continuation threaded through the resulting state. -/
private lemma unlinkBad_run_query_bind
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t → UnlinkAdversary TagId Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run sB =
      (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sB) >>= fun p =>
        (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

/-! ### Coupling invariant and per-step residue lemmas

The coupling between the multiple- and single-session ideal worlds and the bad-event world is
threaded by `MSBInv`, a *reader-stable* relation on the three handler states. It records that the
session counters agree across the three worlds (reader queries never touch counters) and that the
bad flag has not yet fired (once it fires, the `Pr[bad]` term already dominates). The cache
relation needed for the per-query coupling is supplied to the per-step residue lemmas as part of
`MSBInv`; those two lemmas — one for tag queries, one for reader queries — are the genuine
probabilistic core and are isolated below. -/

/-- Reader-stable coupling invariant relating a multiple-session ideal state, a single-session
ideal state and a bad-event state: the three session counters agree and the bad flag is unset.
Session counters are untouched by reader queries, so this part of the relation is reader-stable;
the cache-level coupling required for the per-query bounds is re-established inside the residue
lemmas. -/
private def MSBInv
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sS : UnlinkState TagId × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) : Prop :=
  sM.1.sessionsUsed = sS.1.sessionsUsed ∧
    sM.1.sessionsUsed = sB.sessionsUsed ∧ sB.bad = false

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The initial states of the three worlds satisfy the coupling invariant. -/
private lemma MSBInv_init :
    MSBInv (TagId := TagId) (Nonce := Nonce) (Digest := Digest) (sessionsPerTag := sessionsPerTag)
      (UnlinkState.init, ∅) (UnlinkState.init, ∅) UnlinkBadState.init :=
  ⟨rfl, rfl, rfl⟩

/-! ### Composed-handler eager-table equivalence

The composed ideal handler `multipleIdealQueryImpl` embeds the lazy random oracle inside a
stateful handler over `UnlinkOracleSpec`. The lemma below lifts the top-level lazy-vs-eager-table
equivalence (`OracleComp.evalDist_simulateQ_randomOracle_run'_eq_tableExtending`) to this composed
handler: running `multipleIdealQueryImpl` from `(s, c)` has the same output distribution as
sampling a full random-oracle table `g`, overlaying the cache `c`, and running the *real*
multiple-session handler `multipleTableHandler` deterministically against that table.

This is the multiple-world half of the recommended eager-sampling reformulation; it does not touch
the coupled-table union bound or the two residue `sorry`s. -/

section EagerComposed

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- Deterministic real multiple-session handler keyed directly on a random-oracle table
`g : TagId × Nonce → Digest`. This is `unlinkMultipleQueryImpl prfs k` for any PRF package whose
`evalMultiple k` is the curried table; phrasing it on the raw table lets the eager-table
equivalence be stated without a `prfs`/`k` witness. -/
noncomputable def multipleTableHandler (g : TagId × Nonce → Digest) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId) ProbComp) :=
  unlinkTagQueryImpl (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
    (fun tag nonce => g (tag, nonce))
    (multiplePattern (TagId := TagId) sessionsPerTag) +
  unlinkReaderQueryImpl (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
    (fun tag nonce => g (tag, nonce))
    (multiplePattern (TagId := TagId) sessionsPerTag)

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ multipleIdealQueryImpl` of a `query_bind`, run from a state and projected to its
output bit: the per-query handler followed by the recursive simulation of the continuation.
General-codomain version of `multipleIdeal_run'_query_bind`. -/
private lemma multipleIdeal_run'_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' sM =
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sM) >>= fun p =>
        (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `simulateQ multipleTableHandler` of a `query_bind`, run from a state and projected to its
output: the per-query handler followed by the recursive simulation of the continuation. -/
private lemma multipleTable_run'_query_bind' {α : Type} (g : TagId × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : UnlinkState TagId) :
    (simulateQ (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g) (liftM (OracleSpec.query t) >>= f)).run' s =
      (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g t s) >>= fun p =>
        (simulateQ (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `multipleTableHandler` on a tag query with the slot budget exhausted: returns `none`. -/
private lemma multipleTableHandler_tag_run_of_not_lt (g : TagId × Nonce → Digest)
    (tag : TagId) (s : UnlinkState TagId)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) s) = pure (none, s) := by
  unfold multipleTableHandler
  rw [QueryImpl.add_apply_inl]
  change (unlinkTagQueryImpl (fun tag nonce => g (tag, nonce))
    (multiplePattern (TagId := TagId) sessionsPerTag) tag).run s = _
  unfold unlinkTagQueryImpl
  simp [StateT.run_bind, StateT.run_get, hslot]

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `multipleTableHandler` on a tag query with a free slot: sample a nonce, look up the table at
`(tag, nonce)`, advance the session counter. -/
private lemma multipleTableHandler_tag_run_of_lt (g : TagId × Nonce → Digest)
    (tag : TagId) (s : UnlinkState TagId)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) s) =
      ($ᵗ Nonce) >>= fun nonce =>
        pure (some (⟨nonce, g (tag, nonce)⟩ : TagTranscript Nonce Digest),
          { s with sessionsUsed :=
            Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }) := by
  unfold multipleTableHandler
  rw [QueryImpl.add_apply_inl]
  change (unlinkTagQueryImpl (fun tag nonce => g (tag, nonce))
    (multiplePattern (TagId := TagId) sessionsPerTag) tag).run s = _
  unfold unlinkTagQueryImpl
  simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set,
    hslot, multiplePattern, bind_pure_comp]

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `multipleTableHandler` on a reader query: deterministic acceptance against the table, with the
state untouched. -/
private lemma multipleTableHandler_reader_run (g : TagId × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript) s) =
      pure (ReaderReply.ofBool (unlinkReaderAccepts (TagId := TagId) (Slot := TagId)
        (Nonce := Nonce) (Digest := Digest) (fun tag nonce => g (tag, nonce))
        (multiplePattern (TagId := TagId) sessionsPerTag) transcript), s) := by
  unfold multipleTableHandler
  rw [QueryImpl.add_apply_inr]
  change (unlinkReaderQueryImpl (fun tag nonce => g (tag, nonce))
    (multiplePattern (TagId := TagId) sessionsPerTag) transcript).run s = _
  unfold unlinkReaderQueryImpl
  rfl

omit [DecidableEq Digest] in
/-- **Cache-branch eager-table step.** A single lazy-random-oracle lookup `idealCacheStep` at a
domain point `d`, followed by sampling a full random-oracle table for the remaining computation,
has the same output distribution as directly sampling the table: the fresh on-demand draw of a
cache miss is absorbed by `OracleComp.evalDist_uniformSample_bind_update_map`.

This is the per-query workhorse for an eager-sampling reformulation of the composed ideal handler:
it reconciles the lazy cache step with the up-front table draw, generalized over an arbitrary
continuation `ψ` of the resulting full table. -/
private lemma evalDist_idealCacheStep_bind_uniformTable {D : Type} [DecidableEq D] [Finite D]
    [Finite Digest] [SampleableType (D → Digest)]
    {β : Type} (c : (D →ₒ Digest).QueryCache) (d : D) (ψ : (D → Digest) → β) :
    𝒟[do let r ← idealCacheStep (Digest := Digest) c d;
          let g ← $ᵗ (D → Digest);
          pure (ψ (OracleComp.tableExtending r.2 g))] =
      𝒟[do let g ← $ᵗ (D → Digest); pure (ψ (OracleComp.tableExtending c g))] := by
  classical
  haveI : Nonempty Digest := ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  unfold idealCacheStep
  rcases hc : c d with _ | u
  · dsimp only
    rw [show (($ᵗ Digest) >>= fun u => pure (u, c.cacheQuery d u)) >>=
              (fun r => ($ᵗ (D → Digest)) >>= fun g =>
                pure (ψ (OracleComp.tableExtending r.2 g)))
          = ($ᵗ Digest) >>= fun u => ($ᵗ (D → Digest)) >>= fun g =>
              pure ((fun g' => ψ (OracleComp.tableExtending c g')) (Function.update g d u))
        from by
          rw [bind_assoc]
          refine bind_congr fun u => ?_
          rw [pure_bind]
          refine bind_congr fun g => ?_
          rw [OracleComp.tableExtending_cacheQuery,
            OracleComp.tableExtending_update_of_none c g hc u]]
    exact OracleComp.evalDist_uniformSample_bind_update_map (R := Digest) d
      (fun g' => ψ (OracleComp.tableExtending c g'))
  · dsimp only
    rw [pure_bind]

/-! #### Milestone 1: the reader table-iteration lemma

`idealCacheMapM` folds the lazy random-oracle lookup `idealCacheStep` over a list of cache cells —
this is exactly the reader query's behaviour under the composed ideal handler. The lemmas below lift
the single-cell eager-table absorption (`evalDist_idealCacheStep_bind_uniformTable`) to a whole
list, by induction on the cell list. The end result: folding `idealCacheStep` over a list `l` and
then sampling one full table is distributionally the same as sampling the full table up front and
reading the cells deterministically against `tableExtending`. -/

omit [DecidableEq Digest] in
/-- After one `idealCacheStep` at `d`, the resulting cache stores the produced digest at `d`. -/
private lemma idealCacheStep_cache_self {D : Type} [DecidableEq D]
    (c : (D →ₒ Digest).QueryCache) (d : D)
    (r : Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheStep (Digest := Digest) c d)) :
    r.2 d = some r.1 := by
  classical
  unfold idealCacheStep at hr
  rcases hc : c d with _ | u
  · rw [hc] at hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨u, _, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp [QueryCache.cacheQuery]
  · rw [hc] at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact hc

omit [DecidableEq Digest] in
/-- After one `idealCacheStep` at `d`, the resulting cache's domain includes `d`. -/
private lemma idealCacheStep_cache_self_dom {D : Type} [DecidableEq D]
    (c : (D →ₒ Digest).QueryCache) (d : D)
    (r : Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheStep (Digest := Digest) c d)) :
    (r.2 d).isSome := by
  rw [idealCacheStep_cache_self c d r hr]
  rfl

omit [DecidableEq Digest] in
/-- One `idealCacheStep` at `d` leaves all other cells of the cache untouched. -/
private lemma idealCacheStep_cache_off {D : Type} [DecidableEq D]
    (c : (D →ₒ Digest).QueryCache) (d : D)
    (r : Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheStep (Digest := Digest) c d))
    (d' : D) (hd' : d' ≠ d) :
    r.2 d' = c d' := by
  classical
  unfold idealCacheStep at hr
  rcases hc : c d with _ | u
  · rw [hc] at hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨u, _, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp [QueryCache.cacheQuery_of_ne _ _ hd']
  · rw [hc] at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rfl

omit [DecidableEq Digest] in
/-- One `idealCacheStep` at `e` leaves any already-cached cell `d` unchanged. -/
private lemma idealCacheStep_preserves_some {D : Type} [DecidableEq D]
    (c : (D →ₒ Digest).QueryCache) (e : D)
    (r : Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheStep (Digest := Digest) c e))
    (d : D) (hd : (c d).isSome) :
    r.2 d = c d := by
  classical
  by_cases hde : d = e
  · subst hde
    unfold idealCacheStep at hr
    rcases hc : c d with _ | u
    · rw [hc] at hd; simp at hd
    · rw [hc] at hr
      rw [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact hc
  · exact idealCacheStep_cache_off c e r hr d hde

omit [DecidableEq Digest] in
/-- Folding `idealCacheStep` over `l` leaves any already-cached cell `d` unchanged. -/
private lemma idealCacheMapM_cache_off {D : Type} [DecidableEq D]
    (l : List D) (c : (D →ₒ Digest).QueryCache)
    (r : List Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheMapM (Digest := Digest) l c))
    (d : D) (hd : (c d).isSome) :
    r.2 d = c d := by
  induction l generalizing c r with
  | nil =>
    simp only [idealCacheMapM] at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rfl
  | cons e es ih =>
    simp only [idealCacheMapM] at hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨step, hstep, hr⟩ := hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨rest, hrest, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    have hstepd : (step.2 d).isSome := by
      rw [idealCacheStep_preserves_some c e step hstep d hd]
      exact hd
    have hihrest := ih step.2 rest hrest hstepd
    rw [hihrest, idealCacheStep_preserves_some c e step hstep d hd]

omit [DecidableEq Digest] in
/-- Every result of folding `idealCacheStep` over a list `l` from cache `c` has a final cache that
caches all cells of `l` and agrees with `c` off the cells of `l`. Consequently, overlaying that
final cache on any full table reads each cell of `l` as the stored digest, so the produced read
list is `l.map (tableExtending r.2 g)`. -/
private lemma idealCacheMapM_support {D : Type} [DecidableEq D]
    (l : List D) (c : (D →ₒ Digest).QueryCache)
    (r : List Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheMapM (Digest := Digest) l c))
    (g : D → Digest) :
    r.1 = l.map (OracleComp.tableExtending r.2 g) := by
  induction l generalizing c r with
  | nil =>
    simp only [idealCacheMapM] at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rfl
  | cons d ds ih =>
    simp only [idealCacheMapM] at hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨step, hstep, hr⟩ := hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨rest, hrest, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    have hihrest := ih step.2 rest hrest
    have hstepd : step.2 d = some step.1 :=
      idealCacheStep_cache_self (Digest := Digest) c d step hstep
    have hrestd : rest.2 d = some step.1 := by
      have hoff := idealCacheMapM_cache_off (Digest := Digest) ds step.2 rest hrest d
        (idealCacheStep_cache_self_dom (Digest := Digest) c d step hstep)
      rw [hoff, hstepd]
    simp only [List.map_cons]
    rw [hihrest]
    congr 1
    simp [OracleComp.tableExtending, hrestd]

omit [DecidableEq Digest] in
/-- **Reader table-iteration lemma (Milestone 1).** Folding the lazy random-oracle lookup
`idealCacheStep` over a list of cells `l`, then sampling one full random-oracle table for the
remaining computation, has the same output distribution as directly sampling the table: every
fresh on-demand draw of a cache miss is absorbed into the up-front table draw.

This lifts the single-cell absorption `evalDist_idealCacheStep_bind_uniformTable` to a whole list
by induction on `l`, and is the reader-query workhorse of the eager-sampling reformulation. -/
private lemma evalDist_idealCacheMapM_bind_uniformTable {D : Type} [DecidableEq D] [Finite D]
    [Finite Digest] [SampleableType (D → Digest)]
    {β : Type} (l : List D) (c : (D →ₒ Digest).QueryCache) (ψ : (D → Digest) → β) :
    𝒟[do let r ← idealCacheMapM (Digest := Digest) l c;
          let g ← $ᵗ (D → Digest);
          pure (ψ (OracleComp.tableExtending r.2 g))] =
      𝒟[do let g ← $ᵗ (D → Digest); pure (ψ (OracleComp.tableExtending c g))] := by
  induction l generalizing c with
  | nil =>
    simp only [idealCacheMapM, pure_bind]
  | cons d ds ih =>
    simp only [idealCacheMapM]
    have hreassoc :
        (idealCacheStep (Digest := Digest) c d >>= fun r =>
            idealCacheMapM (Digest := Digest) ds r.2 >>= fun rs =>
              pure (r.1 :: rs.1, rs.2)) >>= (fun r =>
          ($ᵗ (D → Digest)) >>= fun g => pure (ψ (OracleComp.tableExtending r.2 g)))
        = idealCacheStep (Digest := Digest) c d >>= fun r =>
            idealCacheMapM (Digest := Digest) ds r.2 >>= fun rs =>
              ($ᵗ (D → Digest)) >>= fun g =>
                pure (ψ (OracleComp.tableExtending rs.2 g)) := by
      rw [bind_assoc]
      refine bind_congr fun r => ?_
      rw [bind_assoc]
      refine bind_congr fun rs => ?_
      rw [pure_bind]
    rw [hreassoc]
    refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable c d ψ)
    rw [evalDist_bind, evalDist_bind]
    refine congrArg (fun h => 𝒟[idealCacheStep (Digest := Digest) c d] >>= h) ?_
    exact funext fun r => ih r.2

/-- Two probabilistic samples may be drawn in either order: the output distribution of drawing
`mx` then `my` and combining is the same as drawing `my` then `mx`. Proven at the distribution
level by `tsum` rearrangement; the underlying monads need not be commutative as terms. -/
private lemma evalDist_probComp_bind_comm {α₁ α₂ β : Type}
    (mx : ProbComp α₁) (my : ProbComp α₂) (F : α₁ → α₂ → ProbComp β) :
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
  refine tsum_congr fun b => ?_
  refine tsum_congr fun a => ?_
  ring

omit [DecidableEq Digest] in
/-- Computation-valued form of `evalDist_idealCacheStep_bind_uniformTable`: the continuation `Mψ`
returns a probabilistic computation rather than a pure value. -/
private lemma evalDist_idealCacheStep_bind_uniformTable_comp {D : Type} [DecidableEq D] [Finite D]
    [Finite Digest] [SampleableType (D → Digest)]
    {β : Type} (c : (D →ₒ Digest).QueryCache) (d : D) (Mψ : (D → Digest) → ProbComp β) :
    𝒟[do let r ← idealCacheStep (Digest := Digest) c d;
          let g ← $ᵗ (D → Digest);
          Mψ (OracleComp.tableExtending r.2 g)] =
      𝒟[do let g ← $ᵗ (D → Digest); Mψ (OracleComp.tableExtending c g)] := by
  have hbase := evalDist_idealCacheStep_bind_uniformTable c d Mψ
  have hL : (idealCacheStep (Digest := Digest) c d >>= fun r =>
              ($ᵗ (D → Digest)) >>= fun g => Mψ (OracleComp.tableExtending r.2 g))
      = (idealCacheStep (Digest := Digest) c d >>= fun r =>
            ($ᵗ (D → Digest)) >>= fun g =>
            pure (Mψ (OracleComp.tableExtending r.2 g))) >>= id := by
    rw [bind_assoc]; refine bind_congr fun r => ?_
    rw [bind_assoc]; refine bind_congr fun g => ?_
    rw [pure_bind, id]
  have hR : (($ᵗ (D → Digest)) >>= fun g => Mψ (OracleComp.tableExtending c g))
      = (($ᵗ (D → Digest)) >>= fun g =>
            pure (Mψ (OracleComp.tableExtending c g))) >>= id := by
    rw [bind_assoc]; refine bind_congr fun g => ?_
    rw [pure_bind, id]
  rw [hL, hR]
  rw [evalDist_bind (mx := idealCacheStep (Digest := Digest) c d >>= fun r =>
        ($ᵗ (D → Digest)) >>= fun g => pure (Mψ (OracleComp.tableExtending r.2 g)))]
  rw [evalDist_bind (mx := ($ᵗ (D → Digest)) >>= fun g =>
        pure (Mψ (OracleComp.tableExtending c g)))]
  exact congrArg (fun h => h >>= fun c' => 𝒟[id c']) hbase

omit [DecidableEq Digest] in
/-- Computation-valued form of `evalDist_idealCacheMapM_bind_uniformTable`. -/
private lemma evalDist_idealCacheMapM_bind_uniformTable_comp {D : Type} [DecidableEq D] [Finite D]
    [Finite Digest] [SampleableType (D → Digest)]
    {β : Type} (l : List D) (c : (D →ₒ Digest).QueryCache) (Mψ : (D → Digest) → ProbComp β) :
    𝒟[do let r ← idealCacheMapM (Digest := Digest) l c;
          let g ← $ᵗ (D → Digest);
          Mψ (OracleComp.tableExtending r.2 g)] =
      𝒟[do let g ← $ᵗ (D → Digest); Mψ (OracleComp.tableExtending c g)] := by
  have hbase := evalDist_idealCacheMapM_bind_uniformTable l c Mψ
  have hL : (idealCacheMapM (Digest := Digest) l c >>= fun r =>
              ($ᵗ (D → Digest)) >>= fun g => Mψ (OracleComp.tableExtending r.2 g))
      = (idealCacheMapM (Digest := Digest) l c >>= fun r =>
            ($ᵗ (D → Digest)) >>= fun g =>
            pure (Mψ (OracleComp.tableExtending r.2 g))) >>= id := by
    rw [bind_assoc]; refine bind_congr fun r => ?_
    rw [bind_assoc]; refine bind_congr fun g => ?_
    rw [pure_bind, id]
  have hR : (($ᵗ (D → Digest)) >>= fun g => Mψ (OracleComp.tableExtending c g))
      = (($ᵗ (D → Digest)) >>= fun g =>
            pure (Mψ (OracleComp.tableExtending c g))) >>= id := by
    rw [bind_assoc]; refine bind_congr fun g => ?_
    rw [pure_bind, id]
  rw [hL, hR]
  rw [evalDist_bind (mx := idealCacheMapM (Digest := Digest) l c >>= fun r =>
        ($ᵗ (D → Digest)) >>= fun g => pure (Mψ (OracleComp.tableExtending r.2 g)))]
  rw [evalDist_bind (mx := ($ᵗ (D → Digest)) >>= fun g =>
        pure (Mψ (OracleComp.tableExtending c g)))]
  exact congrArg (fun h => h >>= fun c' => 𝒟[id c']) hbase

/-- Distribution-level bind congruence: if two continuations agree (in distribution) on every
output in the support of the head computation, the full binds have equal distributions. -/
private lemma evalDist_bind_congr_of_support {α β : Type}
    (mx : ProbComp α) (my my' : α → ProbComp β)
    (h : ∀ a ∈ support mx, 𝒟[my a] = 𝒟[my' a]) :
    𝒟[mx >>= my] = 𝒟[mx >>= my'] := by
  refine evalDist_ext fun y => ?_
  refine probOutput_bind_congr fun a ha => ?_
  rw [probOutput_def, probOutput_def, h a ha]

/-! #### Milestone 2: composed multiple-world eager-table equivalence

The composed ideal handler `multipleIdealQueryImpl` embeds the lazy random oracle. The lemma below
lifts the eager-table equivalence to the composed handler: running `multipleIdealQueryImpl` from
`(s, c)` has the same output distribution as sampling a full random-oracle table `g`, overlaying
`c`, and running the deterministic real handler `multipleTableHandler (tableExtending c g)`.

The proof is `OracleComp.inductionOn` on the adversary, generalized over the state. The tag-query
case is discharged by the single-cell absorption `evalDist_idealCacheStep_bind_uniformTable`; the
reader-query case by the list absorption `evalDist_idealCacheMapM_bind_uniformTable`. -/

omit [Nonempty TagId] in
/-- **Step A, multiple world (Milestone 2).** Running the composed multiple-session ideal handler
from state `(s, c)` has the same output distribution as sampling a full random-oracle table `g`,
overlaying the cache `c`, and running the deterministic real multiple-session table handler. -/
private lemma evalDist_simulateQ_multipleIdealQueryImpl_run'_eq_tableExtending
    [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId) (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    𝒟[(simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) oa).run' (s, c)] =
      𝒟[do let g ← $ᵗ (TagId × Nonce → Digest);
            (simulateQ (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)) oa).run' s] := by
  induction oa using OracleComp.inductionOn generalizing s c with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    refine (evalDist_ext fun x => ?_).symm
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  | query_bind t f ih =>
    rw [multipleIdeal_run'_query_bind']
    have hrhs : 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
          (simulateQ (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g))
            (liftM (OracleSpec.query t) >>= f)).run' s]
        = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
            (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g) t s) >>= fun p =>
              (simulateQ (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g))
                (f p.1)).run' p.2] := by
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [multipleTable_run'_query_bind']
    rw [hrhs]
    cases t with
    | inl tag =>
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · -- tag query, slot available
        rw [multipleIdealQueryImpl_tag_run_of_lt tag s c hslot]
        set adv := ({ s with sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } : UnlinkState TagId) with hadv
        have hlhs_reassoc :
            ((($ᵗ Nonce) >>= fun nonce => idealCacheStep c (tag, nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest), adv, r.2)) >>= fun p =>
              (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
            = (($ᵗ Nonce) >>= fun nonce => idealCacheStep c (tag, nonce) >>= fun r =>
                (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv, r.2)) := by
          rw [bind_assoc]
          refine bind_congr fun nonce => ?_
          rw [bind_assoc]
          refine bind_congr fun r => ?_
          rw [pure_bind]
        refine (congrArg evalDist hlhs_reassoc).trans ?_
        -- per-nonce eager equivalence under the inner idealCacheStep
        have hlhs_inner : ∀ (n : Nonce),
            𝒟[idealCacheStep c (tag, n) >>= fun r =>
              (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv, r.2)]
            = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
                  (simulateQ (multipleTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c g))
                    (f (some (⟨n, OracleComp.tableExtending c g (tag, n)⟩ :
                      TagTranscript Nonce Digest)))).run' adv] := by
          intro n
          set Mψ : (TagId × Nonce → Digest) → ProbComp Bool := fun g' =>
            (simulateQ (multipleTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) g')
              (f (some (⟨n, g' (tag, n)⟩ : TagTranscript Nonce Digest)))).run' adv with hMψ
          refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable_comp c (tag, n) Mψ)
          refine evalDist_bind_congr_of_support _ _ _ fun r hr => ?_
          rw [ih (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)) adv r.2]
          refine congrArg _ (congrArg _ (funext fun g => ?_))
          have hcell : OracleComp.tableExtending r.2 g (tag, n) = r.1 := by
            simp only [OracleComp.tableExtending,
              idealCacheStep_cache_self c (tag, n) r hr, Option.getD_some]
          rw [hMψ]
          simp only [hcell]
        simp only [multipleTableHandler_tag_run_of_lt _ tag s hslot]
        -- LHS: $ᵗ Nonce >>= fun n => (...)
        -- RHS: $ᵗ g >>= fun g => $ᵗ Nonce >>= fun n => (...) — swap the two samples
        have hrhs_swap :
            (($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
              (($ᵗ Nonce) >>= fun nonce =>
                pure (some (⟨nonce, OracleComp.tableExtending c g (tag, nonce)⟩ :
                  TagTranscript Nonce Digest), adv)) >>= fun p =>
                (simulateQ (multipleTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g)) (f p.1)).run' p.2)
            = (($ᵗ (TagId × Nonce → Digest)) >>= fun g => ($ᵗ Nonce) >>= fun n =>
                (simulateQ (multipleTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g))
                  (f (some (⟨n, OracleComp.tableExtending c g (tag, n)⟩ :
                    TagTranscript Nonce Digest)))).run' adv) := by
          refine bind_congr fun g => ?_
          rw [bind_assoc]
          refine bind_congr fun n => ?_
          rw [pure_bind]
        refine Eq.trans ?_ (congrArg evalDist hrhs_swap).symm
        rw [evalDist_probComp_bind_comm ($ᵗ (TagId × Nonce → Digest)) ($ᵗ Nonce)]
        refine evalDist_bind_congr_of_support _ _ _ fun n _ => ?_
        exact hlhs_inner n
      · -- tag query, slot exhausted
        rw [multipleIdealQueryImpl_tag_run_of_not_lt tag s c hslot]
        show 𝒟[(simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f none)).run' (s, c)] = _
        rw [ih none s c]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [multipleTableHandler_tag_run_of_not_lt _ tag s hslot]
        rfl
    | inr transcript =>
      rw [multipleIdealQueryImpl_reader_run transcript s c]
      set cells := (Finset.univ : Finset TagId).toList.map
        (fun tag => (tag, transcript.nonce)) with hcells
      -- collapse the LHS bind to a single idealCacheMapM bind
      have hlhs_reassoc :
          ((idealCacheMapM cells c >>= fun rs =>
              pure (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s, rs.2))
            >>= fun p => (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
          = (idealCacheMapM cells c >>= fun rs =>
              (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run'
                (s, rs.2)) := by
        rw [bind_assoc]
        refine bind_congr fun rs => ?_
        rw [pure_bind]
      refine (congrArg evalDist hlhs_reassoc).trans ?_
      -- eager equivalence under idealCacheMapM
      set Mψ : (TagId × Nonce → Digest) → ProbComp Bool := fun g' =>
        (simulateQ (multipleTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g')
          (f (ReaderReply.ofBool (decide (∃ d ∈ cells.map g', d = transcript.auth))))).run' s
        with hMψ
      have hstep1 :
          𝒟[idealCacheMapM cells c >>= fun rs =>
              (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run'
                (s, rs.2)]
          = 𝒟[idealCacheMapM cells c >>= fun rs =>
              ($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
                Mψ (OracleComp.tableExtending rs.2 g)] := by
        refine evalDist_bind_congr_of_support _ _ _ fun rs hrs => ?_
        rw [ih (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))) s rs.2]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [hMψ]
        simp only [idealCacheMapM_support cells c rs hrs g]
      rw [hstep1, evalDist_idealCacheMapM_bind_uniformTable_comp cells c Mψ]
      -- RHS: collapse the table-handler reader query
      refine (evalDist_bind_congr_of_support _ _ _ fun g _ => ?_).symm
      rw [multipleTableHandler_reader_run _ transcript s]
      show 𝒟[(simulateQ (multipleTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g))
          (f (ReaderReply.ofBool (unlinkReaderAccepts (TagId := TagId) (Slot := TagId)
            (Nonce := Nonce) (Digest := Digest)
            (fun tag nonce => OracleComp.tableExtending c g (tag, nonce))
            (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run' s] = _
      rw [hMψ]
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
      beta_reduce
      rw [hAccept]

end EagerComposed

/-! ### Open obligation: the multiple-vs-single cache coupling

The two `sorry`-carrying lemmas below — `multipleIdeal_tag_step_le_single_add_bad` and
`multipleIdeal_reader_step_le_single_add_slack` — are the sole open content of the unlinkability
reduction. Everything else is proven: the telescoping
`unlinkabilityAdvantage_le_two_prf_plus_collision`, both PRF-real bridges, the ideal-world collapse
lemmas, the full per-query reduction toolkit, the induction skeleton
`multipleIdeal_le_singleIdeal_add_bad_aux`, and the `pure` base case. Each residue lemma is one
`OracleComp.inductionOn` step (tag query, resp. reader query) with the inductive hypothesis `ih`
available; closing both closes the whole reduction.

**Why this is hard — a state predicate is not enough.** `MSBInv` relates only the three handlers'
session counters, which is why it is preserved by every step. But the per-step *probability* bound
genuinely needs a coupling of the three caches — the multiple world's lazy random oracle over
`TagId × Nonce`, the single world's over `(TagId × Fin sessionsPerTag) × Nonce`, and the bad
world's list-valued `responses`. That coupling is probabilistic, not a state predicate: it must
say the *sampled digests* line up, which an `OracleComp.inductionOn` over a `Prop`-valued
invariant cannot express. An earlier attempt (`MBInv`, a "touched cells agree" predicate) was
removed precisely because no state predicate is both expressive enough and step-stable.

**The concrete obstruction.** A reader query writes **one** cache cell `(tag, n)` in the multiple
world but **`sessionsPerTag` independent** cells `((tag, sid), n)` in the single world. To couple
the two runs one must choose *which* of the single world's `sessionsPerTag` cells mirrors the
multiple world's single cell — but the tag-session index `sid` that a later tag query will read
is not known at the time of the reader query. A later tag session landing on a *non-mirrored*
single-world cell is the source of the unconditional acceptance gap, and it is exactly what the
`|TagId| * sessionsPerTag / |Digest|`-per-query reader-slack term pays for. The nonce-collision
case (two tag sessions of one tag drawing the same nonce: reused in the multiple world, fresh in
the single world) is what the `Pr[unlinkBadExp]` term pays for.

**Recommended route.** A stepwise lazy-cache coupling appears intractable. Reformulate both ideal
worlds by *eager sampling*: draw the entire random-oracle table up front (`fM : TagId × Nonce →
Digest`, `fS : (TagId × Fin sessionsPerTag) × Nonce → Digest`), prove each eager world equal in
distribution to its lazy form, then run both deterministically against a *coupled* pair of tables
(identify `fM (tag, n)` with `fS ((tag, sid₀), n)` for a fixed reference slot `sid₀`). With the
tables fixed, the two runs are deterministic and divergence becomes a decidable event on the
tables — bounded by a union bound: nonce collision (→ `Pr[unlinkBadExp]`) plus a later tag session
reading a non-reference single-world cell (→ the reader-slack term). The per-query reduction
lemmas already proven here (`multipleIdealQueryImpl_tag_run_of_lt` etc., `idealCacheStep`,
`idealCacheMapM`) are the right toolkit for the lazy-vs-eager equivalence step.

**Available infrastructure.** The eager route's first step — a *distribution-level*
lazy-random-oracle = eager-full-table equivalence — is now in place as reusable library lemmas:

* `evalDist_uniformSample_bind_update` in `VCVio/OracleComp/Constructions/SampleableType.lean` is
  the marginalization workhorse: drawing a fresh uniform `u` and then a full uniform table `g` and
  overwriting `g` at `t` with `u` is distributionally a directly drawn uniform table.
* `OracleComp.evalDist_simulateQ_randomOracle_run'_eq_tableExtending` in
  `VCVio/OracleComp/QueryTracking/RandomOracle/EagerTable.lean` is the cache-parametrized
  lazy-vs-eager equivalence: running an `OracleComp (D →ₒ R) α` under the lazy random oracle from
  cache `c` has the same `evalDist` as sampling a full table `g` and evaluating against
  `tableExtending c g`. `evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable` is the
  empty-cache corollary.

**Remaining gap (the composed-handler lift).** The library lemma is stated for a *top-level*
`simulateQ randomOracle oa` over a bare `OracleComp (D →ₒ R) α`. Here the random oracle is
embedded inside the composite handlers `multipleIdealQueryImpl` / `singleIdealQueryImpl`, whose
target is `StateT (UnlinkState × QueryCache) ProbComp` over `UnlinkOracleSpec`: `prfIdealQueryImpl`
interleaves `unifSpec` nonce draws (handled directly into `ProbComp`) with `(D →ₒ R)` queries
(the random oracle threading the cache). To use the eager route one must lift the library
equivalence to the composed-handler level — proving, by induction on the adversary generalized
over the cache, that the run of `multipleIdealQueryImpl` from `(s, c)` equals (in `evalDist`)
sampling a full table extending `c` and running a deterministic-table variant of the handler.

A clean realization of the deterministic-table variant: with the table fixed to `g`, the ideal
handler `multipleIdealQueryImpl` collapses to the *real* PRF handler — i.e. `unlinkMultipleQueryImpl`
with `evalMultiple k (tag, nonce) := tableExtending c g (tag, nonce)` — and likewise the single
world to `unlinkSingleQueryImpl`. The real-handler collapse is already proven
(`simulateQ_prfReal_unlinkToMultiplePRFQueryImpl_run` and its single-world twin).

Suggested order for a dedicated follow-up: (1) lift the eager-table equivalence to the composed
`{multiple,single}IdealQueryImpl` handlers, reusing `tableExtending_*` and the real-handler
collapse lemmas; (2) build the coupled-table union bound (identify `fM (tag, n)` with
`fS ((tag, sid₀), n)` for a reference slot, bound divergence by a union bound over nonce
collisions and non-reference reader cells). Estimated ~500 lines. Best tackled as a dedicated
effort. -/

/-- Per-step coupling residue, tag-query case: given the inductive hypothesis `ih` bounding the
continuation uniformly over invariant-related states and the residual budget, a single tag query
preserves the coupling bound. The slot-collision probability of the multiple world's lazy random
oracle (two sessions of one tag drawing the same nonce) is absorbed into the bad-event term; the
budget is unchanged because tag queries are not counted by `IsQueryBoundP … isRight`.

This is the nonce-collision half of the coupling and is the genuine probabilistic core. -/
private lemma multipleIdeal_tag_step_le_single_add_bad [Fintype Digest]
    (tag : TagId)
    (f : Option (TagTranscript Nonce Digest) → UnlinkAdversary TagId Nonce Digest)
    (qR : ℕ)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sS : UnlinkState TagId × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : MSBInv (sessionsPerTag := sessionsPerTag) sM sS sB)
    (ih : ∀ u,
      ∀ sM' sS' sB', MSBInv (sessionsPerTag := sessionsPerTag) sM' sS' sB' →
        OracleComp.IsQueryBoundP (f u) (fun i => i.isRight) qR →
        Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f u)).run' sM'] ≤
          Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f u)).run' sS'] +
          Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
            (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f u)).run sB'] +
          ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞))
    (hqR : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isRight) qR) :
    Pr[= true | (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag) sM) >>= fun p =>
        (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2] ≤
      Pr[= true | (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag) sS) >>= fun p =>
        (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (Sum.inl tag) sB) >>= fun p =>
        (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run p.2] +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  sorry

/-- Per-step coupling residue, reader-query case: given the inductive hypothesis `ih` bounding the
continuation uniformly over invariant-related states and the residual budget `qR`, a single reader
query preserves the coupling bound at budget `qR + 1`. The single-session reader inspects
`Fintype.card TagId * sessionsPerTag` random-oracle cells against the multiple world's
`Fintype.card TagId`, so the unconditional acceptance gap is `≤ |TagId| * sessionsPerTag / |Digest|`
per reader query; this is the slack paid by the `+ 1` budget increment.

This is the reader-slack half of the coupling and is the genuine probabilistic core. -/
private lemma multipleIdeal_reader_step_le_single_add_slack [Fintype Digest]
    (transcript : TagTranscript Nonce Digest)
    (f : ReaderReply → UnlinkAdversary TagId Nonce Digest)
    (qR : ℕ)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sS : UnlinkState TagId × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : MSBInv (sessionsPerTag := sessionsPerTag) sM sS sB)
    (ih : ∀ u,
      ∀ sM' sS' sB', MSBInv (sessionsPerTag := sessionsPerTag) sM' sS' sB' →
        OracleComp.IsQueryBoundP (f u) (fun i => i.isRight) qR →
        Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f u)).run' sM'] ≤
          Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f u)).run' sS'] +
          Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
            (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f u)).run sB'] +
          ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞))
    (hqR : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isRight) qR) :
    Pr[= true | (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript) sM) >>= fun p =>
        (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2] ≤
      Pr[= true | (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript) sS) >>= fun p =>
        (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (Sum.inr transcript) sB) >>= fun p =>
        (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run p.2] +
      (((qR + 1) * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  sorry

/-- Generalized coupling bound, proved by induction on the adversary. For any three states related
by `MSBInv` and any residual reader-query budget `qR` bounding the adversary's reader queries, the
multiple-session ideal success probability is bounded by the single-session one plus the bad-event
probability plus the reader-slack term `qR * |TagId| * sessionsPerTag / |Digest|`.

The `pure` base case is `multipleIdeal_le_singleIdeal_add_bad_pure`; the `query_bind` step splits
on tag vs. reader queries and delegates to `multipleIdeal_tag_step_le_single_add_bad` and
`multipleIdeal_reader_step_le_single_add_slack`, with the budget bookkeeping supplied by
`isQueryBoundP_query_bind_iff`. -/
private lemma multipleIdeal_le_singleIdeal_add_bad_aux [Fintype Digest]
    (adversary : UnlinkAdversary TagId Nonce Digest) (qR : ℕ)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sS : UnlinkState TagId × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : MSBInv (sessionsPerTag := sessionsPerTag) sM sS sB)
    (hqR : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) qR) :
    Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run' sM] ≤
      Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run' sS] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run sB] +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  induction adversary using OracleComp.inductionOn generalizing qR sM sS sB with
  | pure b =>
    exact le_add_right (multipleIdeal_le_singleIdeal_add_bad_pure b sM sS sB)
  | query_bind t f ih =>
    rw [multipleIdeal_run'_query_bind, singleIdeal_run'_query_bind, unlinkBad_run_query_bind]
    rw [isQueryBoundP_query_bind_iff] at hqR
    obtain ⟨hvalid, hbudget⟩ := hqR
    cases t with
    | inl tag =>
      have hf : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isRight) qR := by
        intro u
        simpa using hbudget u
      refine multipleIdeal_tag_step_le_single_add_bad tag f qR sM sS sB hInv ?_ hf
      intro u sM' sS' sB' hInv' hqR'
      exact ih u qR sM' sS' sB' hInv' hqR'
    | inr transcript =>
      obtain ⟨qR', rfl⟩ : ∃ qR', qR = qR' + 1 := by
        rcases hvalid with hvalid | hvalid
        · exact absurd rfl hvalid
        · exact ⟨qR - 1, by omega⟩
      have hf : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isRight) qR' := by
        intro u
        simpa using hbudget u
      refine multipleIdeal_reader_step_le_single_add_slack transcript f qR' sM sS sB hInv ?_ hf
      intro u sM' sS' sB' hInv' hqR'
      exact ih u qR' sM' sS' sB' hInv' hqR'

/-- Core coupling bound for the unlinkability reduction: the multiple-session ideal world's
success probability is bounded by that of the single-session ideal world plus the nonce-collision
probability `Pr[bad]` plus a reader-slack term.

The multiple- and single-session ideal handlers are *not* identical-until-bad: they are lazy
random oracles over different domains — `TagId × Nonce` for the multiple world,
`(TagId × Fin sessionsPerTag) × Nonce` for the single world — and their reader oracles diverge on
the *first* reader query, unconditionally. The single-session reader queries the random oracle at
`((tag, sid), nonce)` for *every* slot, i.e. `Fintype.card TagId * sessionsPerTag` cells, whereas
the multiple-session reader queries only `Fintype.card TagId` cells `(tag, nonce)`. That slot-count
asymmetry is a divergence unrelated to nonce collisions, so the bound carries two additive terms:
the nonce-collision probability `Pr[bad]` (the multiple world collapses two sessions of one tag
that drew the same nonce onto a single cache cell; the single world keeps them on distinct slots),
and the reader-slack term `qReader * Fintype.card TagId * sessionsPerTag / Fintype.card Digest`
absorbing the extra reader cells, where `qReader` bounds the number of reader queries. -/
private lemma multipleIdeal_le_singleIdeal_add_bad [Fintype Digest]
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) qReader) :
    Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] ≤
      Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          UnlinkBadState.init] +
      ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  exact multipleIdeal_le_singleIdeal_add_bad_aux adversary qReader
    (UnlinkState.init, ∅) (UnlinkState.init, ∅) UnlinkBadState.init
    (MSBInv_init) hqReader

/-- `unlinkBadExp` outputs `true` exactly with the probability that the bad flag fires. -/
private lemma probOutput_unlinkBadExp_eq
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | unlinkBadExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          UnlinkBadState.init] := by
  rw [← probEvent_eq_eq_probOutput, unlinkBadExp, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine tsum_congr fun z => ?_
  by_cases hz : z.2.bad <;> simp [hz]

/-- Coupling bound for the two random-function worlds (the ideal-PRF experiments of the multiple-
and single-session reductions): the gap is bounded by the nonce-collision probability `unlinkBadExp`
plus a reader-slack term. The two worlds are not identical-until-bad — their reader oracles diverge
unconditionally because the single-session reader checks `Fintype.card TagId * sessionsPerTag`
random-oracle cells against the multiple world's `Fintype.card TagId` — so the bound also carries
`qReader * Fintype.card TagId * sessionsPerTag / Fintype.card Digest`. -/
theorem unlinkPRFIdeal_gap_le_unlinkBad [Fintype Digest]
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) qReader) :
    (Pr[= true | PRFScheme.prfIdealExp (unlinkToMultiplePRFReduction
          (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) adversary)]).toReal -
        (Pr[= true | PRFScheme.prfIdealExp (unlinkToSinglePRFReduction
          (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) adversary)]).toReal ≤
      (Pr[= true | unlinkBadExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary]).toReal +
      ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
        (Fintype.card Digest : ℝ) := by
  have hcore := multipleIdeal_le_singleIdeal_add_bad (sessionsPerTag := sessionsPerTag)
    adversary qReader hqReader
  rw [prfIdealExp_unlinkToMultiplePRFReduction_eq_run' adversary,
    prfIdealExp_unlinkToSinglePRFReduction_eq_run' adversary,
    probOutput_unlinkBadExp_eq adversary]
  set M := Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
    (UnlinkState.init, ∅)] with hM
  set S := Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
    (UnlinkState.init, ∅)] with hS
  set B := Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
    (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
      UnlinkBadState.init] with hB
  set slackE := ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
    (Fintype.card Digest : ℝ≥0∞) with hslackE
  have hSt : S ≠ ⊤ := ne_top_of_le_ne_top one_ne_top probOutput_le_one
  have hBt : B ≠ ⊤ := ne_top_of_le_ne_top one_ne_top probEvent_le_one
  have hne : Nonempty Digest := ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  have hcardpos : 0 < Fintype.card Digest := Fintype.card_pos
  have hslackEt : slackE ≠ ⊤ := by
    rw [hslackE]
    refine ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hslackEeq : slackE.toReal =
      ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) / (Fintype.card Digest : ℝ) := by
    rw [hslackE, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have hMt : M.toReal ≤ S.toReal + B.toReal + slackE.toReal := by
    rw [← ENNReal.toReal_add hSt hBt, ← ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨hSt, hBt⟩) hslackEt]
    exact ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hSt, hBt⟩, hslackEt⟩) hcore
  rw [hslackEeq] at hMt
  linarith

/-! ## Main reduction theorem -/

/-- Unlinkability reduction: the multiple-vs-single advantage is bounded by one PRF advantage for
the multiple-session world, one PRF advantage for the single-session world, the bad-event
probability from the intermediate nonce-collision world, and a reader-slack term.

The proof telescopes the three bridge lemmas:
`Pr[Multiple] − Pr[Single]` splits as `(Pr[Multiple] − Pr[MultRF]) + (Pr[MultRF] − Pr[SingleRF])
+ (Pr[SingleRF] − Pr[Single])`, where the first and last differences are absorbed into the two
PRF advantages and the middle difference is bounded by `Pr[unlinkBadExp]` plus the reader-slack
term `qReader * Fintype.card TagId * sessionsPerTag / Fintype.card Digest`. The reader-slack term
is unavoidable: the single-session reader queries the random oracle at `sessionsPerTag` times more
cells than the multiple-session reader, an unconditional gap unrelated to nonce collisions. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_collision [Fintype Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) qReader) :
    ∃ multiAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      ∃ singleAdv : PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest,
        unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) prfs adversary ≤
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv +
            (Pr[= true | unlinkBadExp (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary]).toReal +
            ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
              (Fintype.card Digest : ℝ) := by
  refine ⟨unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary,
    unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary, ?_⟩
  have h1 := prfRealExp_unlinkToMultiplePRFReduction_eq_unlinkMultipleExp prfs adversary
  have h2 := prfRealExp_unlinkToSinglePRFReduction_eq_unlinkSingleExp prfs adversary
  have h3 := unlinkPRFIdeal_gap_le_unlinkBad (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary qReader hqReader
  unfold unlinkabilityAdvantage PRFScheme.prfAdvantage
  rw [h1, h2]
  set M := (Pr[= true | unlinkMultipleExp (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag) prfs adversary]).toReal
  set S := (Pr[= true | unlinkSingleExp (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag) prfs adversary]).toReal
  set MR := (Pr[= true | PRFScheme.prfIdealExp (unlinkToMultiplePRFReduction
    (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) adversary)]).toReal
  set SR := (Pr[= true | PRFScheme.prfIdealExp (unlinkToSinglePRFReduction
    (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) adversary)]).toReal
  have hA : M - MR ≤ |M - MR| := le_abs_self _
  have hB : SR - S ≤ |S - SR| := (le_abs_self (SR - S)).trans_eq (abs_sub_comm SR S)
  linarith [h3]

/-! ## Explicit session-collision bounds

Chaining the proven `unlinkBadExp_le_sessionCollisionBound` onto the reduction theorem gives the
explicit unlinkability bounds in terms of the nonce-collision parameters. -/

/-- Final unlinkability bound: two PRF advantages, the explicit session-collision term, and the
reader-slack term. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound [Fintype Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) qReader)
    (maxNonceProb : ℝ)
    (hmax : ∀ nonce : Nonce,
      (Pr[= nonce | ($ᵗ Nonce)]).toReal ≤ maxNonceProb) :
    ∃ multiAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      ∃ singleAdv : PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest,
        unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) prfs adversary ≤
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv +
            ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ) * maxNonceProb +
            ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
              (Fintype.card Digest : ℝ) := by
  obtain ⟨multiAdv, singleAdv, hSum⟩ :=
    unlinkabilityAdvantage_le_two_prf_plus_collision prfs adversary qReader hqReader
  refine ⟨multiAdv, singleAdv, hSum.trans ?_⟩
  have hBad := unlinkBadExp_le_sessionCollisionBound (sessionsPerTag := sessionsPerTag)
    adversary maxNonceProb hmax
  linarith

/-- Tightest unlinkability bound: when nonces are sampled uniformly (as enforced by
`SampleableType`), the session-collision term is exactly `sessionsPerTag² · |TagId| / |Nonce|`,
plus the reader-slack term. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_uniform_sessionCollisionBound
    [Fintype Nonce] [Fintype Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) qReader) :
    ∃ multiAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      ∃ singleAdv : PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest,
        unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) prfs adversary ≤
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv +
            (sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) /
              (Fintype.card Nonce : ℝ) +
            ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
              (Fintype.card Digest : ℝ) := by
  have hmax : ∀ nonce : Nonce,
      (Pr[= nonce | ($ᵗ Nonce)]).toReal ≤ (Fintype.card Nonce : ℝ)⁻¹ := fun nonce => by
    simp [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  obtain ⟨multiAdv, singleAdv, h⟩ :=
    unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound prfs adversary qReader hqReader
      ((Fintype.card Nonce : ℝ)⁻¹) hmax
  exact ⟨multiAdv, singleAdv, by rwa [div_eq_mul_inv]⟩

end UnlinkReduction

end PRFTagReader
