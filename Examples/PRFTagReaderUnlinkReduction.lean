/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.ProgramLogic.Relational.SimulateQ

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

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `unlinkBadQueryImpl` on a tag query with the slot budget exhausted: returns `none`, state
unchanged. -/
private lemma unlinkBadQueryImpl_tag_run_of_not_lt (tag : TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hslot : ¬ sB.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sB = pure (none, sB) := by
  unfold unlinkBadQueryImpl
  rw [QueryImpl.add_apply_inl]
  change (unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) tag).run sB = _
  unfold unlinkBadTagQueryImpl
  simp [StateT.run_bind, StateT.run_get, hslot]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `unlinkBadQueryImpl` on a tag query with a free slot: sample a nonce and a fresh digest,
record the digest under `(tag, nonce)`, set the `bad` flag if `(tag, nonce)` was already cached,
and advance the session counter. -/
private lemma unlinkBadQueryImpl_tag_run_of_lt (tag : TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hslot : sB.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sB =
      ($ᵗ Nonce) >>= fun nonce =>
        ($ᵗ Digest) >>= fun auth =>
          pure (some (⟨nonce, auth⟩ : TagTranscript Nonce Digest),
            ({ sessionsUsed :=
                Function.update sB.sessionsUsed tag (sB.sessionsUsed tag + 1)
               responses := sB.responses.cacheQuery (tag, nonce)
                 (auth :: Option.getD (sB.responses (tag, nonce)) [])
               bad := sB.bad || (sB.responses (tag, nonce)).isSome } :
              UnlinkBadState TagId Nonce Digest)) := by
  unfold unlinkBadQueryImpl
  rw [QueryImpl.add_apply_inl]
  change (unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) tag).run sB = _
  unfold unlinkBadTagQueryImpl
  simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set, hslot,
    bind_pure_comp]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `unlinkBadQueryImpl` on a reader query: deterministic acceptance against the recorded
random-function responses, state untouched. -/
private lemma unlinkBadQueryImpl_reader_run (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) sB =
      pure (ReaderReply.ofBool (decide (∃ tag ∈ (Finset.univ : Finset TagId),
        transcript.auth ∈ ((sB.responses (tag, transcript.nonce)).getD []))), sB) := by
  unfold unlinkBadQueryImpl
  rw [QueryImpl.add_apply_inr]
  change (unlinkBadReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    transcript).run sB = _
  unfold unlinkBadReaderQueryImpl
  simp [StateT.run_bind, StateT.run_get]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The `bad` flag of `unlinkBadQueryImpl` is monotone: a single per-query step started from a
state with `bad = true` keeps `bad = true`. -/
private lemma unlinkBadQueryImpl_step_preserves_bad
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (sB : UnlinkBadState TagId Nonce Digest) (hbad : sB.bad = true) :
    ∀ z ∈ support ((unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t) sB), z.2.bad = true := by
  cases t with
  | inl tag =>
    by_cases hslot : sB.sessionsUsed tag < sessionsPerTag
    · have key : ∀ z : Option (TagTranscript Nonce Digest) × UnlinkBadState TagId Nonce Digest,
          z ∈ support
            ((unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sB) → z.2.bad = true := by
        intro z hz
        rw [unlinkBadQueryImpl_tag_run_of_lt tag sB hslot] at hz
        obtain ⟨nonce, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
        obtain ⟨auth, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
        rw [mem_support_pure_iff] at hz
        subst hz; simp [hbad]
      exact key
    · intro z hz
      rw [unlinkBadQueryImpl_tag_run_of_not_lt tag sB hslot] at hz
      have hz' := (mem_support_pure_iff _ _).mp hz
      subst hz'; exact hbad
  | inr transcript =>
    intro z hz
    rw [unlinkBadQueryImpl_reader_run transcript sB] at hz
    have hz' := (mem_support_pure_iff _ _).mp hz
    subst hz'; exact hbad

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The `bad` flag of a full `simulateQ unlinkBadQueryImpl` run is monotone: started from a state
with `bad = true` the run keeps `bad = true`. -/
private lemma simulateQ_unlinkBad_preserves_bad
    (adv : UnlinkAdversary TagId Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) (hbad : sB.bad = true) :
    ∀ z ∈ support ((simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run sB), z.2.bad = true := by
  induction adv using OracleComp.inductionOn generalizing sB with
  | pure b =>
    intro z hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz; exact hbad
  | query_bind t f ih =>
    intro z hz
    rw [unlinkBad_run_query_bind] at hz
    obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    exact ih p.1 p.2 (unlinkBadQueryImpl_step_preserves_bad t sB hbad p hp) z hz

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Once the `bad` flag is set, the `Pr[bad]` of the residual `unlinkBadQueryImpl` run is `1`. -/
private lemma probEvent_unlinkBad_bad_eq_one_of_bad
    (adv : UnlinkAdversary TagId Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) (hbad : sB.bad = true) :
    Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run sB] = 1 := by
  rw [probEvent_eq_one_iff]
  exact ⟨by simp, fun z hz => simulateQ_unlinkBad_preserves_bad adv sB hbad z hz⟩

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

/-! ### Pairwise-distinct reader nonces

The reader-slack half of the coupling is sound only when the adversary's reader queries carry
pairwise-distinct nonces: a reader query at nonce `n` programs an entire column of the random
oracle, and the coupling between the multiple- and single-session worlds can charge that column
only once. `HasDistinctUnlinkReaderNonces` is the unlinkability analogue of
`PRFTagReader.HasDistinctReaderNonces` from the authentication collision proof: it bounds, for
every nonce `n`, the number of reader queries carrying `n` by `1`. -/

/-- Per-nonce reader-query predicate on the unlinkability oracle interface. `pReaderNonce n` holds
of a reader query exactly when its transcript carries the nonce `n`, and never holds of a tag
query. Bounding the number of `pReaderNonce n`-queries by `1` for every `n` expresses that the
adversary's reader queries use pairwise-distinct nonces. -/
def pReaderNonce (n : Nonce) : (UnlinkOracleSpec TagId Nonce Digest).Domain → Prop :=
  fun i => match i with
    | Sum.inr tr => tr.nonce = n
    | Sum.inl _ => False

instance pReaderNonceDecidable (n : Nonce) :
    DecidablePred (pReaderNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n) := by
  intro i
  cases i with
  | inr tr => exact (inferInstance : Decidable (tr.nonce = n))
  | inl _ => exact (inferInstance : Decidable False)

/-- The adversary's reader queries use pairwise-distinct nonces: every nonce `n` is carried by at
most one reader query. This is the public hypothesis under which the reader-slack half of the
unlinkability coupling is sound; it rules out the shared-column obstruction that an unrestricted
multiple-vs-single coupling would face. -/
def HasDistinctUnlinkReaderNonces (adversary : UnlinkAdversary TagId Nonce Digest) : Prop :=
  ∀ n : Nonce, OracleComp.IsQueryBoundP adversary (pReaderNonce n) 1

/-- `HasDistinctUnlinkReaderNonces` unfolds definitionally to a per-nonce reader-query bound: it
holds exactly when, for every nonce `n`, at most one reader query carries `n`. -/
lemma hasDistinctUnlinkReaderNonces_iff (adversary : UnlinkAdversary TagId Nonce Digest) :
    HasDistinctUnlinkReaderNonces adversary ↔
      ∀ n : Nonce, OracleComp.IsQueryBoundP adversary (pReaderNonce n) 1 :=
  Iff.rfl

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest]
  [NeZero sessionsPerTag] in
/-- Every `pReaderNonce n`-query is a reader query: `pReaderNonce n` is false on tag (`Sum.inl`)
queries and, on reader (`Sum.inr`) queries, refines `Sum.isRight`. -/
lemma pReaderNonce_imp_isRight (n : Nonce)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain) :
    pReaderNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n t → t.isRight := by
  cases t with
  | inl x => exact fun h => (h : (False : Prop)).elim
  | inr tr => exact fun _ => rfl

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest]
  [NeZero sessionsPerTag] in
/-- An adversary making at most one reader query has pairwise-distinct reader nonces: a single
reader query cannot collide with itself. Adversaries with no reader queries also qualify. -/
theorem hasDistinctUnlinkReaderNonces_of_readerBound
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) 1) :
    HasDistinctUnlinkReaderNonces adversary := fun n =>
  OracleComp.IsQueryBoundP.of_imp (pReaderNonce_imp_isRight n) hq

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

omit [DecidableEq Digest] in
/-- **Single-cell extraction at the bind level.** Drawing a uniform function table `g : D → R` and
then running an arbitrary continuation that depends on `g` and on the cell value `g t` is
distributionally equal to drawing the cell value `u : R` uniformly first, then drawing `g`, then
running the continuation against the `t`-update of `g` (whose `t`-cell is `u`).

This is the bind-level lift of `evalDist_uniformSample_bind_update_map`: instead of carrying a
`pure (ψ g)`-only continuation, the result is parametric over an arbitrary `ProbComp β`-valued
continuation, exposing the cell read `g t` outside the table draw. It is the reusable
cell-extraction step underlying the cell-patch coupling in the hop-A fresh tag-step branch. -/
private lemma evalDist_uniformSample_bind_cell_extract {D R : Type}
    [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)] (t : D) {β : Type}
    (cont : (D → R) → R → ProbComp β) :
    𝒟[do let g ← $ᵗ (D → R); cont g (g t)] =
      𝒟[do let u ← $ᵗ R; let g ← $ᵗ (D → R); cont (Function.update g t u) u] := by
  classical
  -- Factor both sides through a `pure (g, g t)` / `pure (Function.update g t u, u)` pair, then
  -- apply `evalDist_uniformSample_bind_update_map` on the inner pure layer.
  have hLeq :
      (do let g ← $ᵗ (D → R); cont g (g t))
        = ((do let g ← $ᵗ (D → R); pure (g, g t)) >>= fun p : (D → R) × R => cont p.1 p.2) := by
    simp [bind_assoc, pure_bind]
  have hReq :
      (do let u ← $ᵗ R; let g ← $ᵗ (D → R); cont (Function.update g t u) u)
        = ((do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (Function.update g t u, u))
            >>= fun p : (D → R) × R => cont p.1 p.2) := by
    simp [bind_assoc, pure_bind]
  rw [hLeq, hReq]
  have hpureEq : ∀ (g : D → R) (u : R),
      (Function.update g t u, u)
        = ((fun g' : D → R => (g', g' t)) (Function.update g t u)) := by
    intro g u
    show (Function.update g t u, u)
        = (Function.update g t u, (Function.update g t u) t)
    have hself : (Function.update g t u) t = u := Function.update_self (β := fun _ => R) t u g
    rw [hself]
  have hcore :
      𝒟[do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (Function.update g t u, u)]
        = 𝒟[do let g ← $ᵗ (D → R); pure (g, g t)] := by
    have hrw :
        (do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (Function.update g t u, u))
          = (do let u ← $ᵗ R; let g ← $ᵗ (D → R);
                pure ((fun g' : D → R => (g', g' t)) (Function.update g t u))) := by
      refine bind_congr fun u => bind_congr fun g => ?_
      rw [hpureEq g u]
    rw [hrw]
    exact OracleComp.evalDist_uniformSample_bind_update_map (R := R) t
      (fun g' => (g', g' t))
  -- Lift `hcore` through the outer continuation `fun p => cont p.1 p.2`.
  refine evalDist_ext fun y => ?_
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun p => ?_
  rw [show Pr[= p | (do let g ← $ᵗ (D → R); pure (g, g t))]
        = Pr[= p | (do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (Function.update g t u, u))]
      from probOutput_congr rfl hcore.symm]

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
/-- Folding `idealCacheStep` over `l` leaves any cell `d` outside `l` unchanged. -/
private lemma idealCacheMapM_cache_not_mem {D : Type} [DecidableEq D]
    (l : List D) (c : (D →ₒ Digest).QueryCache)
    (r : List Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheMapM (Digest := Digest) l c))
    (d : D) (hd : d ∉ l) :
    r.2 d = c d := by
  induction l generalizing c r with
  | nil =>
    simp only [idealCacheMapM] at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rfl
  | cons e es ih =>
    simp only [List.mem_cons, not_or] at hd
    obtain ⟨hde, hdes⟩ := hd
    simp only [idealCacheMapM] at hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨step, hstep, hr⟩ := hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨rest, hrest, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rw [ih step.2 rest hrest hdes, idealCacheStep_cache_off c e step hstep d hde]

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

/-! #### Milestone 3: composed single-world eager-table equivalence

The single-world analogues of the multiple-world `EagerComposed` helpers: a deterministic real
single-session table handler `singleTableHandler` keyed on a table over
`(TagId × Fin sessionsPerTag) × Nonce`, its `query_bind` / per-query reductions, and the composed
eager-table equivalence for `singleIdealQueryImpl`. -/

/-- Deterministic real single-session handler keyed directly on a random-oracle table
`g : (TagId × Fin sessionsPerTag) × Nonce → Digest`. -/
noncomputable def singleTableHandler (g : (TagId × Fin sessionsPerTag) × Nonce → Digest) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId) ProbComp) :=
  unlinkTagQueryImpl (TagId := TagId) (Slot := TagId × Fin sessionsPerTag) (Nonce := Nonce)
    (Digest := Digest) (fun slot nonce => g (slot, nonce))
    (singlePattern (TagId := TagId) sessionsPerTag) +
  unlinkReaderQueryImpl (TagId := TagId) (Slot := TagId × Fin sessionsPerTag) (Nonce := Nonce)
    (Digest := Digest) (fun slot nonce => g (slot, nonce))
    (singlePattern (TagId := TagId) sessionsPerTag)

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ singleIdealQueryImpl` of a `query_bind`, run from a state and projected to its
output: general-codomain version of `singleIdeal_run'_query_bind`. -/
private lemma singleIdeal_run'_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (sS : UnlinkState TagId × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' sS =
      (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sS) >>= fun p =>
        (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `simulateQ singleTableHandler` of a `query_bind`, run from a state and projected to its
output. -/
private lemma singleTable_run'_query_bind' {α : Type}
    (g : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : UnlinkState TagId) :
    (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g) (liftM (OracleSpec.query t) >>= f)).run' s =
      (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g t s) >>= fun p =>
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `singleTableHandler` on a tag query with the slot budget exhausted: returns `none`. -/
private lemma singleTableHandler_tag_run_of_not_lt
    (g : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (s : UnlinkState TagId)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) s) = pure (none, s) := by
  unfold singleTableHandler
  rw [QueryImpl.add_apply_inl]
  change (unlinkTagQueryImpl (fun slot nonce => g (slot, nonce))
    (singlePattern (TagId := TagId) sessionsPerTag) tag).run s = _
  unfold unlinkTagQueryImpl
  simp [StateT.run_bind, StateT.run_get, hslot]

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `singleTableHandler` on a tag query with a free slot: sample a nonce, look up the table at
`((tag, sid), nonce)`, advance the session counter. -/
private lemma singleTableHandler_tag_run_of_lt
    (g : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (s : UnlinkState TagId)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) s) =
      ($ᵗ Nonce) >>= fun nonce =>
        pure (some (⟨nonce, g ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce)⟩ :
            TagTranscript Nonce Digest),
          { s with sessionsUsed :=
            Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }) := by
  unfold singleTableHandler
  rw [QueryImpl.add_apply_inl]
  change (unlinkTagQueryImpl (fun slot nonce => g (slot, nonce))
    (singlePattern (TagId := TagId) sessionsPerTag) tag).run s = _
  unfold unlinkTagQueryImpl
  simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set,
    hslot, singlePattern, bind_pure_comp]

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `singleTableHandler` on a reader query: deterministic acceptance against the table. -/
private lemma singleTableHandler_reader_run
    (g : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript) s) =
      pure (ReaderReply.ofBool (unlinkReaderAccepts (TagId := TagId)
        (Slot := TagId × Fin sessionsPerTag) (Nonce := Nonce) (Digest := Digest)
        (fun slot nonce => g (slot, nonce))
        (singlePattern (TagId := TagId) sessionsPerTag) transcript), s) := by
  unfold singleTableHandler
  rw [QueryImpl.add_apply_inr]
  change (unlinkReaderQueryImpl (fun slot nonce => g (slot, nonce))
    (singlePattern (TagId := TagId) sessionsPerTag) transcript).run s = _
  unfold unlinkReaderQueryImpl
  rfl

omit [Nonempty TagId] in
/-- **Step A, single world (Milestone 3).** Running the composed single-session ideal handler
from state `(s, c)` has the same output distribution as sampling a full random-oracle table `g`,
overlaying the cache `c`, and running the deterministic real single-session table handler. -/
private lemma evalDist_simulateQ_singleIdealQueryImpl_run'_eq_tableExtending
    [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    𝒟[(simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) oa).run' (s, c)] =
      𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
            (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)) oa).run' s] := by
  induction oa using OracleComp.inductionOn generalizing s c with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    refine (evalDist_ext fun x => ?_).symm
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  | query_bind t f ih =>
    rw [singleIdeal_run'_query_bind']
    have hrhs : 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
          (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g))
            (liftM (OracleSpec.query t) >>= f)).run' s]
        = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
            (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g) t s) >>= fun p =>
              (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g))
                (f p.1)).run' p.2] := by
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [singleTable_run'_query_bind']
    rw [hrhs]
    cases t with
    | inl tag =>
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · rw [singleIdealQueryImpl_tag_run_of_lt tag s c hslot]
        set adv := ({ s with sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } : UnlinkState TagId) with hadv
        set sid := (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) with hsid
        have hlhs_reassoc :
            ((($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest), adv, r.2)) >>= fun p =>
              (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
            = (($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv, r.2)) := by
          rw [bind_assoc]
          refine bind_congr fun nonce => ?_
          rw [bind_assoc]
          refine bind_congr fun r => ?_
          rw [pure_bind]
        refine (congrArg evalDist hlhs_reassoc).trans ?_
        have hlhs_inner : ∀ (n : Nonce),
            𝒟[idealCacheStep c ((tag, sid), n) >>= fun r =>
              (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv, r.2)]
            = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                  (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c g))
                    (f (some (⟨n, OracleComp.tableExtending c g ((tag, sid), n)⟩ :
                      TagTranscript Nonce Digest)))).run' adv] := by
          intro n
          set Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun g' =>
            (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) g')
              (f (some (⟨n, g' ((tag, sid), n)⟩ : TagTranscript Nonce Digest)))).run' adv with hMψ
          refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable_comp c ((tag, sid), n) Mψ)
          refine evalDist_bind_congr_of_support _ _ _ fun r hr => ?_
          rw [ih (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)) adv r.2]
          refine congrArg _ (congrArg _ (funext fun g => ?_))
          have hcell : OracleComp.tableExtending r.2 g ((tag, sid), n) = r.1 := by
            simp only [OracleComp.tableExtending,
              idealCacheStep_cache_self c ((tag, sid), n) r hr, Option.getD_some]
          rw [hMψ]
          simp only [hcell]
        simp only [singleTableHandler_tag_run_of_lt _ tag s hslot]
        have hrhs_swap :
            (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
              (($ᵗ Nonce) >>= fun nonce =>
                pure (some (⟨nonce, OracleComp.tableExtending c g ((tag, sid), nonce)⟩ :
                  TagTranscript Nonce Digest), adv)) >>= fun p =>
                (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g)) (f p.1)).run' p.2)
            = (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                ($ᵗ Nonce) >>= fun n =>
                (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g))
                  (f (some (⟨n, OracleComp.tableExtending c g ((tag, sid), n)⟩ :
                    TagTranscript Nonce Digest)))).run' adv) := by
          refine bind_congr fun g => ?_
          rw [bind_assoc]
          refine bind_congr fun n => ?_
          rw [pure_bind]
        refine Eq.trans ?_ (congrArg evalDist hrhs_swap).symm
        rw [evalDist_probComp_bind_comm ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
          ($ᵗ Nonce)]
        refine evalDist_bind_congr_of_support _ _ _ fun n _ => ?_
        exact hlhs_inner n
      · rw [singleIdealQueryImpl_tag_run_of_not_lt tag s c hslot]
        show 𝒟[(simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f none)).run' (s, c)] = _
        rw [ih none s c]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [singleTableHandler_tag_run_of_not_lt _ tag s hslot]
        rfl
    | inr transcript =>
      rw [singleIdealQueryImpl_reader_run transcript s c]
      set cells := (Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
        (fun slot => (slot, transcript.nonce)) with hcells
      have hlhs_reassoc :
          ((idealCacheMapM cells c >>= fun rs =>
              pure (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s, rs.2))
            >>= fun p => (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
          = (idealCacheMapM cells c >>= fun rs =>
              (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run'
                (s, rs.2)) := by
        rw [bind_assoc]
        refine bind_congr fun rs => ?_
        rw [pure_bind]
      refine (congrArg evalDist hlhs_reassoc).trans ?_
      set Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun g' =>
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g')
          (f (ReaderReply.ofBool (decide (∃ d ∈ cells.map g', d = transcript.auth))))).run' s
        with hMψ
      have hstep1 :
          𝒟[idealCacheMapM cells c >>= fun rs =>
              (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run'
                (s, rs.2)]
          = 𝒟[idealCacheMapM cells c >>= fun rs =>
              ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                Mψ (OracleComp.tableExtending rs.2 g)] := by
        refine evalDist_bind_congr_of_support _ _ _ fun rs hrs => ?_
        rw [ih (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))) s rs.2]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [hMψ]
        simp only [idealCacheMapM_support cells c rs hrs g]
      rw [hstep1, evalDist_idealCacheMapM_bind_uniformTable_comp cells c Mψ]
      refine (evalDist_bind_congr_of_support _ _ _ fun g _ => ?_).symm
      rw [singleTableHandler_reader_run _ transcript s]
      show 𝒟[(simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g))
          (f (ReaderReply.ofBool (unlinkReaderAccepts (TagId := TagId)
            (Slot := TagId × Fin sessionsPerTag) (Nonce := Nonce) (Digest := Digest)
            (fun slot nonce => OracleComp.tableExtending c g (slot, nonce))
            (singlePattern (TagId := TagId) sessionsPerTag) transcript)))).run' s] = _
      rw [hMψ]
      have hAccept : decide (∃ d ∈ cells.map (OracleComp.tableExtending c g),
            d = transcript.auth)
          = unlinkReaderAccepts (TagId := TagId) (Slot := TagId × Fin sessionsPerTag)
            (Nonce := Nonce) (Digest := Digest)
            (fun slot nonce => OracleComp.tableExtending c g (slot, nonce))
            (singlePattern (TagId := TagId) sessionsPerTag) transcript := by
        unfold unlinkReaderAccepts tagAccepts
        rw [hcells]
        simp only [List.map_map, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
          singlePattern, decide_eq_decide, decide_eq_true_eq, Function.comp]
        constructor
        · rintro ⟨d, ⟨slot, rfl⟩, hd⟩
          exact ⟨slot.1, ⟨slot.2, hd⟩⟩
        · rintro ⟨tag, sid, hd⟩
          exact ⟨_, ⟨(tag, sid), rfl⟩, hd⟩
      beta_reduce
      rw [hAccept]

/-! #### Milestone 4 prep: eager-form success probabilities

With both ideal worlds shown equal in distribution to deterministic table-handler runs
(Milestones 2 and 3), the two ideal-world success probabilities are exposed as
table-sampled deterministic runs from the empty cache (`tableExtending ∅ g = g`). These are the
precise eager forms on which the coupled-table union bound operates. -/

omit [Nonempty TagId] in
/-- Eager form of the multiple-session ideal success probability: sample a full random-oracle
table `g`, then run the deterministic real multiple-session table handler. -/
private lemma probOutput_multipleIdeal_run'_eq_tableSample [Fintype Nonce] [Finite Digest]
    (adv : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run'
        (UnlinkState.init, ∅)] =
      Pr[= true | ($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
        (simulateQ (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g) adv).run' UnlinkState.init] := by
  rw [probOutput_def, probOutput_def,
    evalDist_simulateQ_multipleIdealQueryImpl_run'_eq_tableExtending adv UnlinkState.init ∅]
  simp only [OracleComp.tableExtending_empty]

omit [Nonempty TagId] in
/-- Eager form of the single-session ideal success probability: sample a full random-oracle
table `g`, then run the deterministic real single-session table handler. -/
private lemma probOutput_singleIdeal_run'_eq_tableSample [Fintype Nonce] [Finite Digest]
    (adv : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run'
        (UnlinkState.init, ∅)] =
      Pr[= true | ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g) adv).run' UnlinkState.init] := by
  rw [probOutput_def, probOutput_def,
    evalDist_simulateQ_singleIdealQueryImpl_run'_eq_tableExtending adv UnlinkState.init ∅]
  simp only [OracleComp.tableExtending_empty]

/-- The reference-slot projection of a single-session random-oracle table onto a multiple-session
one: read the single-session table at the fixed reference session slot `0`. It is the table-level
coupling map underlying the eager-route comparison of the two ideal worlds. -/
private def projectTable
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) : TagId × Nonce → Digest :=
  fun p => gS ((p.1, (0 : Fin sessionsPerTag)), p.2)

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest] in
/-- **M4a — projecting a uniform single-session table is a uniform multiple-session table.**

Drawing a uniform single-session random-oracle table `gS` and projecting it onto the reference
session slot (`projectTable`) yields the uniform distribution on multiple-session tables. This is
the marginalization step of the coupled-table union bound: the reference-slot cells of `gS` are
themselves jointly uniform and independent of the off-slot cells. -/
private lemma evalDist_projectTable_uniformSample
    [Fintype Nonce] [Finite Digest] [Nonempty Digest] :
    𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
        fun gS => pure (projectTable (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) gS)] =
      𝒟[$ᵗ (TagId × Nonce → Digest)] := by
  have he : Function.Injective
      (fun p : TagId × Nonce => ((p.1, (0 : Fin sessionsPerTag)), p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1.1 h.2
  exact evalDist_uniformSample_map_comp_injective (R := Digest) he

/-! #### Milestone 5: the hybrid table handler

The 2-hop hybrid game closing the unlinkability reduction. The hybrid world `H` runs on the
*single-session* random-oracle table `gS : (TagId × Fin sessionsPerTag) × Nonce → Digest`, with:

* a tag oracle identical to the single-session world's — session `i` of `tag` reads
  `gS ((tag, i), nonce)`, so tag queries are *per-session fresh*;
* a *session-nonce-based* reader oracle. The hybrid state carries, beside the session counters, a
  `sessionNonce : TagId × Fin sessionsPerTag → Option Nonce` recording, for each `(tag, sid)`, the
  nonce that session `sid` of `tag` drew. On a reader query at transcript `(n, v)`, the reader
  accepts when some session `(tag, sid)` has a recorded draw `sessionNonce (tag, sid) = some n`
  with `gS ((tag, sid), n) = v` — i.e. it inspects exactly the cells that honest tag queries
  actually produced.

The `sessionNonce` map is *write-once*: each session `(tag, sid)` draws exactly once (the tag
oracle writes `sessionNonce (tag, sessionsUsed tag)` and strictly increments `sessionsUsed tag`),
so a tag drawing the same nonce twice records *both* draws on distinct keys, never orphaning a
cell. This is what makes the reader sound against the within-tag nonce-collision case, and what
makes the column-freshness invariant of hop B step-stable.

Because its tag oracle matches the single world's, `H` and Single can be coupled on one shared
table `gS` and differ only in the reader (hop B): `H`'s reader checks only the drawn cells, a
subset of the single reader's all-cells check, paying the reader-slack term. -/

/-- Per-session nonce map: records, for each session `(tag, sid)`, the nonce that session drew in
its tag query, or `none` if that session has not been used yet. The hybrid world threads a
`HybridSessionNonce` beside its session counters so that its reader can inspect exactly the cells
that honest tag queries produced. The map is write-once: each `(tag, sid)` is set exactly once. -/
def HybridSessionNonce (TagId Nonce : Type) (sessionsPerTag : ℕ) : Type :=
  TagId × Fin sessionsPerTag → Option Nonce

/-- Empty session-nonce map: no session has drawn a nonce yet. -/
def HybridSessionNonce.init {TagId Nonce : Type} {sessionsPerTag : ℕ} :
    HybridSessionNonce TagId Nonce sessionsPerTag := fun _ => none

/-- Hybrid-world handler state: the session counters together with the session-nonce map. -/
structure HybridState (TagId Nonce : Type) (sessionsPerTag : ℕ) where
  sessionsUsed : TagId → ℕ
  sessionNonce : HybridSessionNonce TagId Nonce sessionsPerTag

/-- Initial hybrid-world state: no sessions used, empty session-nonce map. -/
def HybridState.init {TagId Nonce : Type} {sessionsPerTag : ℕ} :
    HybridState TagId Nonce sessionsPerTag where
  sessionsUsed := fun _ => 0
  sessionNonce := HybridSessionNonce.init

/-- Reader acceptance for the hybrid world at session-nonce map `sn` and single-session table `gS`:
accept the transcript when some session `(tag, sid)` has a recorded draw
`sn (tag, sid) = some nonce` whose cell `gS ((tag, sid), nonce)` matches the authenticator. Only
the cells that honest tag queries actually produced are inspected. -/
def hybridReaderAccepts (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (transcript : TagTranscript Nonce Digest) : Bool :=
  decide (∃ tag : TagId, ∃ sid : Fin sessionsPerTag,
    sn (tag, sid) = some transcript.nonce ∧
      gS ((tag, sid), transcript.nonce) = transcript.auth)

/-- Hybrid-world tag oracle keyed on the single-session table `gS`: identical to the
single-session tag oracle on the session counter, additionally recording the drawn nonce in the
session-nonce map. Session `sid := sessionsUsed tag` of `tag` samples `nonce`, sets
`sessionNonce (tag, sid) := some nonce`, and returns `⟨nonce, gS ((tag, sid), nonce)⟩`. -/
noncomputable def hybridTagHandler (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) :
    QueryImpl (TagId →ₒ Option (TagTranscript Nonce Digest))
      (StateT (HybridState TagId Nonce sessionsPerTag) ProbComp) := fun tag => do
  let st ← get
  if h : st.sessionsUsed tag < sessionsPerTag then
    let sid : Fin sessionsPerTag := ⟨st.sessionsUsed tag, h⟩
    let nonce ← ($ᵗ Nonce : ProbComp Nonce)
    set
      ({ sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1)
         sessionNonce := Function.update st.sessionNonce (tag, sid) (some nonce) } :
        HybridState TagId Nonce sessionsPerTag)
    return some (⟨nonce, gS ((tag, sid), nonce)⟩ : TagTranscript Nonce Digest)
  else
    return none

/-- Hybrid-world reader oracle keyed on the single-session table `gS`: deterministic session-nonce
acceptance against `gS`, with the state untouched. -/
noncomputable def hybridReaderHandler (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (HybridState TagId Nonce sessionsPerTag) ProbComp) := fun transcript => fun s =>
  pure (ReaderReply.ofBool (hybridReaderAccepts (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS s.sessionNonce transcript), s)

/-- Deterministic hybrid handler keyed on a single-session random-oracle table
`gS : (TagId × Fin sessionsPerTag) × Nonce → Digest`: the session-nonce-recording single-session
tag oracle paired with the session-nonce-consulting reader oracle. -/
noncomputable def hybridTableHandler (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (HybridState TagId Nonce sessionsPerTag) ProbComp) :=
  hybridTagHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) gS +
  hybridReaderHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) gS

/-- `simulateQ hybridTableHandler` of a `query_bind`, run from a state and projected to its
output: the per-query handler followed by the recursive simulation of the continuation. -/
private lemma hybridTable_run'_query_bind' {α : Type}
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : HybridState TagId Nonce sessionsPerTag) :
    (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) gS) (liftM (OracleSpec.query t) >>= f)).run' s =
      (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) gS t s) >>= fun p =>
        (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) gS) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-- `hybridTableHandler` on a tag query with the slot budget exhausted: returns `none`, state
unchanged. -/
private lemma hybridTableHandler_tag_run_of_not_lt
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (s : HybridState TagId Nonce sessionsPerTag)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) gS (Sum.inl tag) s) = pure (none, s) := by
  unfold hybridTableHandler
  rw [QueryImpl.add_apply_inl]
  change (hybridTagHandler gS tag).run s = _
  unfold hybridTagHandler
  simp [StateT.run_bind, StateT.run_get, hslot]

/-- `hybridTableHandler` on a tag query with a free slot: sample a nonce, look up the table at
`((tag, sid), nonce)`, advance the session counter, and record the draw in the session-nonce map. -/
private lemma hybridTableHandler_tag_run_of_lt
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (s : HybridState TagId Nonce sessionsPerTag)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) gS (Sum.inl tag) s) =
      ($ᵗ Nonce) >>= fun nonce =>
        pure (some (⟨nonce, gS ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce)⟩ :
            TagTranscript Nonce Digest),
          ({ sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)
             sessionNonce := Function.update s.sessionNonce (tag, ⟨s.sessionsUsed tag, hslot⟩)
              (some nonce) } :
            HybridState TagId Nonce sessionsPerTag)) := by
  unfold hybridTableHandler
  rw [QueryImpl.add_apply_inl]
  change (hybridTagHandler gS tag).run s = _
  unfold hybridTagHandler
  simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set,
    hslot, bind_pure_comp]

/-- `hybridTableHandler` on a reader query: deterministic session-nonce acceptance against the
table, state untouched. -/
private lemma hybridTableHandler_reader_run
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) (s : HybridState TagId Nonce sessionsPerTag) :
    (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) gS (Sum.inr transcript) s) =
      pure (ReaderReply.ofBool (hybridReaderAccepts (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) gS s.sessionNonce transcript), s) := by
  unfold hybridTableHandler
  rw [QueryImpl.add_apply_inr]
  rfl

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] in
/-- Hybrid session-nonce acceptance is monotone in the table-cell agreement: whenever the hybrid
reader accepts a transcript at session-nonce map `sn` and table `gS`, the single-session reader
`unlinkReaderAccepts … singlePattern` at the same table also accepts it — `H`'s accept condition
inspects a *subset* of the cells the single reader checks (only the drawn ones). -/
private lemma hybridReaderAccepts_imp_singleReaderAccepts
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (transcript : TagTranscript Nonce Digest)
    (h : hybridReaderAccepts (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) gS sn transcript = true) :
    unlinkReaderAccepts (TagId := TagId) (Slot := TagId × Fin sessionsPerTag)
      (Nonce := Nonce) (Digest := Digest) (fun slot nonce => gS (slot, nonce))
      (singlePattern (TagId := TagId) sessionsPerTag) transcript = true := by
  unfold hybridReaderAccepts at h
  unfold unlinkReaderAccepts tagAccepts singlePattern
  simp only [decide_eq_true_eq] at h ⊢
  obtain ⟨tag, sid, _, hcell⟩ := h
  exact ⟨tag, sid, hcell⟩

/-! #### Hop B: the lazy hybrid handler and its eager-table equivalence

`hybridTableHandler` runs the hybrid world `H` against a *pre-sampled* single-session table `gS`.
For the hop-B coupling we instead need `H` and `Single` to share a *lazily-sampled* random-oracle
cache, so that the cells the single reader inspects but the hybrid reader does not are genuinely
fresh at each reader query. `hybridLazyHandler` is that lazy form: its state is
`HybridState × QueryCache` over the single-session domain `(TagId × Fin sessionsPerTag) × Nonce`,
its tag oracle samples a nonce and consults the cache via `idealCacheStep` (recording the draw in
the session-nonce map), and its reader oracle inspects only the drawn cache cells. -/

/-- Reader acceptance for the lazy hybrid world, read directly off the random-oracle cache `c`:
accept the transcript when some session `(tag, sid)` has a recorded draw
`sn (tag, sid) = some nonce` whose cached cell `c ((tag, sid), nonce)` equals the authenticator.
This is `hybridReaderAccepts` with the table lookup replaced by a cache lookup. -/
def hybridCacheAccepts
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (transcript : TagTranscript Nonce Digest) : Bool :=
  decide (∃ tag : TagId, ∃ sid : Fin sessionsPerTag,
    sn (tag, sid) = some transcript.nonce ∧
      c ((tag, sid), transcript.nonce) = some transcript.auth)

/-- Lazy hybrid handler: the hybrid world `H` run against a lazily-sampled random-oracle cache
rather than a pre-sampled table. The tag oracle samples a nonce, consults the cache at
`((tag, sid), nonce)` via `idealCacheStep`, advances the session counter, and records the draw in
the session-nonce map. The reader oracle inspects only the drawn cache cells via
`hybridCacheAccepts`. -/
noncomputable def hybridLazyHandler :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (HybridState TagId Nonce sessionsPerTag ×
        (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) ProbComp) :=
  fun q => fun p => match q with
    | Sum.inl tag => do
        let s := p.1
        if h : s.sessionsUsed tag < sessionsPerTag then
          let sid : Fin sessionsPerTag := ⟨s.sessionsUsed tag, h⟩
          let nonce ← ($ᵗ Nonce : ProbComp Nonce)
          let r ← idealCacheStep p.2 ((tag, sid), nonce)
          pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
            ({ sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)
               sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) } :
              HybridState TagId Nonce sessionsPerTag), r.2)
        else
          pure (none, p)
    | Sum.inr transcript =>
        pure (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) p.2 p.1.sessionNonce transcript), p)

/-- `simulateQ hybridLazyHandler` of a `query_bind`, run from a state and projected to its
output: the per-query handler followed by the recursive simulation of the continuation. -/
private lemma hybridLazy_run'_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' sH =
      (hybridLazyHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sH) >>= fun p =>
        (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridLazyHandler` on a tag query whose slot budget is exhausted: returns `none`, state
unchanged. -/
private lemma hybridLazyHandler_tag_run_of_not_lt (tag : TagId)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hslot : ¬ sH.1.sessionsUsed tag < sessionsPerTag) :
    (hybridLazyHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sH = pure (none, sH) := by
  show (if _h : sH.1.sessionsUsed tag < sessionsPerTag then _ else pure (none, sH)) = _
  rw [dif_neg hslot]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridLazyHandler` on a tag query with a free slot: sample a nonce, consult the cache at
`((tag, sid), nonce)` via `idealCacheStep`, advance the session counter, record the draw. -/
private lemma hybridLazyHandler_tag_run_of_lt (tag : TagId)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hslot : sH.1.sessionsUsed tag < sessionsPerTag) :
    (hybridLazyHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sH =
      ($ᵗ Nonce) >>= fun nonce =>
        idealCacheStep sH.2 ((tag, ⟨sH.1.sessionsUsed tag, hslot⟩), nonce) >>= fun r =>
          pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
            ({ sessionsUsed :=
                Function.update sH.1.sessionsUsed tag (sH.1.sessionsUsed tag + 1)
               sessionNonce := Function.update sH.1.sessionNonce
                (tag, ⟨sH.1.sessionsUsed tag, hslot⟩) (some nonce) } :
              HybridState TagId Nonce sessionsPerTag), r.2) := by
  show (if h : sH.1.sessionsUsed tag < sessionsPerTag then
      ($ᵗ Nonce) >>= fun nonce =>
        idealCacheStep sH.2 ((tag, ⟨sH.1.sessionsUsed tag, h⟩), nonce) >>= fun r =>
          pure (_, _, r.2)
      else pure (none, sH)) = _
  rw [dif_pos hslot]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridLazyHandler` on a reader query: deterministic session-nonce acceptance read off the
cache, state untouched. -/
private lemma hybridLazyHandler_reader_run (transcript : TagTranscript Nonce Digest)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (hybridLazyHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) sH =
      pure (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) sH.2 sH.1.sessionNonce transcript),
        sH) := by
  rfl

/-- Session-nonce / cache consistency invariant for the lazy hybrid handler: every cell recorded in
the session-nonce map is already present in the random-oracle cache. The lazy hybrid tag oracle
maintains this invariant — it records `sessionNonce (tag, sid) := some nonce` exactly when it
caches the cell `((tag, sid), nonce)` — and it is what lets the lazy reader (which reads only
cached cells) agree with the table reader (which reads the overlaid table `tableExtending c g`). -/
def HybridCacheConsistent
    (s : HybridState TagId Nonce sessionsPerTag)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) : Prop :=
  ∀ (tag : TagId) (sid : Fin sessionsPerTag) (n : Nonce),
    s.sessionNonce (tag, sid) = some n → (c ((tag, sid), n)).isSome

omit [Fintype TagId] [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The initial hybrid state with the empty cache is session-nonce / cache consistent: the empty
session-nonce map records nothing. -/
private lemma hybridCacheConsistent_init :
    HybridCacheConsistent (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) HybridState.init ∅ := by
  intro tag sid n h
  simp [HybridState.init, HybridSessionNonce.init] at h

omit [Fintype TagId] [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The lazy hybrid tag oracle preserves session-nonce / cache consistency: a tag query at `tag`
with a free slot caches the freshly drawn cell `((tag, sid), nonce)` and records exactly that draw,
while leaving every previously recorded draw both still recorded and still cached. The write is to
the fresh key `(tag, sid)`, never overwriting an existing record. -/
private lemma hybridCacheConsistent_tag_step
    (tag : TagId) (s : HybridState TagId Nonce sessionsPerTag)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hcons : HybridCacheConsistent (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) s c)
    (hslot : s.sessionsUsed tag < sessionsPerTag) (nonce : Nonce)
    (r : Digest × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheStep c ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce))) :
    HybridCacheConsistent (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)
      ({ sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)
         sessionNonce := Function.update s.sessionNonce (tag, ⟨s.sessionsUsed tag, hslot⟩)
          (some nonce) } : HybridState TagId Nonce sessionsPerTag)
      r.2 := by
  classical
  intro tag' sid' n' hsn
  dsimp only [HybridState.sessionNonce] at hsn
  by_cases hkey : (tag', sid') = (tag, ⟨s.sessionsUsed tag, hslot⟩)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hkey
    rw [Function.update_self] at hsn
    obtain rfl := Option.some.injEq .. ▸ hsn
    rw [idealCacheStep_cache_self c _ r hr]
    rfl
  · rw [Function.update_of_ne hkey] at hsn
    have hcell := hcons tag' sid' n' hsn
    by_cases hcellkey : ((tag', sid'), n') = ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce)
    · rw [hcellkey, idealCacheStep_cache_self c _ r hr]; rfl
    · rw [idealCacheStep_cache_off c _ r hr _ hcellkey]; exact hcell

omit [SampleableType Nonce] [SampleableType Digest] in
/-- Under session-nonce / cache consistency, the lazy hybrid reader (reading only cached cells)
agrees with the table hybrid reader run against the overlaid table `tableExtending c g`: every
drawn cell is cached, so its cached value equals its `tableExtending` value, and the two acceptance
tests coincide. -/
private lemma hybridCacheAccepts_eq_hybridReaderAccepts_tableExtending
    (s : HybridState TagId Nonce sessionsPerTag)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (g : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (hcons : HybridCacheConsistent (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) s c)
    (transcript : TagTranscript Nonce Digest) :
    hybridCacheAccepts (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) c s.sessionNonce transcript =
      hybridReaderAccepts (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g) s.sessionNonce
        transcript := by
  unfold hybridCacheAccepts hybridReaderAccepts
  refine decide_eq_decide.mpr ⟨?_, ?_⟩
  · rintro ⟨tag, sid, hsn, hcv⟩
    refine ⟨tag, sid, hsn, ?_⟩
    simp only [OracleComp.tableExtending, hcv, Option.getD_some]
  · rintro ⟨tag, sid, hsn, hcv⟩
    refine ⟨tag, sid, hsn, ?_⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hcons tag sid transcript.nonce hsn)
    rw [hv]
    rw [OracleComp.tableExtending, hv, Option.getD_some] at hcv
    rw [hcv]

/-- **Hop B, Step 1.** Running the lazy hybrid handler from a session-nonce / cache consistent
state `(s, c)` has the same output distribution as sampling a full single-session random-oracle
table `g`, overlaying the cache `c`, and running the deterministic table hybrid handler
`hybridTableHandler (tableExtending c g)` from `s`. The hybrid analogue of
`evalDist_simulateQ_singleIdealQueryImpl_run'_eq_tableExtending`. -/
private lemma evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending
    [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest)
    (s : HybridState TagId Nonce sessionsPerTag)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hcons : HybridCacheConsistent (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) s c) :
    𝒟[(simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) oa).run' (s, c)] =
      𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
            (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)) oa).run' s] := by
  induction oa using OracleComp.inductionOn generalizing s c with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    refine (evalDist_ext fun x => ?_).symm
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  | query_bind t f ih =>
    rw [hybridLazy_run'_query_bind']
    have hrhs : 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
          (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g))
            (liftM (OracleSpec.query t) >>= f)).run' s]
        = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
            (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g) t s) >>= fun p =>
              (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g))
                (f p.1)).run' p.2] := by
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [hybridTable_run'_query_bind']
    rw [hrhs]
    cases t with
    | inl tag =>
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · rw [hybridLazyHandler_tag_run_of_lt tag (s, c) hslot]
        set sid := (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) with hsid
        set adv : Nonce → HybridState TagId Nonce sessionsPerTag :=
          fun nonce =>
            { sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1),
              sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) } with hadv
        have hlhs_reassoc :
            ((($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest), adv nonce, r.2))
              >>= fun p =>
              (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
            = (($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv nonce, r.2)) := by
          rw [bind_assoc]
          refine bind_congr fun nonce => ?_
          rw [bind_assoc]
          refine bind_congr fun r => ?_
          rw [pure_bind]
        refine (congrArg evalDist hlhs_reassoc).trans ?_
        have hlhs_inner : ∀ (n : Nonce),
            𝒟[idealCacheStep c ((tag, sid), n) >>= fun r =>
              (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv n, r.2)]
            = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                  (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c g))
                    (f (some (⟨n, OracleComp.tableExtending c g ((tag, sid), n)⟩ :
                      TagTranscript Nonce Digest)))).run' (adv n)] := by
          intro n
          set Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun g' =>
            (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) g')
              (f (some (⟨n, g' ((tag, sid), n)⟩ : TagTranscript Nonce Digest)))).run' (adv n)
            with hMψ
          refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable_comp c ((tag, sid), n) Mψ)
          refine evalDist_bind_congr_of_support _ _ _ fun r hr => ?_
          rw [ih (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)) (adv n) r.2
            (hybridCacheConsistent_tag_step tag s c hcons hslot n r hr)]
          refine congrArg _ (congrArg _ (funext fun g => ?_))
          have hcell : OracleComp.tableExtending r.2 g ((tag, sid), n) = r.1 := by
            simp only [OracleComp.tableExtending,
              idealCacheStep_cache_self c ((tag, sid), n) r hr, Option.getD_some]
          rw [hMψ]
          simp only [hcell]
        simp only [hybridTableHandler_tag_run_of_lt _ tag s hslot]
        have hrhs_swap :
            (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
              (($ᵗ Nonce) >>= fun nonce =>
                pure (some (⟨nonce, OracleComp.tableExtending c g ((tag, sid), nonce)⟩ :
                  TagTranscript Nonce Digest), adv nonce)) >>= fun p =>
                (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g)) (f p.1)).run' p.2)
            = (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                ($ᵗ Nonce) >>= fun n =>
                (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g))
                  (f (some (⟨n, OracleComp.tableExtending c g ((tag, sid), n)⟩ :
                    TagTranscript Nonce Digest)))).run' (adv n)) := by
          refine bind_congr fun g => ?_
          rw [bind_assoc]
          refine bind_congr fun n => ?_
          rw [pure_bind]
        refine Eq.trans ?_ (congrArg evalDist hrhs_swap).symm
        rw [evalDist_probComp_bind_comm ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
          ($ᵗ Nonce)]
        refine evalDist_bind_congr_of_support _ _ _ fun n _ => ?_
        exact hlhs_inner n
      · rw [hybridLazyHandler_tag_run_of_not_lt tag (s, c) hslot]
        show 𝒟[(simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f none)).run' (s, c)] = _
        rw [ih none s c hcons]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [hybridTableHandler_tag_run_of_not_lt _ tag s hslot]
        rfl
    | inr transcript =>
      rw [hybridLazyHandler_reader_run transcript (s, c)]
      show 𝒟[(simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag))
          (f (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce
            transcript)))).run' (s, c)] = _
      rw [ih _ s c hcons]
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [hybridTableHandler_reader_run _ transcript s]
      rw [hybridCacheAccepts_eq_hybridReaderAccepts_tableExtending s c g hcons transcript]
      rfl

/-- **Hop B, deliverable 1.** Eager form of the hybrid-world success probability: running the
lazy hybrid handler from the initial state has the same success probability as sampling a full
single-session random-oracle table `gS` up front and running the deterministic table hybrid
handler. The hybrid analogue of `probOutput_singleIdeal_run'_eq_tableSample`. -/
private lemma probOutput_hybrid_run'_eq_tableSample [Fintype Nonce] [Finite Digest]
    (adv : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run'
        (HybridState.init, ∅)] =
      Pr[= true | ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gS =>
        (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) gS) adv).run' HybridState.init] := by
  rw [probOutput_def, probOutput_def,
    evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending adv HybridState.init ∅
      hybridCacheConsistent_init]
  simp only [OracleComp.tableExtending_empty]

/-! #### Hop A: the spare-fed hybrid handler

The hop-A coupling pairs the multiple world against the hybrid world. The multiple world's reader
queries *write* random-oracle cells keyed on `(TagId × Nonce)` that a later multiple tag query may
reuse; the hybrid world's reader is read-only, so there is no cell for the coupling to align with.
`hybridSpareHandler` is a distribution-preserving reformulation of `hybridLazyHandler` carrying an
extra **spare reservoir** — a `((TagId × Nonce) →ₒ Digest).QueryCache` with the same key shape as
the multiple world's cache. Its reader, beyond the read-only session-cache acceptance test of
`hybridLazyHandler`, folds `idealCacheStep` over `(tag, transcript.nonce)` for every tag, drawing
fresh uniform digests into the reservoir (write-once: `idealCacheStep` skips cells already cached).
Its tag oracle draws a nonce `n` and, if the reservoir already holds `(tag, n)`, consumes that
spare as the tag digest; otherwise it draws fresh exactly as `hybridLazyHandler` does. -/

/-- Spare-fed hybrid handler: `hybridLazyHandler` augmented with a spare reservoir keyed on
`(TagId × Nonce)`. The reader additionally populates the reservoir with fresh uniform digests at
`(tag, transcript.nonce)` for every tag (write-once via `idealCacheStep`), leaving the read-only
output bit unchanged. The tag oracle draws a nonce `n`; if the reservoir holds a spare at
`(tag, n)` it consumes it as the tag digest, recording it in the session cell `((tag, sid), n)` and
*clearing* the reservoir cell so the spare is consumed at most once; otherwise it draws fresh via
`idealCacheStep` on the session cache. -/
noncomputable def hybridSpareHandler :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (HybridState TagId Nonce sessionsPerTag ×
        (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache ×
        ((TagId × Nonce) →ₒ Digest).QueryCache) ProbComp) :=
  fun q => fun p => match q with
    | Sum.inl tag => do
        let s := p.1
        if h : s.sessionsUsed tag < sessionsPerTag then
          let sid : Fin sessionsPerTag := ⟨s.sessionsUsed tag, h⟩
          let nonce ← ($ᵗ Nonce : ProbComp Nonce)
          match p.2.2 (tag, nonce) with
          | some d =>
              pure (some (⟨nonce, d⟩ : TagTranscript Nonce Digest),
                ({ sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)
                   sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) } :
                  HybridState TagId Nonce sessionsPerTag),
                p.2.1.cacheQuery ((tag, sid), nonce) d,
                Function.update p.2.2 (tag, nonce) none)
          | none => do
              let r ← idealCacheStep p.2.1 ((tag, sid), nonce)
              pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
                ({ sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)
                   sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) } :
                  HybridState TagId Nonce sessionsPerTag),
                r.2, p.2.2)
        else
          pure (none, p)
    | Sum.inr transcript => do
        let rs ← idealCacheMapM ((Finset.univ : Finset TagId).toList.map
          (fun tag => (tag, transcript.nonce))) p.2.2
        pure (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) p.2.1 p.1.sessionNonce transcript),
          p.1, p.2.1, rs.2)

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridSpareHandler` on a tag query whose slot budget is exhausted: returns `none`, state
unchanged. -/
private lemma hybridSpareHandler_tag_run_of_not_lt (tag : TagId)
    (p : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache ×
      ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hslot : ¬ p.1.sessionsUsed tag < sessionsPerTag) :
    (hybridSpareHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) p = pure (none, p) := by
  change (if _h : p.1.sessionsUsed tag < sessionsPerTag then _ else pure (none, p)) = _
  rw [dif_neg hslot]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridSpareHandler` on a tag query with a free slot: sample a nonce, then branch on the spare
reservoir. The handler reduces to sampling a nonce followed by the reservoir-keyed continuation
`hybridSpareTagStep`, which consumes a reservoir spare when present and draws fresh otherwise. -/
private lemma hybridSpareHandler_tag_run_of_lt (tag : TagId)
    (p : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache ×
      ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hslot : p.1.sessionsUsed tag < sessionsPerTag) :
    (hybridSpareHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) p =
      ($ᵗ Nonce) >>= fun nonce =>
        (match p.2.2 (tag, nonce) with
          | some d =>
              pure (some (⟨nonce, d⟩ : TagTranscript Nonce Digest),
                ({ sessionsUsed :=
                    Function.update p.1.sessionsUsed tag (p.1.sessionsUsed tag + 1)
                   sessionNonce := Function.update p.1.sessionNonce
                    (tag, ⟨p.1.sessionsUsed tag, hslot⟩) (some nonce) } :
                  HybridState TagId Nonce sessionsPerTag),
                p.2.1.cacheQuery ((tag, ⟨p.1.sessionsUsed tag, hslot⟩), nonce) d,
                Function.update p.2.2 (tag, nonce) none)
          | none =>
              idealCacheStep p.2.1 ((tag, ⟨p.1.sessionsUsed tag, hslot⟩), nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
                  ({ sessionsUsed :=
                      Function.update p.1.sessionsUsed tag (p.1.sessionsUsed tag + 1)
                     sessionNonce := Function.update p.1.sessionNonce
                      (tag, ⟨p.1.sessionsUsed tag, hslot⟩) (some nonce) } :
                    HybridState TagId Nonce sessionsPerTag),
                  r.2, p.2.2)) := by
  change (if h : p.1.sessionsUsed tag < sessionsPerTag then
      ($ᵗ Nonce) >>= fun nonce =>
        (match p.2.2 (tag, nonce) with
          | some d => pure (_, _, _, Function.update p.2.2 (tag, nonce) none)
          | none => idealCacheStep p.2.1 ((tag, ⟨p.1.sessionsUsed tag, h⟩), nonce) >>= fun r =>
              pure (_, _, r.2, p.2.2))
      else pure (none, p)) = _
  rw [dif_pos hslot]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridSpareHandler` on a reader query: fold `idealCacheStep` over the reservoir cells
`(tag, transcript.nonce)` for every tag (write-once spare population), and return the read-only
session-cache acceptance bit unchanged from `hybridLazyHandler`. -/
private lemma hybridSpareHandler_reader_run (transcript : TagTranscript Nonce Digest)
    (p : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache ×
      ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (hybridSpareHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) p =
      idealCacheMapM ((Finset.univ : Finset TagId).toList.map
          (fun tag => (tag, transcript.nonce))) p.2.2 >>= fun rs =>
        pure (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) p.2.1 p.1.sessionNonce transcript),
          p.1, p.2.1, rs.2) := by
  rfl

/-! #### Hop B, deliverable 2: the per-reader-query slack bound

A single reader query under the single-session ideal handler folds `idealCacheStep` over the
column of cells `l`. The hybrid reader inspects only the *already cached* cells; a cell that is
uncached in `c` is sampled fresh. The lemma below bounds the probability that the fresh draws
produce the target authenticator `v` at a cell whose cache slot does not already hold `v`, by
`l.length / |Digest|`. This is the per-step disagreement bound between the hybrid and single
readers. -/

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [NeZero sessionsPerTag] in
/-- **Per-reader-query slack.** Folding `idealCacheStep` over a list `l` of distinct cells: the
probability that the produced digest list contains the target `v` while no cache slot of `l`
already holds `v` is at most `l.length / |Digest|`. Every such occurrence of `v` is a fresh
uniform draw, and a union bound over the list gives the stated cell-count-over-`|Digest|` bound. -/
private lemma probEvent_idealCacheMapM_mem_le {D : Type} [DecidableEq D] [Fintype Digest]
    (l : List D) (hnd : l.Nodup) (c : (D →ₒ Digest).QueryCache) (v : Digest) :
    Pr[fun rs : List Digest × (D →ₒ Digest).QueryCache =>
        v ∈ rs.1 ∧ ∀ d ∈ l, c d ≠ some v | idealCacheMapM l c] ≤
      (l.length : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
  classical
  induction l generalizing c with
  | nil =>
    rw [idealCacheMapM, List.length_nil, Nat.cast_zero, ENNReal.zero_div]
    refine le_of_eq_of_le (probEvent_eq_zero (fun rs hrs => ?_)) (le_refl 0)
    rintro ⟨hmem, _⟩
    rw [support_pure, Set.mem_singleton_iff] at hrs
    subst hrs
    simp at hmem
  | cons d ds ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hdnd, hndtail⟩ := hnd
    rw [idealCacheMapM]
    by_cases hcd : c d = some v
    · refine le_of_eq_of_le (probEvent_eq_zero (fun rs _ => ?_)) (zero_le _)
      rintro ⟨_, hfresh⟩
      exact hfresh d (List.mem_cons_self ..) hcd
    · have hcons_len : ((d :: ds).length : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞)
          = (1 : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞)
            + (ds.length : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
        rw [List.length_cons, Nat.cast_add, Nat.cast_one, ENNReal.add_div, add_comm]
      rw [hcons_len]
      rw [show (fun rs : List Digest × (D →ₒ Digest).QueryCache =>
            v ∈ rs.1 ∧ ∀ d_1 ∈ d :: ds, c d_1 ≠ some v)
          = (fun rs => ¬¬(v ∈ rs.1 ∧ ∀ d_1 ∈ d :: ds, c d_1 ≠ some v)) from by
        funext rs; rw [not_not]]
      refine probEvent_bind_le_add (p := fun r => r.1 ≠ v) ?_ ?_
      · have hstep : Pr[fun r : Digest × (D →ₒ Digest).QueryCache => r.1 = v |
            idealCacheStep c d] ≤ (1 : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
          unfold idealCacheStep
          rcases hc : c d with _ | u
          · simp only [hc]
            rw [bind_pure_comp, probEvent_map]
            refine le_of_eq ?_
            rw [show ((fun r : Digest × (D →ₒ Digest).QueryCache => r.1 = v) ∘
                fun u => (u, c.cacheQuery d u)) = (fun u => u = v) from rfl]
            rw [probEvent_eq_eq_probOutput, probOutput_uniformSample, one_div]
          · simp only [hc] at hcd
            simp only [hc, probEvent_pure]
            by_cases hu : u = v
            · exact absurd (hu ▸ rfl) hcd
            · simp [hu]
        simp only [not_not] at hstep ⊢
        exact hstep
      · intro r hr hrne
        simp only [not_not]
        rw [bind_pure_comp, probEvent_map]
        have hrcache : ∀ d' ∈ ds, r.2 d' = c d' := fun d' hd' =>
          idealCacheStep_cache_off c d r hr d' (fun h => hdnd (h ▸ hd'))
        refine le_trans (probEvent_mono (fun rs _ hrs => ?_)) (ih hndtail r.2)
        simp only [Function.comp, List.mem_cons] at hrs ⊢
        obtain ⟨hmem, hfresh⟩ := hrs
        refine ⟨?_, fun d' hd' => ?_⟩
        · rcases hmem with h | h
          · exact absurd h.symm hrne
          · exact h
        · rw [hrcache d' hd']; exact hfresh d' (Or.inr hd')

/-! #### Hop B, deliverable 3: the coupled reader step and the coupling theorem

`hybridCoupledHandler` is the hybrid world run *in lockstep* with the single-session ideal handler:
its tag oracle is the lazy hybrid tag oracle and its reader oracle folds `idealCacheStep` over the
whole column of cells — exactly as the single reader does, so the two threads keep an identical
random-oracle cache — but its acceptance bit is the session-nonce bit `hybridCacheAccepts` read off
the *pre-extension* cache. The two handlers therefore differ only in the reader's output bit, and
the per-reader-query disagreement is bounded by `probEvent_idealCacheMapM_mem_le`. -/

/-- The column of single-session cells inspected by a reader query at `transcript.nonce`. -/
private noncomputable def hybridReaderCells (transcript : TagTranscript Nonce Digest) :
    List ((TagId × Fin sessionsPerTag) × Nonce) :=
  (Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
    (fun slot => (slot, transcript.nonce))

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The reader-cell column is duplicate-free: `Finset.univ.toList` is `Nodup` and pairing each slot
with the fixed nonce is injective. -/
private lemma hybridReaderCells_nodup (transcript : TagTranscript Nonce Digest) :
    (hybridReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) transcript).Nodup := by
  unfold hybridReaderCells
  refine (Finset.univ : Finset (TagId × Fin sessionsPerTag)).nodup_toList.map ?_
  intro a b hab
  simpa using hab

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The reader-cell column has `|TagId| * sessionsPerTag` cells. -/
private lemma hybridReaderCells_length (transcript : TagTranscript Nonce Digest) :
    (hybridReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) transcript).length
      = Fintype.card TagId * sessionsPerTag := by
  unfold hybridReaderCells
  rw [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin]

omit [Nonempty TagId] [SampleableType Nonce] in
/-- **Per-reader-query coupled disagreement bound.** Fix a cache `c` in which every cached
column-`transcript.nonce` cell is recorded in the session-nonce map `sn` (the column-freshness
invariant guaranteed, at the current reader query, by `HasDistinctUnlinkReaderNonces`). Folding
`idealCacheStep` over the whole column, the probability that the single-session acceptance bit
exceeds the hybrid session-nonce bit `hybridCacheAccepts c sn transcript` is at most
`|TagId| * sessionsPerTag / |Digest|`: the only way they disagree is a fresh draw at an undrawn
cell hitting the authenticator, and `probEvent_idealCacheMapM_mem_le` bounds that. -/
private lemma probEvent_coupledReader_disagree_le [Fintype Digest]
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (transcript : TagTranscript Nonce Digest)
    (hcol : ∀ (tag : TagId) (sid : Fin sessionsPerTag),
      (c ((tag, sid), transcript.nonce)).isSome →
        sn (tag, sid) = some transcript.nonce) :
    Pr[fun rs : List Digest × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache =>
        decide (∃ d ∈ rs.1, d = transcript.auth) = true ∧
          hybridCacheAccepts (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) c sn transcript = false |
        idealCacheMapM (hybridReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) transcript) c] ≤
      (Fintype.card TagId * sessionsPerTag : ℕ) / (Fintype.card Digest : ℝ≥0∞) := by
  classical
  rw [← hybridReaderCells_length (TagId := TagId) (Digest := Digest) transcript]
  push_cast
  refine le_trans (probEvent_mono fun rs _ hrs => ?_)
    (probEvent_idealCacheMapM_mem_le _
      (hybridReaderCells_nodup (TagId := TagId) (Digest := Digest) transcript) c transcript.auth)
  obtain ⟨haccept, hreject⟩ := hrs
  rw [decide_eq_true_eq] at haccept
  refine ⟨haccept.1, fun cell hcell hcc => ?_⟩
  obtain ⟨slot, rfl⟩ : ∃ slot, cell = (slot, transcript.nonce) := by
    unfold hybridReaderCells at hcell
    rw [List.mem_map] at hcell
    obtain ⟨slot, _, rfl⟩ := hcell
    exact ⟨slot, rfl⟩
  have hdrawn := hcol slot.1 slot.2 (by rw [hcc]; rfl)
  rw [hybridCacheAccepts, decide_eq_false_iff_not] at hreject
  exact hreject ⟨slot.1, slot.2, hdrawn, hcc⟩

/-- **Coupled hybrid handler.** The hybrid world run *in lockstep* with the single-session ideal
handler. Its tag oracle is the lazy hybrid tag oracle (`hybridLazyHandler` on `Sum.inl`); its
reader oracle folds `idealCacheStep` over the *whole* single-session column — exactly as
`singleIdealQueryImpl` does — so the random-oracle cache evolves identically in the two worlds.
The reader's output bit, however, is the session-nonce bit `hybridCacheAccepts` read off the
*pre-fold* cache, so the coupled handler returns the same answers as `hybridLazyHandler` while
maintaining a cache in lockstep with `singleIdealQueryImpl`. -/
noncomputable def hybridCoupledHandler :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (HybridState TagId Nonce sessionsPerTag ×
        (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) ProbComp) :=
  fun q => fun p => match q with
    | Sum.inl tag => hybridLazyHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag) p
    | Sum.inr transcript => do
        let rs ← idealCacheMapM (hybridReaderCells (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) transcript) p.2
        pure (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) p.2 p.1.sessionNonce transcript),
          p.1, rs.2)

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ hybridCoupledHandler` of a `query_bind`, run from a state and projected to its
output: the per-query handler followed by the recursive simulation of the continuation. -/
private lemma hybridCoupled_run'_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' sH =
      (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sH) >>= fun p =>
        (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridCoupledHandler` on a tag query: identical to `hybridLazyHandler`. -/
private lemma hybridCoupledHandler_tag_run (tag : TagId)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sH =
      (hybridLazyHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sH := rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridCoupledHandler` on a reader query: fold `idealCacheStep` over the whole single-session
column, return the session-nonce bit read off the pre-fold cache, advance the cache. -/
private lemma hybridCoupledHandler_reader_run (transcript : TagTranscript Nonce Digest)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) sH =
      idealCacheMapM (hybridReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) transcript) sH.2 >>= fun rs =>
        pure (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) sH.2 sH.1.sessionNonce transcript),
          sH.1, rs.2) := rfl

/-- **Coupled hybrid eager-table equivalence.** Running the coupled hybrid handler from a
session-nonce / cache consistent state `(s, c)` has the same output distribution as sampling a full
single-session random-oracle table `g`, overlaying the cache `c`, and running the deterministic
table hybrid handler `hybridTableHandler (tableExtending c g)` from `s`. The hybrid analogue of
`evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending`; the reader step folds the whole
column but the extra cells are absorbed by `evalDist_idealCacheMapM_bind_uniformTable_comp`. -/
private lemma evalDist_simulateQ_hybridCoupledHandler_run'_eq_tableExtending
    [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest)
    (s : HybridState TagId Nonce sessionsPerTag)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hcons : HybridCacheConsistent (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) s c) :
    𝒟[(simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) oa).run' (s, c)] =
      𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
            (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)) oa).run' s] := by
  induction oa using OracleComp.inductionOn generalizing s c with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    refine (evalDist_ext fun x => ?_).symm
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  | query_bind t f ih =>
    rw [hybridCoupled_run'_query_bind']
    have hrhs : 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
          (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g))
            (liftM (OracleSpec.query t) >>= f)).run' s]
        = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
            (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g) t s) >>= fun p =>
              (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g))
                (f p.1)).run' p.2] := by
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [hybridTable_run'_query_bind']
    rw [hrhs]
    cases t with
    | inl tag =>
      rw [hybridCoupledHandler_tag_run tag (s, c)]
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · rw [hybridLazyHandler_tag_run_of_lt tag (s, c) hslot]
        set sid := (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) with hsid
        set adv : Nonce → HybridState TagId Nonce sessionsPerTag :=
          fun nonce =>
            { sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1),
              sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) } with hadv
        have hlhs_reassoc :
            ((($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest), adv nonce, r.2))
              >>= fun p =>
              (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
            = (($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv nonce, r.2)) := by
          rw [bind_assoc]
          refine bind_congr fun nonce => ?_
          rw [bind_assoc]
          refine bind_congr fun r => ?_
          rw [pure_bind]
        refine (congrArg evalDist hlhs_reassoc).trans ?_
        have hlhs_inner : ∀ (n : Nonce),
            𝒟[idealCacheStep c ((tag, sid), n) >>= fun r =>
              (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv n, r.2)]
            = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                  (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c g))
                    (f (some (⟨n, OracleComp.tableExtending c g ((tag, sid), n)⟩ :
                      TagTranscript Nonce Digest)))).run' (adv n)] := by
          intro n
          set Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun g' =>
            (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) g')
              (f (some (⟨n, g' ((tag, sid), n)⟩ : TagTranscript Nonce Digest)))).run' (adv n)
            with hMψ
          refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable_comp c ((tag, sid), n) Mψ)
          refine evalDist_bind_congr_of_support _ _ _ fun r hr => ?_
          rw [ih (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)) (adv n) r.2
            (hybridCacheConsistent_tag_step tag s c hcons hslot n r hr)]
          refine congrArg _ (congrArg _ (funext fun g => ?_))
          have hcell : OracleComp.tableExtending r.2 g ((tag, sid), n) = r.1 := by
            simp only [OracleComp.tableExtending,
              idealCacheStep_cache_self c ((tag, sid), n) r hr, Option.getD_some]
          rw [hMψ]
          simp only [hcell]
        simp only [hybridTableHandler_tag_run_of_lt _ tag s hslot]
        have hrhs_swap :
            (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
              (($ᵗ Nonce) >>= fun nonce =>
                pure (some (⟨nonce, OracleComp.tableExtending c g ((tag, sid), nonce)⟩ :
                  TagTranscript Nonce Digest), adv nonce)) >>= fun p =>
                (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g)) (f p.1)).run' p.2)
            = (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                ($ᵗ Nonce) >>= fun n =>
                (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g))
                  (f (some (⟨n, OracleComp.tableExtending c g ((tag, sid), n)⟩ :
                    TagTranscript Nonce Digest)))).run' (adv n)) := by
          refine bind_congr fun g => ?_
          rw [bind_assoc]
          refine bind_congr fun n => ?_
          rw [pure_bind]
        refine Eq.trans ?_ (congrArg evalDist hrhs_swap).symm
        rw [evalDist_probComp_bind_comm ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
          ($ᵗ Nonce)]
        refine evalDist_bind_congr_of_support _ _ _ fun n _ => ?_
        exact hlhs_inner n
      · rw [hybridLazyHandler_tag_run_of_not_lt tag (s, c) hslot]
        show 𝒟[(simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f none)).run' (s, c)] = _
        rw [ih none s c hcons]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [hybridTableHandler_tag_run_of_not_lt _ tag s hslot]
        rfl
    | inr transcript =>
      rw [hybridCoupledHandler_reader_run transcript (s, c)]
      set cells := hybridReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) transcript with hcells
      have hlhs_reassoc :
          ((idealCacheMapM cells c >>= fun rs =>
              pure (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce transcript),
                s, rs.2))
            >>= fun p => (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
          = (idealCacheMapM cells c >>= fun rs =>
              (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce
                  transcript)))).run' (s, rs.2)) := by
        rw [bind_assoc]
        refine bind_congr fun rs => ?_
        rw [pure_bind]
      refine (congrArg evalDist hlhs_reassoc).trans ?_
      set Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun g' =>
        (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g')
          (f (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce
            transcript)))).run' s
        with hMψ
      have hstep1 :
          𝒟[idealCacheMapM cells c >>= fun rs =>
              (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce
                  transcript)))).run' (s, rs.2)]
          = 𝒟[idealCacheMapM cells c >>= fun rs =>
              ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                Mψ (OracleComp.tableExtending rs.2 g)] := by
        refine evalDist_bind_congr_of_support _ _ _ fun rs hrs => ?_
        have hcons' : HybridCacheConsistent (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) s rs.2 := by
          intro tag' sid' n' hsn
          exact idealCacheMapM_cache_off cells c rs hrs ((tag', sid'), n')
            (hcons tag' sid' n' hsn) ▸ hcons tag' sid' n' hsn
        rw [ih (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce transcript))
          s rs.2 hcons']
      rw [hstep1, evalDist_idealCacheMapM_bind_uniformTable_comp cells c Mψ]
      refine (evalDist_bind_congr_of_support _ _ _ fun g _ => ?_).symm
      rw [hybridTableHandler_reader_run _ transcript s]
      rw [hMψ]
      rw [hybridCacheAccepts_eq_hybridReaderAccepts_tableExtending s c g hcons transcript]
      rfl

/-- **Coupled hybrid handler distributional equivalence.** Running the coupled hybrid handler from
the initial state has the same output distribution as running the lazy hybrid handler. Both equal
the eager-table form (`evalDist_simulateQ_hybridCoupledHandler_run'_eq_tableExtending` and
`evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending`); caching the extra column cells the
hybrid output ignores does not change the hybrid output distribution. -/
private lemma evalDist_simulateQ_hybridCoupledHandler_run'_eq_lazy
    [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest) :
    𝒟[(simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) oa).run' (HybridState.init, ∅)] =
      𝒟[(simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) oa).run' (HybridState.init, ∅)] := by
  rw [evalDist_simulateQ_hybridCoupledHandler_run'_eq_tableExtending oa HybridState.init ∅
      hybridCacheConsistent_init,
    evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending oa HybridState.init ∅
      hybridCacheConsistent_init]

/-- The coupled hybrid handler has the same success probability as the lazy hybrid handler. -/
private lemma probOutput_hybridCoupled_run'_eq_lazy [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run'
        (HybridState.init, ∅)] =
      Pr[= true | (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run'
        (HybridState.init, ∅)] := by
  rw [probOutput_def, probOutput_def, evalDist_simulateQ_hybridCoupledHandler_run'_eq_lazy oa]

/-- **Disagreement-aware additive bind bound.** If the disagreement set `D` has probability at
most `ε₁` under `mx`, and off `D` the continuation `my` is within `ε₂` of the reference
continuation `oc`, then `Pr[q | mx >>= my] ≤ Pr[q | mx >>= oc] + ε₁ + ε₂`. The exceptional set `D`
is charged its full mass `ε₁`; everywhere else the per-point gap `ε₂` is paid. -/
private lemma probEvent_bind_le_add_of_disagree {α β : Type} {mx : ProbComp α}
    {my oc : α → ProbComp β} {q : β → Prop} {D : α → Prop} [DecidablePred D] {ε₁ ε₂ : ℝ≥0∞}
    (hD : Pr[D | mx] ≤ ε₁)
    (h : ∀ x ∈ support mx, ¬ D x → Pr[q | my x] ≤ Pr[q | oc x] + ε₂) :
    Pr[q | mx >>= my] ≤ Pr[q | mx >>= oc] + ε₁ + ε₂ := by
  have := Classical.decPred q
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[q | my x]
      ≤ ∑' x, (Pr[= x | mx] * Pr[q | oc x]
            + (if D x then Pr[= x | mx] else 0) + Pr[= x | mx] * ε₂) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · by_cases hDx : D x
          · simp only [if_pos hDx]
            calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * 1 := mul_le_mul' le_rfl probEvent_le_one
              _ = Pr[= x | mx] := mul_one _
              _ ≤ Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] + Pr[= x | mx] * ε₂ := by
                  refine le_add_right (le_add_left le_rfl)
          · simp only [if_neg hDx, add_zero]
            calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * (Pr[q | oc x] + ε₂) :=
                  mul_le_mul' le_rfl (h x hx hDx)
              _ = Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * ε₂ := left_distrib ..
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, if D x then Pr[= x | mx] else 0) + (∑' x, Pr[= x | mx] * ε₂) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ (∑' x, Pr[= x | mx] * Pr[q | oc x]) + ε₁ + ε₂ := by
        refine add_le_add (add_le_add le_rfl ?_) ?_
        · rw [← probEvent_eq_tsum_ite]; exact hD
        · rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left (zero_le _) tsum_probOutput_le_one

/-- **Three-way disagreement-aware additive bind bound (hop A).** A coupled three-world variant of
`probEvent_bind_le_add_of_disagree`: the three worlds share the sampling computation `mx`, and at
each shared sample `x`, off the disagreement set `D` the `my`-world is bounded by the `oc`-world
plus the per-step slack `ε`, while on `D` the `ob`-world (the bad world) already fires its event
`r` with probability `1`. The conclusion charges the disagreement to `Pr[r | mx >>= ob]`. -/
private lemma probEvent_bind_le_add_bad_of_disagree {α β γ : Type} {mx : ProbComp α}
    {my : α → ProbComp β} {oc : α → ProbComp β} {ob : α → ProbComp γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} [DecidablePred D] {ε : ℝ≥0∞}
    (hbad : ∀ x ∈ support mx, D x → Pr[r | ob x] = 1)
    (h : ∀ x ∈ support mx, ¬ D x → Pr[q | my x] ≤ Pr[q | oc x] + ε) :
    Pr[q | mx >>= my] ≤ Pr[q | mx >>= oc] + Pr[r | mx >>= ob] + ε := by
  have := Classical.decPred q
  have := Classical.decPred r
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[q | my x]
      ≤ ∑' x, (Pr[= x | mx] * Pr[q | oc x]
            + Pr[= x | mx] * Pr[r | ob x] + Pr[= x | mx] * ε) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · by_cases hDx : D x
          · calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * 1 := mul_le_mul' le_rfl probEvent_le_one
              _ = Pr[= x | mx] * Pr[r | ob x] := by rw [hbad x hx hDx]
              _ ≤ Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                    + Pr[= x | mx] * ε := le_add_right (le_add_left le_rfl)
          · calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * (Pr[q | oc x] + ε) :=
                  mul_le_mul' le_rfl (h x hx hDx)
              _ = Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * ε := left_distrib ..
              _ ≤ Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                    + Pr[= x | mx] * ε := by
                  rw [add_right_comm]
                  exact le_add_right le_rfl
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, Pr[= x | mx] * Pr[r | ob x]) + (∑' x, Pr[= x | mx] * ε) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, Pr[= x | mx] * Pr[r | ob x]) + ε := by
        refine add_le_add le_rfl ?_
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left (zero_le _) tsum_probOutput_le_one

/-- **Four-way disagreement-aware additive bind bound (hop A).** A strengthening of
`probEvent_bind_le_add_bad_of_disagree`: the per-step inductive hypothesis itself carries a
bad-event term, so off the disagreement set `D` the `my`-world is bounded by the `oc`-world plus the
*per-shared-sample* bad probability `Pr[r | ob x]` plus the slack `ε`. On `D` the `ob`-world already
fires `r` with probability `1`. Both cases are charged into the aggregate `Pr[r | mx >>= ob]`, so
the conclusion is the same shape as the three-way bound. -/
private lemma probEvent_bind_le_add_bad_of_disagree' {α β γ : Type} {mx : ProbComp α}
    {my : α → ProbComp β} {oc : α → ProbComp β} {ob : α → ProbComp γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} [DecidablePred D] {ε : ℝ≥0∞}
    (hbad : ∀ x ∈ support mx, D x → Pr[r | ob x] = 1)
    (h : ∀ x ∈ support mx, ¬ D x → Pr[q | my x] ≤ Pr[q | oc x] + Pr[r | ob x] + ε) :
    Pr[q | mx >>= my] ≤ Pr[q | mx >>= oc] + Pr[r | mx >>= ob] + ε := by
  have := Classical.decPred q
  have := Classical.decPred r
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[q | my x]
      ≤ ∑' x, (Pr[= x | mx] * Pr[q | oc x]
            + Pr[= x | mx] * Pr[r | ob x] + Pr[= x | mx] * ε) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · by_cases hDx : D x
          · calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * 1 := mul_le_mul' le_rfl probEvent_le_one
              _ = Pr[= x | mx] * Pr[r | ob x] := by rw [hbad x hx hDx]
              _ ≤ Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                    + Pr[= x | mx] * ε := le_add_right (le_add_left le_rfl)
          · calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * (Pr[q | oc x] + Pr[r | ob x] + ε) :=
                  mul_le_mul' le_rfl (h x hx hDx)
              _ = Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                    + Pr[= x | mx] * ε := by rw [left_distrib, left_distrib]
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, Pr[= x | mx] * Pr[r | ob x]) + (∑' x, Pr[= x | mx] * ε) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, Pr[= x | mx] * Pr[r | ob x]) + ε := by
        refine add_le_add le_rfl ?_
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left (zero_le _) tsum_probOutput_le_one

/-- **Four-way disagreement+bad additive bind bound.** A merge of
`probEvent_bind_le_add_of_disagree` with the three-world `probEvent_bind_le_add_bad_of_disagree`:
the disagreement set `D` (a *table-level* exceptional set, not a bad event) is charged its full
mass `ε₁`; everywhere off `D` the `my`-world is bounded by the `oc`-world plus the per-shared-sample
bad probability `Pr[r | ob x]` plus the slack `ε₂`. -/
private lemma probEvent_bind_le_add_bad_disagree {α β γ : Type} {mx : ProbComp α}
    {my : α → ProbComp β} {oc : α → ProbComp β} {ob : α → ProbComp γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} [DecidablePred D] {ε₁ ε₂ : ℝ≥0∞}
    (hD : Pr[ D | mx] ≤ ε₁)
    (h : ∀ x ∈ support mx, ¬ D x → Pr[ q | my x] ≤ Pr[ q | oc x] + Pr[ r | ob x] + ε₂) :
    Pr[q | mx >>= my] ≤ Pr[q | mx >>= oc] + Pr[r | mx >>= ob] + ε₁ + ε₂ := by
  have := Classical.decPred q
  have := Classical.decPred r
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[q | my x]
      ≤ ∑' x, (Pr[= x | mx] * Pr[q | oc x]
            + Pr[= x | mx] * Pr[r | ob x] + (if D x then Pr[= x | mx] else 0)
            + Pr[= x | mx] * ε₂) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · by_cases hDx : D x
          · simp only [if_pos hDx]
            calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * 1 := mul_le_mul' le_rfl probEvent_le_one
              _ = Pr[= x | mx] := mul_one _
              _ ≤ Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                    + Pr[= x | mx] + Pr[= x | mx] * ε₂ := by
                  calc Pr[= x | mx]
                      = 0 + 0 + Pr[= x | mx] + 0 := by ring
                    _ ≤ Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                          + Pr[= x | mx] + Pr[= x | mx] * ε₂ := by
                        gcongr <;> exact zero_le _
          · simp only [if_neg hDx, add_zero]
            calc Pr[= x | mx] * Pr[q | my x]
                ≤ Pr[= x | mx] * (Pr[q | oc x] + Pr[r | ob x] + ε₂) :=
                  mul_le_mul' le_rfl (h x hx hDx)
              _ = Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * Pr[r | ob x]
                    + Pr[= x | mx] * ε₂ := by rw [left_distrib, left_distrib]
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, Pr[= x | mx] * Pr[r | ob x])
          + (∑' x, if D x then Pr[= x | mx] else 0) + (∑' x, Pr[= x | mx] * ε₂) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ (∑' x, Pr[= x | mx] * Pr[q | oc x])
          + (∑' x, Pr[= x | mx] * Pr[r | ob x]) + ε₁ + ε₂ := by
        refine add_le_add (add_le_add le_rfl ?_) ?_
        · rw [← probEvent_eq_tsum_ite]; exact hD
        · rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left (zero_le _) tsum_probOutput_le_one

/-! #### Hop B, deliverable 4: the coupled hybrid-vs-single coupling theorem

The coupled hybrid handler `hybridCoupledHandler` and the single-session ideal handler
`singleIdealQueryImpl` evolve their random-oracle cache and session counters in lockstep — they
differ only in the reader oracle's *output bit*. The hybrid reader accepts on a subset of the
single reader's cells, so the only disagreement is the single reader accepting on a non-tag-drawn
cell. Under `HasDistinctUnlinkReaderNonces` that cell is genuinely fresh, and
`probEvent_coupledReader_disagree_le` bounds the per-reader-query gap by
`|TagId| * sessionsPerTag / |Digest|`. -/

/-- Coupling invariant for hop B: a cached column-`n` cell that was *not* produced by the tag draw
of its own session forces the residual computation to make no further reader query at `n`. Tag
draws set the cache cell and the `sessionNonce` record together, so a non-tag-drawn cached cell can
only come from an earlier reader query; `HasDistinctUnlinkReaderNonces` then rules out a second
reader query at that nonce. -/
private def HybridColFresh (oa : UnlinkAdversary TagId Nonce Digest)
    (s : HybridState TagId Nonce sessionsPerTag)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) : Prop :=
  ∀ (n : Nonce) (tag : TagId) (sid : Fin sessionsPerTag),
    (c ((tag, sid), n)).isSome → s.sessionNonce (tag, sid) ≠ some n →
      OracleComp.IsQueryBoundP oa (pReaderNonce n) 0

/-- Write-once invariant for the hybrid session-nonce map: a session that has not yet been used
(its index is at or beyond the session counter) carries no recorded nonce. -/
private def HybridWriteOnce (s : HybridState TagId Nonce sessionsPerTag) : Prop :=
  ∀ (tag : TagId) (sid : Fin sessionsPerTag),
    s.sessionsUsed tag ≤ sid.val → s.sessionNonce (tag, sid) = none

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The initial hybrid state satisfies the write-once invariant: nothing is recorded. -/
private lemma hybridWriteOnce_init :
    HybridWriteOnce (TagId := TagId) (Nonce := Nonce)
      (sessionsPerTag := sessionsPerTag) HybridState.init := by
  intro tag sid _
  rfl

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The empty cache satisfies the coupling invariant vacuously. -/
private lemma hybridColFresh_init (oa : UnlinkAdversary TagId Nonce Digest)
    (s : HybridState TagId Nonce sessionsPerTag) :
    HybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) oa s ∅ := by
  intro n tag sid hsome _
  simp at hsome

/-- **Hop B, core coupling bound.** For any hybrid state `s` and single state `sS` with equal
session counters, sharing a random-oracle cache `c`, the coupled hybrid handler's success
probability is bounded by the single-session ideal handler's plus the reader-slack term
`qR * |TagId| * sessionsPerTag / |Digest|`, provided the adversary has pairwise-distinct reader
nonces (`hdist`), at most `qR` reader queries (`hqR`), and the cache satisfies the coupling
invariants `HybridColFresh`/`HybridWriteOnce`. Proved by induction on the adversary. -/
private lemma hybridCoupled_le_singleIdeal_add_readerSlack_aux [Fintype Digest]
    (oa : UnlinkAdversary TagId Nonce Digest) (qR : ℕ)
    (s : HybridState TagId Nonce sessionsPerTag) (sS : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hcounter : s.sessionsUsed = sS.sessionsUsed)
    (hqR : OracleComp.IsQueryBoundP oa (fun i => i.isRight) qR)
    (hdist : ∀ n : Nonce, OracleComp.IsQueryBoundP oa (pReaderNonce n) 1)
    (hwo : HybridWriteOnce (TagId := TagId) (Nonce := Nonce)
      (sessionsPerTag := sessionsPerTag) s)
    (hfresh : HybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) oa s c) :
    Pr[= true | (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' (s, c)] ≤
      Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' (sS, c)] +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  induction oa using OracleComp.inductionOn generalizing qR s sS c with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    exact le_add_right (le_refl _)
  | query_bind t f ih =>
    rw [hybridCoupled_run'_query_bind', singleIdeal_run'_query_bind']
    cases t with
    | inl tag =>
      -- Tag query: the two handlers are pointwise identical; recurse with `ε₁ = 0`.
      have hqRf : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isRight) qR := by
        intro u
        have := hqR
        rw [OracleComp.isQueryBoundP_query_bind_iff] at this
        simpa using this.2 u
      have hdistf : ∀ u, ∀ n, OracleComp.IsQueryBoundP (f u) (pReaderNonce n) 1 := by
        intro u n
        have := hdist n
        rw [OracleComp.isQueryBoundP_query_bind_iff] at this
        simpa [pReaderNonce] using this.2 u
      have hfreshf : ∀ u, ∀ n, OracleComp.IsQueryBoundP
          (liftM (OracleSpec.query (Sum.inl tag : (UnlinkOracleSpec TagId Nonce Digest).Domain))
            >>= f) (pReaderNonce n) 0 →
          OracleComp.IsQueryBoundP (f u) (pReaderNonce n) 0 := by
        intro u n hb
        rw [OracleComp.isQueryBoundP_query_bind_iff] at hb
        simpa [pReaderNonce] using hb.2 u
      have hcounter_tag : sS.sessionsUsed tag = s.sessionsUsed tag := (congrFun hcounter tag).symm
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · rw [hybridCoupledHandler_tag_run tag (s, c),
          hybridLazyHandler_tag_run_of_lt tag (s, c) hslot,
          singleIdealQueryImpl_tag_run_of_lt tag sS c (hcounter_tag ▸ hslot)]
        dsimp only
        simp only [hcounter_tag]
        set sid := (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) with hsid
        set advH : Nonce → HybridState TagId Nonce sessionsPerTag := fun nonce =>
          { sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1),
            sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) } with hadvH
        set advS : UnlinkState TagId :=
          { sS with sessionsUsed :=
            Function.update sS.sessionsUsed tag (s.sessionsUsed tag + 1) } with hadvS
        -- Reassociate both binds to a shared `mx`.
        set mx : ProbComp (Nonce × Digest ×
            (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :=
          ($ᵗ Nonce) >>= fun n => idealCacheStep c ((tag, sid), n) >>= fun r => pure (n, r)
          with hmx
        have hreassocH :
            (($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
                  ({ sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1),
                     sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) } :
                    HybridState TagId Nonce sessionsPerTag), r.2))
              >>= (fun p => (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
            = mx >>= fun nr =>
                (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨nr.1, nr.2.1⟩ : TagTranscript Nonce Digest)))).run'
                    (advH nr.1, nr.2.2) := by
          rw [hmx]
          simp only [bind_assoc, pure_bind, hadvH, hadvS]
        have hreassocS :
            (($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest), advS, r.2))
              >>= (fun p => (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
            = mx >>= fun nr =>
                (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨nr.1, nr.2.1⟩ : TagTranscript Nonce Digest)))).run'
                    (advS, nr.2.2) := by
          rw [hmx]
          simp only [bind_assoc, pure_bind, hadvH, hadvS]
        rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
        refine le_trans (le_of_eq (congrArg (fun m => probEvent m (· = true)) hreassocH)) ?_
        refine le_trans ?_ (le_of_eq (congrArg (fun z => z +
          ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞))
          (congrArg (fun m => probEvent m (· = true)) hreassocS.symm)))
        refine le_trans (probEvent_bind_le_add_of_disagree (D := fun _ => False)
          (ε₁ := 0)
          (ε₂ := ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞))
          (oc := fun nr => (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag))
            (f (some (⟨nr.1, nr.2.1⟩ : TagTranscript Nonce Digest)))).run' (advS, nr.2.2))
          (by simp) ?_) (le_of_eq (by rw [add_zero]))
        · -- per-point inductive step
          rintro nr hnr -
          obtain ⟨n, hn, r, hr, hnreq⟩ : ∃ n, n ∈ support ($ᵗ Nonce) ∧
              ∃ r, r ∈ support (idealCacheStep c ((tag, sid), n)) ∧ nr = (n, r) := by
            rw [hmx, mem_support_bind_iff] at hnr
            obtain ⟨n, hn, hrest⟩ := hnr
            rw [mem_support_bind_iff] at hrest
            obtain ⟨r, hr, hpure⟩ := hrest
            rw [support_pure, Set.mem_singleton_iff] at hpure
            exact ⟨n, hn, r, hr, hpure⟩
          subst hnreq
          have hcellself : r.2 ((tag, sid), n) = some r.1 :=
            idealCacheStep_cache_self c ((tag, sid), n) r hr
          have hcounter' : (advH n).sessionsUsed = advS.sessionsUsed := by
            rw [hadvH, hadvS]
            dsimp only [HybridState.sessionsUsed]
            rw [hcounter]
          have hwo' : HybridWriteOnce (TagId := TagId) (Nonce := Nonce)
              (sessionsPerTag := sessionsPerTag) (advH n) := by
            intro tag' sid' hle
            simp only [hadvH] at hle ⊢
            by_cases htag : tag' = tag
            · subst htag
              rw [Function.update_self] at hle
              have hne : sid' ≠ sid := by
                intro h; rw [h, hsid] at hle; simp at hle
              rw [Function.update_of_ne (by simp [Prod.ext_iff, hne])]
              exact hwo tag' sid' (by omega)
            · rw [Function.update_of_ne htag] at hle
              rw [Function.update_of_ne (by simp [htag])]
              exact hwo tag' sid' hle
          have hfresh' : HybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag)
              (f (some (⟨n, r.1⟩ : TagTranscript Nonce Digest))) (advH n) r.2 := by
            intro n' tag' sid' hsome hne
            refine hfreshf _ n' ?_
            by_cases hkey : ((tag', sid'), n') = ((tag, sid), n)
            · obtain ⟨hkk, rfl⟩ := Prod.mk.injEq .. ▸ hkey
              obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hkk
              exact absurd (by rw [hadvH]; exact Function.update_self ..) hne
            · have hcoff : r.2 ((tag', sid'), n') = c ((tag', sid'), n') :=
                idealCacheStep_cache_off c ((tag, sid), n) r hr _ hkey
              rw [hcoff] at hsome
              have hsnH : (advH n).sessionNonce (tag', sid') ≠ some n' := hne
              have hsn : s.sessionNonce (tag', sid') ≠ some n' := by
                simp only [hadvH] at hsnH
                by_cases hkey2 : (tag', sid') = (tag, sid)
                · rw [hkey2, hwo tag sid (by simp [hsid])]
                  simp
                · rwa [Function.update_of_ne hkey2] at hsnH
              exact hfresh n' tag' sid' hsome hsn
          have hih := ih (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)) qR (advH n) advS r.2
            hcounter' (hqRf _) (fun n' => hdistf _ n') hwo' hfresh'
          rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput] at hih
          exact hih
      · rw [hybridCoupledHandler_tag_run tag (s, c),
          hybridLazyHandler_tag_run_of_not_lt tag (s, c) hslot,
          singleIdealQueryImpl_tag_run_of_not_lt tag sS c (hcounter_tag ▸ hslot)]
        have hfresh' : HybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (f none) s c := by
          intro n tag' sid' hsome hne
          exact hfreshf none n (hfresh n tag' sid' hsome hne)
        exact ih none qR s sS c hcounter (hqRf none) (fun n => hdistf none n) hwo hfresh'
    | inr transcript =>
      -- Reader query: handlers fold the same column; the output bits may disagree.
      set n₀ := transcript.nonce with hn₀
      rw [hybridCoupledHandler_reader_run transcript (s, c),
        singleIdealQueryImpl_reader_run transcript sS c]
      set cells := (Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
        (fun slot => (slot, transcript.nonce)) with hcells
      have hcellseq : cells = hybridReaderCells (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) transcript := rfl
      -- Budgets after the reader query.
      have hqRsplit := hqR
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hqRsplit
      obtain ⟨hvalid, hbudget⟩ := hqRsplit
      have hqRpos : 0 < qR := by
        rcases hvalid with h | h
        · exact absurd rfl h
        · exact h
      obtain ⟨qR', rfl⟩ : ∃ qR', qR = qR' + 1 := ⟨qR - 1, by omega⟩
      have hqRf : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isRight) qR' := by
        intro u; simpa using hbudget u
      -- the residual budget at `n₀` is exhausted
      have hb0 : ∀ u, OracleComp.IsQueryBoundP (f u) (pReaderNonce n₀) 0 := by
        intro u
        have := hdist n₀
        rw [OracleComp.isQueryBoundP_query_bind_iff] at this
        have h2 := this.2 u
        simp only [pReaderNonce, hn₀, if_pos rfl] at h2
        simpa using h2
      -- off-`n₀` budget transfers to the continuation
      have hbn : ∀ u, ∀ n, n ≠ n₀ → OracleComp.IsQueryBoundP
          (liftM (OracleSpec.query (Sum.inr transcript :
            (UnlinkOracleSpec TagId Nonce Digest).Domain)) >>= f) (pReaderNonce n) 0 →
          OracleComp.IsQueryBoundP (f u) (pReaderNonce n) 0 := by
        intro u n hne hb
        rw [OracleComp.isQueryBoundP_query_bind_iff] at hb
        have h2 := hb.2 u
        have hpfalse : ¬ pReaderNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n
            (Sum.inr transcript) := fun h => hne (h.symm)
        simpa [hpfalse] using h2
      -- `hcol`: at the current reader nonce, no non-tag-drawn cached cell
      have hcol : ∀ (tag : TagId) (sid : Fin sessionsPerTag),
          (c ((tag, sid), n₀)).isSome → s.sessionNonce (tag, sid) = some n₀ := by
        intro tag sid hsome
        by_contra hne
        have hbad := hfresh n₀ tag sid hsome hne
        rw [OracleComp.isQueryBoundP_query_bind_iff] at hbad
        have hp : pReaderNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n₀
            (Sum.inr transcript) := rfl
        rcases hbad.1 with h | h
        · exact h hp
        · exact absurd h (lt_irrefl 0)
      -- reassociate both reader binds to a shared `mx`
      set mx : ProbComp (List Digest ×
          (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :=
        idealCacheMapM cells c with hmx
      set hybBit := hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce transcript
        with hhybBit
      have hreassocH :
          (mx >>= fun rs => pure (ReaderReply.ofBool hybBit, s, rs.2))
            >>= (fun p => (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
          = mx >>= fun rs =>
              (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool hybBit))).run' (s, rs.2) := by
        rw [bind_assoc]
        refine bind_congr fun rs => ?_
        rw [pure_bind]
      have hreassocS :
          (mx >>= fun rs =>
              pure (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), sS, rs.2))
            >>= (fun p => (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
          = mx >>= fun rs =>
              (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run'
                (sS, rs.2) := by
        rw [bind_assoc]
        refine bind_congr fun rs => ?_
        rw [pure_bind]
      rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
      refine le_trans (le_of_eq (congrArg (fun m => probEvent m (· = true)) hreassocH)) ?_
      refine le_trans ?_ (le_of_eq (congrArg (fun z => z +
        (((qR' + 1) * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
          (Fintype.card Digest : ℝ≥0∞))
        (congrArg (fun m => probEvent m (· = true)) hreassocS.symm)))
      classical
      set D : List Digest × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache → Prop :=
        fun rs => decide (∃ d ∈ rs.1, d = transcript.auth) = true ∧ hybBit = false with hD
      have hslackeq :
          (((qR' + 1) * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
              (Fintype.card Digest : ℝ≥0∞)
            = (Fintype.card TagId * sessionsPerTag : ℕ) / (Fintype.card Digest : ℝ≥0∞)
              + ((qR' * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
                (Fintype.card Digest : ℝ≥0∞) := by
        rw [← ENNReal.add_div]
        congr 1
        push_cast
        ring
      refine le_trans (probEvent_bind_le_add_of_disagree (D := D)
        (ε₁ := (Fintype.card TagId * sessionsPerTag : ℕ) / (Fintype.card Digest : ℝ≥0∞))
        (ε₂ := ((qR' * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
          (Fintype.card Digest : ℝ≥0∞))
        (oc := fun rs => (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag))
          (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run' (sS, rs.2))
        ?_ ?_) (le_of_eq (by rw [add_assoc, ← hslackeq]))
      · -- the disagreement probability is bounded by the per-query slack
        have hdis := probEvent_coupledReader_disagree_le (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce transcript hcol
        rw [hmx, hcellseq]
        exact hdis
      · -- off the disagreement set, the bits agree; recurse with `ε₂ = 0`
        intro rs hrs hDrs
        have hrsmem : rs ∈ support (idealCacheMapM cells c) := by rw [hmx] at hrs; exact hrs
        -- `hybBit → single bit`
        have himp : hybBit = true →
            decide (∃ d ∈ rs.1, d = transcript.auth) = true := by
          intro hht
          rw [hhybBit, hybridCacheAccepts, decide_eq_true_eq] at hht
          obtain ⟨tag, sid, hsn, hcv⟩ := hht
          rw [decide_eq_true_eq]
          refine ⟨transcript.auth, ?_, rfl⟩
          have hcellmem : ((tag, sid), n₀) ∈ cells := by
            rw [hcells]
            exact List.mem_map.mpr ⟨(tag, sid), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩
          have hcoff : rs.2 ((tag, sid), n₀) = c ((tag, sid), n₀) :=
            idealCacheMapM_cache_off cells c rs hrsmem ((tag, sid), n₀) (by rw [hcv]; rfl)
          have hrs1 : rs.1 = cells.map (OracleComp.tableExtending rs.2
              (fun _ => transcript.auth)) :=
            idealCacheMapM_support cells c rs hrsmem (fun _ => transcript.auth)
          rw [hrs1]
          refine List.mem_map.mpr ⟨((tag, sid), n₀), hcellmem, ?_⟩
          rw [OracleComp.tableExtending, hcoff, hcv, Option.getD_some]
        -- the bits are equal
        have hbiteq : decide (∃ d ∈ rs.1, d = transcript.auth) = hybBit := by
          have hDrs' : ¬ (decide (∃ d ∈ rs.1, d = transcript.auth) = true ∧ hybBit = false) :=
            hDrs
          rcases hb : hybBit with _ | _
          · -- hybBit false: `¬ D rs` forces single false
            rcases hd : decide (∃ d ∈ rs.1, d = transcript.auth) with _ | _
            · rfl
            · exact absurd ⟨hd, hb⟩ hDrs'
          · -- hybBit true: single true by `himp`
            exact himp hb
        beta_reduce
        rw [hbiteq]
        -- recurse on the shared continuation `f (ReaderReply.ofBool hybBit)`
        rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput]
        have hfresh' : HybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (f (ReaderReply.ofBool hybBit)) s rs.2 := by
          intro n tag sid hsome hne
          by_cases hnn : n = n₀
          · subst hnn; exact hb0 _
          · have hcellnotmem : ((tag, sid), n) ∉ cells := by
              rw [hcells]
              simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, not_exists]
              intro slot hslot
              exact hnn (congrArg Prod.snd hslot).symm
            have hcoff : rs.2 ((tag, sid), n) = c ((tag, sid), n) :=
              idealCacheMapM_cache_not_mem cells c rs hrsmem ((tag, sid), n) hcellnotmem
            rw [hcoff] at hsome
            exact hbn _ n hnn (hfresh n tag sid hsome hne)
        have hdistcont : ∀ n, OracleComp.IsQueryBoundP (f (ReaderReply.ofBool hybBit))
            (pReaderNonce n) 1 := by
          intro n
          by_cases hnn : n = n₀
          · subst hnn
            exact (hb0 (ReaderReply.ofBool hybBit)).mono (Nat.zero_le 1)
          · have := hdist n
            rw [OracleComp.isQueryBoundP_query_bind_iff] at this
            have h2 := this.2 (ReaderReply.ofBool hybBit)
            have hpf : ¬ pReaderNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                n (Sum.inr transcript) := fun h => hnn h.symm
            simpa [hpf] using h2
        exact ih (ReaderReply.ofBool hybBit) qR' s sS rs.2 hcounter (hqRf _)
          hdistcont hwo hfresh'

/-- **Hop B.** Under `HasDistinctUnlinkReaderNonces` and a reader-query bound `qReader`, the hybrid
world `H` (run as the lazy hybrid handler from the initial state) succeeds with probability at most
that of the single-session ideal world plus the reader-slack term
`qReader * |TagId| * sessionsPerTag / |Digest|`.

The lazy hybrid handler and the coupled hybrid handler agree in distribution
(`probOutput_hybridCoupled_run'_eq_lazy`), and the coupled handler is bounded against
`singleIdealQueryImpl` by `hybridCoupled_le_singleIdeal_add_readerSlack_aux`; the empty cache and
initial state satisfy the coupling invariants `hybridColFresh_init` / `hybridWriteOnce_init`. -/
theorem hybrid_le_singleIdeal_add_readerSlack [Fintype Nonce] [Fintype Digest]
    (adversary : UnlinkAdversary TagId Nonce Digest) (qReader : ℕ)
    (hdist : HasDistinctUnlinkReaderNonces adversary)
    (hqReader : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) qReader) :
    Pr[= true | (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (HybridState.init, ∅)] ≤
      Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] +
      ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  rw [← probOutput_hybridCoupled_run'_eq_lazy adversary]
  refine hybridCoupled_le_singleIdeal_add_readerSlack_aux adversary qReader
    HybridState.init UnlinkState.init ∅ rfl hqReader
    ((hasDistinctUnlinkReaderNonces_iff adversary).mp hdist)
    (hybridWriteOnce_init) (hybridColFresh_init adversary HybridState.init)

/-! ### Hop A: the multiple-vs-hybrid cache coupling

Hop A couples the multiple-session ideal handler `multipleIdealQueryImpl` (a lazy random oracle
over `TagId × Nonce`, whose tag oracle reuses the cell `(tag, nonce)` whenever two sessions of one
tag draw the same nonce) against the per-session-fresh hybrid handler `hybridLazyHandler` (a lazy
random oracle over `(TagId × Fin sessionsPerTag) × Nonce`, whose tag oracle always consults a fresh
session slot `(tag, sid)`). Off the within-tag nonce collision the two worlds produce the same
fresh-uniform digest, so the gap is charged to two terms: the collision goes into the bad-world
probability `Pr[bad]` and the reader-cell asymmetry goes into the reader-slack
`qReader * |TagId| / |Digest|`.

The coupling is threaded by `MHBInv`, a state relation on the three handler states (the multiple
cache, the hybrid cache + session-nonce map, and the bad-world `responses` cache). -/

/-- **Hop A coupling invariant.** Relates a multiple-session ideal state `sM`, a hybrid-world state
`sH`, and a bad-event state `sB`. It records that:

* the three worlds' session counters agree (reader-stable, untouched by reader queries);
* the bad flag has not yet fired;
* the multiple cache and the bad-world `responses` cache have the same support — a `(tag, nonce)`
  pair is cached in the multiple world exactly when it has a recorded random-function response in
  the bad world (off `bad`, the bad world has drawn each cached pair exactly once, so its response
  list is a singleton);
* the multiple cache cell at a *tag-drawn* nonce mirrors the corresponding per-session hybrid cell:
  whenever a hybrid session `(tag, sid)` recorded the draw `sn (tag, sid) = some nonce`, the
  multiple cell `(tag, nonce)` and the hybrid cell `((tag, sid), nonce)` carry the same digest;
* the hybrid session-nonce map is collision-free per tag: at most one session of each tag has
  drawn any given nonce (this is exactly the off-collision regime);
* the hybrid session-nonce map is write-once: a session at or beyond the session counter has no
  recorded nonce;
* the hybrid cache only records cells produced by a tag draw: a cached hybrid cell
  `((tag, sid), nonce)` has `sessionNonce (tag, sid) = some nonce`;
* conversely the hybrid cache and session-nonce map are consistent: a recorded draw
  `sessionNonce (tag, sid) = some nonce` has the cell `((tag, sid), nonce)` cached. -/
private def MHBInv
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) : Prop :=
  sM.1.sessionsUsed = sH.1.sessionsUsed ∧
    sM.1.sessionsUsed = sB.sessionsUsed ∧
    sB.bad = false ∧
    (∀ tag n, (sM.2 (tag, n)).isSome ↔ (sB.responses (tag, n)).isSome) ∧
    (∀ tag sid n, sH.1.sessionNonce (tag, sid) = some n →
      sM.2 (tag, n) = sH.2 ((tag, sid), n)) ∧
    (∀ tag sid₁ sid₂ n, sH.1.sessionNonce (tag, sid₁) = some n →
      sH.1.sessionNonce (tag, sid₂) = some n → sid₁ = sid₂) ∧
    (∀ tag (sid : Fin sessionsPerTag), sH.1.sessionsUsed tag ≤ sid.val →
      sH.1.sessionNonce (tag, sid) = none) ∧
    (∀ tag sid n, (sH.2 ((tag, sid), n)).isSome →
      sH.1.sessionNonce (tag, sid) = some n) ∧
    (∀ tag sid n, sH.1.sessionNonce (tag, sid) = some n →
      (sH.2 ((tag, sid), n)).isSome)

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The three initial states satisfy the hop-A coupling invariant: counters are all zero, the bad
flag is unset, all caches and the session-nonce map are empty. -/
private lemma MHBInv_init :
    MHBInv (TagId := TagId) (Nonce := Nonce) (Digest := Digest) (sessionsPerTag := sessionsPerTag)
      (UnlinkState.init, ∅) (HybridState.init, ∅) UnlinkBadState.init := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tag n; simp [UnlinkBadState.init]
  · intro tag sid n h; exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])
  · intro tag sid₁ sid₂ n h; exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])
  · intro tag sid _; rfl
  · intro tag sid n h; exact absurd h (by simp)
  · intro tag sid n h; exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])

/-- The list of multiple-world cells inspected by a reader query at `transcript.nonce`: one cell
`(tag, transcript.nonce)` per tag. -/
private noncomputable def multipleReaderCells (transcript : TagTranscript Nonce Digest) :
    List (TagId × Nonce) :=
  (Finset.univ : Finset TagId).toList.map (fun tag => (tag, transcript.nonce))

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The multiple-world reader-cell list is duplicate-free. -/
private lemma multipleReaderCells_nodup (transcript : TagTranscript Nonce Digest) :
    (multipleReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      transcript).Nodup := by
  unfold multipleReaderCells
  refine (Finset.univ : Finset TagId).nodup_toList.map ?_
  intro a b hab
  simpa using hab

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The multiple-world reader-cell list has exactly `|TagId|` cells. -/
private lemma multipleReaderCells_length (transcript : TagTranscript Nonce Digest) :
    (multipleReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      transcript).length = Fintype.card TagId := by
  unfold multipleReaderCells
  rw [List.length_map, Finset.length_toList, Finset.card_univ]

omit [Nonempty TagId] [SampleableType Nonce] in
/-- **Per-reader-query multiple-vs-hybrid disagreement bound.** Fix a multiple cache `cM`, a hybrid
cache `cH` and a session-nonce map `sn`. Suppose every multiple cell `(tag, transcript.nonce)` that
is *already cached* was produced by a tag draw — recorded in `sn` (`hcol`) — and that every
tag-drawn cell of the multiple cache mirrors the hybrid cache (`hcorr`, the `MHBInv` cache
correspondence). Then, folding `idealCacheStep` over the `|TagId|` multiple reader cells, the
probability that the multiple reader accepts while the hybrid reader (`hybridCacheAccepts`) rejects
is at most `|TagId| / |Digest|`: the only way they disagree is a fresh draw at a never-drawn cell
hitting the authenticator, bounded by `probEvent_idealCacheMapM_mem_le`. -/
private lemma probEvent_multipleReader_disagree_le [Fintype Digest]
    (cM : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (cH : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (transcript : TagTranscript Nonce Digest)
    (hcol : ∀ tag, (cM (tag, transcript.nonce)).isSome →
      ∃ sid, sn (tag, sid) = some transcript.nonce)
    (hcorr : ∀ tag sid n, sn (tag, sid) = some n → cM (tag, n) = cH ((tag, sid), n)) :
    Pr[fun rs : List Digest × ((TagId × Nonce) →ₒ Digest).QueryCache =>
        decide (∃ d ∈ rs.1, d = transcript.auth) = true ∧
          hybridCacheAccepts (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) cH sn transcript = false |
        idealCacheMapM (multipleReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          transcript) cM] ≤
      (Fintype.card TagId : ℕ) / (Fintype.card Digest : ℝ≥0∞) := by
  classical
  rw [← multipleReaderCells_length (TagId := TagId) (Digest := Digest) transcript]
  push_cast
  refine le_trans (probEvent_mono fun rs _ hrs => ?_)
    (probEvent_idealCacheMapM_mem_le _
      (multipleReaderCells_nodup (TagId := TagId) (Digest := Digest) transcript) cM
      transcript.auth)
  obtain ⟨haccept, hreject⟩ := hrs
  rw [decide_eq_true_eq] at haccept
  refine ⟨haccept.1, fun cell hcell hcc => ?_⟩
  obtain ⟨tag, rfl⟩ : ∃ tag, cell = (tag, transcript.nonce) := by
    unfold multipleReaderCells at hcell
    rw [List.mem_map] at hcell
    obtain ⟨tag, _, rfl⟩ := hcell
    exact ⟨tag, rfl⟩
  -- the cell `(tag, transcript.nonce)` is cached and equals `auth`; it must be tag-drawn
  obtain ⟨sid, hsid⟩ := hcol tag (by rw [hcc]; rfl)
  rw [hybridCacheAccepts, decide_eq_false_iff_not] at hreject
  refine hreject ⟨tag, sid, hsid, ?_⟩
  rw [← hcorr tag sid transcript.nonce hsid, hcc]

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Hop A, off-collision tag-step invariant preservation.** Given `MHBInv sM sH sB`, a free slot
`hslot`, an off-collision nonce `n` (`sM.2 (tag, n) = none`) and a digest `u`, the three
post-states produced by the off-collision tag step — the multiple, hybrid and bad worlds all
caching the fresh digest `u` for tag `tag` at nonce `n` — again satisfy `MHBInv`. -/
private lemma MHBInv_tag_step
    (tag : TagId) (n : Nonce) (u : Digest)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : MHBInv (sessionsPerTag := sessionsPerTag) sM sH sB)
    (hslot : sM.1.sessionsUsed tag < sessionsPerTag)
    (hfresh : sM.2 (tag, n) = none) :
    MHBInv (sessionsPerTag := sessionsPerTag)
      ({ sM.1 with sessionsUsed :=
          Function.update sM.1.sessionsUsed tag (sM.1.sessionsUsed tag + 1) },
        sM.2.cacheQuery (tag, n) u)
      (({ sessionsUsed :=
            Function.update sH.1.sessionsUsed tag (sH.1.sessionsUsed tag + 1),
          sessionNonce := Function.update sH.1.sessionNonce
            (tag, ⟨sM.1.sessionsUsed tag, hslot⟩) (some n) } :
          HybridState TagId Nonce sessionsPerTag),
        sH.2.cacheQuery ((tag, ⟨sM.1.sessionsUsed tag, hslot⟩), n) u)
      ({ sessionsUsed :=
            Function.update sB.sessionsUsed tag (sB.sessionsUsed tag + 1),
          responses := sB.responses.cacheQuery (tag, n)
            (u :: Option.getD (sB.responses (tag, n)) []),
          bad := sB.bad || (sB.responses (tag, n)).isSome } :
          UnlinkBadState TagId Nonce Digest) := by
  obtain ⟨hcMH, hcMB, hbad, hsupp, hcorr, hcollfree, hwo, hrec, hcons⟩ := hInv
  set sid : Fin sessionsPerTag := ⟨sM.1.sessionsUsed tag, hslot⟩ with hsid
  -- the bad-world `responses` cell `(tag, n)` is empty off-collision
  have hBfresh : sB.responses (tag, n) = none := by
    have hni := hsupp tag n
    rw [hfresh] at hni
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at hni
    exact Option.not_isSome_iff_eq_none.mp hni
  -- the hybrid cell `((tag, sid), n)` is empty: `sid` is the unused current slot
  have hHfresh : sH.2 ((tag, sid), n) = none := by
    by_contra hne
    have hsnsome := hrec tag sid n (Option.isSome_iff_ne_none.mpr hne)
    rw [hwo tag sid (by rw [← hcMH, hsid])] at hsnsome
    exact absurd hsnsome (by simp)
  -- no session of `tag` had drawn `n` before (else the multiple cell would be cached)
  have hnodrawn : ∀ sid', sH.1.sessionNonce (tag, sid') ≠ some n := by
    intro sid' hsn'
    have := hcorr tag sid' n hsn'
    rw [hfresh] at this
    exact absurd (hcons tag sid' n hsn') (by rw [← this]; simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [HybridState.sessionsUsed]; rw [hcMH]
  · dsimp only; rw [hcMB]
  · rw [hbad, hBfresh]; rfl
  · -- multiple/bad cache support
    intro tag' n'
    dsimp only
    by_cases hkey : (tag', n') = (tag, n)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
      rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]; simp
    · rw [QueryCache.cacheQuery_of_ne _ _ hkey, QueryCache.cacheQuery_of_ne _ _ hkey]
      exact hsupp tag' n'
  · -- multiple/hybrid cache correspondence
    intro tag' sid' n' hsn'
    dsimp only at hsn' ⊢
    by_cases hts : (tag', sid') = (tag, sid)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hts
      rw [Function.update_self] at hsn'
      obtain rfl : n' = n := (Option.some.inj hsn').symm
      rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
    · rw [Function.update_of_ne hts] at hsn'
      by_cases hmkey : (tag', n') = (tag, n)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmkey
        exact absurd hsn' (hnodrawn sid')
      · rw [QueryCache.cacheQuery_of_ne _ _ hmkey]
        have hhkey : ((tag', sid'), n') ≠ ((tag, sid), n) := fun h => hts (congrArg Prod.fst h)
        rw [QueryCache.cacheQuery_of_ne _ _ hhkey]
        exact hcorr tag' sid' n' hsn'
  · -- collision-freeness
    intro tag' s₁ s₂ n' h₁ h₂
    dsimp only at h₁ h₂
    by_cases ht1 : (tag', s₁) = (tag, sid)
    · obtain ⟨htg, hs₁⟩ := Prod.mk.inj ht1
      subst hs₁; subst htg
      rw [Function.update_self] at h₁
      obtain rfl : n' = n := (Option.some.inj h₁).symm
      by_cases ht2 : (tag', s₂) = (tag', sid)
      · exact ((Prod.mk.inj ht2).2).symm
      · rw [Function.update_of_ne ht2] at h₂
        exact absurd h₂ (hnodrawn s₂)
    · rw [Function.update_of_ne ht1] at h₁
      by_cases ht2 : (tag', s₂) = (tag, sid)
      · obtain ⟨htg, hs₂⟩ := Prod.mk.inj ht2
        subst hs₂; subst htg
        rw [Function.update_self] at h₂
        obtain rfl : n' = n := (Option.some.inj h₂).symm
        exact absurd h₁ (hnodrawn s₁)
      · rw [Function.update_of_ne ht2] at h₂
        exact hcollfree tag' s₁ s₂ n' h₁ h₂
  · -- write-once
    intro tag' sid' hle
    dsimp only at hle ⊢
    by_cases htag : tag' = tag
    · subst htag
      rw [Function.update_self] at hle
      have hne : sid' ≠ sid := by
        intro h; rw [h, hsid] at hle; rw [← hcMH] at hle; simp only [Fin.val] at hle; omega
      rw [Function.update_of_ne (by simp [Prod.ext_iff, hne])]
      exact hwo tag' sid' (by omega)
    · rw [Function.update_of_ne htag] at hle
      rw [Function.update_of_ne (by simp [htag])]
      exact hwo tag' sid' hle
  · -- cache-recorded
    intro tag' sid' n' hsome
    dsimp only at hsome ⊢
    by_cases hhkey : ((tag', sid'), n') = ((tag, sid), n)
    · obtain ⟨hkk, rfl⟩ := Prod.mk.inj hhkey
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkk
      rw [Function.update_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hhkey] at hsome
      have hsn := hrec tag' sid' n' hsome
      have hts : (tag', sid') ≠ (tag, sid) := by
        intro h
        rw [h] at hsn
        rw [hwo tag sid (by rw [← hcMH, hsid])] at hsn
        exact absurd hsn (by simp)
      rw [Function.update_of_ne hts]
      exact hsn
  · -- cache-consistency
    intro tag' sid' n' hsn'
    dsimp only at hsn' ⊢
    by_cases hts : (tag', sid') = (tag, sid)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hts
      rw [Function.update_self] at hsn'
      obtain rfl : n' = n := (Option.some.inj hsn').symm
      rw [QueryCache.cacheQuery_self]; simp
    · rw [Function.update_of_ne hts] at hsn'
      have hhkey : ((tag', sid'), n') ≠ ((tag, sid), n) := fun h => hts (congrArg Prod.fst h)
      rw [QueryCache.cacheQuery_of_ne _ _ hhkey]
      exact hcons tag' sid' n' hsn'

/-! ### Hop A: the instrumented multiple-session handler

`multipleIdealQueryImpl`'s state — a lazy random-oracle cache over `(TagId × Nonce)` — cannot
express "a within-tag tag–tag nonce collision has occurred": the cache key does not record whether
a cell was written by a tag draw or by a reader query, and a collision is history. The
instrumented handler `multipleBadQueryImpl` carries, beside the multiple-ideal state, a full
bad-world `UnlinkBadState` whose `bad` flag fires exactly on a tag-written cell collision. Its
*output bit* is identical to `multipleIdealQueryImpl`'s — the instrumentation only threads an extra
state component — so `Pr[= true]` is unchanged (`probOutput_multipleBad_run'_eq_multipleIdeal`),
while `Pr[bad]` is exactly the bad-world collision probability
(`probEvent_multipleBad_bad_eq_unlinkBad`). -/

/-- Joint handler state for the instrumented multiple-session world: the multiple-ideal state
(session counters + lazy random-oracle cache over `TagId × Nonce`) paired with a full bad-world
`UnlinkBadState` whose `responses` cache and `bad` flag detect within-tag nonce collisions. -/
abbrev MultipleBadState (TagId Nonce Digest : Type) (sessionsPerTag : ℕ) : Type :=
  (UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) ×
    UnlinkBadState TagId Nonce Digest

/-- Bad-world state advance on a tag query: given the previous bad state `sB` and the transcript
the multiple-ideal tag oracle produced, advance `sB` exactly as `unlinkBadTagQueryImpl` would —
recording the drawn digest and firing `bad` on a repeat `(tag, nonce)`. A `none` transcript (slot
exhausted) leaves `sB` untouched. -/
def multipleBadAdvance (tag : TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (r : Option (TagTranscript Nonce Digest)) : UnlinkBadState TagId Nonce Digest :=
  match r with
  | none => sB
  | some tr =>
      { sessionsUsed := Function.update sB.sessionsUsed tag (sB.sessionsUsed tag + 1)
        responses := sB.responses.cacheQuery (tag, tr.nonce)
          (tr.auth :: Option.getD (sB.responses (tag, tr.nonce)) [])
        bad := sB.bad || (sB.responses (tag, tr.nonce)).isSome }

/-- Instrumented multiple-session handler: runs `multipleIdealQueryImpl` on the multiple-ideal
component and, on a tag query, advances the bad-world component via `multipleBadAdvance`. Reader
queries leave the bad-world component untouched. The first projection of the output equals
`multipleIdealQueryImpl`'s output. -/
noncomputable def multipleBadQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (MultipleBadState TagId Nonce Digest sessionsPerTag) ProbComp) :=
  fun q => fun p => match q with
    | Sum.inl tag =>
        (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) p.1 >>= fun r =>
          pure (r.1, (r.2.1, r.2.2), multipleBadAdvance tag p.2 r.1)
    | Sum.inr transcript =>
        (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) p.1 >>= fun r =>
          pure (r.1, (r.2.1, r.2.2), p.2)

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `multipleBadQueryImpl` on a tag query: the multiple-ideal tag step with the bad-world component
advanced by `multipleBadAdvance`. -/
private lemma multipleBadQueryImpl_tag_run (tag : TagId)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) s =
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) s.1 >>= fun r =>
        pure (r.1, (r.2.1, r.2.2), multipleBadAdvance tag s.2 r.1) := rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `multipleBadQueryImpl` on a reader query: the multiple-ideal reader step, bad-world component
untouched. -/
private lemma multipleBadQueryImpl_reader_run (transcript : TagTranscript Nonce Digest)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) s =
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) s.1 >>= fun r =>
        pure (r.1, (r.2.1, r.2.2), s.2) := rfl

open OracleComp.ProgramLogic.Relational in
omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- **Hop A, output equivalence.** The instrumented handler `multipleBadQueryImpl` produces the
same output distribution as `multipleIdealQueryImpl`: the bad-world component it threads beside the
multiple-ideal state never feeds back into the output bit. Hence `Pr[= true]` is unchanged. -/
private lemma probOutput_multipleBad_run'_eq_multipleIdeal
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) :
    Pr[= true | (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run' (s, sB)] =
      Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run' s] := by
  have hrt : RelTriple
      ((simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) adversary).run' (s, sB))
      ((simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) adversary).run' s)
      (EqRel Bool) := by
    refine relTriple_simulateQ_run'
      (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag))
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag))
      (fun s₁ s₂ => s₁.1 = s₂) adversary ?_ (s, sB) s rfl
    intro t s₁ s₂ hs
    -- the head: `multipleBadQueryImpl t s₁` is `multipleIdealQueryImpl t s₁.1 >>= pure (…)`
    subst hs
    cases t with
    | inl tag =>
      show RelTriple
        ((multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) s₁.1 >>= fun r =>
          pure (r.1, (r.2.1, r.2.2), multipleBadAdvance tag s₁.2 r.1))
        ((multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) s₁.1) _
      refine relTriple_of_evalDist_eq_right
        (congrArg evalDist (bind_pure ((multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) s₁.1))) ?_
      refine relTriple_bind (relTriple_refl _) ?_
      rintro a b rfl
      exact relTriple_pure_pure ⟨rfl, rfl⟩
    | inr transcript =>
      show RelTriple
        ((multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) s₁.1 >>= fun r =>
          pure (r.1, (r.2.1, r.2.2), s₁.2))
        ((multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) s₁.1) _
      refine relTriple_of_evalDist_eq_right
        (congrArg evalDist (bind_pure ((multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) s₁.1))) ?_
      refine relTriple_bind (relTriple_refl _) ?_
      rintro a b rfl
      exact relTriple_pure_pure ⟨rfl, rfl⟩
  exact probOutput_eq_of_relTriple_eqRel hrt true

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The bad flag threaded by `multipleBadQueryImpl` is monotone under a single per-query step:
started from a `MultipleBadState` whose bad flag is set, every output state still has it set.
`multipleBadAdvance` only ever OR-s into the flag, and reader queries leave the bad-world component
untouched. -/
private lemma multipleBadQueryImpl_step_preserves_bad
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) (hbad : s.2.bad = true) :
    ∀ z ∈ support ((multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t) s), z.2.2.bad = true := by
  cases t with
  | inl tag =>
    intro z hz
    rw [multipleBadQueryImpl_tag_run tag s] at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    cases hr : r.1 with
    | none => simp [multipleBadAdvance, hr, hbad]
    | some tr => simp [multipleBadAdvance, hr, hbad]
  | inr transcript =>
    intro z hz
    rw [multipleBadQueryImpl_reader_run transcript s] at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    exact hbad

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Bad monotonicity for a full `simulateQ multipleBadQueryImpl` run: started from a state whose
bad flag is set, every reachable output state keeps it set. This is the `hmono` hypothesis of the
heterogeneous bad+slack `simulateQ` rule. -/
private lemma multipleBadQueryImpl_run_preserves_bad {α : Type}
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) (hbad : s.2.bad = true) :
    ∀ z ∈ support ((simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run s), z.2.2.bad = true := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b =>
    intro z hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz; exact hbad
  | query_bind t f ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    exact ih p.1 p.2 (multipleBadQueryImpl_step_preserves_bad t s hbad p hp) z hz

/-! ### Hop A: spare uniform draws are distribution-neutral

The hop-A coupling pairs each multiple-cache cell written by a *reader* query with a reserved
hybrid "spare" digest. Operationally the hybrid side draws those spares and discards them. The
lemma below is the soundness core making that free: appending any failure-free probabilistic
prefix to a computation — in particular a fold of fresh uniform digest draws via
`idealCacheMapM` — leaves the output distribution unchanged. `ProbComp` never fails
(`probFailure_eq_zero`), so a discarded draw cannot shift any output probability. -/

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Appending a failure-free probabilistic prefix and discarding its result is
distribution-neutral: `𝒟[mx >>= fun _ => my] = 𝒟[my]`. Since every `ProbComp` has zero failure
probability, the discarded draw `mx` contributes only the constant factor `1`. -/
private lemma evalDist_bind_const_eq {α β : Type} (mx : ProbComp α) (my : ProbComp β) :
    𝒟[mx >>= fun _ => my] = 𝒟[my] := by
  refine evalDist_ext fun y => ?_
  rw [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- **Spare draws are distribution-neutral.** Folding `idealCacheStep` over an arbitrary list of
domain points — drawing a fresh uniform digest at every uncached cell — and then discarding the
result leaves the output distribution unchanged. This is the soundness core of the hop-A
spare-draws coupling: the hybrid reader may draw `|TagId|` spare digests it never reads, matching
the cells the multiple reader writes, without shifting any output probability. -/
private lemma evalDist_idealCacheMapM_bind_const_eq {D β : Type} [DecidableEq D]
    (l : List D) (c : (D →ₒ Digest).QueryCache) (my : ProbComp β) :
    𝒟[idealCacheMapM l c >>= fun _ => my] = 𝒟[my] :=
  evalDist_bind_const_eq (idealCacheMapM l c) my

end EagerComposed

/-! ### Hop A: the multiple-vs-hybrid coupling relation

The heterogeneous bad+slack `simulateQ` rule couples the instrumented multiple handler
`multipleBadQueryImpl` (state `MultipleBadState`, the multiple-ideal state paired with the
bad-world `UnlinkBadState`) against the lazy hybrid handler `hybridLazyHandler` (state
`HybridState × QueryCache`). `MHBRel` repackages the three-way coupling invariant `MHBInv` —
which relates a multiple-ideal state, a hybrid state and a bad-world state — as the binary
relation the rule expects, by pairing the multiple-ideal and bad-world components inside the
`MultipleBadState`. -/

/-- Hop-A coupling relation for the heterogeneous bad+slack `simulateQ` rule: relate a
`MultipleBadState` (a multiple-ideal state `s₁.1` together with a bad-world state `s₁.2`) and a
lazy-hybrid state `s₂` exactly when the underlying three components satisfy `MHBInv`. -/
private def MHBRel
    (s₁ : MultipleBadState TagId Nonce Digest sessionsPerTag)
    (s₂ : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) : Prop :=
  MHBInv (sessionsPerTag := sessionsPerTag) s₁.1 s₂ s₁.2

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The initial `MultipleBadState` and lazy-hybrid state are `MHBRel`-related. -/
private lemma MHBRel_init :
    MHBRel (TagId := TagId) (Nonce := Nonce) (Digest := Digest) (sessionsPerTag := sessionsPerTag)
      ((UnlinkState.init, ∅), UnlinkBadState.init) (HybridState.init, ∅) :=
  MHBInv_init

/-! ### Hop A: the reader-aware coupling relation `HopACoupling`

`MHBInv`/`MHBRel` is *insufficient* for hop A: its clause
`(sM.2 (tag, n)).isSome ↔ (sB.responses (tag, n)).isSome` couples the multiple-ideal cache
one-to-one with the bad-world `responses` cache. But the multiple-session *reader* oracle writes
the multiple cache — `multipleIdealQueryImpl_reader_run` folds `idealCacheMapM`, caching every
`(tag, n)` cell it inspects — while leaving the bad-world `responses` untouched
(`multipleBadQueryImpl_reader_run`). So after one reader query that biconditional is broken.

`HopACoupling` is the reader-aware replacement. It distinguishes multiple-cache cells written by
*tag* queries from those written by *reader* queries: a cell `(tag, n)` is *tag-written* exactly
when some hybrid session recorded the draw, `∃ sid, sH.sessionNonce (tag, sid) = some n`. The
bad-world `responses` cache then mirrors precisely the *tag-written* cells (clause `hbadcol`),
not the whole multiple cache — so a reader query, which writes only reader cells, preserves it.
The cache correspondence `hcorr` already quantifies only over recorded sessions, hence is itself
reader-stable: reader-written cells (whose nonce is in no session) are simply not constrained. -/

/-- Reader-aware hop-A coupling invariant relating a multiple-ideal state `sM`
(`UnlinkState × multiple cache`), a lazy-hybrid state `sH` (`HybridState × hybrid cache`) and a
bad-world state `sB` (`UnlinkBadState`).

The clauses are those of `MHBInv` except that the multiple/bad cache biconditional is replaced by
`hbadcol`: the bad-world `responses` cache holds an entry at `(tag, n)` *exactly* for the
tag-written cells — those `n` recorded by some session of `tag`. This makes the invariant stable
under reader queries, which write the multiple cache but not the bad-world or session-nonce
components. -/
private def HopACoupling
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) : Prop :=
  sM.1.sessionsUsed = sH.1.sessionsUsed ∧
    sM.1.sessionsUsed = sB.sessionsUsed ∧
    sB.bad = false ∧
    (∀ tag n, (sB.responses (tag, n)).isSome ↔
      ∃ sid, sH.1.sessionNonce (tag, sid) = some n) ∧
    (∀ tag sid n, sH.1.sessionNonce (tag, sid) = some n →
      sM.2 (tag, n) = sH.2 ((tag, sid), n)) ∧
    (∀ tag sid₁ sid₂ n, sH.1.sessionNonce (tag, sid₁) = some n →
      sH.1.sessionNonce (tag, sid₂) = some n → sid₁ = sid₂) ∧
    (∀ tag (sid : Fin sessionsPerTag), sH.1.sessionsUsed tag ≤ sid.val →
      sH.1.sessionNonce (tag, sid) = none) ∧
    (∀ tag sid n, (sH.2 ((tag, sid), n)).isSome →
      sH.1.sessionNonce (tag, sid) = some n) ∧
    (∀ tag sid n, sH.1.sessionNonce (tag, sid) = some n →
      (sH.2 ((tag, sid), n)).isSome)

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The three initial states satisfy the reader-aware hop-A coupling: counters are all zero, the
bad flag is unset, and all caches and the session-nonce map are empty. -/
private lemma HopACoupling_init :
    HopACoupling (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)
      (UnlinkState.init, ∅) (HybridState.init, ∅) UnlinkBadState.init := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tag n
    simp only [UnlinkBadState.init, QueryCache.empty_apply, Option.isSome_none,
      Bool.false_eq_true, false_iff, not_exists]
    intro sid h
    exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])
  · intro tag sid n h; exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])
  · intro tag sid₁ sid₂ n h; exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])
  · intro tag sid _; rfl
  · intro tag sid n h; exact absurd h (by simp)
  · intro tag sid n h; exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])

/-- Reader-aware hop-A coupling relation for the heterogeneous bad+slack `simulateQ` rule: relate a
`MultipleBadState` (multiple-ideal state `s₁.1` together with a bad-world state `s₁.2`) and a
lazy-hybrid state `s₂` exactly when the three underlying components satisfy `HopACoupling`. -/
private def HopARel
    (s₁ : MultipleBadState TagId Nonce Digest sessionsPerTag)
    (s₂ : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) : Prop :=
  HopACoupling (sessionsPerTag := sessionsPerTag) s₁.1 s₂ s₁.2

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The initial `MultipleBadState` and lazy-hybrid state are `HopARel`-related. -/
private lemma HopARel_init :
    HopARel (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)
      ((UnlinkState.init, ∅), UnlinkBadState.init) (HybridState.init, ∅) :=
  HopACoupling_init

/-- **Hop A freshness invariant** (the `HybridColFresh`-analogue for the multiple cache). A cached
multiple-cache cell `(tag, n)` that was *not* produced by a tag draw — no session of `tag` recorded
the nonce `n` in the hybrid session-nonce map `sH.1.sessionNonce` — can only have been written by
an earlier *reader* query. Under `HasDistinctUnlinkReaderNonces` a second reader query at `n` is
then impossible, which is recorded here as the residual reader budget at `n` being exhausted.

The hybrid tag oracle records `sessionNonce (tag, sid) := some n` exactly when it draws nonce `n`
for session `(tag, sid)`, and the hop-A cache correspondence `HopACoupling.hcorr` ties tag-drawn
multiple cells to recorded sessions; so a cached multiple cell with no recorded session is genuinely
reader-written. This predicate is the freshness witness that the reader-step coupling threads
through the induction, exactly mirroring `HybridColFresh` in hop B. -/
private def HopAColFresh (oa : UnlinkAdversary TagId Nonce Digest)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (cM : ((TagId × Nonce) →ₒ Digest).QueryCache) : Prop :=
  ∀ (n : Nonce) (tag : TagId),
    (cM (tag, n)).isSome → (∀ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) ≠ some n) →
      OracleComp.IsQueryBoundP oa (pReaderNonce n) 0

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The empty multiple cache satisfies the hop-A freshness invariant vacuously: no cell is cached,
so the hypothesis `(cM (tag, n)).isSome` is never met. -/
private lemma hopAColFresh_init (oa : UnlinkAdversary TagId Nonce Digest)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    HopAColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) oa sH ∅ := by
  intro n tag hsome _
  simp at hsome

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- **Hop A, reader-step coupling stability.** A multiple-session reader query folds
`idealCacheStep` over its cells, extending the multiple cache `sM.2` to some `r.2` while leaving
the session counters, the hybrid state and the bad-world state untouched. Because `idealCacheStep`
only fills `none` cells — never overwriting an already-cached cell — and every tag-written cell is
already cached (clause `hcorr` together with the hybrid cache/session-nonce consistency), the
reader-extended state still satisfies `HopACoupling`. This is the precise sense in which the
reader-aware invariant is stable across reader queries. -/
private lemma HopACoupling_reader_step
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : HopACoupling (sessionsPerTag := sessionsPerTag) sM sH sB)
    (cells : List (TagId × Nonce))
    (r : List Digest × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheMapM (Digest := Digest) cells sM.2)) :
    HopACoupling (sessionsPerTag := sessionsPerTag) (sM.1, r.2) sH sB := by
  obtain ⟨hcnt1, hcnt2, hbad, hbadcol, hcorr, hcolfree, hwo, hhyb1, hhyb2⟩ := hInv
  refine ⟨hcnt1, hcnt2, hbad, hbadcol, ?_, hcolfree, hwo, hhyb1, hhyb2⟩
  intro tag sid n hsn
  have hcell : (sM.2 (tag, n)).isSome := by
    rw [hcorr tag sid n hsn]
    exact hhyb2 tag sid n hsn
  rw [idealCacheMapM_cache_off cells sM.2 r hr (tag, n) hcell]
  exact hcorr tag sid n hsn

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Hop A, off-collision tag-step coupling stability.** Given `HopACoupling sM sH sB`, a free
slot `hslot`, an off-collision nonce `n` (`sM.2 (tag, n) = none`) and a digest `u`, the three
post-states produced by the off-collision tag step — the multiple, hybrid and bad worlds all
caching the fresh digest `u` for tag `tag` at nonce `n` — again satisfy `HopACoupling`.

Off-collision means no session of `tag` had drawn `n` before, so the new draw both extends the
session-nonce map at the fresh slot `sid` and writes a fresh bad-world `responses` entry; the
reader-aware clause `hbadcol` is preserved because both the new session record and the new
bad-world entry sit at the same cell `(tag, n)`. -/
private lemma HopACoupling_tag_step
    (tag : TagId) (n : Nonce) (u : Digest)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : HopACoupling (sessionsPerTag := sessionsPerTag) sM sH sB)
    (hslot : sM.1.sessionsUsed tag < sessionsPerTag)
    (hfresh : sM.2 (tag, n) = none) :
    HopACoupling (sessionsPerTag := sessionsPerTag)
      ({ sM.1 with sessionsUsed :=
          Function.update sM.1.sessionsUsed tag (sM.1.sessionsUsed tag + 1) },
        sM.2.cacheQuery (tag, n) u)
      (({ sessionsUsed :=
            Function.update sH.1.sessionsUsed tag (sH.1.sessionsUsed tag + 1),
          sessionNonce := Function.update sH.1.sessionNonce
            (tag, ⟨sM.1.sessionsUsed tag, hslot⟩) (some n) } :
          HybridState TagId Nonce sessionsPerTag),
        sH.2.cacheQuery ((tag, ⟨sM.1.sessionsUsed tag, hslot⟩), n) u)
      ({ sessionsUsed :=
            Function.update sB.sessionsUsed tag (sB.sessionsUsed tag + 1),
          responses := sB.responses.cacheQuery (tag, n)
            (u :: Option.getD (sB.responses (tag, n)) []),
          bad := sB.bad || (sB.responses (tag, n)).isSome } :
          UnlinkBadState TagId Nonce Digest) := by
  obtain ⟨hcMH, hcMB, hbad, hbadcol, hcorr, hcollfree, hwo, hrec, hcons⟩ := hInv
  set sid : Fin sessionsPerTag := ⟨sM.1.sessionsUsed tag, hslot⟩ with hsid
  -- no session of `tag` had drawn `n` before (else the multiple cell would be cached)
  have hnodrawn : ∀ sid', sH.1.sessionNonce (tag, sid') ≠ some n := by
    intro sid' hsn'
    have := hcorr tag sid' n hsn'
    rw [hfresh] at this
    exact absurd (hcons tag sid' n hsn') (by rw [← this]; simp)
  -- the bad-world `responses` cell `(tag, n)` is empty off-collision
  have hBfresh : sB.responses (tag, n) = none := by
    rw [← Option.not_isSome_iff_eq_none, hbadcol tag n, not_exists]
    intro sid' hsn'
    exact hnodrawn sid' hsn'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [HybridState.sessionsUsed]; rw [hcMH]
  · dsimp only; rw [hcMB]
  · rw [hbad, hBfresh]; rfl
  · -- bad-world / session-nonce correspondence
    intro tag' n'
    dsimp only
    by_cases hkey : (tag', n') = (tag, n)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
      rw [QueryCache.cacheQuery_self]
      exact ⟨fun _ => ⟨sid, Function.update_self _ _ _⟩, fun _ => rfl⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ hkey, hbadcol tag' n']
      constructor
      · rintro ⟨sid', hsn'⟩
        refine ⟨sid', ?_⟩
        have hts : (tag', sid') ≠ (tag, sid) := by
          rintro h
          obtain ⟨htg, hsd⟩ := Prod.mk.inj h
          rw [htg, hsd, hwo tag sid (by rw [← hcMH, hsid])] at hsn'
          exact absurd hsn' (by simp)
        rw [Function.update_of_ne hts]; exact hsn'
      · rintro ⟨sid', hsn'⟩
        by_cases hts : (tag', sid') = (tag, sid)
        · obtain ⟨htg, hsd⟩ := Prod.mk.inj hts
          rw [htg, hsd, Function.update_self] at hsn'
          exact absurd (Prod.ext htg (Option.some.inj hsn').symm) hkey
        · rw [Function.update_of_ne hts] at hsn'
          exact ⟨sid', hsn'⟩
  · -- multiple/hybrid cache correspondence
    intro tag' sid' n' hsn'
    dsimp only at hsn' ⊢
    by_cases hts : (tag', sid') = (tag, sid)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hts
      rw [Function.update_self] at hsn'
      obtain rfl : n' = n := (Option.some.inj hsn').symm
      rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
    · rw [Function.update_of_ne hts] at hsn'
      by_cases hmkey : (tag', n') = (tag, n)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmkey
        exact absurd hsn' (hnodrawn sid')
      · rw [QueryCache.cacheQuery_of_ne _ _ hmkey]
        have hhkey : ((tag', sid'), n') ≠ ((tag, sid), n) := fun h => hts (congrArg Prod.fst h)
        rw [QueryCache.cacheQuery_of_ne _ _ hhkey]
        exact hcorr tag' sid' n' hsn'
  · -- collision-freeness
    intro tag' s₁ s₂ n' h₁ h₂
    dsimp only at h₁ h₂
    by_cases ht1 : (tag', s₁) = (tag, sid)
    · obtain ⟨htg, hs₁⟩ := Prod.mk.inj ht1
      subst hs₁; subst htg
      rw [Function.update_self] at h₁
      obtain rfl : n' = n := (Option.some.inj h₁).symm
      by_cases ht2 : (tag', s₂) = (tag', sid)
      · exact ((Prod.mk.inj ht2).2).symm
      · rw [Function.update_of_ne ht2] at h₂
        exact absurd h₂ (hnodrawn s₂)
    · rw [Function.update_of_ne ht1] at h₁
      by_cases ht2 : (tag', s₂) = (tag, sid)
      · obtain ⟨htg, hs₂⟩ := Prod.mk.inj ht2
        subst hs₂; subst htg
        rw [Function.update_self] at h₂
        obtain rfl : n' = n := (Option.some.inj h₂).symm
        exact absurd h₁ (hnodrawn s₁)
      · rw [Function.update_of_ne ht2] at h₂
        exact hcollfree tag' s₁ s₂ n' h₁ h₂
  · -- write-once
    intro tag' sid' hle
    dsimp only at hle ⊢
    by_cases htag : tag' = tag
    · subst htag
      rw [Function.update_self] at hle
      have hne : sid' ≠ sid := by
        intro h; rw [h, hsid] at hle; rw [← hcMH] at hle; simp only [Fin.val] at hle; omega
      rw [Function.update_of_ne (by simp [Prod.ext_iff, hne])]
      exact hwo tag' sid' (by omega)
    · rw [Function.update_of_ne htag] at hle
      rw [Function.update_of_ne (by simp [htag])]
      exact hwo tag' sid' hle
  · -- cache-recorded
    intro tag' sid' n' hsome
    dsimp only at hsome ⊢
    by_cases hhkey : ((tag', sid'), n') = ((tag, sid), n)
    · obtain ⟨hkk, rfl⟩ := Prod.mk.inj hhkey
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkk
      rw [Function.update_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hhkey] at hsome
      have hsn := hrec tag' sid' n' hsome
      have hts : (tag', sid') ≠ (tag, sid) := by
        intro h
        rw [h] at hsn
        rw [hwo tag sid (by rw [← hcMH, hsid])] at hsn
        exact absurd hsn (by simp)
      rw [Function.update_of_ne hts]
      exact hsn
  · -- cache-consistency
    intro tag' sid' n' hsn'
    dsimp only at hsn' ⊢
    by_cases hts : (tag', sid') = (tag, sid)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hts
      rw [Function.update_self] at hsn'
      obtain rfl : n' = n := (Option.some.inj hsn').symm
      rw [QueryCache.cacheQuery_self]; simp
    · rw [Function.update_of_ne hts] at hsn'
      have hhkey : ((tag', sid'), n') ≠ ((tag, sid), n) := fun h => hts (congrArg Prod.fst h)
      rw [QueryCache.cacheQuery_of_ne _ _ hhkey]
      exact hcons tag' sid' n' hsn'

/-! ### Hop A: closing `multipleIdeal_le_hybrid_add_bad`

The reader and tag per-query coupling steps are discharged below and assembled through the
heterogeneous bad+slack `simulateQ` rule `probOutput_simulateQ_run'_le_add_bad_add_slack`. -/

omit [Nonempty TagId] [SampleableType Nonce] [NeZero sessionsPerTag] in
/-- If a multiple-reader cell `(tag, n)` is already cached with digest `v`, then folding
`idealCacheStep` over a cell list containing `(tag, n)` produces a drawn list containing `v`: a
cached cell is read back unchanged. -/
private lemma mem_drawn_of_cached_cell {D : Type} [DecidableEq D]
    (l : List D) (c : (D →ₒ Digest).QueryCache)
    (rs : List Digest × (D →ₒ Digest).QueryCache)
    (hrs : rs ∈ support (idealCacheMapM (Digest := Digest) l c))
    (d : D) (hd : d ∈ l) (v : Digest) (hcd : c d = some v) :
    v ∈ rs.1 := by
  classical
  have hr2 : rs.2 d = c d :=
    idealCacheMapM_cache_off l c rs hrs d (by rw [hcd]; rfl)
  have hmap := idealCacheMapM_support l c rs hrs (fun _ => v)
  rw [hmap]
  refine List.mem_map.mpr ⟨d, hd, ?_⟩
  simp [OracleComp.tableExtending, hr2, hcd]

omit [Nonempty TagId] [SampleableType Nonce] [NeZero sessionsPerTag] in
/-- **Hop A, reader-step output domination.** Under `HopACoupling sM sH sB`, whenever the lazy
hybrid reader accepts a transcript (`hybridCacheAccepts` reads `true`), the multiple reader also
accepts: the accepting hybrid session cell mirrors a cached multiple cell holding the
authenticator, which the multiple reader fold reads back into its drawn list. Hence the two
readers disagree only in the direction `multiple accepts, hybrid rejects`. -/
private lemma multipleReader_accepts_of_hybridCacheAccepts
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : HopACoupling (sessionsPerTag := sessionsPerTag) sM sH sB)
    (transcript : TagTranscript Nonce Digest)
    (rs : List Digest × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hrs : rs ∈ support (idealCacheMapM (multipleReaderCells (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) transcript) sM.2))
    (hhyb : hybridCacheAccepts (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) sH.2 sH.1.sessionNonce transcript = true) :
    decide (∃ d ∈ rs.1, d = transcript.auth) = true := by
  classical
  obtain ⟨_, _, _, _, hcorr, _, _, _, _⟩ := hInv
  rw [hybridCacheAccepts, decide_eq_true_eq] at hhyb
  obtain ⟨tag, sid, hsn, hcell⟩ := hhyb
  have hmcell : sM.2 (tag, transcript.nonce) = some transcript.auth := by
    rw [hcorr tag sid transcript.nonce hsn]; exact hcell
  have hmem : (tag, transcript.nonce) ∈ multipleReaderCells (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) transcript := by
    unfold multipleReaderCells
    exact List.mem_map.mpr ⟨tag, Finset.mem_toList.mpr (Finset.mem_univ tag), rfl⟩
  exact decide_eq_true (⟨transcript.auth,
    mem_drawn_of_cached_cell _ sM.2 rs hrs (tag, transcript.nonce) hmem transcript.auth hmcell,
    rfl⟩)

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ multipleBadQueryImpl` of a `query_bind`, run from a state and projected to its
output bit: the per-query handler followed by the recursive simulation of the continuation. -/
private lemma multipleBad_run'_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' s =
      (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t s) >>= fun p =>
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ multipleBadQueryImpl` of a `query_bind`, run from a state and projected to its full
output: the per-query handler followed by the recursive simulation of the continuation. -/
private lemma multipleBad_run_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run s =
      (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t s) >>= fun p =>
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

/-! ### Hop A: the eager-table instrumented multiple handler

The `HopACoupling`-`inductionOn` route for the hop-A coupling bound is a proven dead end: a
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
private lemma multipleBadTable_run_query_bind' {α : Type} (g : TagId × Nonce → Digest)
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
private lemma multipleBadTableHandler_step_preserves_bad (g : TagId × Nonce → Digest)
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
    cases hr : r.1 with
    | none => simp [multipleBadAdvance, hbad]
    | some tr => simp [multipleBadAdvance, hbad]
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
private lemma multipleBadTableHandler_run_preserves_bad {α : Type} (g : TagId × Nonce → Digest)
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

/-- **Eager-table equivalence for the instrumented multiple handler.** Running the instrumented
multiple handler `multipleBadQueryImpl` from `((s, c), sB)` has the same *full-output* distribution
(output bit, multiple-ideal state and bad-world state) as sampling a full random-oracle table `g`,
overlaying the cache `c`, and running the deterministic instrumented table handler
`multipleBadTableHandler (tableExtending c g)` from `(s, sB)`.

Proved by induction on the adversary, generalized over the state. It mirrors
`evalDist_simulateQ_multipleIdealQueryImpl_run'_eq_tableExtending`, threading the bad-world
component (which `multipleBadAdvance` advances deterministically from the realized transcript). -/
private lemma evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending
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
        show (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)
            (Sum.inr transcript)) s >>= _ = _
        rw [multipleTableHandler_reader_run _ transcript s]
        rfl
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
private noncomputable def chooseSid
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag) (tag : TagId) (n : Nonce) :
    Fin sessionsPerTag :=
  if h : ∃ sid : Fin sessionsPerTag, sn (tag, sid) = some n then h.choose else 0

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [SampleableType Digest] in
/-- When some session of `tag` drew `n`, `chooseSid` returns a witness session. -/
private lemma chooseSid_spec (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (tag : TagId) (n : Nonce) (h : ∃ sid : Fin sessionsPerTag, sn (tag, sid) = some n) :
    sn (tag, chooseSid (sessionsPerTag := sessionsPerTag) sn tag n) = some n := by
  rw [chooseSid, dif_pos h]
  exact h.choose_spec

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [SampleableType Digest] in
/-- Off-collision (`hcf`), `chooseSid sn tag n` is *the* session that drew `n`. -/
private lemma chooseSid_eq (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (hcf : ∀ tag sid₁ sid₂ n, sn (tag, sid₁) = some n → sn (tag, sid₂) = some n → sid₁ = sid₂)
    (tag : TagId) (sid : Fin sessionsPerTag) (n : Nonce) (hsn : sn (tag, sid) = some n) :
    chooseSid (sessionsPerTag := sessionsPerTag) sn tag n = sid :=
  hcf tag _ sid n (chooseSid_spec sn tag n ⟨sid, hsn⟩) hsn

/-- The coupling injection from multiple-world cells to hybrid-world cells induced by a
session-nonce map `sn`: send `(tag, n)` to the cell `((tag, chooseSid sn tag n), n)`. -/
private noncomputable def couplingEmbed
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag) :
    TagId × Nonce → (TagId × Fin sessionsPerTag) × Nonce :=
  fun p => ((p.1, chooseSid (sessionsPerTag := sessionsPerTag) sn p.1 p.2), p.2)

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [SampleableType Digest] in
/-- The coupling embedding is injective: it preserves the tag and the nonce coordinates. -/
private lemma couplingEmbed_injective
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
private lemma evalDist_couplingProject_uniformSample [Fintype Nonce] [Finite Digest]
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag) :
    𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
        fun gH => pure (gH ∘ couplingEmbed (sessionsPerTag := sessionsPerTag) sn)] =
      𝒟[$ᵗ (TagId × Nonce → Digest)] := by
  haveI : Nonempty Digest := ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  exact evalDist_uniformSample_map_comp_injective (R := Digest)
    (couplingEmbed_injective (sessionsPerTag := sessionsPerTag) sn)

/-- **Hop A, eager-coupled core.** The deterministic-table form of the hop-A coupling bound: with
both worlds eagerized (the multiple-side instrumented handler `multipleBadTableHandler` run against
`tableExtending sM2 gM`, the hybrid handler `hybridTableHandler` run against
`tableExtending sH2 gH`), the multiple success probability is bounded by the hybrid success
probability plus the bad-event probability plus the per-reader-query slack.

The two table samples are coupled cell-by-cell: an outer uniform draw of the hybrid table `gH`
determines, at every drawn hybrid cell `((tag,sid),n)`, the multiple value `gM(tag,n)` — the
multiple table being recovered from the hybrid table along the injective `couplingEmbed`
(see `evalDist_couplingProject_uniformSample`). The induction threads the reader budget `qR`
exactly as `hybridCoupled_le_singleIdeal_add_readerSlack_aux`.

### Open obligation (the two `query_bind` cases)

The `tag` slot-exhausted branch is closed (both handlers return `pure (none, …)` with state
untouched, so the step collapses to the continuation `f none` and the goal is exactly `ih`). The
two remaining `sorry`s are:

1. The **tag step, slot-available branch.** With `hslot : sM.1.sessionsUsed tag < sessionsPerTag`,
   both handlers unfold to `nonce ← $ᵗ Nonce` followed by a fresh per-cell read:
   `tableExtending sM.2 gM (tag, nonce)` on the multiple side, `tableExtending sH.2 gH ((tag,sid),
   nonce)` on the hybrid side, where `sid = ⟨sM.1.sessionsUsed tag, hslot⟩` is statically known.
   The cleanest split is on collision rather than on the global `couplingEmbed`: at each tag step
   the eager caches `sM.2`/`sH.2` carry only *tag-drawn* cells (the eager reader does not write
   them; only the `ih`-recording at past tag draws does), so a cell `sM.2 (tag, nonce)` being
   `some w` means a past session of `tag` already drew `nonce` — exactly the bad event. Hence:

   * **Bad branch** (`∃ sid', sH.1.sessionNonce (tag, sid') = some nonce`): `multipleBadAdvance`
     fires `bad`, the monotone lemma `multipleBadQueryImpl_step_preserves_bad` propagates it to
     the output, and the whole branch is absorbed into the `Pr[·.2.bad]` term via
     `probEvent_bind_le_add_bad_of_disagree'`.
   * **Fresh branch** (off-collision): `sM.2 (tag, nonce) = none` and
     `sH.2 ((tag,sid), nonce) = none` (by `HopACoupling`'s `hcons`+`hwo`), so the two cell reads
     are independent uniform draws of `gM` and `gH`. Couple them via two applications of
     `evalDist_uniformSample_bind_update` (one per table) sharing a single fresh `u ← $ᵗ Digest`;
     record `(tag, nonce) ↦ u` into both caches, advance the multiple/hybrid/bad components by
     `HopACoupling_tag_step`, and recurse with `ih` at the extended cache.

2. The **reader step.** Both readers fold over the column at `transcript.nonce`. Per-cell
   coupling from the tag-step patching maintains `tableExtending sM.2 gM (tag, n) =
   tableExtending sH.2 gH ((tag, chosen-sid), n)` for every tag-drawn `(tag, n)`. For non-recorded
   `(tag, n)`, the multiple reads a fresh `gM (tag, n)` which can spuriously match the
   authenticator with probability `1 / |Digest|`, but the hybrid skips that slot — so the
   disagreement set carries mass `|TagId| / |Digest|` per reader query, charged once via
   `probEvent_multipleReader_disagree_le` + `multipleReader_accepts_of_hybridCacheAccepts`, then
   `hdist` rules out a future reader query at the same nonce so the bookkeeping does not double-
   count; recurse with `qR' = qR - 1` and an updated `HopAColFresh`. -/
private lemma multipleBadEager_le_hybridEager_aux [Fintype Nonce] [Fintype Digest]
    (oa : UnlinkAdversary TagId Nonce Digest) (qR qT : ℕ)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : HopACoupling (sessionsPerTag := sessionsPerTag) sM sH sB)
    (hqR : OracleComp.IsQueryBoundP oa (fun i => i.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP oa (fun i => i.isLeft) qT)
    (hdist : ∀ n : Nonce, OracleComp.IsQueryBoundP oa (pReaderNonce n) 1)
    (hfresh : HopAColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) oa sH sM.2) :
    Pr[= true | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)] ≤
      Pr[= true | do
        let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sH.2 gH)) oa).run' sH.1] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qR * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
  classical
  induction oa using OracleComp.inductionOn generalizing qR qT sM sH sB with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, StateT.run'_eq, map_pure, bind_pure_comp]
    have h1 : Pr[= true | (fun _ => b) <$> ($ᵗ (TagId × Nonce → Digest))] =
        Pr[= true | (fun _ => b) <$> ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] := by
      rw [← bind_pure_comp, ← bind_pure_comp, probOutput_bind_const, probOutput_bind_const,
        probFailure_uniformSample, probFailure_uniformSample]
    exact le_add_right (le_add_right (le_add_right (le_of_eq h1)))
  | query_bind t f ih =>
    simp only [multipleBadTable_run_query_bind', hybridTable_run'_query_bind', map_bind]
    cases t with
    | inl tag =>
      -- Continuation query-bound facts: a tag query is neither charged by `isRight` nor by
      -- `pReaderNonce`, so the reader-side budgets pass straight through. The tag-step budget
      -- `qT` decrements by one (the head tag query consumes one unit).
      have hqRf : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isRight = true) qR := by
        intro u
        have := hqR
        rw [OracleComp.isQueryBoundP_query_bind_iff] at this
        simpa using this.2 u
      have hqTsplit := hqT
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hqTsplit
      have hqTpos : 0 < qT := by
        rcases hqTsplit.1 with h | h
        · exact absurd rfl h
        · exact h
      obtain ⟨qT', rfl⟩ : ∃ qT', qT = qT' + 1 := ⟨qT - 1, by omega⟩
      have hqTf : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isLeft = true) qT' := by
        intro u; simpa using hqTsplit.2 u
      have hdistf : ∀ u, ∀ n, OracleComp.IsQueryBoundP (f u) (pReaderNonce n) 1 := by
        intro u n
        have := hdist n
        rw [OracleComp.isQueryBoundP_query_bind_iff] at this
        simpa [pReaderNonce] using this.2 u
      have hfreshf : ∀ u, HopAColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (f u) sH sM.2 := by
        intro u n tg hsome hns
        have hb := hfresh n tg hsome hns
        rw [OracleComp.isQueryBoundP_query_bind_iff] at hb
        simpa [pReaderNonce] using hb.2 u
      by_cases hslot : sM.1.sessionsUsed tag < sessionsPerTag
      · -- **Slot-available tag step.** Unfold both table handlers to their nonce-sampling forms;
        -- the per-cell coupling at a fresh nonce is delegated to `evalDist_uniformSample_bind_update`
        -- on each side. The bad/fresh split charges collisions into `Pr[·.2.bad]` and discharges
        -- the fresh case by `HopACoupling_tag_step` + `ih`.
        have hslotH : sH.1.sessionsUsed tag < sessionsPerTag := by
          rw [← congrFun hInv.1 tag]; exact hslot
        set sidH : Fin sessionsPerTag := ⟨sH.1.sessionsUsed tag, hslotH⟩ with hsidH
        set advM : UnlinkState TagId :=
          { sM.1 with sessionsUsed :=
              Function.update sM.1.sessionsUsed tag (sM.1.sessionsUsed tag + 1) } with hadvM
        set advH : Nonce → HybridState TagId Nonce sessionsPerTag := fun n =>
          ({ sessionsUsed :=
                Function.update sH.1.sessionsUsed tag (sH.1.sessionsUsed tag + 1),
             sessionNonce := Function.update sH.1.sessionNonce (tag, sidH) (some n) } :
            HybridState TagId Nonce sessionsPerTag) with hadvH
        -- Multiple-handler unfold at a free slot: sample a nonce, look up the table, advance
        -- multi/bad. The `← hadvM` rewrite is what lets `simp only [bind_assoc, pure_bind]`
        -- match (see the parallel proof at line 5189).
        have hMstep : ∀ g : TagId × Nonce → Digest,
            multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) (sM.1, sB)
            = ($ᵗ Nonce) >>= fun n =>
                pure (some (⟨n, g (tag, n)⟩ : TagTranscript Nonce Digest),
                  advM, multipleBadAdvance tag sB
                    (some (⟨n, g (tag, n)⟩ : TagTranscript Nonce Digest))) := by
          intro g
          change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) sM.1
              >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1)) = _
          rw [multipleTableHandler_tag_run_of_lt g tag sM.1 hslot, ← hadvM]
          exact bind_assoc ..
        -- Hybrid-handler unfold at a free slot.
        have hHstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) gS (Sum.inl tag) sH.1
            = ($ᵗ Nonce) >>= fun n =>
                pure (some (⟨n, gS ((tag, sidH), n)⟩ : TagTranscript Nonce Digest), advH n) := by
          intro gS
          rw [hybridTableHandler_tag_run_of_lt gS tag sH.1 hslotH, ← hsidH]
        -- **Step 1.** Lift `hMstep`/`hHstep` into the goal by `bind_congr`, flattening the inner
        -- `($ᵗ Nonce) >>= pure (…)` against the outer continuation via `bind_assoc` + `pure_bind`.
        -- This is a syntactic equality (no `evalDist` needed) because `hMstep`/`hHstep` are equalities
        -- of `ProbComp` values and `bind_congr` rewrites under the outer table draws.
        have hLHS_eq :
            (do let gM ← $ᵗ (TagId × Nonce → Digest)
                let a ← multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sM.2 gM)
                  (Sum.inl tag) (sM.1, sB)
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
                  (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending sM.2 gM)) (f a.1)).run a.2)
            = (do let gM ← $ᵗ (TagId × Nonce → Digest)
                  let n ← $ᵗ Nonce
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      z.1) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending sM.2 gM))
                      (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest)))).run
                      (advM, multipleBadAdvance tag sB
                        (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest)))) := by
          refine bind_congr fun gM => ?_
          rw [hMstep (OracleComp.tableExtending sM.2 gM)]
          exact bind_assoc ..
        have hRHS_eq :
            (do let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                let p ← hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sH.2 gH)
                  (Sum.inl tag) sH.1
                (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending sH.2 gH)) (f p.1)).run' p.2)
            = (do let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let n ← $ᵗ Nonce
                  (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                    (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending sH.2 gH))
                    (f (some (⟨n, OracleComp.tableExtending sH.2 gH ((tag, sidH), n)⟩ :
                        TagTranscript Nonce Digest)))).run' (advH n)) := by
          refine bind_congr fun gH => ?_
          rw [hHstep (OracleComp.tableExtending sH.2 gH)]
          exact bind_assoc ..
        have hBAD_eq :
            (do let gM ← $ᵗ (TagId × Nonce → Digest)
                let a ← multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sM.2 gM)
                  (Sum.inl tag) (sM.1, sB)
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending sM.2 gM)) (f a.1)).run a.2)
            = (do let gM ← $ᵗ (TagId × Nonce → Digest)
                  let n ← $ᵗ Nonce
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending sM.2 gM))
                      (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest)))).run
                      (advM, multipleBadAdvance tag sB
                        (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest)))) := by
          refine bind_congr fun gM => ?_
          rw [hMstep (OracleComp.tableExtending sM.2 gM)]
          exact bind_assoc ..
        rw [hLHS_eq, hRHS_eq, hBAD_eq]
        -- **Step 2.** Commute the outer table draw past the inner `n ← $ᵗ Nonce` at the `𝒟[·]`
        -- level (NOT syntactic) via `evalDist_probComp_bind_comm`, so the shared nonce draw is the
        -- outermost sample on every side. This is the canonical setup for
        -- `probEvent_bind_le_add_bad_of_disagree'` with `mx := $ᵗ Nonce`.
        have hLHS_comm :
            𝒟[(do let gM ← $ᵗ (TagId × Nonce → Digest)
                  let n ← $ᵗ Nonce
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      z.1) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending sM.2 gM))
                      (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest)))).run
                      (advM, multipleBadAdvance tag sB
                        (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest))))]
            = 𝒟[(do let n ← $ᵗ Nonce
                    let gM ← $ᵗ (TagId × Nonce → Digest)
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending sM.2 gM))
                        (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                            TagTranscript Nonce Digest))))] :=
          evalDist_probComp_bind_comm ($ᵗ (TagId × Nonce → Digest)) ($ᵗ Nonce) _
        have hRHS_comm :
            𝒟[(do let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let n ← $ᵗ Nonce
                  (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending sH.2 gH))
                    (f (some (⟨n, OracleComp.tableExtending sH.2 gH ((tag, sidH), n)⟩ :
                        TagTranscript Nonce Digest)))).run' (advH n))]
            = 𝒟[(do let n ← $ᵗ Nonce
                    let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending sH.2 gH))
                      (f (some (⟨n, OracleComp.tableExtending sH.2 gH ((tag, sidH), n)⟩ :
                          TagTranscript Nonce Digest)))).run' (advH n))] :=
          evalDist_probComp_bind_comm
            ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
        have hBAD_comm :
            𝒟[(do let gM ← $ᵗ (TagId × Nonce → Digest)
                  let n ← $ᵗ Nonce
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending sM.2 gM))
                      (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest)))).run
                      (advM, multipleBadAdvance tag sB
                        (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest))))]
            = 𝒟[(do let n ← $ᵗ Nonce
                    let gM ← $ᵗ (TagId × Nonce → Digest)
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending sM.2 gM))
                        (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                            TagTranscript Nonce Digest))))] :=
          evalDist_probComp_bind_comm ($ᵗ (TagId × Nonce → Digest)) ($ᵗ Nonce) _
        rw [show Pr[= true | _] = _ from probOutput_congr rfl hLHS_comm,
            show Pr[= true | _] = _ from probOutput_congr rfl hRHS_comm,
            show probEvent _ _ = _ from probEvent_congr' (fun _ _ => Iff.rfl) hBAD_comm]
        -- **Step 3.** Apply `probEvent_bind_le_add_bad_of_disagree'` with the shared `$ᵗ Nonce`
        -- draw, splitting on collision: `D n := ∃ sid, sH.1.sessionNonce (tag, sid) = some n`.
        -- Combine the digest- and nonce-side slacks into one ε via `add_assoc` so the lemma's
        -- conclusion `... + ε` matches the four-term RHS.
        simp only [← probEvent_eq_eq_probOutput]
        classical
        rw [add_assoc _ _ _]
        refine probEvent_bind_le_add_bad_of_disagree'
          (D := fun n : Nonce =>
              ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n)
          ?_ ?_
        · -- **Bad branch (collision).** A past session of `tag` already drew `n`, so by
          -- `hInv.hbadcol` the bad-world `responses` cell `(tag, n)` is already filled. Hence
          -- `multipleBadAdvance` flips `bad := false || true = true`, then
          -- `multipleBadTableHandler_run_preserves_bad` propagates `bad = true` through the
          -- continuation. Push the outer `(z.1, z.2.2) <$> ·` map into the predicate via
          -- `probEvent_map`, then unfold the bind into the support.
          intro n _ hcoll
          have hcell : (sB.responses (tag, n)).isSome = true := by
            rw [hInv.2.2.2.1]; exact hcoll
          have hadvBad : ∀ d : Digest,
              (multipleBadAdvance tag sB
                  (some (⟨n, d⟩ : TagTranscript Nonce Digest))).bad = true := by
            intro d; simp [multipleBadAdvance, hInv.2.2.1, hcell]
          rw [probEvent_eq_one_iff]
          refine ⟨probFailure_eq_zero, ?_⟩
          intro z hz
          rw [mem_support_bind_iff] at hz
          obtain ⟨gM, _, hzM⟩ := hz
          rw [support_map, Set.mem_image] at hzM
          obtain ⟨w, hw, hzeq⟩ := hzM
          subst hzeq
          exact multipleBadTableHandler_run_preserves_bad
            (OracleComp.tableExtending sM.2 gM)
            (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                TagTranscript Nonce Digest)))
            (advM, multipleBadAdvance tag sB
              (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                TagTranscript Nonce Digest)))
            (hadvBad _) w hw
        · -- **Fresh branch (off-collision).** No session of `tag` drew `n`. By `hInv.hbadcol`
          -- the bad-world `responses` cell is unfilled, so `multipleBadAdvance` does not flip
          -- `bad`. Couple `gM(tag, n)` and `gH((tag, sidH), n)` to a shared fresh `u ← $ᵗ Digest`
          -- via two `evalDist_uniformSample_bind_update` applications, then advance the coupling
          -- by `HopACoupling_tag_step` and recurse with `ih`.
          intro n _ hncoll
          -- **Structural facts derivable from `hInv` at the off-collision nonce `n`:**
          -- the bad-world `responses` cell is unfilled, and the new hybrid cell `((tag, sidH), n)`
          -- is fresh (since `sidH` is the next-to-allocate slot and `hwo` / `hhyb1` rule out
          -- recorded sessions there).
          have hBfresh : sB.responses (tag, n) = none := by
            rw [← Option.not_isSome_iff_eq_none, hInv.2.2.2.1]
            exact hncoll
          have hSnNone : sH.1.sessionNonce (tag, sidH) = none := by
            -- `sidH.val = sH.1.sessionsUsed tag`, so by `hInv.hwo` (clause 7) the session-nonce is
            -- `none`.
            exact hInv.2.2.2.2.2.2.1 tag sidH (le_refl _)
          have hHcellNone : sH.2 ((tag, sidH), n) = none := by
            -- Contrapositive of `hhyb1` (clause 8): if the hybrid cache cell were some, the
            -- session-nonce would be `some n`, contradicting `hSnNone`.
            rw [← Option.not_isSome_iff_eq_none]
            intro hsome
            have hsn := hInv.2.2.2.2.2.2.2.1 tag sidH n hsome
            rw [hSnNone] at hsn
            cases hsn
          by_cases hMcellNone : sM.2 (tag, n) = none
          · -- **Sub-case A (principal): the multi cache is unfilled at `(tag, n)`.** Couple the
            -- two outer table draws `gM, gH` via two `evalDist_uniformSample_bind_update_map`
            -- applications sharing one fresh `u ← $ᵗ Digest`: after patching,
            -- `tableExtending sM.2 (gM_patched) (tag, n) = u` (by `tableExtending_update_of_none`
            -- and `hMcellNone`) and `tableExtending sH.2 (gH_patched) ((tag, sidH), n) = u`
            -- (by `hHcellNone`). The advanced multi state `mbAdv tag sB (some ⟨n, u⟩)` has
            -- `bad = false` (by `hBfresh`), so `HopACoupling_tag_step` holds at every `u` and
            -- `ih (some ⟨n, u⟩) qR (advM, sM.2.cacheQuery (tag, n) u)
            --     (advH n_with_session, sH.2.cacheQuery ((tag, sidH), n) u)
            --     (mbAdv tag sB (some ⟨n, u⟩))` provides the inductive bound at the patched
            -- states.
            --
            -- **Per-`u` post-state bad flag.** With `sB.responses (tag, n) = none`,
            -- `multipleBadAdvance` does not flip `bad`, so the post-bad-state is `false`-flagged at
            -- every `u`.
            have hPostBad : ∀ u : Digest,
                (multipleBadAdvance tag sB
                  (some (⟨n, u⟩ : TagTranscript Nonce Digest))).bad = false := by
              intro u
              simp [multipleBadAdvance, hInv.2.2.1, hBfresh]
            -- **Per-`u` post-state coupling.** With both multi and hybrid caches unfilled at the
            -- target cell, `HopACoupling_tag_step` packages the advance of all three states.
            -- We reshape `advH n` and `multipleBadAdvance tag sB (some ⟨n, u⟩)` into the
            -- canonical post-state form expected by the lemma.
            have hcMH' : sM.1.sessionsUsed tag = sH.1.sessionsUsed tag := congrFun hInv.1 tag
            have hsidEq : (⟨sM.1.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) = sidH := by
              apply Fin.eq_of_val_eq; exact hcMH'
            have hInvNew : ∀ u : Digest,
                HopACoupling (sessionsPerTag := sessionsPerTag)
                  ({ sM.1 with sessionsUsed :=
                        Function.update sM.1.sessionsUsed tag (sM.1.sessionsUsed tag + 1) },
                    sM.2.cacheQuery (tag, n) u)
                  (advH n, sH.2.cacheQuery ((tag, sidH), n) u)
                  (multipleBadAdvance tag sB
                    (some (⟨n, u⟩ : TagTranscript Nonce Digest))) := by
              intro u
              have hstep := HopACoupling_tag_step (sessionsPerTag := sessionsPerTag)
                tag n u sM sH sB hInv hslot hMcellNone
              -- `HopACoupling_tag_step` produces post-hybrid state with `⟨sM.1.sessionsUsed tag, hslot⟩`
              -- as the new session index; rewrite to the user-defined `sidH`.
              rw [hsidEq] at hstep
              -- Reshape `multipleBadAdvance tag sB (some ⟨n, u⟩)` to the explicit record form.
              have hBadEq :
                  multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest))
                  = ({ sessionsUsed :=
                          Function.update sB.sessionsUsed tag (sB.sessionsUsed tag + 1),
                       responses := sB.responses.cacheQuery (tag, n)
                         (u :: Option.getD (sB.responses (tag, n)) []),
                       bad := sB.bad || (sB.responses (tag, n)).isSome } :
                      UnlinkBadState TagId Nonce Digest) := by
                simp [multipleBadAdvance]
              rw [hBadEq]
              -- Reshape `advH n` to the explicit `HybridState` record form used by the lemma.
              have hadvHEq : advH n
                  = ({ sessionsUsed :=
                          Function.update sH.1.sessionsUsed tag (sH.1.sessionsUsed tag + 1),
                       sessionNonce := Function.update sH.1.sessionNonce (tag, sidH) (some n) } :
                      HybridState TagId Nonce sessionsPerTag) := by
                rw [hadvH]
              rw [hadvHEq]
              exact hstep
            -- **Per-`u` `HopAColFresh` stability.** The advanced multi cache adds the cell
            -- `(tag, n)`; the advanced hybrid session-nonce map adds `(tag, sidH) ↦ some n`.
            -- A cached cell `(tag', n')` with no recorded session in the advanced map either
            -- coincides with the new entry (contradicting the no-session hypothesis at `n'`) or
            -- lifts the pre-advance freshness witness `hfreshf (some ⟨n, u⟩)` at `(tag', n')`.
            have hFreshNew : ∀ u : Digest,
                HopAColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag) (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
                  (advH n, sH.2.cacheQuery ((tag, sidH), n) u)
                  (sM.2.cacheQuery (tag, n) u) := by
              intro u n' tag' hcell hns
              -- Split on whether `(tag', n')` is the freshly cached cell.
              by_cases hkey : (tag', n') = (tag, n)
              · -- The advanced session-nonce map sends `(tag, sidH)` to `some n` = `some n'`,
                -- contradicting the universal `≠ some n'` hypothesis at `sidH`.
                obtain ⟨htag, hnn⟩ := Prod.mk.inj hkey
                refine absurd ?_ (hns sidH)
                show (advH n).sessionNonce (tag', sidH) = some n'
                rw [hadvH, htag, hnn]
                exact Function.update_self _ _ _
              · -- The freshly cached cell is elsewhere; reduce to the pre-advance witness.
                have hcell' : (sM.2 (tag', n')).isSome := by
                  rwa [QueryCache.cacheQuery_of_ne _ _ hkey] at hcell
                have hns' : ∀ sid, sH.1.sessionNonce (tag', sid) ≠ some n' := by
                  intro sid hsn
                  -- The pre-advance session-nonce at `(tag', sid)` equals the post-advance
                  -- value unless `(tag', sid) = (tag, sidH)`; rule out the latter and conclude.
                  by_cases hts : (tag', sid) = (tag, sidH)
                  · obtain ⟨htg, hsd⟩ := Prod.mk.inj hts
                    rw [htg, hsd, hInv.2.2.2.2.2.2.1 tag sidH (le_refl _)] at hsn
                    cases hsn
                  · refine hns sid ?_
                    show (advH n).sessionNonce (tag', sid) = some n'
                    rw [hadvH]
                    show Function.update sH.1.sessionNonce (tag, sidH) (some n) (tag', sid) = some n'
                    rw [Function.update_of_ne hts]
                    exact hsn
                exact hfreshf (some (⟨n, u⟩ : TagTranscript Nonce Digest)) n' tag' hcell' hns'
            -- **Per-`u` inductive hypothesis.** All preconditions of `ih` are now in scope at
            -- the cacheQuery-extended states. The remaining work is to relate the goal's outer
            -- `gM`/`gH` draws (where the patched cell is read from `tableExtending sM.2 gM` /
            -- `tableExtending sH.2 gH`) to this `ih` shape (where the cell read from
            -- `tableExtending (sM.2.cacheQuery (tag, n) u) gM` / `tableExtending (...) gH` is
            -- deterministically `u`), via `evalDist_uniformSample_bind_update_map` and
            -- `tableExtending_update_of_none` at each side.
            have hIh : ∀ u : Digest,
                Pr[= true | do
                    let gM ← $ᵗ (TagId × Nonce → Digest)
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending (sM.2.cacheQuery (tag, n) u) gM))
                        (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, u⟩ : TagTranscript Nonce Digest)))] ≤
                  Pr[= true | do
                    let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending (sH.2.cacheQuery ((tag, sidH), n) u) gH))
                      (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' (advH n)] +
                  Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true | do
                    let gM ← $ᵗ (TagId × Nonce → Digest)
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending (sM.2.cacheQuery (tag, n) u) gM))
                        (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, u⟩ : TagTranscript Nonce Digest)))] +
                  ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) /
                    (Fintype.card Digest : ℝ≥0∞) +
                  ((qR * qT' : ℕ) : ℝ≥0∞) /
                    (Fintype.card Nonce : ℝ≥0∞) := fun u =>
              ih (some (⟨n, u⟩ : TagTranscript Nonce Digest)) qR qT'
                (advM, sM.2.cacheQuery (tag, n) u)
                (advH n, sH.2.cacheQuery ((tag, sidH), n) u)
                (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
                (hInvNew u) (hqRf _) (hqTf _) (hdistf _) (hFreshNew u)
            -- **Cell-read simplification at the off-collision multi cell.** With `hMcellNone`,
            -- `tableExtending sM.2 gM (tag, n) = gM (tag, n)`: the multi-side cell read collapses
            -- to a direct lookup in the freshly drawn table `gM`.
            have hMcellRead : ∀ gM : TagId × Nonce → Digest,
                OracleComp.tableExtending sM.2 gM (tag, n) = gM (tag, n) := by
              intro gM
              simp [OracleComp.tableExtending, hMcellNone]
            -- **Cell-patch identity.** After patching `gM` at `(tag, n)` with `u`, the
            -- `tableExtending`-overlay equals the cache-extended overlay against the original `gM`.
            have hMpatchTable : ∀ (gM : TagId × Nonce → Digest) (u : Digest),
                OracleComp.tableExtending sM.2 (Function.update gM (tag, n) u)
                  = OracleComp.tableExtending (sM.2.cacheQuery (tag, n) u) gM := by
              intro gM u
              rw [← OracleComp.tableExtending_update_of_none sM.2 gM hMcellNone u,
                ← OracleComp.tableExtending_cacheQuery sM.2 gM (tag, n) u]
            -- **LHS distributional lift.** Define the multi-side continuation `contM gM u`
            -- abstracting the inner `simulateQ`-run-projection, parametric over both the drawn
            -- table `gM` and the cell value `u`. Then the goal LHS is `gM ← $ᵗ; contM gM (gM (tag, n))`
            -- (using `hMcellRead`), which the cell-extract helper lifts to
            -- `u ← $ᵗ Digest; gM ← $ᵗ; contM (Function.update gM (tag, n) u) u`, and the
            -- `hMpatchTable` rewrite absorbs the patched `gM` into a `cacheQuery` against the
            -- original `gM`, matching the `hIh u` LHS shape.
            set contM : (TagId × Nonce → Digest) → Digest →
                ProbComp (Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest)) :=
              fun gM u =>
                (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending sM.2 gM))
                  (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                  (advM, multipleBadAdvance tag sB
                    (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
              with hcontM
            have hLHS_lift :
                𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$> contM gM (OracleComp.tableExtending sM.2 gM (tag, n))]
                = 𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$> contM (Function.update gM (tag, n) u) u] := by
              -- Step 1: collapse `tableExtending sM.2 gM (tag, n)` to `gM (tag, n)`.
              have hStep1 :
                  𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$> contM gM (OracleComp.tableExtending sM.2 gM (tag, n))]
                  = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$> contM gM (gM (tag, n))] := by
                refine evalDist_bind_congr_of_support _ _ _ fun gM _ => ?_
                rw [hMcellRead gM]
              rw [hStep1]
              -- Step 2: apply the cell-extract helper.
              haveI : Nonempty Digest :=
                ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
              exact evalDist_uniformSample_bind_cell_extract (R := Digest)
                (D := TagId × Nonce) (tag, n)
                (fun gM u =>
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      z.1) <$> contM gM u)
            -- The patched-`gM` form on the RHS of `hLHS_lift` is distributionally equal to the
            -- `cacheQuery`-extended form via `hMpatchTable`.
            have hLHS_align :
                𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$> contM (Function.update gM (tag, n) u) u]
                = 𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending (sM.2.cacheQuery (tag, n) u) gM))
                        (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, u⟩ : TagTranscript Nonce Digest)))] := by
              refine evalDist_bind_congr_of_support _ _ _ fun u _ => ?_
              refine evalDist_bind_congr_of_support _ _ _ fun gM _ => ?_
              show 𝒟[(fun z => z.1) <$> contM (Function.update gM (tag, n) u) u] = _
              rw [hcontM]
              show 𝒟[(fun z => z.1) <$>
                  (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending sM.2 (Function.update gM (tag, n) u)))
                    (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                    (advM, multipleBadAdvance tag sB
                      (some (⟨n, u⟩ : TagTranscript Nonce Digest)))] = _
              rw [hMpatchTable gM u]
            -- **Hybrid-side cell-patch transformation.** Same shape as the multi side, with the
            -- hybrid cell `((tag, sidH), n)`, the hybrid handler `hybridTableHandler`, and the
            -- hybrid post-state `advH n`. The cell-is-none hypothesis is `hHcellNone`.
            have hHcellRead : ∀ gH : (TagId × Fin sessionsPerTag) × Nonce → Digest,
                OracleComp.tableExtending sH.2 gH ((tag, sidH), n) = gH ((tag, sidH), n) := by
              intro gH
              simp [OracleComp.tableExtending, hHcellNone]
            have hHpatchTable :
                ∀ (gH : (TagId × Fin sessionsPerTag) × Nonce → Digest) (u : Digest),
                  OracleComp.tableExtending sH.2 (Function.update gH ((tag, sidH), n) u)
                    = OracleComp.tableExtending (sH.2.cacheQuery ((tag, sidH), n) u) gH := by
              intro gH u
              rw [← OracleComp.tableExtending_update_of_none sH.2 gH hHcellNone u,
                ← OracleComp.tableExtending_cacheQuery sH.2 gH ((tag, sidH), n) u]
            set contH : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → Digest →
                ProbComp Bool :=
              fun gH u =>
                (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending sH.2 gH))
                  (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' (advH n)
              with hcontH
            have hRHS_lift :
                𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gH =>
                    contH gH (OracleComp.tableExtending sH.2 gH ((tag, sidH), n))]
                = 𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gH =>
                    contH (Function.update gH ((tag, sidH), n) u) u] := by
              have hStep1 :
                  𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gH =>
                      contH gH (OracleComp.tableExtending sH.2 gH ((tag, sidH), n))]
                  = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gH =>
                      contH gH (gH ((tag, sidH), n))] := by
                refine evalDist_bind_congr_of_support _ _ _ fun gH _ => ?_
                rw [hHcellRead gH]
              rw [hStep1]
              haveI : Nonempty Digest :=
                ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
              exact evalDist_uniformSample_bind_cell_extract (R := Digest)
                (D := (TagId × Fin sessionsPerTag) × Nonce) ((tag, sidH), n)
                (fun gH u => contH gH u)
            have hRHS_align :
                𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gH =>
                    contH (Function.update gH ((tag, sidH), n) u) u]
                = 𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gH =>
                      (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending (sH.2.cacheQuery ((tag, sidH), n) u) gH))
                        (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' (advH n)] := by
              refine evalDist_bind_congr_of_support _ _ _ fun u _ => ?_
              refine evalDist_bind_congr_of_support _ _ _ fun gH _ => ?_
              show 𝒟[contH (Function.update gH ((tag, sidH), n) u) u] = _
              rw [hcontH]
              show 𝒟[(simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending sH.2 (Function.update gH ((tag, sidH), n) u)))
                  (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' (advH n)] = _
              rw [hHpatchTable gH u]
            -- **Multi-side BAD cell-patch transformation.** Same `contM`/`hMcellRead`/`hMpatchTable`
            -- machinery as the LHS lift, just with the `(z.1, z.2.2)` projection.
            have hBAD_lift :
                𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      contM gM (OracleComp.tableExtending sM.2 gM (tag, n))]
                = 𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$> contM (Function.update gM (tag, n) u) u] := by
              have hStep1 :
                  𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        contM gM (OracleComp.tableExtending sM.2 gM (tag, n))]
                  = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$> contM gM (gM (tag, n))] := by
                refine evalDist_bind_congr_of_support _ _ _ fun gM _ => ?_
                rw [hMcellRead gM]
              rw [hStep1]
              haveI : Nonempty Digest :=
                ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
              exact evalDist_uniformSample_bind_cell_extract (R := Digest)
                (D := TagId × Nonce) (tag, n)
                (fun gM u =>
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$> contM gM u)
            have hBAD_align :
                𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$> contM (Function.update gM (tag, n) u) u]
                = 𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending (sM.2.cacheQuery (tag, n) u) gM))
                        (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, u⟩ : TagTranscript Nonce Digest)))] := by
              refine evalDist_bind_congr_of_support _ _ _ fun u _ => ?_
              refine evalDist_bind_congr_of_support _ _ _ fun gM _ => ?_
              show 𝒟[(fun z => (z.1, z.2.2)) <$>
                  contM (Function.update gM (tag, n) u) u] = _
              rw [hcontM]
              show 𝒟[(fun z => (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending sM.2 (Function.update gM (tag, n) u)))
                    (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                    (advM, multipleBadAdvance tag sB
                      (some (⟨n, u⟩ : TagTranscript Nonce Digest)))] = _
              rw [hMpatchTable gM u]
            -- **Final integration step.** Rewrite the goal using the three cell-patch lifts to
            -- expose a shared outer `u ← $ᵗ Digest`; apply the disagreement-free pointwise bind
            -- bound (`D := fun _ => False`) with `hIh u` as the pointwise per-`u` inequality.
            -- Unfold `contM`/`contH` in the lift hypotheses to match the goal's syntactic form
            -- (the `set`-introduced abbreviations are propositional, not definitional, so the
            -- goal does not see them after subsequent tactics).
            simp only [hcontM, hcontH]
              at hLHS_lift hLHS_align hRHS_lift hRHS_align hBAD_lift hBAD_align
            rw [show probEvent _ _ = _ from
                probEvent_congr' (fun _ _ => Iff.rfl) (hLHS_lift.trans hLHS_align),
              show probEvent _ _ = _ from
                probEvent_congr' (fun _ _ => Iff.rfl) (hRHS_lift.trans hRHS_align),
              show probEvent _ _ = _ from
                probEvent_congr' (fun _ _ => Iff.rfl) (hBAD_lift.trans hBAD_align)]
            refine probEvent_bind_le_add_bad_of_disagree'
              (D := fun _ : Digest => False)
              (fun u _ hF => absurd hF id)
              (fun u _ _ => ?_)
            -- The pointwise inequality is `hIh u`, with `Pr[= true | ·]` normalized to
            -- `probEvent (· = true) ·` by `← probEvent_eq_eq_probOutput`. The outer goal's RHS
            -- has been re-associated by `rw [add_assoc _ _ _]` so that `s_digest + s_nonce` is
            -- one ε; re-associate `hu`'s RHS in the same way before weakening
            -- `qR * qT' / |Nonce|` to the head's `qR * (qT' + 1) / |Nonce|`.
            have hu := hIh u
            simp only [← probEvent_eq_eq_probOutput] at hu
            rw [add_assoc] at hu
            refine hu.trans ?_
            gcongr
            omega
          · -- **Sub-case B: the multi cache holds `(tag, n)` from a prior reader query.**
            -- Extract `d` from the cell, the constant multi-side cell read, and the freshness
            -- bound for the residual continuation `f (some ⟨n, d⟩)`.
            have hMcellSome : (sM.2 (tag, n)).isSome := by
              rw [Option.isSome_iff_ne_none]; exact hMcellNone
            obtain ⟨d, hMcellEq⟩ : ∃ d, sM.2 (tag, n) = some d := Option.isSome_iff_exists.mp hMcellSome
            have hMcellReadB : ∀ gM : TagId × Nonce → Digest,
                OracleComp.tableExtending sM.2 gM (tag, n) = d := by
              intro gM
              simp [OracleComp.tableExtending, hMcellEq]
            -- `hfreshf (some ⟨n, d⟩)` gives `HopAColFresh (f (some ⟨n, d⟩)) sH sM.2`; applied at
            -- the off-collision multi cell, this exhausts the reader budget at nonce `n`.
            have hPReaderZero :
                OracleComp.IsQueryBoundP (f (some (⟨n, d⟩ : TagTranscript Nonce Digest)))
                  (pReaderNonce n) 0 := by
              refine hfreshf (some (⟨n, d⟩ : TagTranscript Nonce Digest)) n tag hMcellSome ?_
              intro sid hsn
              exact hncoll ⟨sid, hsn⟩
            -- **Open obligation (Sub-B coupling).** Closing this branch requires charging the
            -- per-tag-step Sub-B mismatch against the `qR * |TagId| / |Digest|` slack:
            --
            -- Multi side reads `d` deterministically:
            --   `multi-LHS = Pr[= true | gM ← $ᵗ; ... (f (some ⟨n, d⟩)) ... (advM, mbAdv tag sB (some ⟨n, d⟩))]`
            -- which is independent of `gM (tag, n)` since `sM.2 (tag, n)` overrides via
            -- `tableExtending`.
            --
            -- Hybrid side draws fresh `u` at `((tag, sidH), n)`:
            --   `hybrid-RHS = Pr[= true | gH ← $ᵗ; ... (f (some ⟨n, gH ((tag,sidH),n)⟩)) ... (advH _)]`
            -- which is uniform in the cell value.
            --
            -- The standard `HopACoupling_tag_step` does NOT apply (it requires
            -- `sM.2 (tag, n) = none`). Strategy options:
            --   (a) Define a Sub-B-aware coupling that allows the multi cache to already hold
            --       `d` and requires the hybrid draw to land on `d` (prob `1/|Digest|`); charge
            --       the off-coupling probability into the running slack.
            --   (b) Bound multi-LHS ≤ |Digest| * (hybrid-RHS at u = d) ≤ |Digest| * hybrid-RHS,
            --       impractical since |Digest| is large.
            --   (c) Use `hPReaderZero` more aggressively: since the residual makes no further
            --       reader queries at `n`, the multi-hybrid difference is only via tag-step
            --       cache reads — bound by `(sessionsPerTag * |TagId|) / |Nonce|`. Doesn't
            --       match the existing slack shape `qR * |TagId| / |Digest|`.
            --
            -- Approach (a) appears closest but requires extending `HopACoupling` with a
            -- "tolerated cell-state mismatch" clause and a corresponding slack accounting in
            -- the inductive bound. This may be cleaner to land as a separate refinement of
            -- the bound statement.
            sorry
      · -- Slot exhausted: both table handlers return `none` with state untouched, so the step
        -- collapses to the continuation `f none` and the goal is exactly the induction hypothesis.
        have hnotH : ¬ sH.1.sessionsUsed tag < sessionsPerTag := by
          rw [← congrFun hInv.1 tag]; exact hslot
        have hM : ∀ g : TagId × Nonce → Digest,
            multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) (sM.1, sB)
            = pure (none, sM.1, sB) := by
          intro g
          change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) sM.1
              >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1)) = pure (none, sM.1, sB)
          rw [multipleTableHandler_tag_run_of_not_lt g tag sM.1 hslot]
          rfl
        have hH : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) gS (Sum.inl tag) sH.1
            = pure (none, sH.1) :=
          fun gS => hybridTableHandler_tag_run_of_not_lt gS tag sH.1 hnotH
        simp only [hM, hH, pure_bind]
        -- Weaken the IH's `qR * qT' / |Nonce|` slack to the head's `qR * (qT' + 1) / |Nonce|`.
        -- The `pure_bind` simp lets the goal expose its plain-IH shape; the `gcongr` subgoals on
        -- the success/bad terms are reflexive after that, and only the slack weakening remains.
        refine (ih none qR qT' sM sH sB hInv (hqRf none) (hqTf none) (hdistf none)
            (hfreshf none)).trans ?_
        gcongr <;> first | rfl | omega
    | inr transcript =>
      -- **Reader step (open).** Both table handlers fold the same column deterministically; the
      -- multiple reader may speculatively accept where the hybrid rejects. Charge the per-query
      -- asymmetry `|TagId|/|Digest|` via `probEvent_multipleReader_disagree_le` and
      -- `multipleReader_accepts_of_hybridCacheAccepts`; `hdist` (threaded) rules out a second
      -- reader query at a written nonce.
      sorry

/-- **Hop A, core coupling bound.** Threaded by the reader-aware coupling invariant `HopACoupling`
and the freshness witness `HopAColFresh`, the instrumented multiple handler's success probability
is bounded by the lazy hybrid handler's plus the bad-event probability plus the reader-slack term
`qR * |TagId| / |Digest|`.

**Eager route.** Both worlds are eagerized to deterministic-table handlers
(`evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending`,
`evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending`); the resulting deterministic runs are
coupled cell-by-cell by `multipleBadEager_le_hybridEager_aux`. -/
private lemma multipleBad_le_hybrid_add_bad_add_slack_aux [Fintype Nonce] [Fintype Digest]
    (oa : UnlinkAdversary TagId Nonce Digest) (qR qT : ℕ)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : HopACoupling (sessionsPerTag := sessionsPerTag) sM sH sB)
    (hqR : OracleComp.IsQueryBoundP oa (fun i => i.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP oa (fun i => i.isLeft) qT)
    (hdist : ∀ n : Nonce, OracleComp.IsQueryBoundP oa (pReaderNonce n) 1)
    (hfresh : HopAColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) oa sH sM.2) :
    Pr[= true | (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' (sM, sB)] ≤
      Pr[= true | (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' sH] +
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run (sM, sB)] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qR * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
  classical
  -- **Eager route, step A.** Eagerize all three `Pr` terms with the landed equivalences, then
  -- discharge the resulting eager-coupled bound by `multipleBadEager_le_hybridEager_aux`.
  have hM := evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending
    (sessionsPerTag := sessionsPerTag) oa sM.1 sM.2 sB
  have hH := evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending oa sH.1 sH.2
    hInv.2.2.2.2.2.2.2.2
  -- Multiple-side success term: `run' = (·.1) <$> run`, factored through `(z.1,z.2.2) <$> run`.
  have hMsucc :
      Pr[= true | (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' (sM, sB)] =
      Pr[= true | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)] := by
    rw [probOutput_def, probOutput_def]
    have hlhs : (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' (sM, sB) =
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.1) <$>
          ((fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => (z.1, z.2.2)) <$>
            (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run (sM, sB)) := by
      rw [Functor.map_map]; rfl
    have hrhs : (do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)) =
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.1) <$>
          (do
            let gM ← $ᵗ (TagId × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)) := by
      rw [map_bind]
      refine bind_congr fun gM => ?_
      rw [Functor.map_map]
    have hM' : (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
          (z.1, z.2.2)) <$>
        𝒟[(simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) oa).run (sM, sB)]
        = 𝒟[do
            let g ← $ᵗ (TagId × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending sM.2 g)) oa).run (sM.1, sB)] := by
      rw [← evalDist_map]; exact hM
    rw [hlhs, hrhs, evalDist_map, evalDist_map, evalDist_map, hM']
  -- Multiple-side bad term: factored through `(z.1,z.2.2) <$> run`.
  have hMbad :
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run (sM, sB)] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)] := by
    have hbadev :
        (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad = true) =
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.2.bad = true) ∘
          (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => (z.1, z.2.2)) := rfl
    rw [hbadev, ← probEvent_map]
    exact probEvent_congr' (fun _ _ => Iff.rfl) hM
  -- Hybrid-side success term.
  have hHsucc :
      Pr[= true | (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' sH] =
      Pr[= true | do
        let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sH.2 gH)) oa).run'
          sH.1] := by
    rw [probOutput_def, probOutput_def]
    have := hH
    rw [show ((sH.1, sH.2) : HybridState TagId Nonce sessionsPerTag × _) = sH from rfl] at this
    rw [this]
  rw [hMsucc, hHsucc, hMbad]
  exact multipleBadEager_le_hybridEager_aux oa qR qT sM sH sB hInv hqR hqT hdist hfresh

/-- **Hop A.** Under `HasDistinctUnlinkReaderNonces` and a reader-query bound `qReader`, the
multiple-session ideal world succeeds with probability at most that of the hybrid world plus the
within-tag nonce-collision probability plus the reader-slack term `qReader * |TagId| / |Digest|`. -/
theorem multipleIdeal_le_hybrid_add_bad [Fintype Nonce] [Fintype Digest]
    (adversary : UnlinkAdversary TagId Nonce Digest) (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag)
    (hdist : HasDistinctUnlinkReaderNonces adversary) :
    Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] ≤
      Pr[= true | (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (HybridState.init, ∅)] +
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)] +
      ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
  rw [← probOutput_multipleBad_run'_eq_multipleIdeal adversary (UnlinkState.init, ∅)
    UnlinkBadState.init]
  exact multipleBad_le_hybrid_add_bad_add_slack_aux adversary qReader qTag
    (UnlinkState.init, ∅) (HybridState.init, ∅) UnlinkBadState.init
    HopACoupling_init hqReader hqTag
    ((hasDistinctUnlinkReaderNonces_iff adversary).mp hdist)
    (hopAColFresh_init adversary (HybridState.init, ∅))

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
