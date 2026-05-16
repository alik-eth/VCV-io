/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader

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
  sorry

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
  sorry

/-- Identical-until-bad coupling: the gap between the two random-function worlds (the ideal-PRF
experiments of the multiple- and single-session reductions) is bounded by the nonce-collision
probability `unlinkBadExp`. The two worlds proceed identically until two sessions of one tag draw
the same nonce — exactly the event `unlinkBadExp` records. -/
theorem unlinkPRFIdeal_gap_le_unlinkBad
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    (Pr[= true | PRFScheme.prfIdealExp (unlinkToMultiplePRFReduction
          (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) adversary)]).toReal -
        (Pr[= true | PRFScheme.prfIdealExp (unlinkToSinglePRFReduction
          (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) adversary)]).toReal ≤
      (Pr[= true | unlinkBadExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary]).toReal := by
  sorry

/-! ## Main reduction theorem -/

/-- Unlinkability reduction: the multiple-vs-single advantage is bounded by one PRF advantage for
the multiple-session world, one PRF advantage for the single-session world, and the bad-event
probability from the intermediate nonce-collision world.

The proof telescopes the three bridge lemmas:
`Pr[Multiple] − Pr[Single]` splits as `(Pr[Multiple] − Pr[MultRF]) + (Pr[MultRF] − Pr[SingleRF])
+ (Pr[SingleRF] − Pr[Single])`, where the first and last differences are absorbed into the two
PRF advantages and the middle difference is bounded by `Pr[unlinkBadExp]`. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_collision
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    ∃ multiAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      ∃ singleAdv : PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest,
        unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) prfs adversary ≤
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv +
            (Pr[= true | unlinkBadExp (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary]).toReal := by
  refine ⟨unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary,
    unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary, ?_⟩
  have h1 := prfRealExp_unlinkToMultiplePRFReduction_eq_unlinkMultipleExp prfs adversary
  have h2 := prfRealExp_unlinkToSinglePRFReduction_eq_unlinkSingleExp prfs adversary
  have h3 := unlinkPRFIdeal_gap_le_unlinkBad (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary
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

/-- Final unlinkability bound: two PRF advantages plus the explicit session-collision term. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ)
    (hmax : ∀ nonce : Nonce,
      (Pr[= nonce | ($ᵗ Nonce)]).toReal ≤ maxNonceProb) :
    ∃ multiAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      ∃ singleAdv : PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest,
        unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) prfs adversary ≤
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv +
            ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ) * maxNonceProb := by
  obtain ⟨multiAdv, singleAdv, hSum⟩ :=
    unlinkabilityAdvantage_le_two_prf_plus_collision prfs adversary
  refine ⟨multiAdv, singleAdv, hSum.trans ?_⟩
  have hBad := unlinkBadExp_le_sessionCollisionBound (sessionsPerTag := sessionsPerTag)
    adversary maxNonceProb hmax
  linarith

/-- Tightest unlinkability bound: when nonces are sampled uniformly (as enforced by
`SampleableType`), the session-collision term is exactly `sessionsPerTag² · |TagId| / |Nonce|`. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_uniform_sessionCollisionBound
    [Fintype Nonce]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    ∃ multiAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      ∃ singleAdv : PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest,
        unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) prfs adversary ≤
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv +
            (sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) /
              (Fintype.card Nonce : ℝ) := by
  have hmax : ∀ nonce : Nonce,
      (Pr[= nonce | ($ᵗ Nonce)]).toReal ≤ (Fintype.card Nonce : ℝ)⁻¹ := fun nonce => by
    simp [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  obtain ⟨multiAdv, singleAdv, h⟩ :=
    unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound prfs adversary
      ((Fintype.card Nonce : ℝ)⁻¹) hmax
  exact ⟨multiAdv, singleAdv, by rwa [div_eq_mul_inv]⟩

end UnlinkReduction

end PRFTagReader
