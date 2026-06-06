/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.MultipleToHybrid.EagerReader

/-!
# PRF Tag/Reader Protocol — Multiple-to-hybrid eager coupling, reader step (Path A)

The Path-A reader-query branch of `multipleBadEager_le_hybridEager_aux_PathA`.

Path A replaces the `HasDistinctUnlinkReaderNonces` hypothesis (`hdist`) of the original
`multipleBadEager_reader_step` with a `MultipleBadPathACoupling` invariant and widens the bad
event to include the `badReader` flag. The PathA handler `multipleBadTableHandlerPathA` advances
the bad state on each reader query via `multipleBadReaderAdvanceEager`, which flips `badReader`
when a stale cell at `transcript.nonce` matches `transcript.auth`. The widened bad event
`z.2.bad ∨ z.2.badReader` therefore charges exactly the cases the original `hcol` ruled out.

The lemma `multipleBadEager_reader_step_PathA` discharges the `| inr transcript =>` branch of the
`query_bind` case in the Path-A central induction. The strategy mirrors the original
`multipleBadEager_reader_step`, with two key differences:

* The PathA LHS handler reduces `(Sum.inr transcript) (sM.1, sB)` to `pure (bit, sM.1, sB')`
  where `sB' := multipleBadReaderAdvanceEager transcript g sB`. The bit is determined by
  `unlinkReaderAccepts` exactly as in the original; the advance only affects the bad-state
  component, which is projected away on the success side and charged on the bad side.
* The off-`D` IH application uses `MultipleBadPathACoupling_reader_step` (lazy → post-reader
  cache `rs.2`) to thread the Path-A coupling through the IH; the disagreement set `D` is
  unchanged from the original.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- **Path-A reader step of the eager-coupled core.** Closes the `| inr transcript =>` branch of
the `query_bind` case inside `multipleBadEager_le_hybridEager_aux_PathA`. Both handlers collapse
the head reader query to a deterministic `pure`; the PathA LHS additionally advances the bad
state via `multipleBadReaderAdvanceEager`. Lazifying the multi-side table draw to
`idealCacheMapM cells sM.2` exposes a disagreement set bounded by `|TagId| / |Digest|`
(`probEvent_multipleReader_disagree_le`); off the disagreement set the IH closes the
per-list-`rs` pointwise bound via `MultipleBadPathACoupling_reader_step`. -/
lemma multipleBadEager_reader_step_PathA [Fintype Nonce] [Fintype Digest]
    (transcript : TagTranscript Nonce Digest)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inr transcript) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (hoa : oa = liftM (OracleSpec.query
      (spec := UnlinkOracleSpec TagId Nonce Digest) (Sum.inr transcript)) >>= f)
    (qR qT qRInit : ℕ)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : MultipleHybridCoupling (sessionsPerTag := sessionsPerTag) sM sH sB)
    (hAB : MultipleBadPathACoupling (TagId := TagId) (Nonce := Nonce) (Digest := Digest) sM.2 sB)
    (hqR : OracleComp.IsQueryBoundP oa (fun i => i.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP oa (fun i => i.isLeft) qT)
    (hfresh : MultipleHybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) oa sB sH sM.2)
    (hCacheBound : ∀ tag : TagId,
      (Finset.univ.filter (fun n : Nonce =>
        (sM.2 (tag, n)).isSome ∧
          ¬ ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n)).card ≤
        qRInit - qR)
    (hqRle : qR ≤ qRInit)
    (ih : ∀ (u : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inr transcript))
        (qR qT qRInit : ℕ)
        (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
        (sH : HybridState TagId Nonce sessionsPerTag ×
          (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
        (sB : UnlinkBadState TagId Nonce Digest),
        MultipleHybridCoupling (sessionsPerTag := sessionsPerTag) sM sH sB →
        MultipleBadPathACoupling (TagId := TagId) (Nonce := Nonce) (Digest := Digest) sM.2 sB →
        OracleComp.IsQueryBoundP (f u) (fun i => i.isRight = true) qR →
        OracleComp.IsQueryBoundP (f u) (fun i => i.isLeft = true) qT →
        MultipleHybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (f u) sB sH sM.2 →
        (∀ tag : TagId,
          (Finset.univ.filter (fun n : Nonce =>
            (sM.2 (tag, n)).isSome ∧
              ¬ ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n)).card ≤
            qRInit - qR) →
        qR ≤ qRInit →
        Pr[= true | do
            let gM ← $ᵗ (TagId × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
              (simulateQ (multipleBadTableHandlerPathA (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending sM.2 gM)) (f u)).run (sM.1, sB)] ≤
          Pr[= true | do
            let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sH.2 gH)) (f u)).run'
              sH.1] +
          Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad ∨ z.2.badReader | do
            let gM ← $ᵗ (TagId × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerPathA (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending sM.2 gM)) (f u)).run (sM.1, sB)] +
          ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
          ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞)) :
    Pr[= true | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerPathA (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)] ≤
      Pr[= true | do
        let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sH.2 gH)) oa).run'
          sH.1] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad ∨ z.2.badReader | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandlerPathA (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
  sorry

end UnlinkReduction

end PRFTagReader
