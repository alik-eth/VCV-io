/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.DirectCoupling
import Examples.PRFTagReader.DirectCoupling.StepLemmas
import Examples.PRFTagReader.DirectCoupling.Swap
import Examples.PRFTagReader.DirectCoupling.ReaderCase
import Examples.PRFTagReader.MultipleToHybrid.EagerSetup

/-!
# PRF Tag/Reader Protocol — Direct M_ideal/S_ideal Coupling, Headline Composition

This module composes the per-step direct-coupling primitives from
`Examples.PRFTagReader.DirectCoupling` (the `slotZeroEmbed` / `slotZeroSubTable` cell
identification, the sub-table uniform sampler, the deterministic reader lift, and the
first-session tag-step equality) into the headline bound

```
Pr[multipleIdealQueryImpl true] ≤
  Pr[singleIdealQueryImpl true] + Pr[bad]
    + qReader·|TagId| / |Digest| + qReader·qTag / |Nonce|
    + qReader·|TagId|·sessionsPerTag / |Digest|
    + qTag·|TagId|·sessionsPerTag / |Digest| + qTag·sessionsPerTag / |Digest|
```

for every adversary, with no distinctness hypothesis on its reader nonces. The bound carries two
tag-side slack terms (the last two above) on top of the reader and nonce-aliasing slacks.

The direct coupling identifies the multiple-session world's RO cell `(tag, n)` with the
single-session world's reference-slot cell `((tag, 0), n)` via `slotZeroEmbed` /
`slotZeroSubTable`. Under this identification:

* **Tag step, slot 0.** Both worlds read the cell `((tag, 0), n)` of a shared `gS` — identical
  step (`multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero`).
* **Tag step, slot ≥ 1.** M reads `gS((tag, 0), n)` (sub-table); S reads `gS((tag, k), n)` —
  independent uniforms off a nonce collision. The `multipleBadAdvance` bad flag captures the
  nonce-collision case; off-bad, the per-step output distributions agree marginally because
  both reads are fresh uniforms.
* **Reader step.** Only the slot-0 column at the queried nonce is lazified on both sides, so the M
  reader bit collapses to a deterministic bit `m` of the resulting cache while slot-positive cells
  stay uncached. M-accept implies S-accept (`mReader_accepts_imp_sReader_accepts`), and this
  implication is one-sided: when `m` is `true` both sides continue with the same reply, and when
  `m` is `false` the S-side's slot-positive collision branch is *discarded* over `ℝ≥0∞`, charging
  only the collision event's uniform mass `≤ |TagId| · sessionsPerTag / |Digest|` per reader query.

## Main results

* `multipleBadEager_le_singleEager_DC_aux` — eager-form direct coupling aux, by structural
  induction on the adversary, coupling the multiple-session world directly to the single-session
  world with no distinctness hypothesis on the reader nonces.
* `multipleIdeal_le_singleIdeal_add_bad_DC` — lazy-form headline, the standard eagerization of the
  eager-form aux, again with no reader-nonce distinctness hypothesis.

## Layout

This file is deliberately concentrated in the eager-form aux
`multipleBadEager_le_singleEager_DC_aux`; downstream wrappers (the lazy headline,
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

/-! ### Eager-form direct-coupling aux

The structural induction over the adversary, coupling M-side
`multipleBadTableHandler (slotZeroSubTable gS)` (with `UnlinkBadState` instrumentation) against
S-side `singleTableHandler gS` over a shared single-session RO table `gS`. M is coupled directly to
S via the slot-0 sub-table embedding, with no intermediate hybrid world.

The aux is deliberately formulated in terms of *eager* table handlers and a *shared* draw `$ᵗ gS`;
the lazy headline `multipleIdeal_le_singleIdeal_add_bad_DC` below recovers it via the standard
eagerization equivalences. -/

omit [Nonempty TagId] in
/-- **Direct M-S coupling aux (eager).** Under a shared `$ᵗ gS` sample, the eager-form fine handler
`multipleBadTableHandlerFine (slotZeroSubTable (tableExtending c gS))` (with `UnlinkBadState`
instrumentation) success probability is bounded by the eager-form `singleTableHandler
(tableExtending c gS)` success probability, plus the multiple-bad `bad`-probability, plus four
additive slacks: `qR·|TagId|/|Digest|`, `qRInit·qT/|Nonce|`, `qR·|TagId|·sessionsPerTag/|Digest|`,
and `qT·|TagId|·sessionsPerTag/|Digest|`.

The coupling is hypothesis- and invariant-free at the eager level: no reader-nonce distinctness
hypothesis, no cache-coupling invariant, and no collision-freshness predicate. The bound is
established by structural induction over the adversary `oa`:

* **Tag steps.** The slot-0 sub-table embedding is fixed (independent of state); at slot 0 the M
  and S tag responses agree pointwise. Slot-positive tag divergence is captured by the
  `multipleBadAdvance` bad flag — off-bad, M and S produce statistically identical fresh uniforms
  despite reading different cells. The per-nonce disagreement is split on membership in `R`, the
  set of reader-touched nonces: off `R` the response invariant `hRespInv` carries the closed
  argument through, and the on-`R` mass is charged to the `qRInit·qT/|Nonce|` slack.
* **Reader steps.** Only the slot-0 column at the queried nonce is lazified on both sides (via
  `idealCacheMapM` over the cells `{((T,0), nonce) : T}`), extending the cache `c → c₀` while
  leaving slot-positive cells uncached so the strong cache invariant `hcInv` survives. The M
  reader bit then collapses to a deterministic bit `m` of `c₀`. When `m = true` the S reader also
  accepts (the slot-0 witness lifts), both sides continue with the same reply, and the induction
  hypothesis at `(c₀, qR', R ∪ {nonce})` closes the step. When `m = false`, M rejects; the asymmetry
  `mAcc ⟹ sAcc` is one-sided, so over `ℝ≥0∞` the S-side's slot-positive collision branch is
  *discarded*: the actual S reader bit equals `cacheBadReader gS`, and replacing it by the constant
  `false` reply costs exactly the collision event `E gS := ∃ T sid ≠ 0, gS ((T,sid), nonce) = auth`,
  whose uniform mass `≤ |TagId|·sessionsPerTag/|Digest|` is charged to a single slack unit.

The first-time-per-nonce bookkeeping is threaded through `qRInit`, `R`, and `hqRle : qR + R.card ≤
qRInit`: each reader query inserts its nonce into `R`, and the reader-drawn slot-0 cache entries
only break `hRespInv` off `R`, which the gated form `hRespInv` (conditioned on `n ∉ R`) absorbs.

The aux is deliberately formulated in terms of eager table handlers and a shared draw `$ᵗ gS`; the
lazy headline `multipleIdeal_le_singleIdeal_add_bad_DC` recovers it via the standard eagerization
equivalences. -/
lemma multipleBadEager_le_singleEager_DC_aux [Fintype Nonce] [Fintype Digest]
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
  -- Induction cases: pure / tag slot-zero / tag slot-positive / tag slot-exhausted / reader.
  classical
  induction oa using OracleComp.inductionOn generalizing qR qT s c sB R hqRle hcInv hRespInv with
  | pure b =>
    -- Pure case: both sides collapse the `simulateQ` to `pure b`. After `simp`, the LHS
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
        · -- Slot-zero tag case (k = 0 fresh). The `Sum.inl tag` branch of
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
          -- does not depend on `gFine`. By
          -- `multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero`,
          -- M-handler step = S-handler step, then
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
        · -- Slot-positive tag case (1 ≤ k < sp). M reads slot-0 cell, S reads slot-K cell
          -- (K ≠ 0).
          -- **Cell-pair independence strategy.** Each side marginalizes its own cell via a
          -- single-cell helper (`evalDist_uniformSample_bind_update_map`), giving the IH a fresh
          -- slot-0 draw on the M side; the resulting slot-0 → slot-K cache extension is then
          -- bridged on the S side by the permutation lemma `singleTableHandler_cache_swap_eq`.
          -- No per-step `cacheBadReader` charge is needed at this site: the per-step
          -- `|TagId| · sp / |Digest|` unit carved out of the `qT`-based slack is dropped via
          -- `le_self_add` (cell-pair independence gives per-`n` equality).
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
          -- M-Fine and S step shapes via `slotPositive_MFine_tag_step` /
          -- `slotPositive_S_tag_step`. Note: M reads slot-0 cell of
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
      · -- Slot-exhausted tag case. Both M-Fine and S handlers return `pure (none, s, sB)` /
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
      -- Reader case: the asymmetric-discard step. Delegated to `dcAux_reader_step`, which takes
      -- the induction hypothesis `ih` as an explicit premise.
      exact dcAux_reader_step qRInit qR qT s c sB R hqRle hcInv hRespInv transcript k ih hqR hqT

end UnlinkReduction

/-! ### Lazy-form headline

The lazy-form multiple-vs-single ideal-world bound, holding for every adversary with no
distinctness hypothesis on its reader nonces. Routes through
`multipleBadEager_le_singleEager_DC_aux` via the standard eagerization equivalences for the
multiple-bad handler (`evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending`) and the
single-ideal handler (`probOutput_singleIdeal_run'_eq_tableSample`). -/

namespace UnlinkReduction

/-- **Multi-to-single via direct M-S coupling.** Bounds the multiple-session ideal world by the
single-session ideal world plus the multiple-bad collision probability and five unconditional
slack terms, for every adversary and with no distinctness hypothesis on its reader nonces. Two of
the slacks are tag-side, `qTag·|TagId|·sessionsPerTag / |Digest|` and `qTag·sessionsPerTag /
|Digest|`.

The direct M-S coupling via `slotZeroSubTable` works
unconditionally on the adversary (no nonce-distinctness assumption) because the per-step
identification of M's cell `(tag, n)` with S's cell `((tag, 0), n)` is a fixed embedding, not a
state-dependent one. The bound is supplied by `multipleBadEager_le_singleEager_DC_aux`, lifted to
the lazy ideal handlers by the standard eagerization equivalences and instantiated at `R = ∅`,
`qRInit = qReader`. -/
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
  -- **Step 4b.** Fine-shape bridges. The aux's signature carries an outer
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
  -- `qTag * sessionsPerTag / |Digest|` slack is unused headroom, dropped via `le_self_add`.
  exact haux.trans le_self_add

end UnlinkReduction

end DirectCouplingCompose

end PRFTagReader
