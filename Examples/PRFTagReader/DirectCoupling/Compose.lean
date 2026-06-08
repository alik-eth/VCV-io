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
    exact le_add_right (le_add_right (le_add_right (le_add_right le_rfl)))
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
          rw [hSplit]
          -- Goal: `success + bad + slack₁ + (qR/|N| + slack₂(qT')) + slack₃`.
          -- Reassociate to `success + bad + qR/|N| + (slack₁ + slack₂(qT') + slack₃)`.
          rw [show ∀ a b c d e f : ℝ≥0∞, a + b + c + (d + e) + f = a + b + d + (c + e + f) from
                fun a b c d e f => by ring]
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
            rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput, ← add_assoc, ← add_assoc]
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
            rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput, ← add_assoc, ← add_assoc]
            exact hihA
        · -- **Tag slot-positive step (slot available).** M reads `gS((tag, 0), n)` (sub-table);
          -- S reads `gS((tag, k), n)` for `k = s.sessionsUsed tag ≥ 1`. Off-bad (fresh nonce),
          -- both cells are independent uniforms → marginal distribution agree (each is uniform
          -- on Digest). On-bad (nonce aliases prior), `multipleBadAdvance` flips the bad flag;
          -- the M-side bad event absorbs the deterministic divergence via
          -- `multipleBadTableHandler_run_preserves_bad`. Use `probEvent_bind_le_add_bad_disagree`
          -- with `D := λ n, (sB.responses (tag, n)).isSome` for the disagreement (collision)
          -- mass charging `Pr[D | $ᵗ Nonce] ≤ qT/|Nonce|`. The off-D branch closes by the
          -- per-cell uniformity of `gS((tag, 0), n)` vs `gS((tag, k), n)`. See DC Session 6 task.
          sorry
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
      -- **Phase C (next commit).** Lift unfolds via `simp only [..., hMstep_with_bad, hSstep]`,
      -- case-split on `Macc gS` and the `(Macc, Sacc) = (F, T)` flip event, bound flip mass
      -- by `|TagId| · sp / |Digest|`, apply IH at each `b ∈ {T, F}` for the off-flip branch.
      sorry

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
