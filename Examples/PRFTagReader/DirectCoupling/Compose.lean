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
          -- **Phase C (next commit).** Per-`n`: case-split on `c ((tag, 0), n)`.
          -- * `some u₀`: cell read is `u₀`, apply IH at `(k (some ⟨n, u₀⟩), qR, qT', advM, c,
          --   multipleBadAdvance tag sB (some ⟨n, u₀⟩))`.
          -- * `none`: marginalize cell `((tag, 0), n)` via `evalDist_uniformSample_bind_update_map`,
          --   apply IH at `(k (some ⟨n, u⟩), qR, qT', advM, c.cacheQuery ((tag, 0), n) u,
          --   multipleBadAdvance tag sB (some ⟨n, u⟩))` for each fresh `u`.
          -- Integrate over `n` via `probEvent_bind_le_add_bad_disagree` with empty disagree set,
          -- or via the elementary `probEvent_uniformSample_bind_le` form.
          sorry
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
      -- **Reader query.** `mReader_accepts_imp_sReader_accepts` (Session 2) gives the
      -- M-accept → S-accept direction deterministically. The S-accepts-but-M-rejects gap (in
      -- the favorable direction for the headline inequality when output `true` on accept) is
      -- bounded by the cell-cardinality slack `|TagId| · sessionsPerTag / |Digest|` per reader
      -- query — the same shape as `probEvent_eagerReaderFlip_le` in `MultipleToHybrid/Eager.lean`
      -- but with `sessionsPerTag`-times more cells on the S side. See DC Session 6 task.
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
  -- **Plan (Session 7).** Eagerize the LHS and the bad term via
  -- `evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending` at the initial cache `∅`,
  -- which collapses `tableExtending ∅ g` to `g` via `OracleComp.tableExtending_empty`. Eagerize
  -- the S-side term via `probOutput_singleIdeal_run'_eq_tableSample`. Bridge the M-side from `g`
  -- (over `TagId × Nonce → Digest`) to `slotZeroSubTable gS` (over the larger S-side domain) via
  -- `evalDist_slotZeroSubTable_uniformSample` (DirectCoupling.lean Session 1). Then apply
  -- `multipleBadEager_le_singleEager_DC_aux`.
  sorry

end UnlinkReduction

end DirectCouplingCompose

end PRFTagReader
