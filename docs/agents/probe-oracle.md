# First-Fire Probe Oracle (Adaptive Guessing and Deferred Sampling)

This guide covers the probe-oracle library in
`VCVio/OracleComp/QueryTracking/RandomOracle/` (`FirstFire.lean`, `ProbeOracle.lean`,
`ProbeEquiv.lean`, `ProbeAmbient.lean`, `ProbeColumn.lean`, `RevealTilt.lean`) and the two
consumer chains that show how to use it (`Examples/PRFTagReader/AuthProbe.lean` and
`Examples/PRFTagReader/DirectCoupling/Sharp*.lean`).

The core object is a lazily sampled oracle whose state records, per cell, exactly what the
adversary's view has determined: `CellKnowledge R` is either `known v` (the value is pinned) or
`excluded S` (a finite set of values ruled out by Boolean misses), and
`ProbeState D R := D → CellKnowledge R`. A *probe* `(d, a)` reveals only the bit
"does cell `d` hold `a`?"; a *reveal* hands over the cell's value. A probe **fires** when it is
genuine (undetermined cell, not-yet-excluded target) and hits. The headline bounds are exact
first-fire telescopes: `q` adaptive probes fire with probability at most `q / (|R| - m)` when
every exclusion set has at most `m` elements.

## When To Reach For This

Three argument shapes the library solves cleanly:

1. **Adaptive guessing at lazily-sampled values, including re-targets.** The adversary guesses
   at cells whose values are drawn on demand, and later guesses may target a cell that already
   answered one Boolean. After a miss at `a₁`, a second probe of the same cell fires with
   conditional probability `1 / (|R| - 1) > 1 / |R|`, so a per-step union bound charging each
   step its maximum overshoots (two probes cost `2 / (|R| - 1)`, exceeding the true total); the
   first-fire telescope `1/|R| + (1 - 1/|R|) · 1/(|R| - 1) = 2/|R|` is exact, and
   `probEvent_probeTwo_retarget_le` meets it with equality. *Litmus test: does a later guess
   depend on the Boolean reply to an earlier guess at the same lazily-sampled cell?*
2. **"Condition on the adversary's view."** `CellKnowledge` (`known v` | `excluded S`) *is* the
   conditional law of the cell given the replies so far — uniform on `Finset.univ \ S` —
   represented syntactically as state. No measure-theoretic conditioning ever appears in a
   proof; `probeStep` draws fresh from the allowed set and retains only the bit. *Litmus test:
   does the paper proof say "conditioned on the transcript, the cell is uniform on the
   remaining values"?*
3. **Deferred sampling / eager-lazy switching.** `genTable K` draws a full table consistent
   with a knowledge state `K` (every cell independent, uniform on its allowed set), and
   `evalDist_genTable_bind_eagerProbeImpl` proves that eager table-then-deterministic-answers
   equals lazy per-query sampling, for every adversary and mid-run knowledge state. *Litmus
   test: does one hop of the proof want the whole table drawn up front while another wants it
   drawn on demand?*

Anti-patterns — do not force these through the probe oracle:

- **Birthday / multi-target collisions**: the event "this query matches *any* previously seen
  value" needs a target set that grows with the transcript; a probe compares one cell against
  one value, and growing target sets are not supported.
- **Joint AND-events across cells**: the fired flag is a monotone OR of per-probe fires; there
  is no machinery for the probability that two specific cells *simultaneously* hold two
  specific values.
- **Lattice hardness reductions**: nothing here is about uniform-cell guessing games; stay in
  `LatticeCrypto/HardnessAssumptions/`.
- **Log-based birthday bounds**: `VCVio/OracleComp/QueryTracking/Birthday.lean` is the tool for
  collision probability over a query log; the probe oracle adds nothing there.

## The Layer Map

| Layer | Key names | What it gives |
|-------|-----------|---------------|
| `FirstFire.lean` | `probeStep`, `probeMany`, `ProbeState.ExclLe`, `CellKnowledge.genuine`, `probEvent_probeMany_le`, `firstFire_telescope_step` | Strategy-form telescope: an adaptive strategy (`List Bool → D × R`) issuing `q` probes from an `ExclLe m` state fires with probability `≤ q / (|R| - m)` |
| `ProbeOracle.lean` | `probeSpec`, `ProbeOp`, `probeImpl`, `revealStep`, `probEvent_simulateQ_probeImpl_le` | The same bound for free-monad adversaries `OracleComp (probeSpec D R) α` under `IsQueryBoundP (fun t => t.isProbe = true) q`; reveal queries are free (never charged, unconstrained) |
| `ProbeEquiv.lean` | `CellKnowledge.allowed`, `genTable`, `ProbeState.Feasible`, `eagerProbeImpl`, `evalDist_genTable_bind_eagerProbeImpl` | Deferred-sampling equivalence: lazy `probeImpl` = draw `genTable K`, answer eagerly. The *equivalence* needs `K.Feasible` (infeasible states make `genTable` fail a.s.); the transferred *bounds* (`probEvent_genTable_bind_eagerProbeImpl_le`) do not |
| `ProbeAmbient.lean` | `probeImplWith`, `eagerProbeImplWith`, `probEvent_simulateQ_probeImplWith_le`, `evalDist_genTable_bind_eagerProbeImplWith`, `knowledgeOfCache`, `evalDist_map_tableExtending_uniformSample`, `probEvent_uniformSample_bind_eagerProbeImplWith_le`, `probEvent_uniformSample_tableExtending_bind_eagerProbeImplWith_le` | Everything above over `spec + probeSpec D R` with ambient queries answered by a `QueryImpl spec ProbComp`; the `tableExtending` bridge enters from a `QueryCache`, and the `$ᵗ (D → R)` entry points connect to eager full-table draws |
| `ProbeColumn.lean` | `probeColumnSplit`, `evalDist_genTable_bind_probeColumnSplit`, `probEvent_probeColumnSplit_fired_le`, `probeColumnSplit_support`, `probeColumnSplit_support_exclLe`, `probOutput_genTable_bind_pure_comp`, `probEvent_apply_eq_genTable_le`, `evalDist_map_comp_equiv_genTable`, `evalDist_map_comp_injective_genTable`, `evalDist_map_comp_genTable_congr` | Column splits: lazify a batch comparison of many cells against one target at the Boolean level. The redistribution law is a single shared prefix, so all positions of a coupling (success, reference, bad) rewrite along it simultaneously. Pushforwards relabel `genTable` along cell equivalences/injections |
| `RevealTilt.lean` | `probEvent_bind_uniformSelectFinset_sdiff_le` | The restricted-vs-full tilt: seeding a continuation from `$ (Finset.univ \ S)` instead of `$ Finset.univ` costs at most `|S| / |V|` on any event — the exact coupling defect, sharper than `|S| / (|V| - |S|)` |

Decision guide:

- Adversary is a bare strategy (no free monad)? `probeMany` + `probEvent_probeMany_le`.
- Adversary is an `OracleComp` over probes/reveals only? `probeImpl` +
  `probEvent_simulateQ_probeImpl_le`.
- Adversary also samples coins or queries other oracles? The `*With` layer in
  `ProbeAmbient.lean`; enter from a cache via `knowledgeOfCache` + the `tableExtending` bridge.
- Two-world coupling where a step reads a whole column or compares conditioned reveals?
  `ProbeColumn.lean` splits + `RevealTilt.lean`, over a shared `genTable`.

## Recipe 1: Single-World Union Bound

The pattern behind the collision bound's forge-growth lemma
(`Examples/PRFTagReader/AuthProbe.lean`); use it to bound "the adversary makes some oracle
output match a target" by `q · (cells per query) / |R|`:

1. Write the deterministic table-keyed handler for your experiment (`authTableHandler g`).
2. Write a translator into the combined signature `unifSpec + probeSpec D R`
   (`authProbeTranslator`): randomness goes through the ambient (left) oracle, honest cell
   creation becomes a *reveal*, and the event-relevant test becomes a batch of *probes* (one
   reader query probes every cell of a column against the transcript's authenticator).
3. Prove per-`g` faithfulness at the term level, not just `evalDist`:
   `fst_simulateQ_eagerProbeImplWith_translator_run` shows
   `Prod.fst <$>` (coupled run) `= liftM` (auth run) — the eager implementation is
   deterministic given `g`, so this is a structural induction.
4. Prove fired dominance as a support invariant
   (`simulateQ_eagerProbeImplWith_translator_support_fired`): every `known` cell is
   honest-or-already-fired, a same-(cell, value) re-probe is an excluded-mem deterministic
   `false`, so any growth of the forgery log forces the fired flag (monotone by
   `probeImpl_run_support_fired_mono`).
5. Transfer the query bound (`isQueryBoundP_run_simulateQ_authProbeTranslator`): `q` reader
   queries become `q * |TagId|` probe queries.
6. Conclude through the ambient entry point
   `probEvent_uniformSample_tableExtending_bind_eagerProbeImplWith_le`: starting cache `c` maps
   to `knowledgeOfCache c` (all exclusion sets empty), giving `q · |TagId| / |Digest|`.

## Recipe 2: Two-World Sharp Coupling

The pattern behind the sharp unlinkability headline
(`Examples/PRFTagReader/DirectCoupling/Sharp{Aux,ReaderCase,TagSlotPositive,Compose}.lean`).
This is a *recipe*, not an API: the invariant and case analysis are protocol-specific, and a
second relational consumer should prompt extracting the reusable skeleton. For a minimal
self-contained instance (one reader step, one tag step), read
`Examples/PRFTagReader/DirectCoupling/ProbeGate.lean` first.

- Both worlds read **one shared probe state `K`** on the larger world's cell domain; the three
  coupling positions `sharpM`, `sharpS`, `sharpBad` all open with the same `genTable K` draw.
- The induction (`sharpCoupling_aux`) threads a six-conjunct invariant:
  `slotPosExcluded` (slot-positive cells never determined — the poisoned-cache firewall),
  `liveSlotsFresh` (unconsumed sessions untouched, so S-side reveals stay full-uniform),
  `knownRecorded` (determined cells are tag-written, so a tag step meeting one fires `bad`),
  `ProbeState.ExclLe` (per-cell exclusion budget `qRInit - qR`),
  `slotZeroRowExcl ≤ qRInit - qR` (per-row potential paying the averaged tilt), and
  `ProbeState.Feasible`.
- The slack decomposes into three charges, each tied to one case:
  - **fire** `qR · |TagId| / (|Digest| - qRInit)` — reader case (`sharpAux_reader_step`): the
    column split `evalDist_genTable_bind_probeColumnSplit` materializes only Booleans, and the
    fired mass `probEvent_probeColumnSplit_fired_le` is dropped outright (the IH never sees
    fired states);
  - **tilt** `qT · qRInit / (|Nonce| · |Digest|)` — slot-positive tag case
    (`sharpAux_tag_slotPositive`): the M side reveals from `Digest ∖ S₀`, the S side from all
    of `Digest`; `probEvent_bind_uniformSelectFinset_sdiff_le` charges `|S₀| / |Digest|`, paid
    from the `slotZeroRowExcl` potential averaged over the fresh nonce
    (`probEvent_bind_le_add_tsum` in `VCVio/EvalDist/Monad/Disagreement.lean`);
  - **discard** `qR · |TagId| · sessionsPerTag / (|Digest| - qRInit)` — reader case, off-fire
    `false` branch: the S-side acceptance reduces to a slot-positive collision indicator,
    replaced by `ko` at the cost of its mass under the residual table
    (`probEvent_apply_eq_genTable_le` plus a union bound over the column).
- The slot-zero tag case (`sharpAux_tag_slotZero` in `SharpAux.lean`) couples exactly: both
  worlds reveal the same shared cell, zero charge. The slot-positive case re-centers the two
  worlds on one knowledge state via a cell-swap pushforward (`evalDist_sharpS_swap_bridge`,
  built from `update_known_eq_swap_update`, `evalDist_map_comp_equiv_genTable`, and
  `singleTableHandler_simulateQ_swap_invariant`); bad-state bookkeeping invisible to the output
  is erased by the cacheBad bridges in `MultipleToHybrid/EagerSetup.lean` before the IH fires.
- Assembly (`multipleIdeal_le_singleIdeal_add_bad_DC_sharp` in `SharpCompose.lean`)
  instantiates at `ProbeState.init` and identifies `genTable` with the uniform table draw
  (`evalDist_genTable_init`).

## Lean Tripwires

Mechanical issues that have each cost real time in these files:

- **Non-Miller continuation positions diverge in term mode.** Applying a lemma whose
  continuation argument sits in non-Miller position (e.g. `fun u gS => …` where the metavariable
  must unify against a large `(gS d)`-dependent body) with a stated expected type sends `whnf`
  unification off a cliff. Fix: defer — `have h := lemma … fun u gS => …; exact h`. Several
  precedents in `SharpAux.lean`.
- **`rw [support_pure]` fails in `OptionT ProbComp`.** The `Alternative`-derived `Pure` instance
  is not syntactically the one in the lemma; use `mem_support_pure_iff` instead.
- **Sum-`Range` payload types need ascriptions.** When a handler mixes components of a `+`-spec,
  values of `spec.Range (Sum.inr t)` are not reducibly the component's range; expect explicit
  type ascriptions or `change`-retyping (see the ascribed `pure` payloads in
  `ProbeAmbient.lean` and the handler lemmas in `AuthProbe.lean`).
- **Ascribe do-lambda result types.** Anonymous continuations inside `do` blocks that return
  state tuples elaborate to the wrong monad without a result-type ascription.
- **Use full `ProbeState.*` names on `Function.update` terms.** `ProbeState` is an `abbrev` for
  a pi type, so dot-notation generalization fails on updated states; write
  `ProbeState.ExclLe (Function.update st d _) m`, not `(Function.update st d _).ExclLe m`,
  in statements you intend to `rw` with.
- **`rcases h : e` substitutes `e` in the goal.** When `e` occurs in the goal and you only
  wanted the hypothesis, the substitution changes the goal shape; use
  `obtain`/`cases` with an explicit equation when that matters.

## Semantic Load-Bearing Facts

The sharp coupling's optimality analysis depends on three properties of the PRF tag/reader
source; changing any of them silently invalidates the slack accounting (they would resurrect a
`Θ(qT / |Nonce|)` adversary the current slacks do not cover):

- the single-session reader samples **all** slots of a tag's column
  (`singleIdealQueryImpl_reader_run` in `Examples/PRFTagReader/Table.lean` tests
  `Finset.univ : Finset (TagId × Fin sessionsPerTag)`);
- `bad` fires on **within-tag repeats only** (`multipleBadAdvance` in
  `Examples/PRFTagReader/MultipleToHybrid/Setup.lean`);
- reader replies are **one bit** (`ReaderReply` is `ok | ko`; leaking *which* cell matched
  breaks the analysis).

The sharp and sibling headlines deliberately coexist: see the comparison in the module
docstring of `Examples/PRFTagReader/DirectCoupling/SharpCompose.lean` — at
`qReader ≥ |Digest|` the sharp denominators vanish while the sibling
`multipleIdeal_le_singleIdeal_add_bad_DC` (`DirectCoupling/Compose.lean`) stays finite, and in
realistic regimes the sharp tilt is strictly smaller. Do not delete either.
