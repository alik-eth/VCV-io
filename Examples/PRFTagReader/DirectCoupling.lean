/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.Table

/-!
# PRF Tag/Reader Protocol — Direct M_ideal/S_ideal Coupling Foundations

Session 1 foundations for the direct coupling that identifies the multiple-session ideal world's
cell `(tag, n)` with the reference slot `((tag, 0), n)` of the single-session ideal world.

The two ideal worlds run on different random-oracle tables — `g : TagId × Nonce → Digest` for the
multiple-session world and `gS : (TagId × Fin sessionsPerTag) × Nonce → Digest` for the
single-session world. The coupling map embeds the multiple-session domain into the single-session
domain along the reference session slot `0`, so that the multiple-session table is recovered as a
sub-table of the single-session one.

## Main definitions

* `slotZeroEmbed` — the cell-identification embedding
  `(tag, n) ↦ ((tag, 0), n)` from the multiple-session domain into the single-session domain.
* `slotZeroSubTable` — the multiple-session sub-table of a single-session table obtained by
  precomposing with `slotZeroEmbed`.

## Main results

* `slotZeroEmbed_injective` — the embedding is injective, the prerequisite for marginalization
  of a uniform single-session table onto a uniform multiple-session sub-table.
* `evalDist_slotZeroSubTable_uniformSample` — drawing `gS` uniformly and projecting through
  `slotZeroSubTable` yields the uniform distribution on multiple-session tables. This is the
  eager-form coupling lifting the single-session sampler to a multiple-session sub-sampler.
* `mReaderCellsFinset_image_subset_sReaderCellsFinset` — at any fixed transcript, the
  multiple-side reader cells `{(tag, nonce) | tag ∈ TagId}` embed (via `slotZeroEmbed`) into the
  single-side reader cells `{((tag, sid), nonce) | tag ∈ TagId, sid ∈ Fin sessionsPerTag}` — the
  cell-level inclusion that underlies the slack-free reader-side bound in subsequent sessions.

The `slotZeroEmbed` and `slotZeroSubTable` names are thin, intent-naming aliases over the
established sibling `projectTable`; the distribution and cell-subset lemmas re-derive the
underlying facts in the explicit shape used by the direct coupling argument.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section DirectCoupling

variable {TagId Nonce Digest : Type}
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-! ### The cell-identification embedding -/

/-- The cell-identification embedding for the direct M_ideal/S_ideal coupling.

The multiple-session ideal world's domain `TagId × Nonce` embeds into the single-session ideal
world's domain `(TagId × Fin sessionsPerTag) × Nonce` along the reference session slot `0`:
`(tag, n) ↦ ((tag, 0), n)`. -/
@[reducible] def slotZeroEmbed :
    TagId × Nonce → (TagId × Fin sessionsPerTag) × Nonce :=
  fun p => ((p.1, (0 : Fin sessionsPerTag)), p.2)

@[simp] lemma slotZeroEmbed_apply (tag : TagId) (n : Nonce) :
    (slotZeroEmbed (sessionsPerTag := sessionsPerTag) (tag, n)) =
      ((tag, (0 : Fin sessionsPerTag)), n) := rfl

/-- The cell-identification embedding is injective.

This is the prerequisite for marginalization: the reference-slot cells of a single-session table
form a fresh, independent uniform block, reindexed by the multiple-session domain. -/
lemma slotZeroEmbed_injective :
    Function.Injective
      (slotZeroEmbed (TagId := TagId) (Nonce := Nonce) (sessionsPerTag := sessionsPerTag)) := by
  intro p q h
  simp only [slotZeroEmbed, Prod.mk.injEq] at h
  exact Prod.ext h.1.1 h.2

/-! ### Sub-table extraction along the embedding -/

/-- Sub-table extraction: project a single-session random-oracle table
`gS : (TagId × Fin sessionsPerTag) × Nonce → Digest` onto the multiple-session sub-table by
reading the reference session slot `0`, i.e. precompose with `slotZeroEmbed`.

`slotZeroSubTable gS (tag, n) = gS ((tag, 0), n)`. -/
@[reducible] def slotZeroSubTable
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) : TagId × Nonce → Digest :=
  gS ∘ slotZeroEmbed

@[simp] lemma slotZeroSubTable_apply
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) (tag : TagId) (n : Nonce) :
    slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (tag, n) =
      gS ((tag, (0 : Fin sessionsPerTag)), n) := rfl

/-- `slotZeroSubTable` agrees with the sibling `projectTable` from `Table.lean`. -/
lemma slotZeroSubTable_eq_projectTable
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) :
    slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS =
      projectTable (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) gS := rfl

/-! ### Eager-table coupling: uniform sub-table from uniform full table -/

/-- **Eager-table coupling.** Drawing a uniform single-session random-oracle table `gS` and
projecting it onto the multiple-session sub-table via `slotZeroSubTable` yields the uniform
distribution on multiple-session tables.

This is the foundational marginalization step of the direct M_ideal/S_ideal coupling: the
reference-slot cells of `gS` are themselves jointly uniform and independent of the off-slot
cells, so the multiple-session sub-table is uniform whenever the single-session full table is. -/
lemma evalDist_slotZeroSubTable_uniformSample
    [Fintype TagId] [DecidableEq TagId]
    [Fintype Nonce] [DecidableEq Nonce]
    [Finite Digest] [Nonempty Digest] [SampleableType Digest] :
    𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
        fun gS => pure (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)] =
      𝒟[$ᵗ (TagId × Nonce → Digest)] :=
  evalDist_uniformSample_map_comp_injective (R := Digest)
    (slotZeroEmbed_injective (TagId := TagId) (Nonce := Nonce)
      (sessionsPerTag := sessionsPerTag))

/-! ### Reader-side cell inclusion under the embedding -/

section ReaderCells

variable [Fintype TagId] [DecidableEq TagId] [DecidableEq Nonce]

/-- Multiple-side reader cells at a fixed transcript: the set of `(TagId × Nonce)` cells that the
multiple-session reader inspects at `transcript`, namely `{(tag, transcript.nonce) | tag}`. -/
def mReaderCellsFinset (transcript : TagTranscript Nonce Digest) :
    Finset (TagId × Nonce) :=
  (Finset.univ : Finset TagId).image (fun tag => (tag, transcript.nonce))

/-- Single-side reader cells at a fixed transcript: the set of
`((TagId × Fin sessionsPerTag) × Nonce)` cells the single-session reader inspects at
`transcript`, namely `{((tag, sid), transcript.nonce) | tag, sid}`. -/
def sReaderCellsFinset (transcript : TagTranscript Nonce Digest) :
    Finset ((TagId × Fin sessionsPerTag) × Nonce) :=
  (Finset.univ : Finset (TagId × Fin sessionsPerTag)).image
    (fun slot => (slot, transcript.nonce))

/-- **Reader-cell inclusion under the embedding.** At any fixed transcript, the image of the
multiple-side reader cells under `slotZeroEmbed` is contained in the single-side reader cells.

Concretely: every multiple-side cell `(tag, transcript.nonce)` becomes the single-side cell
`((tag, 0), transcript.nonce)`, which is one of the cells the single-side reader inspects (the
`sid = 0` slot). This is the cell-level inclusion that drives the slack-free reader-side bound:
the multiple-side reader inspects strictly fewer cells than the single-side reader. -/
lemma mReaderCellsFinset_image_subset_sReaderCellsFinset
    (transcript : TagTranscript Nonce Digest) :
    (mReaderCellsFinset (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      transcript).image
        (slotZeroEmbed (TagId := TagId) (Nonce := Nonce)
          (sessionsPerTag := sessionsPerTag)) ⊆
      sReaderCellsFinset (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) transcript := by
  intro x hx
  simp only [mReaderCellsFinset, sReaderCellsFinset, Finset.mem_image, Finset.mem_univ,
    true_and] at hx ⊢
  obtain ⟨p, ⟨tag, rfl⟩, rfl⟩ := hx
  exact ⟨(tag, (0 : Fin sessionsPerTag)), rfl⟩

/-- Multiple-side reader-cell cardinality: `|TagId|`. -/
lemma card_mReaderCellsFinset (transcript : TagTranscript Nonce Digest) :
    (mReaderCellsFinset (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      transcript).card = Fintype.card TagId := by
  unfold mReaderCellsFinset
  rw [Finset.card_image_of_injective _
    (fun _ _ h => (Prod.mk.injEq _ _ _ _).mp h |>.1), Finset.card_univ]

omit [NeZero sessionsPerTag] in
/-- Single-side reader-cell cardinality: `|TagId| * sessionsPerTag`. -/
lemma card_sReaderCellsFinset (transcript : TagTranscript Nonce Digest) :
    (sReaderCellsFinset (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) transcript).card =
        Fintype.card TagId * sessionsPerTag := by
  unfold sReaderCellsFinset
  rw [Finset.card_image_of_injective _
    (fun _ _ h => (Prod.mk.injEq _ _ _ _).mp h |>.1), Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin]

end ReaderCells

/-! ### Compatibility with the sibling eager-form -/

/-- `slotZeroSubTable` agrees with `projectTable` pointwise. Useful for rewriting Session 1's
direct-coupling statements into the established sibling phrasing in `Table.lean`. -/
@[simp] lemma slotZeroSubTable_eq_projectTable_apply
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) (p : TagId × Nonce) :
    slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS p =
      projectTable (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) gS p := rfl

end DirectCoupling

end PRFTagReader
