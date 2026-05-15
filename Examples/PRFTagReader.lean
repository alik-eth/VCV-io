/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# PRF Tag/Reader Protocol

This file formalizes a simple RFID-style tag/reader protocol. Each tag is assigned a secret and,
when queried, samples a fresh nonce `n` and outputs `(n, F(secret, n))`. A reader accepts a
transcript `(n, a)` whenever some registered tag secret makes `a` equal to `F(secret, n)`.

The file defines:

- an active authentication game, where the adversary wins by making the reader accept a transcript
  that was not previously emitted by the honest tag oracle;
- a multiple-session unlinkability game, where all sessions of a tag reuse the same per-tag secret;
- a single-session unlinkability game, where each session uses an independent per-session secret;
- an intermediate bad-event world that records nonce collisions across repeated sessions.

The theorem statements at the end package the intended security story: authentication reduces to
PRF security plus an ideal-world argument, and unlinkability reduces to PRF security plus a nonce
collision bound.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

/-- Transcript emitted by a tag in one session: a fresh nonce together with its authenticator. -/
structure TagTranscript (Nonce Digest : Type) where
  nonce : Nonce
  auth : Digest
deriving DecidableEq, Repr

/-- Reader's protocol response. `ok` means that the transcript was accepted, and `ko` means that
it was rejected. -/
inductive ReaderReply where
  | ok
  | ko
deriving DecidableEq, Repr, Inhabited

namespace ReaderReply

/-- Convert a boolean acceptance decision into the concrete protocol reply. -/
def ofBool : Bool → ReaderReply
  | true => .ok
  | false => .ko

/-- Predicate exposing whether a reader reply is accepting. -/
def accepts : ReaderReply → Bool
  | .ok => true
  | .ko => false

end ReaderReply

/-- Session-slot assignment for a tag/reader world with `sessionsPerTag` many protocol sessions
available to each tag. Real unlinkability worlds reuse one slot per tag; ideal worlds may allocate
a fresh slot per session. -/
structure SessionPattern (TagId Slot : Type) (sessionsPerTag : ℕ) where
  slot : TagId → Fin sessionsPerTag → Slot

section Pattern

variable {TagId : Type} (sessionsPerTag : ℕ)

/-- Real session pattern: every session of a given tag reuses the same slot. -/
def multiplePattern : SessionPattern TagId TagId sessionsPerTag where
  slot := fun tag _ => tag

/-- Ideal unlinkability pattern: each session of each tag receives its own fresh slot. -/
def singlePattern : SessionPattern TagId (TagId × Fin sessionsPerTag) sessionsPerTag where
  slot := fun tag sid => (tag, sid)

end Pattern

/-- Packaging of the two keyed hash families used by the protocol. `evalMultiple` models secret
reuse across all sessions of a tag, while `evalSingle` models an independent secret for each
session of each tag. -/
structure TagReaderPRFs (K TagId Nonce Digest : Type) (sessionsPerTag : ℕ) where
  keygen : ProbComp K
  evalMultiple : K → TagId → Nonce → Digest
  evalSingle : K → TagId → Fin sessionsPerTag → Nonce → Digest

namespace TagReaderPRFs

variable {K TagId Nonce Digest : Type} {sessionsPerTag : ℕ}
  (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)

/-- Derived PRF scheme for the multiple-session world. -/
def multiplePRFScheme : PRFScheme K (TagId × Nonce) Digest where
  keygen := prfs.keygen
  eval := fun k input => prfs.evalMultiple k input.1 input.2

/-- Derived PRF scheme for the single-session world. -/
def singlePRFScheme : PRFScheme K ((TagId × Fin sessionsPerTag) × Nonce) Digest where
  keygen := prfs.keygen
  eval := fun k input => prfs.evalSingle k input.1.1 input.1.2 input.2

end TagReaderPRFs

/-- Authentication-game state: the honest tag transcripts emitted so far, together with all
reader acceptances that cannot be traced back to a prior honest tag output. -/
structure AuthState (TagId Nonce Digest : Type) where
  honestOutputs : Finset (TagId × TagTranscript Nonce Digest)
  readerForged : Finset (TagId × TagTranscript Nonce Digest)

/-- Ideal authentication-game state: the cached random-function table, together with the same
observable logs used in the real game. -/
structure AuthIdealState (TagId Nonce Digest : Type) where
  responses : ((TagId × Nonce) →ₒ Digest).QueryCache
  honestOutputs : Finset (TagId × TagTranscript Nonce Digest)
  readerForged : Finset (TagId × TagTranscript Nonce Digest)

section AuthState

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest]

/-- Initial real authentication-game state. -/
def AuthState.init : AuthState TagId Nonce Digest where
  honestOutputs := ∅
  readerForged := ∅

/-- Initial ideal authentication-game state. -/
def AuthIdealState.init : AuthIdealState TagId Nonce Digest where
  responses := ∅
  honestOutputs := ∅
  readerForged := ∅

end AuthState

/-- Unlinkability-game state: how many sessions of each tag have already been consumed. -/
structure UnlinkState (TagId : Type) where
  sessionsUsed : TagId → ℕ

/-- Bad-world state for the multiple-session unlinkability proof: session counters, the list of
random-function responses seen for each `(tag, nonce)` pair, and the bad-event flag. -/
structure UnlinkBadState (TagId Nonce Digest : Type) where
  sessionsUsed : TagId → ℕ
  responses : ((TagId × Nonce) →ₒ List Digest).QueryCache
  bad : Bool

section UnlinkState

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest]

/-- Initial unlinkability-game state. -/
def UnlinkState.init : UnlinkState TagId where
  sessionsUsed := fun _ => 0

/-- Initial unlinkability bad-event state. -/
def UnlinkBadState.init : UnlinkBadState TagId Nonce Digest where
  sessionsUsed := fun _ => 0
  responses := ∅
  bad := false

end UnlinkState

/-- Authentication-game oracle interface: a tag oracle and a reader oracle. -/
def AuthOracleSpec (TagId Nonce Digest : Type) :=
  (TagId →ₒ TagTranscript Nonce Digest) + ((TagTranscript Nonce Digest) →ₒ ReaderReply)

/-- Unlinkability-game oracle interface: a session-bounded tag oracle and a reader oracle. -/
def UnlinkOracleSpec (TagId Nonce Digest : Type) :=
  (TagId →ₒ Option (TagTranscript Nonce Digest)) +
    ((TagTranscript Nonce Digest) →ₒ ReaderReply)

/-- Authentication adversaries are oracle computations over the tag and reader interfaces. -/
abbrev AuthAdversary (TagId Nonce Digest : Type) :=
  OracleComp (AuthOracleSpec TagId Nonce Digest) Unit

/-- Unlinkability adversaries are oracle computations over the bounded-tag and reader interfaces. -/
abbrev UnlinkAdversary (TagId Nonce Digest : Type) :=
  OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool

section AuthGame

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest]

/-- Honest tag oracle for the real authentication game. -/
def authTagQueryImpl (hash : TagId → Nonce → Digest) :
    QueryImpl (TagId →ₒ TagTranscript Nonce Digest)
      (StateT (AuthState TagId Nonce Digest) ProbComp) := fun tag => do
        let st ← get
        let nonce ← ($ᵗ Nonce : ProbComp Nonce)
        let auth := hash tag nonce
        let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
        set
          { st with
            honestOutputs := insert (tag, transcript) st.honestOutputs }
        return transcript

/-- Reader oracle for the real authentication game. It accepts any transcript that
matches some tag's hash image and logs acceptances that were never emitted by the honest tag
oracle. -/
def authReaderQueryImpl (hash : TagId → Nonce → Digest) :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (AuthState TagId Nonce Digest) ProbComp) := fun transcript => do
        let st ← get
        let accepted := decide (∃ tag, hash tag transcript.nonce = transcript.auth)
        let newForged := Finset.univ.filter fun tag =>
          hash tag transcript.nonce = transcript.auth ∧ (tag, transcript) ∉ st.honestOutputs
        set { st with readerForged := st.readerForged ∪ (newForged.image (·, transcript)) }
        return ReaderReply.ofBool accepted

/-- Combined real-game oracle implementation for authentication. -/
def authRealQueryImpl (hash : TagId → Nonce → Digest) :
    QueryImpl (AuthOracleSpec TagId Nonce Digest)
      (StateT (AuthState TagId Nonce Digest) ProbComp) :=
  authTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) hash +
    authReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) hash

/-- Real active-authentication experiment. -/
def authExp {K : Type} {sessionsPerTag : ℕ}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest) : ProbComp Bool := do
  let k ← prfs.keygen
  let (_, st) ← (simulateQ
    (authRealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (fun tag nonce => prfs.evalMultiple k tag nonce))
    adversary).run AuthState.init
  return decide (st.readerForged ≠ ∅)

end AuthGame

section AuthIdealGame

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]

/-- Honest tag oracle for the ideal authentication world. It queries a lazy random
function table and records the emitted transcript. -/
def authIdealTagQueryImpl :
    QueryImpl (TagId →ₒ TagTranscript Nonce Digest)
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) := fun tag => do
        let st ← get
        let nonce ← ($ᵗ Nonce : ProbComp Nonce)
        let key := (tag, nonce)
        let (auth, responses) ←
          match st.responses key with
          | some out => pure (out, st.responses)
          | none => do
              let out ← ($ᵗ Digest : ProbComp Digest)
              pure (out, st.responses.cacheQuery key out)
        let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
        set
          ({ responses := responses
             honestOutputs := insert (tag, transcript) st.honestOutputs
             readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)
        return transcript

/-- Reader oracle for the ideal authentication world. It only accepts transcripts that
were previously generated for the queried tag and nonce in the cached random-function table. -/
def authIdealReaderQueryImpl :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) := fun transcript => do
        let st ← get
        let matching := Finset.univ.filter fun tag =>
          st.responses (tag, transcript.nonce) = some transcript.auth
        let newForged := matching.filter fun tag =>
          (tag, transcript) ∉ st.honestOutputs
        set
          ({ responses := st.responses
             honestOutputs := st.honestOutputs
             readerForged := st.readerForged ∪ (newForged.image (·, transcript))
           } : AuthIdealState TagId Nonce Digest)
        return ReaderReply.ofBool (decide (matching.Nonempty))

/-- Combined ideal-game oracle implementation for authentication. -/
def authIdealQueryImpl :
    QueryImpl (AuthOracleSpec TagId Nonce Digest)
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) :=
  authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) +
    authIdealReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)

/-- Ideal active-authentication experiment. The keyed hash is replaced by a lazy random function on
`(tag, nonce)`, and the reader only accepts transcripts that match the cached table. -/
def authIdealExp
    (adversary : AuthAdversary TagId Nonce Digest) : ProbComp Bool := do
  let (_, st) ← (simulateQ
    (authIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
    adversary).run AuthIdealState.init
  return decide (st.readerForged ≠ ∅)

end AuthIdealGame

section AuthRFGame

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]

/-- Lazy random-function lookup at `(tag, nonce)`: return the cached digest if present, otherwise
sample a fresh uniform digest and cache it. This is the `randomOracle` step expressed directly on
the `responses` table of `AuthIdealState`. -/
def authRFLookup (tag : TagId) (nonce : Nonce) :
    StateT (AuthIdealState TagId Nonce Digest) ProbComp Digest := do
  let st ← get
  match st.responses (tag, nonce) with
  | some d => pure d
  | none =>
      let d ← ($ᵗ Digest : ProbComp Digest)
      set ({ st with responses := st.responses.cacheQuery (tag, nonce) d } :
        AuthIdealState TagId Nonce Digest)
      return d

/-- Reader oracle for the random-function authentication world. Unlike the look-up-only
`authIdealReaderQueryImpl`, this reader queries the lazy random function for every tag at the
transcript's nonce, creating fresh cache entries for uncached pairs. It accepts when some digest
matches the submitted authenticator and records non-honest matches as forgeries. -/
noncomputable def authRFReaderQueryImpl :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) := fun transcript => do
  let pairs ← (Finset.univ : Finset TagId).toList.mapM (fun tag => do
    let d ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      tag transcript.nonce
    return (tag, d))
  let st ← get
  let accepted : Bool := decide (∃ p ∈ pairs, p.2 = transcript.auth)
  let newForged : Finset TagId :=
    ((pairs.filter fun p => decide (p.2 = transcript.auth ∧
        (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset
  set ({ st with readerForged := st.readerForged ∪ (newForged.image (·, transcript)) } :
    AuthIdealState TagId Nonce Digest)
  return ReaderReply.ofBool accepted

/-- Combined oracle implementation for the random-function authentication world: the honest tag
oracle of the ideal world together with the fresh-drawing random-function reader. -/
noncomputable def authRFQueryImpl :
    QueryImpl (AuthOracleSpec TagId Nonce Digest)
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) :=
  authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) +
    authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)

/-- Direct form of the random-function authentication experiment: run the adversary against
`authRFQueryImpl` and win when a forged reader acceptance is recorded. -/
noncomputable def authRFDirectExp
    (adversary : AuthAdversary TagId Nonce Digest) : ProbComp Bool := do
  let (_, st) ← (simulateQ
    (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
    adversary).run AuthIdealState.init
  return decide (st.readerForged ≠ ∅)

end AuthRFGame

section AuthReduction

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest]

/-- Query the PRF oracle on `(tag, nonce)` to obtain its digest. -/
private def authPRFQuery (tag : TagId) (nonce : Nonce) :
    OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest :=
  (unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr (tag, nonce))

/-- Tag-oracle implementation that samples a nonce uniformly and queries the PRF oracle for
the authenticator. Models `authTagQueryImpl` with the hash replaced by a PRF oracle call. -/
def authToPRFTagImpl :
    QueryImpl (TagId →ₒ TagTranscript Nonce Digest)
      (StateT (AuthState TagId Nonce Digest)
        (OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))) := fun tag => do
  let st ← get
  let nonce ← (OracleComp.liftComp (spec := unifSpec)
    (superSpec := unifSpec + ((TagId × Nonce) →ₒ Digest)) ($ᵗ Nonce) :
    OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Nonce)
  let auth ← authPRFQuery (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce
  let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
  set { st with honestOutputs := insert (tag, transcript) st.honestOutputs }
  return transcript

/-- Reader-oracle implementation that queries the PRF oracle for every tag at the transcript's
nonce in order to identify the matching tags. Models `authReaderQueryImpl` with the hash
replaced by a PRF oracle call. -/
noncomputable def authToPRFReaderImpl :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (AuthState TagId Nonce Digest)
        (OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))) := fun transcript => do
  let st ← get
  let pairs ←
    (Finset.univ : Finset TagId).toList.mapM
      (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
      (fun tag => do
        let d ← authPRFQuery (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          tag transcript.nonce
        return (tag, d))
  let accepted : Bool := decide (∃ p ∈ pairs, p.2 = transcript.auth)
  let newForged : Finset TagId :=
    ((pairs.filter fun p => decide (p.2 = transcript.auth ∧
        (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset
  set { st with readerForged := st.readerForged ∪ (newForged.image (·, transcript)) }
  return ReaderReply.ofBool accepted

/-- Combined oracle implementation that simulates the authentication game while hashing through
the PRF oracle. -/
noncomputable def authToPRFQueryImpl :
    QueryImpl (AuthOracleSpec TagId Nonce Digest)
      (StateT (AuthState TagId Nonce Digest)
        (OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))) :=
  authToPRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) +
    authToPRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)

/-- PRF distinguisher derived from an authentication adversary. The reduction runs the auth game
with every call to `prfs.evalMultiple k tag nonce` replaced by a query to the PRF oracle on
`(tag, nonce)`. It returns `true` exactly when the reader records a forged acceptance during the
simulation. -/
noncomputable def authToPRFReduction
    (adversary : AuthAdversary TagId Nonce Digest) :
    PRFScheme.PRFAdversary (TagId × Nonce) Digest :=
  ((simulateQ (authToPRFQueryImpl
      (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) adversary).run AuthState.init >>=
    fun p => pure (decide (p.2.readerForged ≠ ∅)) :
    OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Bool)

end AuthReduction

section UnlinkGame

variable {TagId Slot Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- Reader acceptance for a fixed tag in a given unlinkability session pattern. -/
def tagAccepts (hash : Slot → Nonce → Digest)
    (pattern : SessionPattern TagId Slot sessionsPerTag)
    (tag : TagId) (transcript : TagTranscript Nonce Digest) : Bool :=
  decide (∃ sid : Fin sessionsPerTag,
    hash (pattern.slot tag sid) transcript.nonce = transcript.auth)

/-- Reader acceptance test for a fixed unlinkability session pattern. -/
def unlinkReaderAccepts (hash : Slot → Nonce → Digest)
    (pattern : SessionPattern TagId Slot sessionsPerTag)
    (transcript : TagTranscript Nonce Digest) : Bool :=
  decide (∃ tag,
    tagAccepts (TagId := TagId) (Slot := Slot) (Nonce := Nonce) (Digest := Digest)
      hash pattern tag transcript)

/-- Tag oracle for a fixed unlinkability session pattern. It returns `none` once the session cap
for the queried tag is exhausted. -/
def unlinkTagQueryImpl (hash : Slot → Nonce → Digest)
    (pattern : SessionPattern TagId Slot sessionsPerTag) :
    QueryImpl (TagId →ₒ Option (TagTranscript Nonce Digest))
      (StateT (UnlinkState TagId) ProbComp) := fun tag => do
        let st ← get
        if h : st.sessionsUsed tag < sessionsPerTag then
          let sid : Fin sessionsPerTag := ⟨st.sessionsUsed tag, h⟩
          let nonce ← ($ᵗ Nonce : ProbComp Nonce)
          let auth := hash (pattern.slot tag sid) nonce
          let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
          set
            { st with
              sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1) }
          return some transcript
        else
          return none

/-- Reader oracle for a fixed unlinkability session pattern. -/
def unlinkReaderQueryImpl (hash : Slot → Nonce → Digest)
    (pattern : SessionPattern TagId Slot sessionsPerTag) :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (UnlinkState TagId) ProbComp) := fun transcript =>
        return ReaderReply.ofBool <| unlinkReaderAccepts (TagId := TagId) (Slot := Slot)
          (Nonce := Nonce) (Digest := Digest) hash pattern transcript

/-- Combined multiple-session unlinkability oracle implementation. -/
def unlinkMultipleQueryImpl {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (k : K) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId) ProbComp) :=
  unlinkTagQueryImpl (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
    (fun tag nonce => prfs.evalMultiple k tag nonce)
    (multiplePattern (TagId := TagId) sessionsPerTag) +
    unlinkReaderQueryImpl (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
      (fun tag nonce => prfs.evalMultiple k tag nonce)
      (multiplePattern (TagId := TagId) sessionsPerTag)

/-- Combined single-session unlinkability oracle implementation. -/
def unlinkSingleQueryImpl {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (k : K) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId) ProbComp) :=
  unlinkTagQueryImpl (TagId := TagId) (Slot := TagId × Fin sessionsPerTag)
    (Nonce := Nonce) (Digest := Digest)
    (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
    (singlePattern (TagId := TagId) sessionsPerTag) +
    unlinkReaderQueryImpl (TagId := TagId) (Slot := TagId × Fin sessionsPerTag)
      (Nonce := Nonce) (Digest := Digest)
      (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
      (singlePattern (TagId := TagId) sessionsPerTag)

/-- Multiple-session unlinkability world: each tag reuses its own slot across all sessions. -/
def unlinkMultipleExp {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) : ProbComp Bool := do
  let k ← prfs.keygen
  (simulateQ (unlinkMultipleQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) prfs k) adversary).run' UnlinkState.init

/-- Single-session unlinkability world: each tag query consumes a fresh slot, while the reader
checks all session slots for that tag. -/
def unlinkSingleExp {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) : ProbComp Bool := do
  let k ← prfs.keygen
  (simulateQ (unlinkSingleQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) prfs k) adversary).run' UnlinkState.init

/-- One-sided unlinkability gap `Pr[Multiple] - Pr[Single]` between the two session-allocation
worlds. -/
noncomputable def unlinkabilityAdvantage {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) : ℝ :=
  (Pr[= true | unlinkMultipleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag) prfs adversary]).toReal -
    (Pr[= true | unlinkSingleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag) prfs adversary]).toReal

end UnlinkGame

section BadEvent

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- Tag oracle for the `RF_bad` multiple-session collision world. It
samples a fresh ideal hash output on every tag query, records all outputs associated with a given
`(tag, nonce)` pair, and sets `bad` once some pair is queried twice. -/
def unlinkBadTagQueryImpl :
    QueryImpl (TagId →ₒ Option (TagTranscript Nonce Digest))
      (StateT (UnlinkBadState TagId Nonce Digest) ProbComp) := fun tag => do
        let st ← get
        if _h : st.sessionsUsed tag < sessionsPerTag then
          let nonce ← ($ᵗ Nonce : ProbComp Nonce)
          let auth ← ($ᵗ Digest : ProbComp Digest)
          let outputs := auth :: Option.getD (st.responses (tag, nonce)) []
          let bad := st.bad || (st.responses (tag, nonce)).isSome
          let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
          set
            ({ sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1)
               responses := st.responses.cacheQuery (tag, nonce) outputs
               bad := bad } : UnlinkBadState TagId Nonce Digest)
          return some transcript
        else
          return none

/-- Reader oracle for the `RF_bad` multiple-session world. It accepts when the queried digest
appears among the cached random-function outputs for some tag at the given nonce. -/
def unlinkBadReaderQueryImpl :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (UnlinkBadState TagId Nonce Digest) ProbComp) := fun transcript => do
        let st ← get
        let accepted := decide (∃ tag ∈ (Finset.univ : Finset TagId),
          transcript.auth ∈ ((st.responses (tag, transcript.nonce)).getD []))
        return ReaderReply.ofBool accepted

/-- Oracle implementation for the `RF_bad` multiple-session world. -/
def unlinkBadQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkBadState TagId Nonce Digest) ProbComp) :=
  unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag)
    +
    unlinkBadReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)

/-- Bad-event experiment from the `RF_bad` multiple-session collision world. -/
def unlinkBadExp
    (adversary : UnlinkAdversary TagId Nonce Digest) : ProbComp Bool := do
  let (_, st) ← (simulateQ
    (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag))
    adversary).run UnlinkBadState.init
  return st.bad

end BadEvent

section Theorems

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- Random-function authentication experiment. Defined as the ideal PRF experiment applied to the
`authToPRFReduction` distinguisher: every call to `prfs.evalMultiple` in `authExp` is replaced by a
lazy random oracle on `(tag, nonce)` consistent across both tag and reader oracle queries.

This is the natural PRF-replacement ideal world (in contrast to the look-up-only `authIdealExp`,
which is the stronger ideal world where the reader cannot make oracle queries). Random-function
matches against an adversary-submitted transcript contribute to `Pr[authRFExp]`, so it is generally
nonzero. -/
noncomputable def authRFExp
    (adversary : AuthAdversary TagId Nonce Digest) : ProbComp Bool :=
  PRFScheme.prfIdealExp (authToPRFReduction adversary)

omit [Fintype TagId] [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Per-tag-query equivalence: running the reduction's tag-oracle implementation through the real
PRF simulator produces the same distribution and final state as the real auth-game tag oracle
parameterised by `prfs.evalMultiple k`. -/
private lemma simulateQ_prfReal_authToPRFTagImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (tag : TagId) (s : AuthState TagId Nonce Digest) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
        ((authToPRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag).run s) =
      (authTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (fun tag nonce => prfs.evalMultiple k tag nonce) tag).run s := by
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
  unfold authToPRFTagImpl authTagQueryImpl authPRFQuery
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift,
    bind_pure_comp, pure_bind]
  rw [← hImplEq]
  change @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _ impl _ _ = _
  simp only [simulateQ_bind, simulateQ_map, monadLift_eq_self,
    hleft]
  rfl

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Per-reader-query equivalence: running the reduction's reader-oracle implementation through the
real PRF simulator produces the same distribution and final state as the real auth-game reader
oracle parameterised by `prfs.evalMultiple k`. -/
private lemma simulateQ_prfReal_authToPRFReaderImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (transcript : TagTranscript Nonce Digest) (s : AuthState TagId Nonce Digest) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
        ((authToPRFReaderImpl
            (TagId := TagId) (Nonce := Nonce) (Digest := Digest) transcript).run s) =
      (authReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (fun tag nonce => prfs.evalMultiple k tag nonce) transcript).run s := by
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
  have hquery_pair : ∀ (tag : TagId),
      simulateQ impl
        (Prod.mk tag <$> authPRFQuery (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            tag transcript.nonce :
          OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) (TagId × Digest)) =
        pure (tag, prfs.evalMultiple k tag transcript.nonce) := by
    intro tag
    have step : simulateQ impl
        (authPRFQuery (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            tag transcript.nonce) =
        (pure (prfs.evalMultiple k tag transcript.nonce) : ProbComp Digest) := by
      show @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _ impl _ _ = _
      exact hquery (tag, transcript.nonce)
    change @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _ impl _ _ = _
    rw [simulateQ_map, step]
    rfl
  have hmapM :
      simulateQ impl
        ((Finset.univ : Finset TagId).toList.mapM
          (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
          (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId)
            (Nonce := Nonce) (Digest := Digest) tag transcript.nonce)) =
      pure ((Finset.univ : Finset TagId).toList.map
        fun tag => (tag, prfs.evalMultiple k tag transcript.nonce)) := by
    show @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _ impl _ _ = _
    rw [simulateQ_list_mapM]
    induction (Finset.univ : Finset TagId).toList with
    | nil => rfl
    | cons t ts ih =>
      rw [List.mapM_cons, hquery_pair, pure_bind, ih, pure_bind]
      rfl
  have hForged :
      ((((Finset.univ : Finset TagId).toList.map
              fun tag => (tag, prfs.evalMultiple k tag transcript.nonce)).filter
            fun p => decide (p.2 = transcript.auth ∧ (p.1, transcript) ∉ s.honestOutputs)).map
          Prod.fst).toFinset =
        (Finset.univ : Finset TagId).filter fun tag =>
          prfs.evalMultiple k tag transcript.nonce = transcript.auth ∧
            (tag, transcript) ∉ s.honestOutputs := by
    ext tag
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_toList, Prod.exists]
    aesop
  have hAccept :
      decide (∃ p ∈ (Finset.univ : Finset TagId).toList.map
        fun tag => (tag, prfs.evalMultiple k tag transcript.nonce),
        p.2 = transcript.auth) =
      decide (∃ tag, prfs.evalMultiple k tag transcript.nonce = transcript.auth) := by
    congr 1
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    aesop
  unfold authToPRFReaderImpl authReaderQueryImpl
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift,
    bind_pure_comp, pure_bind]
  rw [← hImplEq]
  change @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _ impl _ _ = _
  simp only [simulateQ_bind, simulateQ_map, monadLift_eq_self,
    hmapM, pure_bind, map_pure]
  rw [hForged, hAccept]
  rfl

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Inductive helper: simulating the auth-game adversary through the reduction's query
implementation and then through the real PRF query implementation is the same, state-by-state,
as simulating it directly through the real authentication query implementation with the hash set
to `prfs.evalMultiple k`. Each tag/reader query case follows by unfolding both sides and noting
that `prfRealQueryImpl prfs.multiplePRFScheme k` returns `prfs.evalMultiple k tag nonce` on the
`Sum.inr (tag, nonce)` query. -/
private theorem simulateQ_prfReal_authToPRFQueryImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (adversary : AuthAdversary TagId Nonce Digest)
    (s : AuthState TagId Nonce Digest) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
        ((simulateQ
          (authToPRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          adversary).run s) =
      (simulateQ
        (authRealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (fun tag nonce => prfs.evalMultiple k tag nonce))
        adversary).run s := by
  induction adversary using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    rfl
  | query_bind t f ih =>
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    rcases t with tag | transcript
    · change simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
            ((authToPRFTagImpl tag).run s >>=
              fun p => (simulateQ authToPRFQueryImpl (f p.1)).run p.2) =
          (authTagQueryImpl
            (fun tag nonce => prfs.evalMultiple k tag nonce) tag).run s >>=
            fun p => (simulateQ (authRealQueryImpl
              (fun tag nonce => prfs.evalMultiple k tag nonce)) (f p.1)).run p.2
      rw [simulateQ_bind, simulateQ_prfReal_authToPRFTagImpl_run prfs k tag s]
      refine bind_congr fun p => ?_
      exact ih p.1 p.2
    · change simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
            ((authToPRFReaderImpl transcript).run s >>=
              fun p => (simulateQ authToPRFQueryImpl (f p.1)).run p.2) =
          (authReaderQueryImpl
            (fun tag nonce => prfs.evalMultiple k tag nonce) transcript).run s >>=
            fun p => (simulateQ (authRealQueryImpl
              (fun tag nonce => prfs.evalMultiple k tag nonce)) (f p.1)).run p.2
      rw [simulateQ_bind,
        simulateQ_prfReal_authToPRFReaderImpl_run prfs k transcript s]
      refine bind_congr fun p => ?_
      exact ih p.1 p.2

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The PRF reduction faithfully reproduces the real authentication experiment: under the real
PRF, each oracle query at `(tag, nonce)` returns `prfs.evalMultiple k tag nonce`, so the reduction
runs exactly the same game as `authExp`. -/
theorem prfRealExp_authToPRFReduction_eq_authExp
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest) :
    Pr[= true | PRFScheme.prfRealExp prfs.multiplePRFScheme
        (authToPRFReduction (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary)] =
      Pr[= true | authExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) prfs adversary] := by
  suffices h : PRFScheme.prfRealExp prfs.multiplePRFScheme (authToPRFReduction adversary) =
      authExp prfs adversary by rw [h]
  unfold PRFScheme.prfRealExp authExp
  refine bind_congr (m := ProbComp) fun k => ?_
  show simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
      (authToPRFReduction adversary) =
    (do let (_, st) ← (simulateQ (authRealQueryImpl
      (fun tag nonce => prfs.evalMultiple k tag nonce)) adversary).run AuthState.init
        return decide (st.readerForged ≠ ∅))
  unfold authToPRFReduction
  change simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
      ((simulateQ authToPRFQueryImpl adversary).run AuthState.init >>=
        fun p => pure (decide (p.2.readerForged ≠ ∅))) = _
  rw [simulateQ_bind,
    simulateQ_prfReal_authToPRFQueryImpl_run prfs k adversary AuthState.init]
  refine bind_congr fun p => ?_
  rw [simulateQ_pure]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Authentication reduction statement: the success probability of the active-authentication
adversary is bounded by the PRF distinguishing advantage of the canonical reduction plus the
"random-function" experiment's success probability `authRFExp`.

The conceptually simpler look-up-only ideal world `authIdealExp` is provably zero
(`authIdealExp_eq_zero`), but it is too restrictive to serve as the RHS of this kind of PRF
reduction: when the PRF oracle is replaced by a lazy random function, the reader's queries
on unseen `(tag, nonce)` pairs land on uniformly random digests that may coincide with the
adversary's submitted authenticator. `authRFExp` captures exactly that contribution. -/
theorem authExp_le_prfAdvantage_add_authRF
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest) :
    (Pr[= true | authExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) prfs adversary]).toReal ≤
      PRFScheme.prfAdvantage prfs.multiplePRFScheme
        (authToPRFReduction (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary) +
      (Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) adversary]).toReal := by
  have hreal := prfRealExp_authToPRFReduction_eq_authExp prfs adversary
  have hRF : authRFExp (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary =
      PRFScheme.prfIdealExp (authToPRFReduction adversary) := rfl
  rw [← hreal]
  rw [hRF]
  unfold PRFScheme.prfAdvantage
  set a := (Pr[= true | PRFScheme.prfRealExp prfs.multiplePRFScheme
    (authToPRFReduction (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary)]).toReal
  set b := (Pr[= true | PRFScheme.prfIdealExp
    (authToPRFReduction (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary)]).toReal
  have : a - b ≤ |a - b| := le_abs_self _
  linarith

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Existential form of the authentication reduction: there is a PRF adversary whose
distinguishing advantage, added to the random-function world's success probability
`authRFExp`, bounds the authentication adversary's success probability. The witness is
`authToPRFReduction adversary`. -/
theorem exists_prfAdv_authExp_le_prfAdvantage_add_authRF
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest) :
    ∃ prfAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      (Pr[= true | authExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) prfs adversary]).toReal ≤
        PRFScheme.prfAdvantage prfs.multiplePRFScheme prfAdv +
        (Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) adversary]).toReal :=
  ⟨authToPRFReduction adversary, authExp_le_prfAdvantage_add_authRF prfs adversary⟩

omit [Nonempty TagId] in
/-- In the ideal authentication world, a forged reader acceptance never occurs. -/
theorem authIdealExp_eq_zero
    (adversary : AuthAdversary TagId Nonce Digest) :
    Pr[= true | authIdealExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) adversary] = 0 := by
  let ForgedInv : AuthIdealState TagId Nonce Digest → Prop := fun st => st.readerForged = ∅
  let CacheInv : AuthIdealState TagId Nonce Digest → Prop := fun st =>
    ∀ tag nonce auth, st.responses (tag, nonce) = some auth →
      (tag, ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest)) ∈ st.honestOutputs
  have htagForged :
      QueryImpl.PreservesInv
        (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        ForgedInv := by
    intro tag st hst z hz
    unfold authIdealTagQueryImpl at hz
    simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_eq_self, bind_map_left, support_bind, support_uniformSample, Set.mem_univ,
      Set.iUnion_true, Set.mem_iUnion] at hz
    rcases hz with ⟨i, hz⟩
    cases hresp : st.responses (tag, i) with
    | none =>
      simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
        StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map,
        support_uniformSample, Set.image_univ, Set.mem_range] at hz
      grind
    | some out =>
      simp only [hresp, StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      grind
  have htagCached :
      QueryImpl.PreservesInv
        (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        CacheInv := by
    intro tag st hst z hz
    unfold authIdealTagQueryImpl at hz
    simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_eq_self, bind_map_left, support_bind, support_uniformSample, Set.mem_univ,
      Set.iUnion_true, Set.mem_iUnion] at hz
    rcases hz with ⟨nonce, hz⟩
    cases hresp : st.responses (tag, nonce) with
    | none =>
      simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
        StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map,
        support_uniformSample, Set.image_univ, Set.mem_range] at hz
      rcases hz with ⟨auth, rfl⟩
      intro tag' nonce' auth' hlookup
      by_cases hkey : (tag', nonce') = (tag, nonce)
      · cases hkey
        simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hlookup
        subst auth'
        simp
      · have hlookup' : st.responses (tag', nonce') = some auth' := by
          simpa [QueryCache.cacheQuery_of_ne (cache := st.responses) auth hkey] using hlookup
        exact Finset.mem_insert_of_mem (hst tag' nonce' auth' hlookup')
    | some out =>
      simp only [hresp, StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      rcases hz with rfl
      intro tag' nonce' auth' hlookup
      exact Finset.mem_insert_of_mem (hst tag' nonce' auth' hlookup)
  have hreaderForged :
      ∀ transcript st, ForgedInv st ∧ CacheInv st →
        ∀ z ∈
            support
              (((authIdealReaderQueryImpl
                  (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) transcript).run st),
          ForgedInv z.2 := by
    intro transcript st hst z hz
    have hz' := hz
    have hcached := hst.2
    unfold authIdealReaderQueryImpl at hz'
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_map, StateT.run_set,
      map_pure, support_pure, Set.mem_singleton_iff] at hz'
    rcases hz' with rfl
    unfold ForgedInv at *
    have hnewForged :
        ((Finset.univ.filter fun tag =>
          st.responses (tag, transcript.nonce) = some transcript.auth).filter fun tag =>
            (tag, transcript) ∉ st.honestOutputs) = ∅ := by
      ext tag
      constructor
      · intro hmem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        rcases hmem with ⟨hmatch, hnotmem⟩
        simpa using (False.elim (hnotmem (hcached tag transcript.nonce transcript.auth hmatch)))
      · intro hmem
        simp at hmem
    rw [hst.1, hnewForged, Finset.image_empty, Finset.empty_union]
  have hreaderCached :
      QueryImpl.PreservesInv
        (authIdealReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        CacheInv := by
    intro transcript st hst z hz
    unfold authIdealReaderQueryImpl at hz
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_map, StateT.run_set,
      map_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    exact hst
  have himpl :
      QueryImpl.PreservesInv
        (authIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        (fun st => ForgedInv st ∧ CacheInv st) := by
    intro t st hst z hz
    cases t with
    | inl tag =>
        exact (QueryImpl.PreservesInv.and htagForged htagCached) tag st hst z hz
    | inr transcript =>
        exact ⟨hreaderForged transcript st hst z hz, hreaderCached transcript st hst.2 z hz⟩
  have hfinal :
      ∀ z ∈
          support
            ((simulateQ
                (authIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                adversary).run AuthIdealState.init),
        z.2.readerForged = ∅ := by
    intro z hz
    have hz' :=
      OracleComp.simulateQ_run_preservesInv
        (authIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        (fun st => ForgedInv st ∧ CacheInv st) himpl adversary AuthIdealState.init
        (by simp [ForgedInv, CacheInv, AuthIdealState.init]) z hz
    grind
  refine (probOutput_eq_zero_iff
    (mx := authIdealExp (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary)
    (x := true)).mpr ?_
  intro hmem
  rw [authIdealExp, mem_support_bind_iff] at hmem
  grind

/-- Bundle a reduction state `AuthState × QueryCache` into the corresponding `AuthIdealState`:
the lazy random-oracle cache becomes the `responses` table, and the observable logs carry
through unchanged. -/
private def authRFBundle
    (p : AuthState TagId Nonce Digest × ((TagId × Nonce) →ₒ Digest).QueryCache) :
    AuthIdealState TagId Nonce Digest where
  responses := p.2
  honestOutputs := p.1.honestOutputs
  readerForged := p.1.readerForged

omit [Fintype TagId] [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Per-tag-query equivalence (ideal side): simulating the reduction's tag oracle through the lazy
random oracle, threaded through the cache, matches the ideal auth-game tag oracle. -/
private lemma simulateQ_prfIdeal_authToPRFTagImpl_run
    (tag : TagId) (s : AuthState TagId Nonce Digest)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          ((authToPRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag).run
            s)).run c) =
      (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag).run
        (authRFBundle (s, c)) := by
  let impl : QueryImpl (unifSpec + ((TagId × Nonce) →ₒ Digest))
      (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp) +
      ((TagId × Nonce) →ₒ Digest).randomOracle
  have hImplEq : impl = PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest) := rfl
  have hleft : ∀ {α : Type} (oa : ProbComp α),
      simulateQ impl (liftComp oa (unifSpec + ((TagId × Nonce) →ₒ Digest))) =
        (liftM oa : StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp α) := by
    intro α oa
    trans simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp)) oa
    · exact QueryImpl.simulateQ_add_liftComp_left
        (impl₁' := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp))
        (impl₂' := ((TagId × Nonce) →ₒ Digest).randomOracle) oa
    · rw [simulateQ_liftTarget]
      congr 1
      exact simulateQ_ofLift_eq_self _
  have hquery : ∀ (d : TagId × Nonce),
      simulateQ impl
        (liftM ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr d)) :
          OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest) =
      (((TagId × Nonce) →ₒ Digest).randomOracle d :
        StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp Digest) := by
    intro d
    simp only [simulateQ_query]
    show id <$> impl (Sum.inr d) = _
    rw [id_map]
    rfl
  -- Per-step equality, packaged so the simulator only ever sees explicit `simulateQ_*` shapes.
  have hstep : ∀ (st : AuthState TagId Nonce Digest),
      simulateQ impl
          ((authToPRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag).run st) =
        ((($ᵗ Nonce : ProbComp Nonce) : StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp _)
            >>= fun nonce =>
          (((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce) :
              StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp Digest) >>= fun auth =>
            pure (TagTranscript.mk nonce auth,
              AuthState.mk
                (insert (tag, TagTranscript.mk nonce auth) st.honestOutputs)
                st.readerForged)) := by
    intro st
    have hbody :
        ((authToPRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag).run st) =
          ((liftComp ($ᵗ Nonce) (unifSpec + ((TagId × Nonce) →ₒ Digest))) >>= fun nonce =>
            (liftM ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr (tag, nonce))) :
                OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest) >>= fun auth =>
              pure (TagTranscript.mk nonce auth,
                AuthState.mk
                  (insert (tag, TagTranscript.mk nonce auth) st.honestOutputs)
                  st.readerForged)) := by
      unfold authToPRFTagImpl authPRFQuery
      simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_eq_self,
        StateT.run_map, StateT.run_set, bind_pure_comp, pure_bind, map_bind, map_pure,
        bind_map_left]
      rfl
    rw [hbody, simulateQ_bind, hleft]
    refine bind_congr fun nonce => ?_
    rw [simulateQ_bind, hquery]
    refine bind_congr fun auth => ?_
    rw [simulateQ_pure]
  have hgoal : (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          ((authToPRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag).run
            s)).run c) =
      (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        (((($ᵗ Nonce : ProbComp Nonce) :
              StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp _)
              >>= fun nonce =>
            (((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce) :
                StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp Digest) >>= fun auth =>
              pure (TagTranscript.mk nonce auth,
                AuthState.mk
                  (insert (tag, TagTranscript.mk nonce auth) s.honestOutputs)
                  s.readerForged)).run c) := by
    rw [← hImplEq]
    exact congrArg _ (congrArg (StateT.run · c) (hstep s))
  rw [hgoal]
  unfold authIdealTagQueryImpl
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_eq_self,
    StateT.run_map, StateT.run_set, StateT.run_pure, bind_pure_comp, pure_bind, map_bind,
    map_pure, bind_map_left, Functor.map_map]
  refine bind_congr fun nonce => ?_
  simp only [OracleSpec.randomOracle, QueryImpl.withCaching_apply, StateT.run_bind,
    StateT.run_get, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp, map_bind, map_pure]
  cases hc : c (tag, nonce) with
  | some out =>
    simp only [authRFBundle, hc, map_pure, pure_bind, StateT.run_pure, StateT.run_bind,
      StateT.run_map, StateT.run_set, Functor.map_map]
  | none =>
    simp only [authRFBundle, hc, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
      bind_pure_comp, StateT.run_modifyGet, StateT.run_map, StateT.run_set, map_bind,
      bind_map_left, pure_bind, Functor.map_map, map_pure, uniformSampleImpl,
      HasQuery.toQueryImpl_apply]

omit [Fintype TagId] [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Generalized per-tag-list equivalence used by the reader helper: simulating the reduction's
per-tag PRF queries through the lazy random oracle, threaded through the cache, matches mapping
`authRFLookup` over the same tag list with the cache bundled into the ideal state. -/
private lemma simulateQ_prfIdeal_authToPRFReader_mapM
    (nonce : Nonce) (tags : List TagId) :
    ∀ (st : AuthState TagId Nonce Digest)
      (c : ((TagId × Nonce) →ₒ Digest).QueryCache),
      (fun p => (p.1, authRFBundle (st, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          (tags.mapM (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
            (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) tag nonce))).run c) =
        ((tags.mapM (fun tag => do
            let d ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              tag nonce
            pure (tag, d))).run (authRFBundle (st, c))) := by
  let impl : QueryImpl (unifSpec + ((TagId × Nonce) →ₒ Digest))
      (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp) +
      ((TagId × Nonce) →ₒ Digest).randomOracle
  have hImplEq : impl = PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest) := rfl
  have hquery : ∀ (d : TagId × Nonce),
      simulateQ impl
        (liftM ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr d)) :
          OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest) =
      (((TagId × Nonce) →ₒ Digest).randomOracle d :
        StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp Digest) := by
    intro d
    simp only [simulateQ_query]
    show id <$> impl (Sum.inr d) = _
    rw [id_map]
    rfl
  -- Per-tag step: simulating `Prod.mk tag <$> authPRFQuery tag nonce` is the cached random oracle.
  have hstep : ∀ (tag : TagId),
      simulateQ impl
          (Prod.mk tag <$> authPRFQuery (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            tag nonce) =
        (Prod.mk tag <$> ((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce) :
          StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp (TagId × Digest)) := by
    intro tag
    unfold authPRFQuery
    rw [simulateQ_map]
    congr 1
    exact hquery (tag, nonce)
  -- One `authRFLookup` step on a bundled state factors as the cached random oracle on the cache.
  have hlookup : ∀ (tag : TagId) (st : AuthState TagId Nonce Digest)
      (c : ((TagId × Nonce) →ₒ Digest).QueryCache),
      ((do
          let d ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce
          pure (tag, d)).run (authRFBundle (st, c))) =
        (fun p => ((tag, p.1), authRFBundle (st, p.2))) <$>
          ((((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce) :
            StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp Digest).run c) := by
    intro tag st c
    unfold authRFLookup
    simp only [OracleSpec.randomOracle, QueryImpl.withCaching_apply, StateT.run_bind,
      StateT.run_get, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp, StateT.run_map,
      map_bind]
    cases hc : c (tag, nonce) with
    | some out =>
      simp only [authRFBundle, hc, map_pure, pure_bind, StateT.run_pure]
    | none =>
      simp only [authRFBundle, hc, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
        bind_pure_comp, StateT.run_modifyGet, StateT.run_map, StateT.run_set, map_bind,
        bind_map_left, pure_bind, Functor.map_map, map_pure, uniformSampleImpl,
        HasQuery.toQueryImpl_apply]
  -- The simulated `mapM` is the `mapM` of the cached random oracle (per-tag step `hstep`).
  have hmapM : ∀ (ts : List TagId), simulateQ impl
        (ts.mapM (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
          (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) tag nonce)) =
      ts.mapM (fun tag => Prod.mk tag <$>
        ((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce)) := by
    intro ts
    induction ts with
    | nil => simp only [List.mapM_nil, simulateQ_pure]
    | cons t ts ih =>
      rw [List.mapM_cons, List.mapM_cons, simulateQ_bind, hstep t]
      refine bind_congr fun p => ?_
      rw [simulateQ_bind, ih]
      refine bind_congr fun ps => ?_
      rw [simulateQ_pure]
  intro st c
  -- Push `simulateQ` through `mapM` and the per-tag step, leaving a pure `StateT` list-fold.
  have hgoal : (fun p => (p.1, authRFBundle (st, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          (tags.mapM (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
            (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) tag nonce))).run c) =
      (fun p => (p.1, authRFBundle (st, p.2))) <$>
        ((tags.mapM (fun tag => Prod.mk tag <$>
          ((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce))).run c) := by
    rw [← hImplEq]
    exact congrArg _ (congrArg (StateT.run · c) (hmapM tags))
  rw [hgoal]
  clear hgoal hmapM hstep hquery hImplEq
  -- Induct on the tag list: each `randomOracle` step matches an `authRFLookup` step.
  induction tags generalizing c with
  | nil =>
    simp only [List.mapM_nil, StateT.run_pure, map_pure]
  | cons t ts ih =>
    rw [List.mapM_cons, List.mapM_cons]
    have hhead := hlookup t st c
    -- Expose the head/tail binds on both sides via `StateT.run_bind`.
    simp only [StateT.run_bind, StateT.run_pure, StateT.run_map, map_bind, map_pure,
      bind_pure_comp, bind_map_left, Functor.map_map] at *
    -- Factor the RHS head bind through `((t, ·.1), ·.2) <$> authRFLookup.run`, then use `hhead`.
    rw [show (do
          let p ← (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            t nonce).run (authRFBundle (st, c))
          (fun p_1 => (((t, p.1) :: p_1.1 : List (TagId × Digest)), p_1.2)) <$>
            (List.mapM (fun tag => Prod.mk tag <$> authRFLookup (TagId := TagId)
              (Nonce := Nonce) (Digest := Digest) tag nonce) ts).run p.2) =
        ((fun p => (((t, p.1) : TagId × Digest), p.2)) <$>
            (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              t nonce).run (authRFBundle (st, c))) >>= fun q =>
          (fun p_1 => ((q.1 :: p_1.1 : List (TagId × Digest)), p_1.2)) <$>
            (List.mapM (fun tag => Prod.mk tag <$> authRFLookup (TagId := TagId)
              (Nonce := Nonce) (Digest := Digest) tag nonce) ts).run q.2
      from by rw [bind_map_left]]
    rw [hhead, bind_map_left]
    refine bind_congr fun p => ?_
    have ihp := ih p.2
    simp only [StateT.run_bind, StateT.run_pure, StateT.run_map, map_bind, map_pure,
      bind_pure_comp, bind_map_left, Functor.map_map] at ihp
    rw [show (fun a => (((t, p.1) :: a.1 : List (TagId × Digest)),
            authRFBundle (st, a.2))) <$>
          (List.mapM (fun tag => Prod.mk tag <$>
            ((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce)) ts).run p.2 =
        (fun q => (((t, p.1) :: q.1 : List (TagId × Digest)), q.2)) <$>
          ((fun a => ((a.1 : List (TagId × Digest)), authRFBundle (st, a.2))) <$>
            (List.mapM (fun tag => Prod.mk tag <$>
              ((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce)) ts).run p.2)
      from by rw [Functor.map_map]]
    rw [ihp]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Per-reader-query equivalence (ideal side): simulating the reduction's reader oracle through the
lazy random oracle, threaded through the cache, matches the random-function auth-game reader. -/
private lemma simulateQ_prfIdeal_authToPRFReaderImpl_run
    (transcript : TagTranscript Nonce Digest) (s : AuthState TagId Nonce Digest)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          ((authToPRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            transcript).run s)).run c) =
      (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        transcript).run (authRFBundle (s, c)) := by
  have hmapM := simulateQ_prfIdeal_authToPRFReader_mapM (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) transcript.nonce (Finset.univ : Finset TagId).toList s c
  let impl : QueryImpl (unifSpec + ((TagId × Nonce) →ₒ Digest))
      (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp) +
      ((TagId × Nonce) →ₒ Digest).randomOracle
  have hImplEq : impl = PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest) := rfl
  -- The reduction's reader oracle is a `Functor.map` of the per-tag `mapM` (no nested binds).
  have hbody :
      ((authToPRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          transcript).run s) =
        ((fun pairs => (ReaderReply.ofBool (decide (∃ p ∈ pairs, p.2 = transcript.auth)),
            AuthState.mk s.honestOutputs
              (s.readerForged ∪ ((((pairs.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ s.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript)))))) <$>
          ((Finset.univ : Finset TagId).toList.mapM
            (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
            (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) tag transcript.nonce))) := by
    unfold authToPRFReaderImpl authPRFQuery
    simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_eq_self,
      StateT.run_map, StateT.run_set, bind_pure_comp, pure_bind, map_bind, map_pure,
      bind_map_left, Functor.map_map]
  -- Push `simulateQ` through the `Functor.map`.
  have hsimQ :
      simulateQ impl
          ((authToPRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            transcript).run s) =
        (fun pairs => (ReaderReply.ofBool (decide (∃ p ∈ pairs, p.2 = transcript.auth)),
            AuthState.mk s.honestOutputs
              (s.readerForged ∪ ((((pairs.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ s.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript)))))) <$>
          simulateQ impl
            ((Finset.univ : Finset TagId).toList.mapM
              (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
              (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) tag transcript.nonce)) := by
    rw [hbody, simulateQ_map]
  -- Rewrite the goal's `simulateQ` body through `hsimQ`, then through `hmapM`.
  have hgoal : (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          ((authToPRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            transcript).run s)).run c) =
      (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        (((fun pairs => (ReaderReply.ofBool (decide (∃ p ∈ pairs, p.2 = transcript.auth)),
            AuthState.mk s.honestOutputs
              (s.readerForged ∪ ((((pairs.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ s.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript)))))) <$>
          simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
            ((Finset.univ : Finset TagId).toList.mapM
              (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
              (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) tag transcript.nonce))).run c) := by
    rw [← hImplEq]
    exact congrArg _ (congrArg (StateT.run · c) hsimQ)
  rw [hgoal]
  simp only [StateT.run_map, map_bind, Functor.map_map]
  -- Factor the reader's post-processing through the bundling map `(·.1, authRFBundle (s, ·.2))`,
  -- so the simulated per-tag `mapM` can be replaced by the `authRFLookup`-`mapM` via `hmapM`.
  rw [show (fun a : List (TagId × Digest) × ((TagId × Nonce) →ₒ Digest).QueryCache =>
          ((ReaderReply.ofBool (decide (∃ p ∈ a.1, p.2 = transcript.auth)),
            authRFBundle (AuthState.mk s.honestOutputs
              (s.readerForged ∪ ((((a.1.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ s.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript)))), a.2)) :
            ReaderReply × AuthIdealState TagId Nonce Digest)) =
        (fun q : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
          ((ReaderReply.ofBool (decide (∃ p ∈ q.1, p.2 = transcript.auth)),
            AuthIdealState.mk q.2.responses q.2.honestOutputs
              (q.2.readerForged ∪ ((((q.1.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ q.2.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript))))) :
            ReaderReply × AuthIdealState TagId Nonce Digest)) ∘
          (fun p : List (TagId × Digest) × ((TagId × Nonce) →ₒ Digest).QueryCache =>
            ((p.1, authRFBundle (s, p.2)) :
            List (TagId × Digest) × AuthIdealState TagId Nonce Digest))
      from by funext a; simp only [Function.comp_apply, authRFBundle]]
  rw [show ((fun q : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
          ((ReaderReply.ofBool (decide (∃ p ∈ q.1, p.2 = transcript.auth)),
            AuthIdealState.mk q.2.responses q.2.honestOutputs
              (q.2.readerForged ∪ ((((q.1.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ q.2.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript))))) :
            ReaderReply × AuthIdealState TagId Nonce Digest)) ∘
        (fun p : List (TagId × Digest) × ((TagId × Nonce) →ₒ Digest).QueryCache =>
          ((p.1, authRFBundle (s, p.2)) :
          List (TagId × Digest) × AuthIdealState TagId Nonce Digest))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          ((Finset.univ : Finset TagId).toList.mapM
            (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
            (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) tag transcript.nonce))).run c) =
      (fun q : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
          ((ReaderReply.ofBool (decide (∃ p ∈ q.1, p.2 = transcript.auth)),
            AuthIdealState.mk q.2.responses q.2.honestOutputs
              (q.2.readerForged ∪ ((((q.1.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ q.2.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript))))) :
            ReaderReply × AuthIdealState TagId Nonce Digest)) <$>
        ((fun p : List (TagId × Digest) × ((TagId × Nonce) →ₒ Digest).QueryCache =>
          ((p.1, authRFBundle (s, p.2)) :
          List (TagId × Digest) × AuthIdealState TagId Nonce Digest)) <$>
          (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
            ((Finset.univ : Finset TagId).toList.mapM
              (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
              (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) tag transcript.nonce))).run c)
    from by rw [Functor.map_map]; rfl]
  rw [hmapM]
  -- Both sides are now the per-tag `mapM` followed by the same reader bookkeeping.
  unfold authRFReaderQueryImpl
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_eq_self,
    StateT.run_map, StateT.run_set, StateT.run_pure, bind_pure_comp, pure_bind, map_bind,
    map_pure, bind_map_left, Functor.map_map, authRFBundle]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Inductive helper (ideal side): simulating the auth-game adversary through the reduction's
query implementation and then through the lazy random oracle, threaded through the cache, is the
same as simulating it directly through the random-function auth query implementation, with the
cache bundled into the ideal state. -/
private theorem simulateQ_prfIdeal_authToPRFQueryImpl_run
    (adversary : AuthAdversary TagId Nonce Digest)
    (s : AuthState TagId Nonce Digest)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          ((simulateQ
            (authToPRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
            adversary).run s)).run c) =
      (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        adversary).run (authRFBundle (s, c)) := by
  induction adversary using OracleComp.inductionOn generalizing s c with
  | pure x =>
    show (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          (pure (x, s))).run c) =
      (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        (pure x)).run (authRFBundle (s, c))
    rw [simulateQ_pure, simulateQ_pure]
    simp only [StateT.run_pure, map_pure]
  | query_bind t f ih =>
    rcases t with tag | transcript
    · -- Tag query: use the per-tag-query ideal helper, then the induction hypothesis.
      have hstep := simulateQ_prfIdeal_authToPRFTagImpl_run (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) tag s c
      change (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
          ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
            (((authToPRFTagImpl tag).run s) >>= fun p =>
              (simulateQ authToPRFQueryImpl (f p.1)).run p.2)).run c) =
        ((authIdealTagQueryImpl tag).run (authRFBundle (s, c))) >>= fun p =>
          (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
            (f p.1)).run p.2
      rw [simulateQ_bind]
      simp only [StateT.run_bind, map_bind]
      rw [show (do
            let a ← (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
              ((authToPRFTagImpl tag).run s)).run c
            (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
              (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
                ((simulateQ authToPRFQueryImpl (f a.1.1)).run a.1.2)).run a.2) =
          ((fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
              (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
                ((authToPRFTagImpl tag).run s)).run c) >>= fun q =>
            (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
              (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
                ((simulateQ authToPRFQueryImpl (f q.1)).run
                  (AuthState.mk q.2.honestOutputs q.2.readerForged))).run q.2.responses
        from by rw [bind_map_left]; rfl]
      refine Eq.trans (congrArg
        (fun (x : ProbComp (TagTranscript Nonce Digest × AuthIdealState TagId Nonce Digest)) =>
          x >>= fun q =>
          (fun p : (Unit × AuthState TagId Nonce Digest) ×
              ((TagId × Nonce) →ₒ Digest).QueryCache =>
            (p.1.1, authRFBundle (p.1.2, p.2))) <$>
            (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
              ((simulateQ authToPRFQueryImpl (f q.1)).run
                (AuthState.mk q.2.honestOutputs q.2.readerForged))).run q.2.responses) hstep) ?_
      refine bind_congr fun p => ?_
      exact ih p.1 (AuthState.mk p.2.honestOutputs p.2.readerForged) p.2.responses
    · -- Reader query: use the per-reader-query ideal helper, then the induction hypothesis.
      have hstep := simulateQ_prfIdeal_authToPRFReaderImpl_run (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) transcript s c
      change (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
          ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
            (((authToPRFReaderImpl transcript).run s) >>= fun p =>
              (simulateQ authToPRFQueryImpl (f p.1)).run p.2)).run c) =
        ((authRFReaderQueryImpl transcript).run (authRFBundle (s, c))) >>= fun p =>
          (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
            (f p.1)).run p.2
      rw [simulateQ_bind]
      simp only [StateT.run_bind, map_bind]
      rw [show (do
            let a ← (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
              ((authToPRFReaderImpl transcript).run s)).run c
            (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
              (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
                ((simulateQ authToPRFQueryImpl (f a.1.1)).run a.1.2)).run a.2) =
          ((fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
              (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
                ((authToPRFReaderImpl transcript).run s)).run c) >>= fun q =>
            (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
              (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
                ((simulateQ authToPRFQueryImpl (f q.1)).run
                  (AuthState.mk q.2.honestOutputs q.2.readerForged))).run q.2.responses
        from by rw [bind_map_left]; rfl]
      refine Eq.trans (congrArg
        (fun (x : ProbComp (ReaderReply × AuthIdealState TagId Nonce Digest)) =>
          x >>= fun q =>
          (fun p : (Unit × AuthState TagId Nonce Digest) ×
              ((TagId × Nonce) →ₒ Digest).QueryCache =>
            (p.1.1, authRFBundle (p.1.2, p.2))) <$>
            (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
              ((simulateQ authToPRFQueryImpl (f q.1)).run
                (AuthState.mk q.2.honestOutputs q.2.readerForged))).run q.2.responses) hstep) ?_
      refine bind_congr fun p => ?_
      exact ih p.1 (AuthState.mk p.2.honestOutputs p.2.readerForged) p.2.responses

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The random-function authentication experiment coincides with its direct form: running the PRF
reduction against a lazy random oracle (`authRFExp`) produces the same distribution as running the
adversary against the directly-defined random-function oracle `authRFQueryImpl` (`authRFDirectExp`).

The lazy random oracle answering the reduction's PRF queries at `(tag, nonce)` is exactly the
`responses` table threaded by `authRFQueryImpl`. -/
theorem authRFExp_eq_authRFDirectExp
    (adversary : AuthAdversary TagId Nonce Digest) :
    authRFExp (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary =
      authRFDirectExp (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary := by
  unfold authRFExp authRFDirectExp PRFScheme.prfIdealExp authToPRFReduction
  have hquery := simulateQ_prfIdeal_authToPRFQueryImpl_run (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) adversary AuthState.init ∅
  -- `authRFBundle (AuthState.init, ∅)` is `AuthIdealState.init`.
  have hinit : authRFBundle (AuthState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest),
      (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache)) = AuthIdealState.init := rfl
  rw [hinit] at hquery
  -- Reduce the reduction's `simulateQ … >>= pure (decide …)` and apply the inductive helper.
  change (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
      (((simulateQ authToPRFQueryImpl adversary).run AuthState.init) >>=
        fun p => pure (decide (p.2.readerForged ≠ ∅)))).run' ∅ =
    (do
      let (_, st) ← (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest)) adversary).run AuthIdealState.init
      return decide (st.readerForged ≠ ∅))
  rw [simulateQ_bind]
  simp only [StateT.run'_eq, StateT.run_bind, map_bind]
  rw [← hquery]
  simp only [StateT.run_map, map_bind, Functor.map_map, simulateQ_pure, StateT.run_pure,
    bind_pure_comp, map_pure, authRFBundle]

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- One `authRFLookup` step preserves the invariant `responses t₀ = some d`: a cache hit leaves the
table unchanged, and a cache miss only writes a fresh entry at the looked-up point, which is
necessarily distinct from `t₀` since `t₀` is already cached. -/
private lemma authRFLookup_responses_some_preservesInv
    (t₀ : TagId × Nonce) (d : Digest) (tag : TagId) (nonce : Nonce) :
    StateT.PreservesInv
      (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce)
      (fun st => st.responses t₀ = some d) := by
  intro st hst z hz
  unfold authRFLookup at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hresp : st.responses (tag, nonce) with
  | some out =>
    simp only [hresp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    exact hst
  | none =>
    simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
      StateT.run_map, StateT.run_set, support_bind, support_uniformSample, Set.mem_univ,
      Set.mem_iUnion, support_map, Set.mem_image, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨i, -, x, rfl, rfl⟩ := hz
    have hkey : t₀ ≠ (tag, nonce) := by
      rintro rfl
      rw [hresp] at hst
      simp at hst
    change (st.responses.cacheQuery (tag, nonce) i.1) t₀ = some d
    rw [QueryCache.cacheQuery_of_ne _ _ hkey]
    exact hst

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- The reader's `mapM` of `authRFLookup` over a list of tags preserves the invariant
`responses t₀ = some d`, by iterating `authRFLookup_responses_some_preservesInv`. -/
private lemma authRFLookup_mapM_responses_some_preservesInv
    (t₀ : TagId × Nonce) (d : Digest) (nonce : Nonce) (tags : List TagId) :
    StateT.PreservesInv
      (tags.mapM (fun tag => do
        let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce
        pure (tag, dg)))
      (fun st => st.responses t₀ = some d) := by
  induction tags with
  | nil =>
    simp only [List.mapM_nil]
    exact StateT.preservesInv_of_statePreserving _ _ (StateT.statePreserving_pure _)
  | cons hd tl ih =>
    rw [List.mapM_cons]
    refine StateT.preservesInv_bind _ _ _ ?_ ?_
    · refine StateT.preservesInv_bind _ _ _ ?_ ?_
      · exact authRFLookup_responses_some_preservesInv t₀ d hd nonce
      · intro dg
        exact StateT.preservesInv_of_statePreserving _ _ (StateT.statePreserving_pure _)
    · intro p
      refine StateT.preservesInv_bind _ _ _ ih ?_
      intro ps
      exact StateT.preservesInv_of_statePreserving _ _ (StateT.statePreserving_pure _)

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The lazy random-oracle cache threaded by `authRFQueryImpl` only grows: once a point `t₀`
holds a digest `d`, every reachable later state still has `t₀ ↦ d`. -/
private lemma authRFQueryImpl_responses_some_preservesInv
    (t₀ : TagId × Nonce) (d : Digest) :
    QueryImpl.PreservesInv
      (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
      (fun st => st.responses t₀ = some d) := by
  intro t st hst z hz
  cases t with
  | inl tag =>
    have htag : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (Sum.inl tag)).run st =
        (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag).run st :=
      rfl
    rw [htag] at hz
    unfold authIdealTagQueryImpl at hz
    simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_eq_self, bind_map_left] at hz
    obtain ⟨nonce, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
    cases hresp : st.responses (tag, nonce) with
    | none =>
      simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
        StateT.run_map, StateT.run_set, map_pure, Functor.map_map] at hz
      rw [map_eq_bind_pure_comp] at hz
      obtain ⟨auth, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      simp only [Function.comp_apply] at hz
      subst hz
      have hkey : t₀ ≠ (tag, nonce) := by
        rintro rfl
        rw [hresp] at hst
        simp at hst
      change (st.responses.cacheQuery (tag, nonce) auth) t₀ = some d
      rw [QueryCache.cacheQuery_of_ne _ _ hkey]
      exact hst
    | some out =>
      simp only [hresp, StateT.run_map, StateT.run_set, map_pure] at hz
      rcases hz with rfl
      exact hst
  | inr transcript =>
    have hrd : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (Sum.inr transcript)).run st =
        (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          transcript).run st :=
      rfl
    rw [hrd] at hz
    unfold authRFReaderQueryImpl at hz
    simp only [bind_pure_comp, StateT.run_bind] at hz
    obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
    simp only [StateT.run_get, pure_bind, StateT.run_map, StateT.run_set, map_pure] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact authRFLookup_mapM_responses_some_preservesInv t₀ d transcript.nonce
      (Finset.univ : Finset TagId).toList st hst p hp

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- One `authRFLookup tag nonce` step at a point distinct from `t₀` preserves `responses t₀ = none`.
The looked-up point `(tag, nonce)` differs from `t₀`, so a cache miss writes elsewhere. -/
private lemma authRFLookup_responses_none_preservesInv
    (t₀ : TagId × Nonce) (tag : TagId) (nonce : Nonce) (hne : (tag, nonce) ≠ t₀) :
    StateT.PreservesInv
      (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce)
      (fun st => st.responses t₀ = none) := by
  intro st hst z hz
  unfold authRFLookup at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hresp : st.responses (tag, nonce) with
  | some out =>
    simp only [hresp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    exact hst
  | none =>
    simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
      StateT.run_map, StateT.run_set, support_bind, support_uniformSample, Set.mem_univ,
      Set.mem_iUnion, support_map, Set.mem_image, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨i, -, x, rfl, rfl⟩ := hz
    change (st.responses.cacheQuery (tag, nonce) i.1) t₀ = none
    rw [QueryCache.cacheQuery_of_ne _ _ (fun h => hne h.symm)]
    exact hst

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- The reader's `mapM` of `authRFLookup` at a nonce different from `t₀.2` preserves
`responses t₀ = none`: every looked-up point `(tag, nonce)` differs from `t₀`. -/
private lemma authRFLookup_mapM_responses_none_preservesInv
    (t₀ : TagId × Nonce) (nonce : Nonce) (hne : nonce ≠ t₀.2) (tags : List TagId) :
    StateT.PreservesInv
      (tags.mapM (fun tag => do
        let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce
        pure (tag, dg)))
      (fun st => st.responses t₀ = none) := by
  induction tags with
  | nil =>
    simp only [List.mapM_nil]
    exact StateT.preservesInv_of_statePreserving _ _ (StateT.statePreserving_pure _)
  | cons hd tl ih =>
    rw [List.mapM_cons]
    refine StateT.preservesInv_bind _ _ _ ?_ ?_
    · refine StateT.preservesInv_bind _ _ _ ?_ ?_
      · refine authRFLookup_responses_none_preservesInv t₀ hd nonce ?_
        intro hcontra
        exact hne (congrArg Prod.snd hcontra)
      · intro dg
        exact StateT.preservesInv_of_statePreserving _ _ (StateT.statePreserving_pure _)
    · intro p
      refine StateT.preservesInv_bind _ _ _ ih ?_
      intro ps
      exact StateT.preservesInv_of_statePreserving _ _ (StateT.statePreserving_pure _)

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- One `authRFLookup tag nonce` step at the point `t₀` itself, starting from `responses t₀ = none`
(so it is a genuine cache miss), draws a single fresh uniform digest into `t₀`: the probability that
`t₀` ends holding any fixed `v₀` is at most `maxDigestProb`, and it never stays `none`. -/
private lemma authRFLookup_miss_bound
    (maxDigestProb : ℝ≥0∞)
    (hmax : ∀ v : Digest, Pr[= v | ($ᵗ Digest : ProbComp Digest)] ≤ maxDigestProb)
    (t₀ : TagId × Nonce) (v₀ : Digest)
    (st : AuthIdealState TagId Nonce Digest)
    (hnone : st.responses t₀ = none) :
    Pr[fun p => p.2.responses t₀ = some v₀ |
        (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t₀.1 t₀.2).run st] ≤
      maxDigestProb ∧
    Pr[fun p => p.2.responses t₀ = none |
        (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          t₀.1 t₀.2).run st] = 0 := by
  classical
  have hrun : (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      t₀.1 t₀.2).run st =
      ((fun d => (d, ({ st with responses := st.responses.cacheQuery t₀ d } :
          AuthIdealState TagId Nonce Digest))) <$> ($ᵗ Digest : ProbComp Digest)) := by
    unfold authRFLookup
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rw [show st.responses (t₀.1, t₀.2) = none from (Prod.mk.eta ▸ hnone)]
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
      StateT.run_map, StateT.run_set, map_pure, Functor.map_map]
  rw [hrun]
  rw [probEvent_map, probEvent_map]
  refine ⟨?_, ?_⟩
  · have hext : Pr[((fun p => p.2.responses t₀ = some v₀) ∘ fun d =>
          (d, ({ st with responses := st.responses.cacheQuery t₀ d } :
            AuthIdealState TagId Nonce Digest))) | ($ᵗ Digest : ProbComp Digest)] =
        Pr[fun d => d = v₀ | ($ᵗ Digest : ProbComp Digest)] := by
      refine probEvent_ext fun d _ => ?_
      change (st.responses.cacheQuery t₀ d) t₀ = some v₀ ↔ d = v₀
      rw [QueryCache.cacheQuery_self]
      exact Option.some_inj
    rw [hext, probEvent_eq_eq_probOutput]
    exact hmax v₀
  · rw [probEvent_eq_zero_iff]
    intro d _
    change ¬ (st.responses.cacheQuery t₀ d) t₀ = none
    rw [QueryCache.cacheQuery_self]
    exact Option.some_ne_none d

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- A `responses`-only event of the reader's lookup `mapM` over `hd :: tl` factors as the head
lookup followed by the tail `mapM`: the accumulated tag list never affects the `responses` table,
so the event depends only on the threaded state. -/
private lemma authRFLookup_mapM_cons_responses
    (hd : TagId) (tl : List TagId) (nonce : Nonce)
    (st : AuthIdealState TagId Nonce Digest)
    (P : ((TagId × Nonce) →ₒ Digest).QueryCache → Prop) :
    Pr[fun p => P p.2.responses |
        ((hd :: tl).mapM (fun tag => do
          let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce
          pure (tag, dg))).run st] =
      Pr[fun p => P p.2.responses |
        (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) hd nonce).run st >>=
          fun q => (tl.mapM (fun tag => do
            let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce
            pure (tag, dg))).run q.2] := by
  classical
  rw [List.mapM_cons]
  simp only [bind_pure_comp, StateT.run_bind, StateT.run_map, bind_map_left]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun q => ?_
  congr 1
  rw [probEvent_map]
  rfl

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- The reader's `mapM` of `authRFLookup` over a nodup list of tags that contains `t₀.1`, run at
nonce `t₀.2`, fills the cache point `t₀` with exactly one fresh uniform draw: starting from
`responses t₀ = none`, the probability the final state has `t₀ ↦ v₀` plus `maxDigestProb` times the
probability `t₀` is still `none` is at most `maxDigestProb`. -/
private lemma authRFLookup_mapM_miss_bound
    (maxDigestProb : ℝ≥0∞)
    (hmax : ∀ v : Digest, Pr[= v | ($ᵗ Digest : ProbComp Digest)] ≤ maxDigestProb)
    (t₀ : TagId × Nonce) (v₀ : Digest) :
    ∀ (tags : List TagId), tags.Nodup → t₀.1 ∈ tags →
      ∀ (st : AuthIdealState TagId Nonce Digest), st.responses t₀ = none →
        Pr[fun p => p.2.responses t₀ = some v₀ |
            (tags.mapM (fun tag => do
              let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                tag t₀.2
              pure (tag, dg))).run st] +
          maxDigestProb *
            Pr[fun p => p.2.responses t₀ = none |
              (tags.mapM (fun tag => do
                let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  tag t₀.2
                pure (tag, dg))).run st] ≤
        maxDigestProb := by
  classical
  intro tags
  induction tags with
  | nil => intro _ hmem; exact absurd hmem (List.not_mem_nil)
  | cons hd tl ih =>
    intro hnodup hmem st hnone
    rw [authRFLookup_mapM_cons_responses (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        hd tl t₀.2 st (fun c => c t₀ = some v₀),
      authRFLookup_mapM_cons_responses (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        hd tl t₀.2 st (fun c => c t₀ = none)]
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    set f := fun tag => do
      let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag t₀.2
      pure (tag, dg) with hf
    by_cases hhd : hd = t₀.1
    · -- Head lookup is at `t₀` itself: a cache miss that draws the single fresh digest.
      subst hhd
      have hlook := authRFLookup_miss_bound (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        maxDigestProb hmax t₀ v₀ st hnone
      -- After the head lookup `t₀` is pinned, so the tail `mapM` keeps `t₀` filled.
      have hpin : ∀ q ∈ support
          ((authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t₀.1 t₀.2).run st),
          ∃ d, q.2.responses t₀ = some d := by
        intro q hq
        unfold authRFLookup at hq
        simp only [StateT.run_bind, StateT.run_get, pure_bind] at hq
        rw [show st.responses (t₀.1, t₀.2) = none from hnone] at hq
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
          StateT.run_map, StateT.run_set, support_bind, support_uniformSample, Set.mem_univ,
          Set.mem_iUnion, support_map, Set.mem_image, support_pure, Set.mem_singleton_iff] at hq
        obtain ⟨i, -, x, rfl, rfl⟩ := hq
        exact ⟨i.1, QueryCache.cacheQuery_self _ _ _⟩
      have hnone0 :
          ∑' q : Digest × AuthIdealState TagId Nonce Digest,
            Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              t₀.1 t₀.2).run st] *
              Pr[fun p => p.2.responses t₀ = none | (tl.mapM f).run q.2] = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun q => ?_
        by_cases hsupp : q ∈ support
            ((authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              t₀.1 t₀.2).run st)
        · obtain ⟨d, hqd⟩ := hpin q hsupp
          have hz : Pr[fun p => p.2.responses t₀ = none | (tl.mapM f).run q.2] = 0 := by
            rw [probEvent_eq_zero_iff]
            intro p hp
            have hpp := authRFLookup_mapM_responses_some_preservesInv (TagId := TagId)
              (Nonce := Nonce) (Digest := Digest) t₀ d t₀.2 tl q.2 hqd p hp
            simp [hpp]
          rw [hz, mul_zero]
        · rw [probOutput_eq_zero _ q hsupp, zero_mul]
      have hsome_le :
          ∑' q : Digest × AuthIdealState TagId Nonce Digest,
            Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              t₀.1 t₀.2).run st] *
              Pr[fun p => p.2.responses t₀ = some v₀ | (tl.mapM f).run q.2] ≤
            Pr[fun p => p.2.responses t₀ = some v₀ |
              (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                t₀.1 t₀.2).run st] := by
        rw [probEvent_eq_tsum_ite]
        refine ENNReal.tsum_le_tsum fun q => ?_
        by_cases hsupp : q ∈ support
            ((authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              t₀.1 t₀.2).run st)
        · obtain ⟨d, hqd⟩ := hpin q hsupp
          by_cases hdv : d = v₀
          · subst hdv
            rw [if_pos hqd]
            exact le_trans (mul_le_mul' le_rfl probEvent_le_one) (le_of_eq (mul_one _))
          · have hz : Pr[fun p => p.2.responses t₀ = some v₀ | (tl.mapM f).run q.2] = 0 := by
              rw [probEvent_eq_zero_iff]
              intro p hp
              have hpp := authRFLookup_mapM_responses_some_preservesInv (TagId := TagId)
                (Nonce := Nonce) (Digest := Digest) t₀ d t₀.2 tl q.2 hqd p hp
              rw [hpp]
              simp [hdv]
            rw [hz, mul_zero]
            exact zero_le _
        · rw [probOutput_eq_zero _ q hsupp, zero_mul]
          exact zero_le _
      rw [hnone0, mul_zero, add_zero]
      exact le_trans hsome_le hlook.1
    · -- Head lookup is at a tag `≠ t₀.1`: the point `(hd, t₀.2) ≠ t₀`, so `t₀` stays `none`.
      have hmemtl : t₀.1 ∈ tl := by
        rcases List.mem_cons.1 hmem with h | h
        · exact absurd h.symm hhd
        · exact h
      have hnoduptl : tl.Nodup := (List.nodup_cons.1 hnodup).2
      have hne : (hd, t₀.2) ≠ t₀ := by
        intro hc
        exact hhd (congrArg Prod.fst hc)
      have hpres := authRFLookup_responses_none_preservesInv (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) t₀ hd t₀.2 hne
      calc (∑' q : Digest × AuthIdealState TagId Nonce Digest,
              Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                hd t₀.2).run st] *
                Pr[fun p => p.2.responses t₀ = some v₀ | (tl.mapM f).run q.2]) +
            maxDigestProb *
              ∑' q : Digest × AuthIdealState TagId Nonce Digest,
                Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  hd t₀.2).run st] *
                  Pr[fun p => p.2.responses t₀ = none | (tl.mapM f).run q.2]
          = ∑' q : Digest × AuthIdealState TagId Nonce Digest,
              Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                hd t₀.2).run st] *
                (Pr[fun p => p.2.responses t₀ = some v₀ | (tl.mapM f).run q.2] +
                  maxDigestProb *
                    Pr[fun p => p.2.responses t₀ = none | (tl.mapM f).run q.2]) := by
            rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
            refine tsum_congr fun q => ?_
            rw [mul_add]
            congr 1
            rw [mul_left_comm]
        _ ≤ ∑' q : Digest × AuthIdealState TagId Nonce Digest,
              Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                hd t₀.2).run st] * maxDigestProb := by
            refine ENNReal.tsum_le_tsum fun q => ?_
            by_cases hsupp : q ∈ support
                ((authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  hd t₀.2).run st)
            · have hqn : q.2.responses t₀ = none := hpres st hnone q hsupp
              exact mul_le_mul' le_rfl (ih hnoduptl hmemtl q.2 hqn)
            · rw [probOutput_eq_zero _ q hsupp, zero_mul, zero_mul]
        _ = maxDigestProb * ∑' q : Digest × AuthIdealState TagId Nonce Digest,
              Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                hd t₀.2).run st] := by
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun q => ?_
            rw [mul_comm]
        _ ≤ maxDigestProb :=
            le_trans (mul_le_mul' le_rfl tsum_probOutput_le_one) (le_of_eq (mul_one _))

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Single-step random-oracle bound for a cache point `t₀` that is not yet filled: after one
`authRFQueryImpl` query step, the probability that `t₀` ends holding `v₀` plus `maxDigestProb`
times the probability that `t₀` is still unfilled is at most `maxDigestProb`.

A query step fills `t₀` (if at all) with a single fresh uniform `Digest` draw, so the event
`t₀ ↦ v₀` is dominated by `maxDigestProb` times the probability that the step touched `t₀`. -/
private lemma probEvent_authRFQueryImpl_step_core
    (maxDigestProb : ℝ≥0∞)
    (hmax : ∀ v : Digest, Pr[= v | ($ᵗ Digest : ProbComp Digest)] ≤ maxDigestProb)
    (t₀ : TagId × Nonce) (v₀ : Digest)
    (t : AuthOracleSpec TagId Nonce Digest |>.Domain)
    (st : AuthIdealState TagId Nonce Digest)
    (hnone : st.responses t₀ = none) :
    Pr[fun p => p.2.responses t₀ = some v₀ |
        (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run st] +
      maxDigestProb *
        Pr[fun p => p.2.responses t₀ = none |
          (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run st] ≤
      maxDigestProb := by
  classical
  cases t with
  | inl tag =>
    have htag : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (Sum.inl tag)).run st =
        (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag).run st :=
      rfl
    rw [htag]
    -- Reduce the tag handler to a `nonce`-bind whose body either fills `t₀` or leaves it `none`.
    have hrun : (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        tag).run st =
        (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
          (match st.responses (tag, nonce) with
            | some out => pure
                (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                  ({ responses := st.responses,
                     honestOutputs :=
                       insert (tag,
                         ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                         st.honestOutputs,
                     readerForged := st.readerForged } :
                    AuthIdealState TagId Nonce Digest))
            | none => (($ᵗ Digest : ProbComp Digest) >>= fun out => pure
                (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                  ({ responses := st.responses.cacheQuery (tag, nonce) out,
                     honestOutputs :=
                       insert (tag,
                         ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                         st.honestOutputs,
                     readerForged := st.readerForged } :
                    AuthIdealState TagId Nonce Digest)))) :
            ProbComp (TagTranscript Nonce Digest × AuthIdealState TagId Nonce Digest)) := by
      unfold authIdealTagQueryImpl
      simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
        monadLift_eq_self, bind_map_left]
      refine bind_congr fun nonce => ?_
      cases hresp : st.responses (tag, nonce) with
      | some out =>
        simp only [StateT.run_map, StateT.run_set, map_pure]
      | none =>
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
          StateT.run_map, StateT.run_set, map_pure, Functor.map_map]
    rw [hrun]
    -- Per-`nonce` bounds on the two events.
    have hkey : ∀ nonce : Nonce, (tag, nonce) = t₀ ↔ (tag = t₀.1 ∧ nonce = t₀.2) := by
      intro nonce
      constructor
      · intro h; exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      · intro ⟨h1, h2⟩; exact Prod.ext h1 h2
    -- Probability of `t₀ ↦ v₀` after the bind, bounded per `nonce`.
    have hsome :
        Pr[fun p => p.2.responses t₀ = some v₀ |
            (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
              (match st.responses (tag, nonce) with
                | some out => pure
                    (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                      ({ responses := st.responses,
                         honestOutputs :=
                           insert (tag,
                             ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                             st.honestOutputs,
                         readerForged := st.readerForged } :
                        AuthIdealState TagId Nonce Digest))
                | none => (($ᵗ Digest : ProbComp Digest) >>= fun out => pure
                    (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                      ({ responses := st.responses.cacheQuery (tag, nonce) out,
                         honestOutputs :=
                           insert (tag,
                             ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                             st.honestOutputs,
                         readerForged := st.readerForged } :
                        AuthIdealState TagId Nonce Digest)))) :
                ProbComp (TagTranscript Nonce Digest × AuthIdealState TagId Nonce Digest))] ≤
          ∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
            (if (tag, nonce) = t₀ then maxDigestProb else 0) := by
      rw [probEvent_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum fun nonce => mul_le_mul' le_rfl ?_
      by_cases hk : (tag, nonce) = t₀
      · rw [if_pos hk]
        rw [show st.responses (tag, nonce) = none from hk ▸ hnone]
        rw [probEvent_bind_eq_tsum]
        calc ∑' out : Digest, Pr[= out | ($ᵗ Digest : ProbComp Digest)] *
                Pr[fun p => p.2.responses t₀ = some v₀ |
                  (pure (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                    ({ responses := st.responses.cacheQuery (tag, nonce) out,
                       honestOutputs :=
                         insert (tag,
                           ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                           st.honestOutputs,
                       readerForged := st.readerForged } :
                      AuthIdealState TagId Nonce Digest)) :
                    ProbComp (TagTranscript Nonce Digest × AuthIdealState TagId Nonce Digest))]
            = ∑' out : Digest,
                (if out = v₀ then Pr[= out | ($ᵗ Digest : ProbComp Digest)] else 0) := by
              refine tsum_congr fun out => ?_
              rw [probEvent_pure]
              have hco : (st.responses.cacheQuery (tag, nonce) out) t₀ = some out := by
                rw [← hk, QueryCache.cacheQuery_self]
              by_cases hov : out = v₀
              · subst hov
                simp [hco]
              · simp only [hco]
                rw [if_neg (by simp [hov]), if_neg hov, mul_zero]
          _ = Pr[= v₀ | ($ᵗ Digest : ProbComp Digest)] := by
              rw [tsum_ite_eq]
          _ ≤ maxDigestProb := hmax v₀
      · rw [if_neg hk]
        have hne : t₀ ≠ (tag, nonce) := fun h => hk h.symm
        cases hresp : st.responses (tag, nonce) with
        | some out =>
          rw [probEvent_pure]
          simp [hnone]
        | none =>
          rw [probEvent_bind_eq_tsum]
          refine le_of_le_of_eq (le_refl _) ?_
          refine ENNReal.tsum_eq_zero.mpr fun out => ?_
          rw [probEvent_pure]
          simp [QueryCache.cacheQuery_of_ne _ _ hne, hnone]
    -- Probability of `t₀` staying `none` after the bind, bounded per `nonce`.
    have hnoneEv :
        Pr[fun p => p.2.responses t₀ = none |
            (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
              (match st.responses (tag, nonce) with
                | some out => pure
                    (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                      ({ responses := st.responses,
                         honestOutputs :=
                           insert (tag,
                             ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                             st.honestOutputs,
                         readerForged := st.readerForged } :
                        AuthIdealState TagId Nonce Digest))
                | none => (($ᵗ Digest : ProbComp Digest) >>= fun out => pure
                    (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                      ({ responses := st.responses.cacheQuery (tag, nonce) out,
                         honestOutputs :=
                           insert (tag,
                             ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                             st.honestOutputs,
                         readerForged := st.readerForged } :
                        AuthIdealState TagId Nonce Digest)))) :
                ProbComp (TagTranscript Nonce Digest × AuthIdealState TagId Nonce Digest))] ≤
          ∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
            (if (tag, nonce) = t₀ then (0 : ℝ≥0∞) else 1) := by
      rw [probEvent_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum fun nonce => mul_le_mul' le_rfl ?_
      by_cases hk : (tag, nonce) = t₀
      · rw [if_pos hk]
        rw [show st.responses (tag, nonce) = none from hk ▸ hnone]
        rw [probEvent_bind_eq_tsum]
        refine le_of_le_of_eq (le_refl _) ?_
        refine ENNReal.tsum_eq_zero.mpr fun out => ?_
        rw [probEvent_pure]
        have hcache : (st.responses.cacheQuery (tag, nonce) out) t₀ = some out := by
          rw [← hk, QueryCache.cacheQuery_self]
        simp [hcache]
      · rw [if_neg hk]
        exact probEvent_le_one
    -- Combine: total `≤ maxDigestProb * ∑' nonce, Pr[= nonce] ≤ maxDigestProb`.
    refine le_trans (add_le_add hsome (mul_le_mul' le_rfl hnoneEv)) ?_
    have hcollapse :
        (∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
            (if (tag, nonce) = t₀ then maxDigestProb else 0)) +
          maxDigestProb * ∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
            (if (tag, nonce) = t₀ then (0 : ℝ≥0∞) else 1) =
          maxDigestProb * ∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] := by
      have hterm : ∀ nonce : Nonce,
          (Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
              (if (tag, nonce) = t₀ then maxDigestProb else 0)) +
            maxDigestProb * (Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
              (if (tag, nonce) = t₀ then (0 : ℝ≥0∞) else 1)) =
            maxDigestProb * Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] := by
        intro nonce
        by_cases hk : (tag, nonce) = t₀ <;> simp [hk, mul_comm]
      calc (∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
              (if (tag, nonce) = t₀ then maxDigestProb else 0)) +
            maxDigestProb * ∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
              (if (tag, nonce) = t₀ then (0 : ℝ≥0∞) else 1)
          = (∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
                (if (tag, nonce) = t₀ then maxDigestProb else 0)) +
              ∑' nonce : Nonce, maxDigestProb *
                (Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
                  (if (tag, nonce) = t₀ then (0 : ℝ≥0∞) else 1)) := by
            rw [ENNReal.tsum_mul_left]
        _ = ∑' nonce : Nonce,
              ((Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
                  (if (tag, nonce) = t₀ then maxDigestProb else 0)) +
                maxDigestProb * (Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
                  (if (tag, nonce) = t₀ then (0 : ℝ≥0∞) else 1))) := by
            rw [ENNReal.tsum_add]
        _ = ∑' nonce : Nonce, maxDigestProb * Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] :=
            tsum_congr hterm
        _ = maxDigestProb * ∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] := by
            rw [ENNReal.tsum_mul_left]
    rw [hcollapse]
    exact le_trans (mul_le_mul' le_rfl tsum_probOutput_le_one) (le_of_eq (mul_one _))
  | inr transcript =>
    have hrd : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (Sum.inr transcript)).run st =
        (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          transcript).run st :=
      rfl
    rw [hrd]
    -- The reader handler runs the lookup `mapM`, then a `get`/`set` that only touches
    -- `readerForged`; hence the `responses`-field events factor through the `mapM`.
    have hmapM_run : ∀ (P : ((TagId × Nonce) →ₒ Digest).QueryCache → Prop),
        Pr[fun p => P p.2.responses |
            (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              transcript).run st] =
          Pr[fun p => P p.2.responses |
            ((Finset.univ : Finset TagId).toList.mapM (fun tag => do
              let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                tag transcript.nonce
              pure (tag, dg))).run st] := by
      intro P
      unfold authRFReaderQueryImpl
      simp only [bind_pure_comp, StateT.run_bind]
      rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
      refine tsum_congr fun p => ?_
      rw [mul_comm]
      simp only [StateT.run_get, pure_bind, StateT.run_map, StateT.run_set, map_pure,
        probEvent_pure]
      by_cases hP : P p.2.responses <;> simp [hP]
    have heq1 := hmapM_run (fun c => c t₀ = some v₀)
    have heq2 := hmapM_run (fun c => c t₀ = none)
    refine heq1 ▸ heq2 ▸ ?_
    by_cases hnonce : transcript.nonce = t₀.2
    · -- Here `transcript.nonce = t₀.2`, so the lookup `mapM` over `Finset.univ.toList` includes a
      -- cache-miss lookup at `t₀ = (t₀.1, t₀.2)`, drawing one fresh uniform digest that pins `t₀`.
      rw [hnonce]
      exact authRFLookup_mapM_miss_bound (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        maxDigestProb hmax t₀ v₀ (Finset.univ : Finset TagId).toList
        (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ _)) st hnone
    · -- The lookup `mapM` is at a nonce `≠ t₀.2`, so `t₀` is never touched: stays `none`.
      have hpres :=
        authRFLookup_mapM_responses_none_preservesInv (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) t₀ transcript.nonce hnonce (Finset.univ : Finset TagId).toList
      have hsome0 :
          Pr[fun p => p.2.responses t₀ = some v₀ |
            ((Finset.univ : Finset TagId).toList.mapM (fun tag => do
              let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                tag transcript.nonce
              pure (tag, dg))).run st] = 0 := by
        rw [probEvent_eq_zero_iff]
        intro p hp
        have hpn := hpres st hnone p hp
        rw [hpn]
        simp
      have hnone1 :
          Pr[fun p => p.2.responses t₀ = none |
            ((Finset.univ : Finset TagId).toList.mapM (fun tag => do
              let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                tag transcript.nonce
              pure (tag, dg))).run st] ≤ 1 := probEvent_le_one
      rw [hsome0, zero_add]
      exact le_trans (mul_le_mul' le_rfl hnone1) (le_of_eq (mul_one _))


omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Single-point random-oracle bound: a fixed cache point `t₀` is filled by at most one uniform
draw over the whole `authRFQueryImpl` simulation, so it ends holding any fixed digest `v₀` with
probability at most `maxDigestProb`. -/
private lemma probEvent_authRFQueryImpl_responses_eq_le
    {α : Type}
    (maxDigestProb : ℝ≥0∞)
    (hmax : ∀ v : Digest, Pr[= v | ($ᵗ Digest : ProbComp Digest)] ≤ maxDigestProb)
    (adversary : OracleComp (AuthOracleSpec TagId Nonce Digest) α)
    (t₀ : TagId × Nonce) (v₀ : Digest)
    (st : AuthIdealState TagId Nonce Digest)
    (hnone : st.responses t₀ = none) :
    Pr[fun z => z.2.responses t₀ = some v₀ |
        (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          adversary).run st] ≤ maxDigestProb := by
  classical
  -- State-indexed bound: `1` once `t₀ ↦ v₀`, `maxDigestProb` while `t₀` is unfilled, `0` otherwise.
  set stbound : AuthIdealState TagId Nonce Digest → ℝ≥0∞ := fun st =>
    if st.responses t₀ = some v₀ then (1 : ℝ≥0∞)
    else if st.responses t₀ = none then maxDigestProb else 0 with hstbound
  -- General claim: the win probability from any reachable state is bounded by `stbound`.
  have hgen : ∀ (adv : OracleComp (AuthOracleSpec TagId Nonce Digest) α)
      (s : AuthIdealState TagId Nonce Digest),
      Pr[fun z => z.2.responses t₀ = some v₀ |
          (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
            adv).run s] ≤ stbound s := by
    intro adv
    induction adv using OracleComp.inductionOn with
    | pure x =>
      intro s
      simp only [simulateQ_pure, StateT.run_pure, probEvent_pure]
      by_cases hv : s.responses t₀ = some v₀
      · simp only [hv, if_true, hstbound]
        simp
      · simp only [hv, if_false]
        simp only [hstbound]
        positivity
    | query_bind t oa ih =>
      intro s
      simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind, monadLift_self]
      rw [probEvent_bind_eq_tsum]
      -- Bound each continuation by the inductive hypothesis, then bound the step sum.
      have hstep_le :
          ∑' p, Pr[= p |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run s] *
            Pr[fun z => z.2.responses t₀ = some v₀ |
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                (oa p.1)).run p.2] ≤
            ∑' p, Pr[= p |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run s] *
              stbound p.2 := by
        refine ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl (ih p.1 p.2)
      refine le_trans hstep_le ?_
      -- Three cases on the value held at `t₀` in the pre-state `s`.
      by_cases hsv : s.responses t₀ = some v₀
      · -- `t₀` already holds `v₀`: `stbound s = 1`; LEMMA 1 keeps it so, sum `≤ 1`.
        have hpres :=
          authRFQueryImpl_responses_some_preservesInv (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) t₀ v₀ t s hsv
        have hbound : ∀ p ∈ support
            ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run s),
            stbound p.2 = 1 := by
          intro p hp
          simp only [hstbound, hpres p hp, if_true]
        calc ∑' p, Pr[= p |
                (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run s] *
              stbound p.2
            = ∑' p, Pr[= p |
                (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run s] *
                1 := by
              refine tsum_congr fun p => ?_
              by_cases hp : p ∈ support
                  ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                    t).run s)
              · rw [hbound p hp]
              · rw [probOutput_eq_zero_of_not_mem_support hp]; simp
          _ ≤ 1 := by simp only [mul_one]; exact tsum_probOutput_le_one
          _ = stbound s := by simp only [hstbound, hsv, if_true]
      · by_cases hsn : s.responses t₀ = none
        · -- `t₀` is unfilled: `stbound s = maxDigestProb`; this is the core per-step bound.
          have hsplit : ∀ p : (AuthOracleSpec TagId Nonce Digest).Range t ×
              AuthIdealState TagId Nonce Digest, stbound p.2 ≤
              (if p.2.responses t₀ = some v₀ then (1 : ℝ≥0∞) else 0) +
                maxDigestProb * (if p.2.responses t₀ = none then (1 : ℝ≥0∞) else 0) := by
            intro p
            simp only [hstbound]
            by_cases h1 : p.2.responses t₀ = some v₀
            · simp [h1]
            · by_cases h2 : p.2.responses t₀ = none
              · simp [h2]
              · simp [h1, h2]
          have hsum_le :
              ∑' p, Pr[= p |
                  (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                    t).run s] * stbound p.2 ≤
                ∑' p, Pr[= p |
                  (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                    t).run s] *
                  ((if p.2.responses t₀ = some v₀ then (1 : ℝ≥0∞) else 0) +
                    maxDigestProb * (if p.2.responses t₀ = none then (1 : ℝ≥0∞) else 0)) :=
            ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl (hsplit p)
          refine le_trans hsum_le ?_
          -- Distribute the sum into the two probability events.
          have hdist :
              ∑' p, Pr[= p |
                  (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                    t).run s] *
                  ((if p.2.responses t₀ = some v₀ then (1 : ℝ≥0∞) else 0) +
                    maxDigestProb * (if p.2.responses t₀ = none then (1 : ℝ≥0∞) else 0)) =
                Pr[fun p => p.2.responses t₀ = some v₀ |
                    (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                      t).run s] +
                  maxDigestProb *
                    Pr[fun p => p.2.responses t₀ = none |
                      (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                        t).run s] := by
            rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite,
              ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
            refine tsum_congr fun p => ?_
            by_cases h1 : p.2.responses t₀ = some v₀ <;>
              by_cases h2 : p.2.responses t₀ = none <;>
              simp [h1, h2, mul_comm]
          rw [hdist]
          have hcore :=
            probEvent_authRFQueryImpl_step_core (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) maxDigestProb hmax t₀ v₀ t s hsn
          have hgoal : stbound s = maxDigestProb := by
            simp only [hstbound, hsn]
            simp
          rw [hgoal]
          exact hcore
        · -- `t₀` holds some `d ≠ v₀`: `stbound s = 0`; LEMMA 1 keeps `t₀ ↦ d`, sum `= 0`.
          obtain ⟨d, hd⟩ : ∃ d, s.responses t₀ = some d := by
            cases hc : s.responses t₀ with
            | none => exact absurd hc hsn
            | some d => exact ⟨d, rfl⟩
          have hpres :=
            authRFQueryImpl_responses_some_preservesInv (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) t₀ d t s hd
          have hzero : ∀ p ∈ support
              ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                t).run s), stbound p.2 = 0 := by
            intro p hp
            have hpd := hpres p hp
            have hdv : d ≠ v₀ := by
              rintro rfl
              exact hsv hd
            have hne : p.2.responses t₀ ≠ some v₀ := by
              rw [hpd]
              simp [hdv]
            simp only [hstbound, hpd]
            simp [hdv]
          have hsum0 :
              ∑' p, Pr[= p |
                  (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                    t).run s] * stbound p.2 = 0 := by
            refine ENNReal.tsum_eq_zero.mpr fun p => ?_
            by_cases hp : p ∈ support
                ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run s)
            · rw [hzero p hp, mul_zero]
            · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul]
          rw [hsum0]
          exact zero_le _
  have hfinal : stbound st = maxDigestProb := by
    simp only [hstbound, hnone]
    simp
  exact (hgen adversary st).trans (le_of_eq hfinal)

/-- The reader's per-tag lookup pass: run `authRFLookup` at `nonce` for every tag in `tags`,
collecting each looked-up `(tag, digest)` pair. This is the `responses`-touching core of
`authRFReaderQueryImpl`, isolated so that the collision argument can reason about it directly. -/
private noncomputable def authRFReaderLookups
    (nonce : Nonce) (tags : List TagId) :
    StateT (AuthIdealState TagId Nonce Digest) ProbComp (List (TagId × Digest)) :=
  tags.mapM (fun tag => do
    let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce
    pure (tag, dg))

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- Every looked-up pair produced by `authRFReaderLookups` lands in the final cache: if `(tag, d)`
occurs in the result list, the final `responses` table holds `(tag, nonce) ↦ d`. Each lookup pins
its own point, and the tail `mapM` preserves it. -/
private lemma authRFLookup_mapM_pairs_responses
    (nonce : Nonce) (tags : List TagId) (st : AuthIdealState TagId Nonce Digest) :
    ∀ z ∈ support ((authRFReaderLookups (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        nonce tags).run st),
      ∀ p ∈ z.1, z.2.responses (p.1, nonce) = some p.2 := by
  unfold authRFReaderLookups
  induction tags generalizing st with
  | nil =>
    intro z hz
    simp only [List.mapM_nil, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    intro p hp
    simp at hp
  | cons hd tl ih =>
    intro z hz
    rw [List.mapM_cons] at hz
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_map, support_bind, support_map,
      Set.mem_iUnion, Set.mem_image] at hz
    obtain ⟨r, ⟨lk, hlk, rfl⟩, w, hw, rfl⟩ := hz
    -- The head lookup at `hd` pins `(hd, nonce) ↦ lk.1` in `lk.2`.
    have hlook : lk.2.responses (hd, nonce) = some lk.1 := by
      unfold authRFLookup at hlk
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hlk
      cases hresp : st.responses (hd, nonce) with
      | some out =>
        simp only [hresp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hlk
        rcases hlk with rfl
        exact hresp
      | none =>
        simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
          bind_pure_comp, StateT.run_map, StateT.run_set, support_bind, support_uniformSample,
          Set.mem_univ, Set.mem_iUnion, support_map, Set.mem_image, support_pure,
          Set.mem_singleton_iff] at hlk
        obtain ⟨i, -, x, rfl, rfl⟩ := hlk
        exact QueryCache.cacheQuery_self _ _ _
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp'
    · -- `p` is the head pair `(hd, lk.1)`: the tail `mapM` keeps `(hd, nonce)` pinned.
      exact authRFLookup_mapM_responses_some_preservesInv (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (hd, nonce) lk.1 nonce tl lk.2 hlook w hw
    · -- `p` is in the tail pairs: apply the induction hypothesis.
      exact ih lk.2 w hw p hp'

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- `authRFReaderLookups` only writes the `responses` table: the observable logs `honestOutputs`
and `readerForged` are untouched by every reachable outcome. -/
private lemma authRFLookup_mapM_logs_eq
    (nonce : Nonce) (tags : List TagId) (st : AuthIdealState TagId Nonce Digest) :
    ∀ z ∈ support ((authRFReaderLookups (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        nonce tags).run st),
      z.2.honestOutputs = st.honestOutputs ∧ z.2.readerForged = st.readerForged := by
  unfold authRFReaderLookups
  induction tags generalizing st with
  | nil =>
    intro z hz
    simp only [List.mapM_nil, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    exact ⟨rfl, rfl⟩
  | cons hd tl ih =>
    intro z hz
    rw [List.mapM_cons] at hz
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_map, support_bind, support_map,
      Set.mem_iUnion, Set.mem_image] at hz
    obtain ⟨r, ⟨lk, hlk, rfl⟩, w, hw, rfl⟩ := hz
    have hhead : lk.2.honestOutputs = st.honestOutputs ∧ lk.2.readerForged = st.readerForged := by
      unfold authRFLookup at hlk
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hlk
      cases hresp : st.responses (hd, nonce) with
      | some out =>
        simp only [hresp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hlk
        rcases hlk with rfl
        exact ⟨rfl, rfl⟩
      | none =>
        simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
          bind_pure_comp, StateT.run_map, StateT.run_set, support_bind, support_uniformSample,
          Set.mem_univ, Set.mem_iUnion, support_map, Set.mem_image, support_pure,
          Set.mem_singleton_iff] at hlk
        obtain ⟨i, -, x, rfl, rfl⟩ := hlk
        exact ⟨rfl, rfl⟩
    obtain ⟨htail₁, htail₂⟩ := ih lk.2 w hw
    exact ⟨htail₁.trans hhead.1, htail₂.trans hhead.2⟩

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Per-reader-step collision bound. When the pre-state has no recorded forgeries and every cached
cell in the queried nonce's column belongs to `honestOutputs`, one `authRFReaderQueryImpl` step
records a forgery with probability at most `|TagId| * maxDigestProb`.

A reader step makes one fresh random-oracle draw per tag at the transcript's nonce. A cached cell
in that column cannot become a forgery: a match against `transcript.auth` would place
`(tag, transcript)` inside `honestOutputs`, which forgeries exclude. An uncached cell can match the
adversary-chosen authenticator with probability at most `maxDigestProb`. -/
private lemma authRFReaderStep_forge_le
    (transcript : TagTranscript Nonce Digest)
    (st : AuthIdealState TagId Nonce Digest)
    (maxDigestProb : ℝ≥0∞)
    (hmax : ∀ v : Digest, Pr[= v | ($ᵗ Digest : ProbComp Digest)] ≤ maxDigestProb)
    (hforged : st.readerForged = ∅)
    (hcol : ∀ tag : TagId, ∀ d : Digest,
      st.responses (tag, transcript.nonce) = some d →
        (tag, ⟨transcript.nonce, d⟩) ∈ st.honestOutputs) :
    Pr[fun z => z.2.readerForged ≠ ∅ |
        (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          transcript).run st] ≤
      (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
  classical
  -- Abbreviate the per-tag lookup pass and the forged-tag set extracted from its result.
  set lookups := (authRFReaderLookups (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    transcript.nonce (Finset.univ : Finset TagId).toList).run st with hlookups
  set newForged : List (TagId × Digest) → Finset TagId := fun pairs =>
    ((pairs.filter fun p => decide (p.2 = transcript.auth ∧
      (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset with hnewForged
  -- The reader run is the lookup pass followed by a pure log update; push the event through.
  have hmap :
      Pr[fun z => z.2.readerForged ≠ ∅ |
          (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            transcript).run st] =
        Pr[fun mp : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
            (mp.2.readerForged ∪
              (((mp.1.filter fun p => decide (p.2 = transcript.auth ∧
                (p.1, transcript) ∉ mp.2.honestOutputs)).map Prod.fst).toFinset.image
                  (·, transcript))) ≠ ∅ | lookups] := by
    rw [hlookups]
    unfold authRFReaderQueryImpl authRFReaderLookups
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_map,
      StateT.run_set, map_pure]
    rw [probEvent_map]
    rfl
  rw [hmap]
  -- Forge ⇒ some tag lies in `newForged`, which forces a cached-or-fresh match at its column.
  have hstep :
      Pr[fun mp : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
          (mp.2.readerForged ∪
            (((mp.1.filter fun p => decide (p.2 = transcript.auth ∧
              (p.1, transcript) ∉ mp.2.honestOutputs)).map Prod.fst).toFinset.image
                (·, transcript))) ≠ ∅ | lookups] ≤
        Pr[fun mp => ∃ tag ∈ (Finset.univ : Finset TagId), tag ∈ newForged mp.1 | lookups] := by
    refine probEvent_mono fun mp hmp hne => ?_
    obtain ⟨hho, hrf⟩ := authRFLookup_mapM_logs_eq (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) transcript.nonce (Finset.univ : Finset TagId).toList st mp hmp
    rw [hho, hrf, hforged, Finset.empty_union] at hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨tag, htag, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨tag, Finset.mem_univ tag, htag⟩
  refine le_trans hstep ?_
  refine le_trans (probEvent_exists_finset_le_sum (Finset.univ : Finset TagId) lookups
    (fun tag mp => tag ∈ newForged mp.1)) ?_
  -- Per-tag: cached cells cannot forge; uncached cells match with probability ≤ maxDigestProb.
  have hper : ∀ tag : TagId,
      Pr[fun mp => tag ∈ newForged mp.1 | lookups] ≤ maxDigestProb := by
    intro tag
    by_cases hcached : ∃ d, st.responses (tag, transcript.nonce) = some d
    · -- Cached column cell: a match would land in `honestOutputs`, so it is never forged.
      obtain ⟨d, hd⟩ := hcached
      refine le_trans (le_of_eq ?_) (zero_le _)
      rw [probEvent_eq_zero_iff]
      intro mp hmp hmem
      simp only [hnewForged, List.mem_toFinset, List.mem_map, List.mem_filter,
        decide_eq_true_eq] at hmem
      obtain ⟨p, ⟨hpmem, hpauth, hpnh⟩, rfl⟩ := hmem
      have hpresp := authRFLookup_mapM_pairs_responses (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) transcript.nonce (Finset.univ : Finset TagId).toList st mp hmp p hpmem
      -- The cached cell keeps its digest `d`; a forgery would need `p.2 = d = transcript.auth`.
      have hcell : st.responses (p.1, transcript.nonce) = some d := hd
      have hpd : mp.2.responses (p.1, transcript.nonce) = some d :=
        authRFLookup_mapM_responses_some_preservesInv (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (p.1, transcript.nonce) d transcript.nonce
          (Finset.univ : Finset TagId).toList st hcell mp hmp
      have hpd' : p.2 = d := (Option.some.injEq _ _).mp (hpresp.symm.trans hpd)
      have hhonest : (p.1, transcript) ∈ st.honestOutputs := by
        have h := hcol p.1 d hcell
        rw [← hpd', hpauth, show (⟨transcript.nonce, transcript.auth⟩ :
          TagTranscript Nonce Digest) = transcript from rfl] at h
        exact h
      exact hpnh hhonest
    · -- Uncached column cell: bounded by the single-step random-oracle bound.
      simp only [not_exists] at hcached
      have hnone : st.responses (tag, transcript.nonce) = none := by
        cases hc : st.responses (tag, transcript.nonce) with
        | none => rfl
        | some d => exact absurd hc (hcached d)
      have hstepcore := probEvent_authRFQueryImpl_step_core (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) maxDigestProb hmax (tag, transcript.nonce) transcript.auth
        (Sum.inr transcript) st hnone
      have hreaderResp :
          Pr[fun mp : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
              mp.2.responses (tag, transcript.nonce) = some transcript.auth | lookups] ≤
            maxDigestProb := by
        have hrun : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (Sum.inr transcript)).run st =
            (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              transcript).run st := rfl
        have hpush :
            Pr[fun p => p.2.responses (tag, transcript.nonce) = some transcript.auth |
                (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  transcript).run st] =
              Pr[fun mp : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
                mp.2.responses (tag, transcript.nonce) = some transcript.auth | lookups] := by
          rw [hlookups]
          unfold authRFReaderQueryImpl authRFReaderLookups
          simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_map,
            StateT.run_set, map_pure]
          rw [probEvent_map]
          rfl
        rw [← hpush, ← hrun]
        exact le_trans (le_add_right le_rfl) hstepcore
      refine le_trans (probEvent_mono fun mp hmp hmem => ?_) hreaderResp
      simp only [hnewForged, List.mem_toFinset, List.mem_map, List.mem_filter,
        decide_eq_true_eq] at hmem
      obtain ⟨p, ⟨hpmem, hpauth, _⟩, rfl⟩ := hmem
      have hpresp := authRFLookup_mapM_pairs_responses (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) transcript.nonce (Finset.univ : Finset TagId).toList st mp hmp p hpmem
      rw [hpresp, hpauth]
  exact le_trans (Finset.sum_le_sum fun tag _ => hper tag)
    (le_of_eq (by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]))

/-- Per-nonce reader-query predicate on the authentication oracle interface. `pNonce n` holds of a
reader query exactly when its transcript carries the nonce `n`, and never holds of a tag query.
Bounding the number of `pNonce n`-queries by `1` for every `n` expresses that the adversary's
reader queries use pairwise-distinct nonces. -/
def pNonce (n : Nonce) : (AuthOracleSpec TagId Nonce Digest).Domain → Prop :=
  fun i => match i with
    | Sum.inr tr => tr.nonce = n
    | Sum.inl _ => False

instance pNonceDecidable (n : Nonce) :
    DecidablePred (pNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n) := by
  intro i
  cases i with
  | inr tr => exact (inferInstance : Decidable (tr.nonce = n))
  | inl _ => exact (inferInstance : Decidable False)

/-- The adversary's reader queries use pairwise-distinct nonces: every nonce `n` is carried by at
most one reader query. This is the public hypothesis under which the random-function collision
bound is fully proven (`authRFExp_le_collisionBound_of_distinctReaderNonces` and its uniform
specialization); it rules out the shared-cache obstruction that keeps the unrestricted
`authRFExp_le_collisionBound_conjecture` open. -/
def HasDistinctReaderNonces (adversary : AuthAdversary TagId Nonce Digest) : Prop :=
  ∀ n : Nonce, OracleComp.IsQueryBoundP adversary (pNonce n) 1

/-- `HasDistinctReaderNonces` unfolds definitionally to a per-nonce reader-query bound: it holds
exactly when, for every nonce `n`, at most one reader query carries `n`. Use this lemma to
discharge the hypothesis from a per-nonce `IsQueryBoundP` family, or to peel it back when a proof
needs the underlying bound directly. -/
lemma hasDistinctReaderNonces_iff (adversary : AuthAdversary TagId Nonce Digest) :
    HasDistinctReaderNonces adversary ↔
      ∀ n : Nonce, OracleComp.IsQueryBoundP adversary (pNonce n) 1 :=
  Iff.rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Every `pNonce n`-query is a reader query: `pNonce n` is false on tag (`Sum.inl`) queries and,
on reader (`Sum.inr`) queries, refines `Sum.isRight`. -/
lemma pNonce_imp_isRight (n : Nonce) (t : (AuthOracleSpec TagId Nonce Digest).Domain) :
    pNonce (TagId := TagId) (Digest := Digest) n t → t.isRight := by
  cases t with
  | inl x => exact fun h => (h : (False : Prop)).elim
  | inr tr => exact fun _ => rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Intro lemma: an adversary making at most one reader query has pairwise-distinct reader nonces.
A single reader query cannot collide with itself, so the per-nonce bound holds for free; this is
the common case where no bespoke distinctness argument is needed. Adversaries with no reader
queries also qualify — feed `hq.mono (Nat.zero_le 1)`. -/
theorem hasDistinctReaderNonces_of_readerBound
    (adversary : AuthAdversary TagId Nonce Digest)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) 1) :
    HasDistinctReaderNonces adversary := fun n =>
  OracleComp.IsQueryBoundP.of_imp (pNonce_imp_isRight n) hq

/-- Coupled invariant carried by the random-function collision induction. A state `st` satisfies
`forgeInv adversary st` when no forgery has been recorded yet and every cached cell at column
`nonce` is either an honest tag output or sits in a column the residual adversary will never query
again (`IsQueryBoundP adversary (pNonce nonce) 0`). Under pairwise-distinct reader nonces, the
second disjunct fails exactly at the column of the next reader query, so all of that column's
cached cells are honest — the hypothesis needed for the per-step bound. -/
private def forgeInv (adversary : AuthAdversary TagId Nonce Digest)
    (st : AuthIdealState TagId Nonce Digest) : Prop :=
  st.readerForged = ∅ ∧
    ∀ (tag : TagId) (nonce : Nonce) (d : Digest), st.responses (tag, nonce) = some d →
      ((tag, (⟨nonce, d⟩ : TagTranscript Nonce Digest)) ∈ st.honestOutputs ∨
        OracleComp.IsQueryBoundP adversary (pNonce nonce) 0)

omit [Fintype TagId] [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Column-indexed cell invariant of the random-function tag oracle. With a fixed per-column
predicate `Q`, a tag step preserves both an empty forgery log and the property that every cached
cell is honest or sits in a `Q`-column: a freshly cached cell is the honest transcript just
emitted, and every pre-existing cell keeps its disjunct under cache growth. -/
private lemma authIdealTagStep_cell_inv
    (tag : TagId) (st : AuthIdealState TagId Nonce Digest)
    (Q : Nonce → Prop)
    (hread : st.readerForged = ∅)
    (hcell : ∀ (t' : TagId) (n : Nonce) (d : Digest),
      st.responses (t', n) = some d →
        ((t', (⟨n, d⟩ : TagTranscript Nonce Digest)) ∈ st.honestOutputs ∨ Q n)) :
    ∀ z ∈ support ((authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) tag).run st),
      z.2.readerForged = ∅ ∧
        ∀ (t' : TagId) (n : Nonce) (d : Digest), z.2.responses (t', n) = some d →
          ((t', (⟨n, d⟩ : TagTranscript Nonce Digest)) ∈ z.2.honestOutputs ∨ Q n) := by
  intro z hz
  unfold authIdealTagQueryImpl at hz
  simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
    monadLift_eq_self, bind_map_left, support_bind, support_uniformSample, Set.mem_univ,
    Set.iUnion_true, Set.mem_iUnion] at hz
  rcases hz with ⟨nonce, hz⟩
  cases hresp : st.responses (tag, nonce) with
  | none =>
    simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
      StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map,
      support_uniformSample, Set.image_univ, Set.mem_range] at hz
    obtain ⟨auth, rfl⟩ := hz
    refine ⟨hread, ?_⟩
    intro t' n d hlookup
    by_cases hkey : (t', n) = (tag, nonce)
    · -- The freshly cached cell is the honest transcript just emitted.
      cases hkey
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hlookup
      subst hlookup
      exact Or.inl (Finset.mem_insert_self _ _)
    · -- A pre-existing cell keeps its disjunct; honest membership survives the `insert`.
      have hlookup' : st.responses (t', n) = some d := by
        simpa [QueryCache.cacheQuery_of_ne (cache := st.responses) auth hkey] using hlookup
      rcases hcell t' n d hlookup' with hh | hq
      · exact Or.inl (Finset.mem_insert_of_mem hh)
      · exact Or.inr hq
  | some out =>
    simp only [hresp, StateT.run_map, StateT.run_set, map_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl
    refine ⟨hread, ?_⟩
    intro t' n d hlookup
    rcases hcell t' n d hlookup with hh | hq
    · exact Or.inl (Finset.mem_insert_of_mem hh)
    · exact Or.inr hq

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- `authRFReaderLookups` at column `nm` never disturbs cells outside that column: any cached cell
at a nonce `n ≠ nm` keeps its pre-step value in every reachable outcome. -/
private lemma authRFLookup_mapM_responses_eq_of_ne_column
    (nm : Nonce) (tags : List TagId) (t' : TagId) (n : Nonce) (hne : n ≠ nm)
    (st : AuthIdealState TagId Nonce Digest) :
    ∀ z ∈ support ((authRFReaderLookups (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        nm tags).run st),
      z.2.responses (t', n) = st.responses (t', n) := by
  unfold authRFReaderLookups
  induction tags generalizing st with
  | nil =>
    intro z hz
    simp only [List.mapM_nil, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    rfl
  | cons hd tl ih =>
    intro z hz
    rw [List.mapM_cons] at hz
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_map, support_bind, support_map,
      Set.mem_iUnion, Set.mem_image] at hz
    obtain ⟨r, ⟨lk, hlk, rfl⟩, w, hw, rfl⟩ := hz
    have hhead : lk.2.responses (t', n) = st.responses (t', n) := by
      unfold authRFLookup at hlk
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hlk
      cases hresp : st.responses (hd, nm) with
      | some out =>
        simp only [hresp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hlk
        rcases hlk with rfl
        rfl
      | none =>
        simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
          bind_pure_comp, StateT.run_map, StateT.run_set, support_bind, support_uniformSample,
          Set.mem_univ, Set.mem_iUnion, support_map, Set.mem_image, support_pure,
          Set.mem_singleton_iff] at hlk
        obtain ⟨i, -, x, rfl, rfl⟩ := hlk
        change (st.responses.cacheQuery (hd, nm) i.1) (t', n) = st.responses (t', n)
        rw [QueryCache.cacheQuery_of_ne _ _ (fun h => hne (congrArg Prod.snd h))]
    rw [ih lk.2 w hw, hhead]

omit [Nonempty TagId] [SampleableType Nonce] [NeZero sessionsPerTag] in
/-- A reader step at nonce `nm` only adds cells in column `nm`: every reachable outcome leaves the
honest-tag log unchanged, and every cached cell outside column `nm` keeps its pre-step value. -/
private lemma authRFReaderStep_state
    (transcript : TagTranscript Nonce Digest)
    (st : AuthIdealState TagId Nonce Digest) :
    ∀ z ∈ support ((authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        transcript).run st),
      z.2.honestOutputs = st.honestOutputs ∧
        ∀ (t' : TagId) (n : Nonce) (d : Digest), n ≠ transcript.nonce →
          z.2.responses (t', n) = some d → st.responses (t', n) = some d := by
  intro z hz
  -- The reader run is the lookup pass followed by a pure log update.
  have hz' := hz
  unfold authRFReaderQueryImpl at hz'
  simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_map,
    StateT.run_set, map_pure, support_map, Set.mem_image] at hz'
  obtain ⟨mp, hmp, rfl⟩ := hz'
  have hmp' : mp ∈ support ((authRFReaderLookups (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) transcript.nonce (Finset.univ : Finset TagId).toList).run st) := by
    unfold authRFReaderLookups
    exact hmp
  obtain ⟨hho, _⟩ := authRFLookup_mapM_logs_eq (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) transcript.nonce (Finset.univ : Finset TagId).toList st mp hmp'
  refine ⟨hho, ?_⟩
  intro t' n d hncol hcell
  have hcol := authRFLookup_mapM_responses_eq_of_ne_column (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) transcript.nonce (Finset.univ : Finset TagId).toList t' n hncol st mp hmp'
  rw [← hcol]
  exact hcell

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Inductive collision bound for the random-function world under pairwise-distinct reader nonces.
For an adversary making at most `q` reader queries, all on distinct nonces, the probability that a
forgery is recorded while running it against `authRFQueryImpl` from a `forgeInv`-state is at most
`q * |TagId| * maxDigestProb`.

The induction follows the adversary's query structure. A tag query touches no forgery state and
preserves the invariant. A reader query consumes one unit of the `q` budget: the step itself
records a forgery with probability at most `|TagId| * maxDigestProb` (`authRFReaderStep_forge_le`,
whose column-honesty hypothesis is supplied by `forgeInv` together with distinctness), and the
residual adversary contributes at most `(q - 1) * |TagId| * maxDigestProb`. -/
private lemma simulateQ_authRF_forge_le
    (adversary : AuthAdversary TagId Nonce Digest)
    (maxDigestProb : ℝ≥0∞)
    (hmax : ∀ v : Digest, Pr[= v | ($ᵗ Digest : ProbComp Digest)] ≤ maxDigestProb)
    (q : ℕ)
    (st : AuthIdealState TagId Nonce Digest)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (hdistinct : ∀ n : Nonce, OracleComp.IsQueryBoundP adversary (pNonce n) 1)
    (hinv : forgeInv adversary st) :
    Pr[fun z => z.2.readerForged ≠ ∅ |
        (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          adversary).run st] ≤
      (q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
  classical
  induction adversary using OracleComp.inductionOn generalizing st q with
  | pure x =>
    -- No queries: the forgery log is still empty.
    simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, hinv.1, ne_eq, not_true_eq_false,
      ite_false]
    exact zero_le _
  | query_bind t oa ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind, monadLift_self]
    cases t with
    | inl tag =>
      -- A tag query: the budgets pass unchanged, and `forgeInv` is preserved.
      have hstepRun : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (Sum.inl tag)) = authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) tag := rfl
      rw [probEvent_bind_eq_tsum]
      have hcont : ∀ p ∈ support
          ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (Sum.inl tag)).run st),
          Pr[fun z => z.2.readerForged ≠ ∅ |
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                (oa p.1)).run p.2] ≤
            (q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
        intro p hp
        -- Budgets for the continuation: a tag query satisfies neither predicate.
        have hqcont : OracleComp.IsQueryBoundP (oa p.1) (fun i => i.isRight) q := by
          have := (isQueryBoundP_query_bind_iff (p := fun i => i.isRight) (Sum.inl tag) oa q).mp hq
          simpa using this.2 p.1
        have hdcont : ∀ n : Nonce, OracleComp.IsQueryBoundP (oa p.1) (pNonce n) 1 := by
          intro n
          have := (isQueryBoundP_query_bind_iff (p := pNonce n) (Sum.inl tag) oa 1).mp (hdistinct n)
          have hfalse : ¬ pNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n
              (Sum.inl tag) := id
          simpa [hfalse] using this.2 p.1
        -- `forgeInv` for the continuation: the cell budget disjunct passes to `oa p.1`.
        have hinvcont : forgeInv (oa p.1) p.2 := by
          have hcellQ : ∀ (t' : TagId) (n : Nonce) (d : Digest),
              st.responses (t', n) = some d →
                ((t', (⟨n, d⟩ : TagTranscript Nonce Digest)) ∈ st.honestOutputs ∨
                  OracleComp.IsQueryBoundP (oa p.1) (pNonce n) 0) := by
            intro t' n d hcell
            rcases hinv.2 t' n d hcell with hh | hb
            · exact Or.inl hh
            · refine Or.inr ?_
              have := (isQueryBoundP_query_bind_iff (p := pNonce n) (Sum.inl tag) oa 0).mp hb
              have hfalse : ¬ pNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n
                  (Sum.inl tag) := id
              simpa [hfalse] using this.2 p.1
          have hpres := authIdealTagStep_cell_inv (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) tag st (fun n => OracleComp.IsQueryBoundP (oa p.1) (pNonce n) 0)
            hinv.1 hcellQ p (by rwa [hstepRun] at hp)
          exact ⟨hpres.1, hpres.2⟩
        exact ih p.1 q p.2 hqcont hdcont hinvcont
      calc ∑' p, Pr[= p |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (Sum.inl tag)).run st] *
            Pr[fun z => z.2.readerForged ≠ ∅ |
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                (oa p.1)).run p.2]
          ≤ ∑' p, Pr[= p |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (Sum.inl tag)).run st] *
              ((q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb) := by
            refine ENNReal.tsum_le_tsum fun p => ?_
            by_cases hp : p ∈ support
                ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (Sum.inl tag)).run st)
            · exact mul_le_mul' le_rfl (hcont p hp)
            · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]
        _ = (∑' p, Pr[= p |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (Sum.inl tag)).run st]) *
              ((q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb) := by
            rw [ENNReal.tsum_mul_right]
        _ ≤ (q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
            exact le_trans (mul_le_mul' tsum_probOutput_le_one le_rfl) (le_of_eq (one_mul _))
    | inr transcript =>
      -- A reader query: consumes one budget unit. `0 < q` from the reader-query bound.
      have hqsplit := (isQueryBoundP_query_bind_iff (p := fun i => i.isRight)
        (Sum.inr transcript) oa q).mp hq
      have hqpos : 0 < q := by
        have : ¬ ¬ (Sum.inr transcript :
            (AuthOracleSpec TagId Nonce Digest).Domain).isRight = true := by simp
        rcases hqsplit.1 with h | h
        · exact absurd h this
        · exact h
      set nm := transcript.nonce with hnm
      have hdsplit := (isQueryBoundP_query_bind_iff (p := pNonce nm)
        (Sum.inr transcript) oa 1).mp (hdistinct nm)
      have hpNm : pNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) nm
          (Sum.inr transcript) := by simp [pNonce, hnm]
      -- Every column-`nm` cell is honest: the budget disjunct fails for a `pNonce nm`-query.
      have hcol : ∀ tag : TagId, ∀ d : Digest,
          st.responses (tag, transcript.nonce) = some d →
            (tag, (⟨transcript.nonce, d⟩ : TagTranscript Nonce Digest)) ∈ st.honestOutputs := by
        intro tag d hcell
        rcases hinv.2 tag transcript.nonce d hcell with hh | hb
        · exact hh
        · exfalso
          have := (isQueryBoundP_query_bind_iff (p := pNonce transcript.nonce)
            (Sum.inr transcript) oa 0).mp hb
          rcases this.1 with h | h
          · exact h hpNm
          · exact absurd h (lt_irrefl 0)
      -- The per-step forge bound from `authRFReaderStep_forge_le`.
      have hstepRun : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (Sum.inr transcript)).run st =
          (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            transcript).run st := rfl
      have hstepForge :
          Pr[fun z => ¬ z.2.readerForged = ∅ |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (Sum.inr transcript)).run st] ≤
            (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
        rw [hstepRun]
        exact authRFReaderStep_forge_le (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          transcript st maxDigestProb hmax hinv.1 hcol
      -- The continuation bound from the induction hypothesis.
      have hcont : ∀ p ∈ support
          ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (Sum.inr transcript)).run st),
          p.2.readerForged = ∅ →
          Pr[fun z => ¬ z.2.readerForged = ∅ |
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                (oa p.1)).run p.2] ≤
            ((q - 1 : ℕ) : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
        intro p hp hpforged
        -- Budgets for the continuation.
        have hqcont : OracleComp.IsQueryBoundP (oa p.1) (fun i => i.isRight) (q - 1) := by
          have := hqsplit.2 p.1
          simpa using this
        have hdcont : ∀ n : Nonce, OracleComp.IsQueryBoundP (oa p.1) (pNonce n) 1 := by
          intro n
          by_cases hnn : n = nm
          · subst hnn
            have := hdsplit.2 p.1
            rw [if_pos hpNm] at this
            exact this.mono (Nat.zero_le 1)
          · have hsplitn := (isQueryBoundP_query_bind_iff (p := pNonce n)
              (Sum.inr transcript) oa 1).mp (hdistinct n)
            have hfalse : ¬ pNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n
                (Sum.inr transcript) := by
              change ¬ transcript.nonce = n
              rw [← hnm]
              exact fun h => hnn h.symm
            have := hsplitn.2 p.1
            rwa [if_neg hfalse] at this
        -- `forgeInv` for the continuation.
        have hinvcont : forgeInv (oa p.1) p.2 := by
          refine ⟨hpforged, ?_⟩
          intro t' n d hcell
          have hreaderState := authRFReaderStep_state (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) transcript st p (by rwa [hstepRun] at hp)
          by_cases hnn : n = nm
          · -- Column-`nm` cell: the budget disjunct holds for the continuation.
            refine Or.inr ?_
            subst hnn
            have := hdsplit.2 p.1
            rwa [if_pos hpNm] at this
          · -- Cell outside column `nm`: carried over from `st`.
            have hcellst : st.responses (t', n) = some d :=
              hreaderState.2 t' n d hnn hcell
            rcases hinv.2 t' n d hcellst with hh | hb
            · refine Or.inl ?_
              rw [hreaderState.1]
              exact hh
            · refine Or.inr ?_
              have hfalse : ¬ pNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n
                  (Sum.inr transcript) := by
                change ¬ transcript.nonce = n
                rw [← hnm]
                exact fun h => hnn h.symm
              have := (isQueryBoundP_query_bind_iff (p := pNonce n)
                (Sum.inr transcript) oa 0).mp hb
              have := this.2 p.1
              rwa [if_neg hfalse] at this
        exact ih p.1 (q - 1) p.2 hqcont hdcont hinvcont
      -- Combine the step bound and the continuation bound.
      have hcombine := probEvent_bind_le_add
        (mx := (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (Sum.inr transcript)).run st)
        (my := fun p => (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest)) (oa p.1)).run p.2)
        (p := fun z => z.2.readerForged = ∅)
        (q := fun y => y.2.readerForged = ∅)
        (ε₁ := (Fintype.card TagId : ℝ≥0∞) * maxDigestProb)
        (ε₂ := ((q - 1 : ℕ) : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb)
        hstepForge hcont
      calc Pr[fun z => z.2.readerForged ≠ ∅ |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (Sum.inr transcript)).run st >>= fun p =>
                (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest)) (oa p.1)).run p.2]
          ≤ (Fintype.card TagId : ℝ≥0∞) * maxDigestProb +
              ((q - 1 : ℕ) : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := hcombine
        _ = (q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
            have hqcast : (1 : ℝ≥0∞) + ((q - 1 : ℕ) : ℝ≥0∞) = (q : ℝ≥0∞) := by
              have : 1 + (q - 1) = q := Nat.add_sub_cancel' (Nat.succ_le_iff.mpr hqpos)
              exact_mod_cast this
            have hc : (Fintype.card TagId : ℝ≥0∞) * maxDigestProb +
                ((q - 1 : ℕ) : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb =
                (1 + ((q - 1 : ℕ) : ℝ≥0∞)) * ((Fintype.card TagId : ℝ≥0∞) * maxDigestProb) := by
              rw [add_mul, one_mul, mul_assoc]
            rw [hc, hqcast, mul_assoc]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Collision bound for the random-function authentication world: the probability that the
random-function reader records a forged acceptance is bounded by the number of reader queries the
adversary may make, times `|TagId|`, times the per-digest sampling probability `maxDigestProb`.

A forged acceptance can only arise from a *fresh* random-oracle draw: if the reader's query at
`(tag, transcript.nonce)` is already cached, the cached digest was produced by an honest tag
output, so a match against `transcript.auth` lands inside `honestOutputs` and is never recorded as
forged. Each fresh draw is a uniform `Digest`, matching the adversary-chosen `transcript.auth` with
probability at most `maxDigestProb`; every reader query triggers at most `|TagId|` fresh draws. -/
theorem authRFExp_le_collisionBound_conjecture
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (maxDigestProb : ℝ)
    (hmax : ∀ d : Digest,
      (Pr[= d | ($ᵗ Digest : ProbComp Digest)]).toReal ≤ maxDigestProb) :
    (Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) adversary]).toReal ≤
      ((q * Fintype.card TagId : ℕ) : ℝ) * maxDigestProb := by
  -- Status: open in this generality. The reusable random-oracle infrastructure for this bound
  -- is already proven below the `authRFExp_eq_authRFDirectExp` equivalence:
  --   * `authRFQueryImpl_responses_some_preservesInv` — cache monotonicity (a cached point keeps
  --     its digest), and
  --   * `probEvent_authRFQueryImpl_responses_eq_le` — the single-point random-oracle bound
  --     `Pr[final responses t₀ = some v₀] ≤ maxDigestProb` for a fixed point/target.
  -- The fully proven `authRFExp_le_collisionBound_of_distinctReaderNonces` discharges this bound
  -- whenever the adversary's reader queries use pairwise-distinct nonces.
  --
  -- The remaining obstruction to the unrestricted statement is genuine: the random-function
  -- reader writes the shared lazy cache, so two reader queries on the *same* nonce share
  -- reader-created cache entries. A fresh draw made at one reader query can then be matched by a
  -- later reader query's adversary-chosen `auth`, and the per-reader-step bound
  -- `Pr[step records a forgery] ≤ |TagId| * maxDigestProb` fails for states carrying such
  -- entries. Closing the unrestricted bound needs a random-oracle argument that equality-test
  -- feedback (the reader's accept bit) does not help the adversary predict an uncached digest.
  sorry

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Collision bound for the random-function authentication world, restricted to adversaries whose
reader queries use pairwise-distinct nonces. For such an adversary making at most `q` reader
queries, the probability that the random-function reader records a forged acceptance is at most
`q * |TagId| * maxDigestProb`.

The distinctness hypothesis `HasDistinctReaderNonces adversary` states that every nonce is carried
by at most one reader query. It rules out the shared-cache obstruction of the unrestricted
`authRFExp_le_collisionBound_conjecture`:
because no two reader queries write the same cache column, every cached cell in a reader query's
column was produced by an honest tag output, so the per-reader-step forge probability is genuinely
bounded by `|TagId| * maxDigestProb`. -/
theorem authRFExp_le_collisionBound_of_distinctReaderNonces
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (hdistinct : HasDistinctReaderNonces adversary)
    (maxDigestProb : ℝ)
    (hmax : ∀ d : Digest,
      (Pr[= d | ($ᵗ Digest : ProbComp Digest)]).toReal ≤ maxDigestProb) :
    (Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) adversary]).toReal ≤
      ((q * Fintype.card TagId : ℕ) : ℝ) * maxDigestProb := by
  -- Pass to the directly-defined random-function experiment.
  have hmax_ENNReal : ∀ d : Digest,
      Pr[= d | ($ᵗ Digest : ProbComp Digest)] ≤ ENNReal.ofReal maxDigestProb := by
    intro d
    rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top one_ne_top probOutput_le_one)]
    exact ENNReal.ofReal_le_ofReal (hmax d)
  have hlhs : Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) adversary] =
      Pr[fun z : Unit × AuthIdealState TagId Nonce Digest => z.2.readerForged ≠ ∅ |
        (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          adversary).run AuthIdealState.init] := by
    rw [authRFExp_eq_authRFDirectExp, ← probEvent_eq_eq_probOutput, authRFDirectExp,
      probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    simp
  rw [hlhs]
  -- Apply the inductive collision bound from the initial state.
  have hinit : forgeInv (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary
      AuthIdealState.init := by
    refine ⟨rfl, ?_⟩
    intro tag nonce d hcell
    simp [AuthIdealState.init] at hcell
  have hcore := simulateQ_authRF_forge_le (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    adversary (ENNReal.ofReal maxDigestProb) hmax_ENNReal q AuthIdealState.init hq hdistinct hinit
  -- Convert the `ℝ≥0∞` bound to `ℝ`.
  have hconv : (Pr[fun z : Unit × AuthIdealState TagId Nonce Digest => z.2.readerForged ≠ ∅ |
        (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          adversary).run AuthIdealState.init]).toReal ≤
      ((q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * ENNReal.ofReal maxDigestProb).toReal :=
    ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) hcore
  have hsupp : (support ($ᵗ Digest : ProbComp Digest)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ne_eq, ← probFailure_eq_one_iff]
    simp
  obtain ⟨d0, _⟩ := hsupp
  have hmax_nonneg : 0 ≤ maxDigestProb := ENNReal.toReal_nonneg.trans (hmax d0)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hmax_nonneg] at hconv
  rw [Nat.cast_mul]
  exact hconv

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Uniform-`Digest` specialization of `authRFExp_le_collisionBound_conjecture`: when `Digest` is
finite and sampled uniformly, the per-digest probability is `1 / |Digest|`, so the collision bound
is `qReader * |TagId| / |Digest|`. -/
theorem authRFExp_le_uniformCollisionBound_conjecture [Fintype Digest]
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q) :
    (Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) adversary]).toReal ≤
      ((q * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) := by
  have hmax : ∀ d : Digest,
      (Pr[= d | ($ᵗ Digest : ProbComp Digest)]).toReal ≤ (Fintype.card Digest : ℝ)⁻¹ := fun d => by
    simp [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have h := authRFExp_le_collisionBound_conjecture
    (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    adversary q hq ((Fintype.card Digest : ℝ)⁻¹) hmax
  rwa [div_eq_mul_inv]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Uniform-`Digest` specialization of `authRFExp_le_collisionBound_of_distinctReaderNonces`: when
`Digest` is finite and sampled uniformly, the per-digest probability is `1 / |Digest|`, so the
distinct-reader-nonce collision bound reads `q * |TagId| / |Digest|`.

Unlike `authRFExp_le_uniformCollisionBound_conjecture`, whose derivation passes through the
still-open `authRFExp_le_collisionBound_conjecture`, this corollary is fully proven: it routes
through
`authRFExp_le_collisionBound_of_distinctReaderNonces`. -/
theorem authRFExp_le_uniformCollisionBound_of_distinctReaderNonces [Fintype Digest]
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (hdistinct : HasDistinctReaderNonces adversary) :
    (Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) adversary]).toReal ≤
      ((q * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) := by
  have hmax : ∀ d : Digest,
      (Pr[= d | ($ᵗ Digest : ProbComp Digest)]).toReal ≤ (Fintype.card Digest : ℝ)⁻¹ := fun d => by
    simp [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have h := authRFExp_le_collisionBound_of_distinctReaderNonces
    (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    adversary q hq hdistinct ((Fintype.card Digest : ℝ)⁻¹) hmax
  rwa [div_eq_mul_inv]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Worked specialization showing the proved bound in use: an adversary making at most one reader
query satisfies the random-function collision bound with no separate distinctness hypothesis. A
single reader query is vacuously distinct (`hasDistinctReaderNonces_of_readerBound`), so the
forged-acceptance probability is at most `|TagId| / |Digest|`. -/
theorem authRFExp_le_uniformCollisionBound_of_singleReaderQuery [Fintype Digest]
    (adversary : AuthAdversary TagId Nonce Digest)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) 1) :
    (Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) adversary]).toReal ≤
      (Fintype.card TagId : ℝ) / (Fintype.card Digest : ℝ) := by
  have h := authRFExp_le_uniformCollisionBound_of_distinctReaderNonces
    (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    adversary 1 hq (hasDistinctReaderNonces_of_readerBound adversary hq)
  simpa using h

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- End-to-end authentication bound, distinct-reader-nonce regime. Composing the PRF reduction
`authExp_le_prfAdvantage_add_authRF` with the proved collision bound
`authRFExp_le_collisionBound_of_distinctReaderNonces`, the active-authentication adversary's
forgery probability is bounded by a single quantity: the PRF distinguishing advantage of the
canonical reduction plus the collision term `q * |TagId| * maxDigestProb`.

This is the result downstream users should cite — it folds the two-step reduction (PRF hop, then
collision analysis) into one inequality, so there is no need to stitch the intermediate
`authRFExp` world in by hand. -/
theorem authExp_le_prfAdvantage_add_collisionBound
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (hdistinct : HasDistinctReaderNonces adversary)
    (maxDigestProb : ℝ)
    (hmax : ∀ d : Digest,
      (Pr[= d | ($ᵗ Digest : ProbComp Digest)]).toReal ≤ maxDigestProb) :
    (Pr[= true | authExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) prfs adversary]).toReal ≤
      PRFScheme.prfAdvantage prfs.multiplePRFScheme
        (authToPRFReduction (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary) +
      ((q * Fintype.card TagId : ℕ) : ℝ) * maxDigestProb := by
  refine le_trans (authExp_le_prfAdvantage_add_authRF prfs adversary) ?_
  gcongr
  exact authRFExp_le_collisionBound_of_distinctReaderNonces adversary q hq hdistinct
    maxDigestProb hmax

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Existential form of `authExp_le_prfAdvantage_add_collisionBound`: there is a PRF adversary
whose distinguishing advantage, added to the distinct-reader-nonce collision term, bounds the
authentication adversary's forgery probability. The witness is `authToPRFReduction adversary`. -/
theorem exists_prfAdv_authExp_le_prfAdvantage_add_collisionBound
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (hdistinct : HasDistinctReaderNonces adversary)
    (maxDigestProb : ℝ)
    (hmax : ∀ d : Digest,
      (Pr[= d | ($ᵗ Digest : ProbComp Digest)]).toReal ≤ maxDigestProb) :
    ∃ prfAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      (Pr[= true | authExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) prfs adversary]).toReal ≤
        PRFScheme.prfAdvantage prfs.multiplePRFScheme prfAdv +
        ((q * Fintype.card TagId : ℕ) : ℝ) * maxDigestProb :=
  ⟨authToPRFReduction adversary,
    authExp_le_prfAdvantage_add_collisionBound prfs adversary q hq hdistinct maxDigestProb hmax⟩

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Uniform-`Digest` specialization of `authExp_le_prfAdvantage_add_collisionBound`: when `Digest`
is finite and sampled uniformly, the collision term reads `q * |TagId| / |Digest|`, so the
authentication adversary's forgery probability is bounded by the PRF advantage plus
`q * |TagId| / |Digest|`. -/
theorem authExp_le_prfAdvantage_add_uniformCollisionBound [Fintype Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (hdistinct : HasDistinctReaderNonces adversary) :
    (Pr[= true | authExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) prfs adversary]).toReal ≤
      PRFScheme.prfAdvantage prfs.multiplePRFScheme
        (authToPRFReduction (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary) +
      ((q * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) := by
  refine le_trans (authExp_le_prfAdvantage_add_authRF prfs adversary) ?_
  gcongr
  exact authRFExp_le_uniformCollisionBound_of_distinctReaderNonces adversary q hq hdistinct

/-- Unlinkability reduction statement: the multiple-vs-single gap is bounded by one PRF advantage
for the multiple-session world, one PRF advantage for the single-session world, and the bad-event
probability from the intermediate collision world. -/
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
  sorry

/-- The number of still-available successful tag sessions in a bad-event state. -/
private def unlinkBadRemaining (st : UnlinkBadState TagId Nonce Digest) : ℕ :=
  (Finset.univ : Finset TagId).sum fun tag => sessionsPerTag - st.sessionsUsed tag

/-- Reachable bad-event states only cache nonces that came from successful tag sessions. For each
tag, we retain a finite witness set of cached nonces whose size is bounded by that tag's session
counter. -/
private def unlinkBadCacheBounded (st : UnlinkBadState TagId Nonce Digest) : Prop :=
  ∀ tag : TagId, ∃ nonces : Finset Nonce,
    nonces.card ≤ st.sessionsUsed tag ∧
      ∀ nonce : Nonce, (st.responses (tag, nonce)).isSome = true → nonce ∈ nonces

/-- State produced by a successful `RF_bad` tag query after sampling `nonce` and `auth`. -/
private def unlinkBadTagNext
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest) : UnlinkBadState TagId Nonce Digest :=
  { sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1)
    responses := st.responses.cacheQuery (tag, nonce)
      (auth :: Option.getD (st.responses (tag, nonce)) [])
    bad := st.bad || (st.responses (tag, nonce)).isSome }

omit [Fintype TagId] [Nonempty TagId] [DecidableEq TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The initial state satisfies `unlinkBadCacheBounded`: the response cache is empty, so the empty
witness set trivially bounds each tag's nonce count. -/
private lemma unlinkBadCacheBounded_init :
    unlinkBadCacheBounded
      (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) := by
  intro tag
  refine ⟨∅, by simp [UnlinkBadState.init], ?_⟩
  intro nonce hcached
  simp [UnlinkBadState.init] at hcached

omit [Nonempty TagId] [DecidableEq TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The `unlinkBadReaderQueryImpl` does not modify the state. -/
private lemma unlinkBadReaderQueryImpl_state_eq
    (transcript : TagTranscript Nonce Digest)
    (st : UnlinkBadState TagId Nonce Digest) :
    ∀ z ∈ support ((unlinkBadReaderQueryImpl (TagId := TagId)
        (Nonce := Nonce) (Digest := Digest) transcript).run st),
      z.2 = st := by
  intro z hz
  unfold unlinkBadReaderQueryImpl at hz
  simpa using congrArg Prod.snd hz

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- When the tag still has a free slot (`sessionsUsed tag < sessionsPerTag`), the tag oracle samples
a fresh nonce and digest and advances the state via `unlinkBadTagNext`. -/
private lemma unlinkBadTagQueryImpl_run_of_lt
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) tag).run st =
      (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
        ($ᵗ Digest : ProbComp Digest) >>= fun auth =>
          pure (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest),
            unlinkBadTagNext tag st nonce auth)) := by
  simp [unlinkBadTagQueryImpl, unlinkBadTagNext, hslot]

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- When the tag has exhausted its slot budget, the tag oracle returns `none` and leaves the state
unchanged. -/
private lemma unlinkBadTagQueryImpl_run_of_not_lt
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : ¬ st.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) tag).run st = pure (none, st) := by
  simp [unlinkBadTagQueryImpl, hslot]

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Every outcome in the support of a successful tag query has the form
`(some ⟨nonce, auth⟩, unlinkBadTagNext tag st nonce auth)` for some sampled `nonce` and `auth`. -/
private lemma unlinkBadTagQueryImpl_support_of_lt
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    ∀ z ∈ support ((unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) tag).run st),
      ∃ nonce auth,
        z = (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest),
          unlinkBadTagNext tag st nonce auth) := by
  intro z hz
  rw [unlinkBadTagQueryImpl_run_of_lt (sessionsPerTag := sessionsPerTag) tag st hslot,
    mem_support_bind_iff] at hz
  rcases hz with ⟨nonce, _, hz⟩
  rw [mem_support_bind_iff] at hz
  rcases hz with ⟨auth, _, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  exact ⟨nonce, auth, hz⟩

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
    [DecidableEq Digest] [SampleableType Digest] in
/-- `unlinkBadCacheBounded` is preserved by a successful tag step: the new nonce is added to the
witness set, keeping its cardinality within the incremented session counter. -/
private lemma unlinkBadTagNext_cacheBounded
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest)
    (hbounded : unlinkBadCacheBounded st) :
    unlinkBadCacheBounded (unlinkBadTagNext tag st nonce auth) := by
  intro tag'
  obtain ⟨S, hScard, hS⟩ := hbounded tag'
  by_cases htag : tag' = tag
  · subst tag'
    refine ⟨insert nonce S, ?_, ?_⟩
    · have hcard : (insert nonce S).card ≤ st.sessionsUsed tag + 1 :=
        (Finset.card_insert_le nonce S).trans (by omega)
      simpa [unlinkBadTagNext] using hcard
    · intro nonce' hcached
      by_cases hkey : (tag, nonce') = (tag, nonce)
      · simp only [Prod.mk.injEq, true_and] at hkey
        subst nonce'
        exact Finset.mem_insert_self nonce S
      · have hsome : (st.responses (tag, nonce')).isSome = true := by
          simpa [unlinkBadTagNext, QueryCache.cacheQuery_of_ne _ _ hkey] using hcached
        exact Finset.mem_insert_of_mem (hS nonce' hsome)
  · refine ⟨S, ?_, ?_⟩
    · simpa [unlinkBadTagNext, Function.update_of_ne htag] using hScard
    · intro nonce' hcached
      have hkey : (tag', nonce') ≠ (tag, nonce) := by
        intro h
        exact htag (Prod.ext_iff.mp h).1
      have hsome : (st.responses (tag', nonce')).isSome = true := by
        simpa [unlinkBadTagNext, QueryCache.cacheQuery_of_ne _ _ hkey] using hcached
      exact hS nonce' hsome

omit [Fintype TagId] [Nonempty TagId]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- A successful tag step does not push any tag's session counter above `sessionsPerTag`,
preserving the `sessionsUsed ≤ sessionsPerTag` invariant needed by the induction. -/
private lemma unlinkBadTagNext_sessionsUsed_le
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag)
    (hused : ∀ tag, st.sessionsUsed tag ≤ sessionsPerTag) :
    ∀ tag', (unlinkBadTagNext tag st nonce auth).sessionsUsed tag' ≤ sessionsPerTag := by
  intro tag'
  by_cases htag : tag' = tag
  · subst htag
    simp [unlinkBadTagNext, Function.update_self]
    omega
  · simpa [unlinkBadTagNext, Function.update_of_ne htag] using hused tag'

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
    [SampleableType Digest] [NeZero sessionsPerTag] in
/-- A successful tag step decrements `unlinkBadRemaining` by exactly 1, which is the key
step in the union-bound induction. -/
private lemma unlinkBadRemaining_tagNext
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (unlinkBadTagNext tag st nonce auth) =
      unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 := by
  let remainingAt : TagId → ℕ := fun tag' => sessionsPerTag - st.sessionsUsed tag'
  have hpos : 0 < remainingAt tag := Nat.sub_pos_of_lt hslot
  have hpoint :
      (fun tag' : TagId =>
        sessionsPerTag -
          (unlinkBadTagNext tag st nonce auth).sessionsUsed tag') =
        Function.update remainingAt tag (remainingAt tag - 1) := by
    funext tag'
    by_cases htag : tag' = tag
    · subst htag
      simp [unlinkBadTagNext, remainingAt, Function.update_self]
      omega
    · simp [unlinkBadTagNext, remainingAt, Function.update_of_ne htag]
  calc
    unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (unlinkBadTagNext tag st nonce auth)
        = ∑ tag' : TagId, Function.update remainingAt tag (remainingAt tag - 1) tag' := by
          simp [unlinkBadRemaining, hpoint]
    _ = (∑ tag' : TagId, remainingAt tag') - 1 := sum_update_pred hpos
    _ = unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 := by
          simp [unlinkBadRemaining, remainingAt]

omit [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest]
    [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- If any tag still has a free slot, the total remaining budget is positive. Used to justify
the `- 1` arithmetic in `unlinkBadRemaining_tagNext`. -/
private lemma unlinkBadRemaining_pos_of_slot
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    0 < unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st := by
  have hterm : 0 < sessionsPerTag - st.sessionsUsed tag := Nat.sub_pos_of_lt hslot
  have hle : sessionsPerTag - st.sessionsUsed tag ≤
      (Finset.univ : Finset TagId).sum
        (fun tag' => sessionsPerTag - st.sessionsUsed tag') :=
    Finset.single_le_sum (s := (Finset.univ : Finset TagId))
      (f := fun tag' => sessionsPerTag - st.sessionsUsed tag')
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ tag)
  exact lt_of_lt_of_le hterm (by simpa [unlinkBadRemaining] using hle)

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- A single tag step raises `bad` with probability at most `sessionsUsed tag * maxNonceProb`:
the new nonce collides with one of the (at most `sessionsUsed tag`) previously cached nonces,
each matchable with probability at most `maxNonceProb`. -/
private lemma unlinkBadTagStep_bad_le
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (maxNonceProb : ℝ≥0∞)
    (hmax : ∀ n : Nonce, Pr[= n | ($ᵗ Nonce : ProbComp Nonce)] ≤ maxNonceProb)
    (hbad : st.bad = false)
    (hbounded : unlinkBadCacheBounded st) :
    Pr[fun z : Option (TagTranscript Nonce Digest) × UnlinkBadState TagId Nonce Digest =>
        z.2.bad = true |
      (unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) tag).run st] ≤
      (st.sessionsUsed tag : ℝ≥0∞) * maxNonceProb := by
  by_cases hslot : st.sessionsUsed tag < sessionsPerTag
  · rw [unlinkBadTagQueryImpl_run_of_lt (sessionsPerTag := sessionsPerTag) tag st hslot,
      probEvent_bind_eq_tsum]
    have hinner : ∀ nonce : Nonce,
        Pr[fun z : Option (TagTranscript Nonce Digest) × UnlinkBadState TagId Nonce Digest =>
            z.2.bad = true |
          ($ᵗ Digest : ProbComp Digest) >>= fun auth =>
            pure (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest),
              unlinkBadTagNext tag st nonce auth)] =
          if (st.responses (tag, nonce)).isSome then 1 else 0 := by
      intro nonce
      by_cases hcached : (st.responses (tag, nonce)).isSome = true
      · simp [unlinkBadTagNext, hbad, hcached]
      · simp [unlinkBadTagNext, hbad, hcached]
    simp_rw [hinner]
    obtain ⟨S, hScard, hS⟩ := hbounded tag
    calc
      ∑' nonce : Nonce,
          Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
            (if (st.responses (tag, nonce)).isSome then 1 else 0)
          = Pr[fun nonce : Nonce => (st.responses (tag, nonce)).isSome = true |
              ($ᵗ Nonce : ProbComp Nonce)] := by
            simp only [probEvent_eq_tsum_ite]
            refine tsum_congr fun nonce => ?_
            by_cases hcached : (st.responses (tag, nonce)).isSome = true
            · simp [hcached]
            · simp [hcached]
      _ ≤ Pr[fun nonce : Nonce => ∃ n ∈ S, nonce = n |
              ($ᵗ Nonce : ProbComp Nonce)] := by
            apply probEvent_mono
            intro nonce _ hcached
            exact ⟨nonce, hS nonce hcached, rfl⟩
      _ ≤ ∑ n ∈ S, Pr[fun nonce : Nonce => nonce = n |
              ($ᵗ Nonce : ProbComp Nonce)] :=
            probEvent_exists_finset_le_sum S ($ᵗ Nonce : ProbComp Nonce)
              (fun n nonce => nonce = n)
      _ ≤ ∑ _n ∈ S, maxNonceProb := by
            apply Finset.sum_le_sum
            intro n hn
            simpa [probEvent_eq_eq_probOutput] using hmax n
      _ = (S.card : ℝ≥0∞) * maxNonceProb := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (st.sessionsUsed tag : ℝ≥0∞) * maxNonceProb := by
            exact mul_le_mul' (Nat.cast_le.mpr hScard) le_rfl
  · rw [unlinkBadTagQueryImpl_run_of_not_lt (sessionsPerTag := sessionsPerTag) tag st hslot]
    simp [hbad]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- For any adversary and state `st` with `bad = false`,
the probability that bad fires is at most
`(∑ tag, sessionsPerTag − st.sessionsUsed tag) * sessionsPerTag * maxNonceProb`. -/
private lemma simulateQ_unlinkBad_prob_le
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ≥0∞)
    (hmax : ∀ n : Nonce, Pr[= n | ($ᵗ Nonce : ProbComp Nonce)] ≤ maxNonceProb)
    (st : UnlinkBadState TagId Nonce Digest)
    (hbounded : unlinkBadCacheBounded st)
    (hbad : st.bad = false)
    (hused : ∀ tag, st.sessionsUsed tag ≤ sessionsPerTag) :
    Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) adversary).run st] ≤
      (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
        ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
  induction adversary using OracleComp.inductionOn generalizing st with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, hbad, Bool.false_eq_true,
      ite_false]
    exact zero_le _
  | query_bind t oa ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind, monadLift_self]
    cases t with
    | inl tag =>
      simp only [unlinkBadQueryImpl, QueryImpl.add_apply_inl]
      by_cases hslot : st.sessionsUsed tag < sessionsPerTag
      · let step :=
          (unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) tag).run st
        let cont := fun z : Option (TagTranscript Nonce Digest) ×
            UnlinkBadState TagId Nonce Digest =>
          (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) (oa z.1)).run z.2
        have hstep :
            Pr[fun z : Option (TagTranscript Nonce Digest) ×
                  UnlinkBadState TagId Nonce Digest => ¬ z.2.bad = false | step] ≤
              (sessionsPerTag : ℝ≥0∞) * maxNonceProb := by
          have hbadStep :=
            unlinkBadTagStep_bad_le (sessionsPerTag := sessionsPerTag)
              tag st maxNonceProb hmax hbad hbounded
          have hused_le :
              (st.sessionsUsed tag : ℝ≥0∞) * maxNonceProb ≤
                (sessionsPerTag : ℝ≥0∞) * maxNonceProb :=
            mul_le_mul' (Nat.cast_le.mpr (hused tag)) le_rfl
          simpa [step] using hbadStep.trans hused_le
        have hRpos := unlinkBadRemaining_pos_of_slot
          (sessionsPerTag := sessionsPerTag) tag st hslot
        have hcont :
            ∀ z ∈ support step, z.2.bad = false →
              Pr[fun y : Bool × UnlinkBadState TagId Nonce Digest => ¬ y.2.bad = false |
                  cont z] ≤
                ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 : ℕ) : ℝ≥0∞) *
                  ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
          intro z hz hzbad
          obtain ⟨nonce, auth, rfl⟩ :=
            unlinkBadTagQueryImpl_support_of_lt (sessionsPerTag := sessionsPerTag)
              tag st hslot z (by simpa [step] using hz)
          have hnextBounded :=
            unlinkBadTagNext_cacheBounded tag st nonce auth hbounded
          have hnextUsed :=
            unlinkBadTagNext_sessionsUsed_le (sessionsPerTag := sessionsPerTag)
              tag st nonce auth hslot hused
          have hnextRemaining :=
            unlinkBadRemaining_tagNext (sessionsPerTag := sessionsPerTag)
              tag st nonce auth hslot
          have hih :=
            ih (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest))
              (unlinkBadTagNext tag st nonce auth)
              hnextBounded hzbad hnextUsed
          simpa [cont, hnextRemaining] using hih
        have hcombine := probEvent_bind_le_add (mx := step) (my := cont)
          (p := fun z : Option (TagTranscript Nonce Digest) ×
            UnlinkBadState TagId Nonce Digest => z.2.bad = false)
          (q := fun y : Bool × UnlinkBadState TagId Nonce Digest => y.2.bad = false)
          (ε₁ := (sessionsPerTag : ℝ≥0∞) * maxNonceProb)
          (ε₂ := ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 : ℕ) :
              ℝ≥0∞) * ((sessionsPerTag : ℝ≥0∞) * maxNonceProb))
          hstep hcont
        calc
          Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
              step >>= cont]
              ≤ (sessionsPerTag : ℝ≥0∞) * maxNonceProb +
                  ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 : ℕ) :
                    ℝ≥0∞) * ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
                simpa [step, cont] using hcombine
          _ = (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
                let R := unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st
                let c := (sessionsPerTag : ℝ≥0∞) * maxNonceProb
                have hR : 1 + (R - 1) = R := Nat.add_sub_cancel' (Nat.succ_le_iff.mpr hRpos)
                have hRcast : (1 : ℝ≥0∞) + ((R - 1 : ℕ) : ℝ≥0∞) = (R : ℝ≥0∞) := by
                  exact_mod_cast hR
                change c + ((R - 1 : ℕ) : ℝ≥0∞) * c = (R : ℝ≥0∞) * c
                nth_rw 1 [← one_mul c]
                rw [← add_mul, hRcast]
      · change
          Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
            ((unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) tag).run st >>= fun p =>
              (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) (oa p.1)).run
                p.2)] ≤
            (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
              ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)
        rw [unlinkBadTagQueryImpl_run_of_not_lt (sessionsPerTag := sessionsPerTag) tag st hslot]
        simpa using ih none st hbounded hbad hused
    | inr transcript =>
      simp only [unlinkBadQueryImpl, QueryImpl.add_apply_inr]
      rw [probEvent_bind_eq_tsum]
      calc ∑' z, Pr[= z | (unlinkBadReaderQueryImpl transcript).run st] *
              Pr[fun w => w.2.bad | (simulateQ unlinkBadQueryImpl (oa z.1)).run z.2]
          ≤ ∑' z, Pr[= z | (unlinkBadReaderQueryImpl transcript).run st] *
              ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)) := by
            apply ENNReal.tsum_le_tsum
            intro z
            by_cases hmem :
                z ∈ support ((unlinkBadReaderQueryImpl
                    (TagId := TagId) (Nonce := Nonce) (Digest := Digest) transcript).run st)
            · rw [unlinkBadReaderQueryImpl_state_eq transcript st z hmem]
              exact mul_le_mul' le_rfl (ih z.1 st hbounded hbad hused)
            · rw [probOutput_eq_zero_of_not_mem_support hmem]
              simp
        _ = (∑' z, Pr[= z | (unlinkBadReaderQueryImpl transcript).run st]) *
              ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)) := by
            rw [ENNReal.tsum_mul_right]
        _ ≤ 1 * ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
              ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)) := by
            gcongr
            exact tsum_probOutput_le_one
        _ = (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
              ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := one_mul _

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- A pointwise bound on the nonce sampler turns the bad-event probability into an explicit session
collision bound. -/
theorem unlinkBadExp_le_sessionCollisionBound
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ)
    (hmax : ∀ nonce : Nonce,
      (Pr[= nonce | ($ᵗ Nonce)]).toReal ≤ maxNonceProb) :
    (Pr[= true | unlinkBadExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary]).toReal ≤
      ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ) * maxNonceProb := by
  have hmax_ENNReal : ∀ n : Nonce,
      Pr[= n | ($ᵗ Nonce : ProbComp Nonce)] ≤ ENNReal.ofReal maxNonceProb := by
    intro n
    rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top one_ne_top probOutput_le_one)]
    exact ENNReal.ofReal_le_ofReal (hmax n)
  have hlhs : Pr[= true | unlinkBadExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) adversary).run
          UnlinkBadState.init] := by
    rw [← probEvent_eq_eq_probOutput, unlinkBadExp, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    simp
  rw [hlhs]
  have hcore := simulateQ_unlinkBad_prob_le (sessionsPerTag := sessionsPerTag)
    adversary (ENNReal.ofReal maxNonceProb)
    hmax_ENNReal UnlinkBadState.init unlinkBadCacheBounded_init (by simp [UnlinkBadState.init])
    (by simp [UnlinkBadState.init])
  have hconv : (Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) adversary).run
          UnlinkBadState.init]).toReal ≤
      ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
          (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) :
            ℝ≥0∞) *
        ((sessionsPerTag : ℝ≥0∞) * ENNReal.ofReal maxNonceProb)).toReal := by
    exact ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) hcore
  have hremaining :
      unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) =
          sessionsPerTag * Fintype.card TagId := by
    simp [unlinkBadRemaining, UnlinkBadState.init, Finset.sum_const, Finset.card_univ,
      mul_comm]
  have hsupp : (support ($ᵗ Nonce : ProbComp Nonce)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ne_eq, ← probFailure_eq_one_iff]
    simp
  obtain ⟨nonce0, _⟩ := hsupp
  have hmax_nonneg : 0 ≤ maxNonceProb := ENNReal.toReal_nonneg.trans (hmax nonce0)
  simp only [
    hremaining, Nat.cast_mul, toReal_mul, toReal_natCast, ENNReal.toReal_ofReal hmax_nonneg
  ] at hconv
  grind

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

end Theorems

end PRFTagReader
