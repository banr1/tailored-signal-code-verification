/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.ReprMove

/-!
# Decoded Previous Session to Drop Precondition Bridge

Separation-logic entailments (`prevDec_sessionAt`, `prevDec_sessionStateAt_canon`, and
`prevDec_dropPre`) converting the decoded `prostSSGQAt A ss (ssgqOf sess)` into the
`sessionStateAt` precondition of `dropSessionStructure3` on the version-mismatch exit.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.E2E.Record.Serialization (CanonSession)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (prostSSGQAt ssgqOf prostSSGQ_repr prostSSGQ_reprA)

/-- Allocator-polymorphic bridge from `prostSSGQAt A ss (ssgqOf sess)` to `sessionStateReprAt`. -/
theorem prevDec_sessionAt_ext (A : RustAlloc) (sess : Session (List (BitVec 8)))
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩) (ss : BitVec 64) :
    prostSSGQAt A ss (ssgqOf sess) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G sess⌝ ∗ sessionStateReprAt A ss G sess :=
  prostSSGQ_reprA A ⟨some sess⟩ hQ sess rfl ss

theorem prevDec_sessionAt (sess : Session (List (BitVec 8)))
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩) (ss : BitVec 64) :
    prostSSGQAt A0 ss (ssgqOf sess) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G sess⌝ ∗ sessionStateReprAt A0 ss G sess :=
  prevDec_sessionAt_ext A0 sess hQ ss

/-- Allocator-polymorphic bridge from `prostSSGQAt A ss (ssgqOf sess)` to `sessionStateAt` with canonical ghost. -/
theorem prevDec_sessionStateAt_canon_ext (A : RustAlloc) (sess : Session (List (BitVec 8)))
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩) (ss : BitVec 64) :
    prostSSGQAt A ss (ssgqOf sess) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G sess⌝ ∗ sessionStateAt A ss G sess.state := by
  refine Entails.trans (prevDec_sessionAt_ext A sess hQ ss) ?_
  refine Entails.sepExists_elim fun G => Entails.sepExists_right G ?_
  refine sepConj_mono_right ?_
  dsimp only [sessionStateReprAt]
  exact Entails.pure_left fun _ => Entails.refl _

theorem prevDec_sessionStateAt_canon (sess : Session (List (BitVec 8)))
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩) (ss : BitVec 64) :
    prostSSGQAt A0 ss (ssgqOf sess) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G sess⌝ ∗ sessionStateAt A0 ss G sess.state :=
  prevDec_sessionStateAt_canon_ext A0 sess hQ ss

/-- With `session_version = 4`, the decoded previous session entails the `SessionStructure` drop precondition at `ss` with `[ss + 0x148] = 4#32`. -/
theorem prevDec_dropPre_ext (A : RustAlloc) (sess : Session (List (BitVec 8)))
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩) (hv : sess.state.sessionVersion = 4#32)
    (ss : BitVec 64) :
    prostSSGQAt A ss (ssgqOf sess) ⊢
      ∃∗ G : SessionGhost, ∃∗ st : SessionState (List (BitVec 8)),
        ⌜st.sessionVersion = 4#32⌝ ∗ sessionStateAt A ss G st := by
  refine Entails.trans (prevDec_sessionStateAt_canon_ext A sess hQ ss) ?_
  refine Entails.sepExists_elim fun G => Entails.sepExists_right G ?_
  refine Entails.sepExists_right sess.state ?_
  refine Entails.pure_left fun _ => Entails.pure_right hv (Entails.refl _)

theorem prevDec_dropPre (sess : Session (List (BitVec 8)))
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩) (hv : sess.state.sessionVersion = 4#32)
    (ss : BitVec 64) :
    prostSSGQAt A0 ss (ssgqOf sess) ⊢
      ∃∗ G : SessionGhost, ∃∗ st : SessionState (List (BitVec 8)),
        ⌜st.sessionVersion = 4#32⌝ ∗ sessionStateAt A0 ss G st :=
  prevDec_dropPre_ext A0 sess hQ hv ss

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
