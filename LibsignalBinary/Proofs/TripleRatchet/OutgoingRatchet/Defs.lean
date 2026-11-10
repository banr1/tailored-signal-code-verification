/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Defs

/-!
# Specifications for `OutgoingTripleRatchet::from_session_state` and `apply_to_session_state`

Callee `subroutine_ok` hypotheses, internal stack budgets (`otrFromInternalStack`,
`otrApplyInternalStack`), concrete `SessionGhost` transitions (`afterOtrFrom`, `afterOtrApply`),
and `otrApplyRawSpec` for `<OutgoingTripleRatchet>::from_session_state` and
`<OutgoingTripleRatchet>::apply_to_session_state`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters

/-! ## Callee symbol names and `subroutine_ok` hypotheses -/

def RemoteIdentityKeyOk_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr remoteIdentityKeyName) (remoteIdentityKeySpec A img)

def RemoteIdentityKeyOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr remoteIdentityKeyName) (remoteIdentityKeySpec A img)

def DropSpeOk_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr dropSpeName) ((dropSpeSpec A).inImage img)

def DropSpeOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr dropSpeName) ((dropSpeSpec A).inImage img)

/-! ## Stack budgets -/

/-- Internal stack budget of `OTR::from_session_state`: 384-byte frame (`0x180`) plus the
maximum callee budget `dropSpeStack`. -/
abbrev otrFromInternalStack : Nat := 0x180 + dropSpeStack

/-- Internal stack budget of `OTR::apply_to_session_state`: 128-byte frame (`0x80`) plus
`allocHookStack`. -/
abbrev otrApplyInternalStack : Nat := 0x80 + allocHookStack

/-! ## Concrete `SessionGhost` transitions -/

/-- Concrete `SessionGhost` after `OTR::from_session_state`: leaves `G` unchanged when
`st.senderChain = none`, and replaces `G.pq` with the empty `Vec` `{cap = 0, ptr = 1}` when
`st.senderChain = some _` (`mem::take` of `pq_ratchet_state`). -/
def afterOtrFrom (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SessionGhost :=
  match st.senderChain with
  | none => G
  | some _ => { G with pq := ⟨0#64, 1#64⟩ }

/-- Concrete `SessionGhost` after `OTR::apply_to_session_state`: installs the freshly allocated
32-byte `chain_key` buffer `(32, ckPtr)` into `sender`, clears `message_keys`, and moves
`(pqCap, pqPtr)` into `pq`. -/
def afterOtrApply (G : SessionGhost) (sg : SenderChainGhost) (ckPtr pqCap pqPtr : BitVec 64) :
    SessionGhost :=
  { G with sender := some { sg with ck := ⟨32#64, ckPtr⟩ }, pq := ⟨pqCap, pqPtr⟩ }

/-! ## `OutgoingTripleRatchet::from_session_state` -/

/-- Target `subroutine_ok` proposition asserting that
`<OutgoingTripleRatchet>::from_session_state` meets `otrFromSpec A img` on
`tripleRatchetProgAt img.base C ctl abs`. -/
def OtrFromOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr otrFromName) (otrFromSpec A img)

/-! ## `OutgoingTripleRatchet::apply_to_session_state` -/

/-- Image-independent specification of `<OutgoingTripleRatchet>::apply_to_session_state(x0 = o,
x1 = ss)`: allocates a fresh 32-byte `chain_key` buffer, frees the old sender chain-key and
`pq_ratchet_state` buffers, writes `x.ot.applyToSessionState x.st` at `x.ss` (leaving
`memRegion x.o 200`), and panics only on `__rust_alloc` failure. -/
def otrApplyRawSpec (A : RustAlloc) : Spec OtrApplyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.o ∧ s.readReg64 .x1 = x.ss ∧ x.st.senderChain.isSome⌝ ∗
      otrAt A x.o x.pqCap x.pqPtr x.ot ∗ sessionStateAt A x.ss x.G x.st ∗
      stackAt s.sp otrApplyInternalStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ G' : SessionGhost, ⌜x.G.AfterOutgoingRatchetApply G' ∧ G'.pq = ⟨x.pqCap, x.pqPtr⟩⌝ ∗
        sessionStateAt A x.ss G' (x.ot.applyToSessionState x.st)) ∗
      memRegion x.o 200 ∗ stackAt s0.sp otrApplyInternalStack ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def OtrApplyRawOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr otrApplyName)
    (otrApplyRawSpec A)

def OtrApplyOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr otrApplyName) (otrApplySpec A img)

/-! ## `tripleRatchetProgAtExt` generalized target and callee propositions -/

def DeserializeExtOk (b : BitVec 64) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr deserializeName)
    (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeSpec b)

def RemoteIdentityKeyExtOk (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr remoteIdentityKeyName) (remoteIdentityKeySpec A img)

def DropSpeExtOk (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr dropSpeName) ((dropSpeSpec A).inImage img)

def OtrFromExtOk (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr otrFromName) (otrFromSpec A img)

def OtrApplyRawExtOk (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr otrApplyName)
    (otrApplyRawSpec A)

def OtrApplyExtOk (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr otrApplyName) (otrApplySpec A img)

end CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
