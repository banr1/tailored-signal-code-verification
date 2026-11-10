/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet

/-!
# CLI `MessageEncrypt` Callee Bundles

Collects the in-library callee contracts (`EncCallees`, `EncCallees_trap`, `EncCallees_ext`)
required by the CLI `MessageEncrypt` segments.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi

/-! ## Callee Predicates and Bundles -/

/-- The Kyber closure at its rebased address. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + bv% (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")) (kyberMapSpec A)

/-- The CM drop glue at its rebased address. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]")) (cmDropSpec A)

/-- `otrEncryptSpec` restricted to outgoing ratchets whose SPQR state satisfies `Q`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ (Q : List (BitVec 8) → Prop) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (img : Obj.Image) : Spec OtrEncryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl parse S img with
    pre := fun x s => ⌜Q x.ot.pqrState⌝ ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl parse S img).pre x s }

/-- `OTR::encrypt` contract on `tripleRatchetProgAt` restricted to SPQR states satisfying `Q`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) :
    Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ Q C A ctl parse S img)

/-- Bundle of in-library callee contracts required by the CLI `MessageEncrypt` segments
(excluding external hooks and store vtable methods). -/
structure _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncCallees (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) :
    Prop where
  otrFrom : OutgoingRatchet.OtrFromOk img C A ctl abs
  otrApply : OutgoingRatchet.OtrApplyOk img C A ctl abs
  remoteIk : OutgoingRatchet.RemoteIdentityKeyOk img C A ctl abs
  otrEnc : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ Q img C A ctl parse S abs
  unack : UnackItemsOk img C A ctl abs
  kyber : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk img C A ctl abs
  psmNew : PreKeyMsgNewOk img C A ctl abs
  cmDrop : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk img C A ctl abs
  /-- `drop_glue<SessionStructure>` called during final cleanup (`+0xef4`). -/
  dropSs : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs


/-- `trTrapProgAt` variant of `UnackItemsOk`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.UnackItemsOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    (img.base + bv% (ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items"))
    (unackItemsSpec A img)

/-- `trTrapProgAt` variant of `KyberMapOk`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    (img.base + bv% (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>"))
    (kyberMapSpec A)

/-- `trTrapProgAt` variant of `PreKeyMsgNewOk`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.PreKeyMsgNewOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    (img.base + bv% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage>::new"))
    (preKeyMsgNewSpec A)

/-- `trTrapProgAt` variant of `CmDropOk`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    (img.base + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]"))
    (cmDropSpec A)

/-- `trTrapProgAt` variant of `OtrEncryptOkQ`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ_trap
    (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ Q C A ctl parse S img)

/-- `trTrapProgAt` variant of `EncCallees`. -/
structure _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncCallees_trap
    (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop where
  otrFrom : OutgoingRatchet.OtrFromExtOk img A (trTrapExterns C abs)
  otrApply : OutgoingRatchet.OtrApplyExtOk img A (trTrapExterns C abs)
  remoteIk : OutgoingRatchet.RemoteIdentityKeyExtOk img A (trTrapExterns C abs)
  otrEnc : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ_trap Q img C A ctl parse S abs
  unack : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.UnackItemsOk_trap img C A abs
  kyber : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk_trap img C A abs
  psmNew : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.PreKeyMsgNewOk_trap img C A abs
  cmDrop : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk_trap img C A abs
  dropSs : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A (trTrapExterns C abs)

/-- `tripleRatchetProgAtExt` variant of `UnackItemsOk`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.UnackItemsOk_ext
    (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    (img.base + bv% (ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items"))
    (unackItemsSpec A img)

/-- `tripleRatchetProgAtExt` variant of `KyberMapOk`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk_ext
    (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    (img.base + bv% (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>"))
    (kyberMapSpec A)

/-- `tripleRatchetProgAtExt` variant of `PreKeyMsgNewOk`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.PreKeyMsgNewOk_ext
    (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    (img.base + bv% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage>::new"))
    (preKeyMsgNewSpec A)

/-- `tripleRatchetProgAtExt` variant of `CmDropOk`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk_ext
    (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    (img.base + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]"))
    (cmDropSpec A)

/-- `tripleRatchetProgAtExt` variant of `OtrEncryptOkQ`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ_ext
    (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ Q C A ctl parse S img)

/-- `tripleRatchetProgAtExt` variant of `EncCallees` (definitionally equal to `EncCallees_trap` at `trTrapExterns C abs`). -/
structure _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncCallees_ext
    (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop where
  otrFrom : OutgoingRatchet.OtrFromExtOk img A ext
  otrApply : OutgoingRatchet.OtrApplyExtOk img A ext
  remoteIk : OutgoingRatchet.RemoteIdentityKeyExtOk img A ext
  otrEnc : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ_ext Q img C A ctl parse S ext
  unack : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.UnackItemsOk_ext img A ext
  kyber : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk_ext img A ext
  psmNew : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.PreKeyMsgNewOk_ext img A ext
  cmDrop : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk_ext img A ext
  dropSs : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCallees_trap_iff_ext
    (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncCallees_trap Q img C A ctl parse S abs ↔
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncCallees_ext Q img C A ctl parse S
        (trTrapExterns C abs) :=
  ⟨fun h => ⟨h.otrFrom, h.otrApply, h.remoteIk, h.otrEnc, h.unack, h.kyber, h.psmNew, h.cmDrop, h.dropSs⟩,
   fun h => ⟨h.otrFrom, h.otrApply, h.remoteIk, h.otrEnc, h.unack, h.kyber, h.psmNew, h.cmDrop, h.dropSs⟩⟩

end CryptoVerification.LibsignalPublicApi.MessageEncrypt
