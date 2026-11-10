/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.CodeLayout
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Callee Addresses and `.rodata` Helpers for `OTR::encrypt`

Proves fixed-image and relocatable `[LibsignalPlacement]` callee/hook address lemmas, `.rodata`
access lemmas for `"encrypt"`, and `Err(InvalidState("encrypt", msg))` sret packing.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Encrypt


open Arm64 ProofLib CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


/-! ## Callee and hook address lemmas for `OTR::encrypt` (`0x33e0c`) -/

theorem spqrSend_addr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr spqrSendName =
      (tripleRatchetProgAtExt b ext).fnAddr otrEncryptName + bv% (2 ^ 64 + (ls_off% "spqr::send::<libsignal_session::HookRng>") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "spqr::send::<libsignal_session::HookRng>"), (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")]
  bv_omega

theorem spqrSend_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr spqrSendName =
      (tripleRatchetProgAt b C ctl abs).fnAddr otrEncryptName + bv% (2 ^ 64 + (ls_off% "spqr::send::<libsignal_session::HookRng>") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) :=
  spqrSend_addr_eq_ext b (tripleRatchetExterns C ctl abs)

theorem messageKeys_addr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr messageKeysName =
      (tripleRatchetProgAtExt b ext).fnAddr otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::message_keys") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::message_keys"), (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")]
  bv_omega

theorem messageKeys_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr messageKeysName =
      (tripleRatchetProgAt b C ctl abs).fnAddr otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::message_keys") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) :=
  messageKeys_addr_eq_ext b (tripleRatchetExterns C ctl abs)

theorem generateKeys_addr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr generateKeysName =
      (tripleRatchetProgAtExt b ext).fnAddr otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys"), (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")]
  bv_omega

theorem generateKeys_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr generateKeysName =
      (tripleRatchetProgAt b C ctl abs).fnAddr otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) :=
  generateKeys_addr_eq_ext b (tripleRatchetExterns C ctl abs)

theorem signalMessageNew_addr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName =
      (tripleRatchetProgAtExt b ext).fnAddr otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::new"), (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")]
  bv_omega

theorem signalMessageNew_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName =
      (tripleRatchetProgAt b C ctl abs).fnAddr otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) :=
  signalMessageNew_addr_eq_ext b (tripleRatchetExterns C ctl abs)

theorem nextChainKey_addr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr nextChainKeyName =
      (tripleRatchetProgAtExt b ext).fnAddr otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key"), (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")]
  bv_omega

theorem nextChainKey_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr nextChainKeyName =
      (tripleRatchetProgAt b C ctl abs).fnAddr otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) :=
  nextChainKey_addr_eq_ext b (tripleRatchetExterns C ctl abs)

theorem aesEnc_ok_at_encrypt_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (b : BitVec 64) (hC : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr otrEncryptName + bv% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_encrypt" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) (aesEncSpec C.E A) :=
  hC.aes_enc_ok_at otrEncryptName (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_encrypt" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>"))

theorem aesEnc_ok_at_encrypt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (b : BitVec 64) (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr otrEncryptName + bv% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_encrypt" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) (aesEncSpec C.E A) :=
  aesEnc_ok_at_encrypt_ext C A ctl S (tripleRatchetExterns C ctl abs) b
    (Stage2Contracts.of_tripleRatchetProgAt b C A ctl S abs hS)

theorem formatInner_ok_at_encrypt_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (b : BitVec 64) (hC : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr otrEncryptName + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) (formatInnerSpec A) :=
  hC.format_inner_ok_at otrEncryptName (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>"))

theorem formatInner_ok_at_encrypt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (b : BitVec 64) (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr otrEncryptName + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) (formatInnerSpec A) :=
  formatInner_ok_at_encrypt_ext C A ctl S (tripleRatchetExterns C ctl abs) b
    (Stage2Contracts.of_tripleRatchetProgAt b C A ctl S abs hS)

theorem dealloc_ok_at_encrypt_ext (A : RustAlloc) (ext : String → Option (State → State))
    (b : BitVec 64) (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr otrEncryptName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) (rustDeallocSpec A) :=
  hA.dealloc_ok_at otrEncryptName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>"))

theorem dealloc_ok_at_encrypt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (b : BitVec 64) (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr otrEncryptName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) (rustDeallocSpec A) :=
  dealloc_ok_at_encrypt_ext A (tripleRatchetExterns C ctl abs) b
    (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hS.alloc)

/-! ## `.rodata` literal `"encrypt"` (`0x4f3ee`, 7 bytes) -/

open ProofLib.ProgramReflection in
theorem rodata_0x453ee_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 7 = utf8 "encrypt" := by
  rfl_kernel

namespace EncryptCoreFacts

theorem of_rodata_loads_eq {li : Arm64.Obj.LinkedImage} {img : Arm64.Obj.Image}
    {m : Memory} {P : SepProp} (himg : Arm64.Obj.Loads li img)
    {dataOff : Nat} (hdo : li.dataOff = dataOff)
    {secOff secLen : Nat} {bs : List (BitVec 8)}
    (hsec : (secOff, secLen) ∈ li.roData)
    (hoff : dataOff ≤ secOff) (hlen : secLen < 2 ^ 32)
    (hdlen : secOff - dataOff + secLen ≤ li.data.length)
    (hrel : li.relocs.all
      (fun r => decide (r.off + r.width ≤ secOff - dataOff ∨ secOff - dataOff + secLen ≤ r.off)) = true)
    (heq : (li.data.drop (secOff - dataOff)).take secLen = bs)
    (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + BitVec.ofNat 64 secOff) ↦ᵣ bs) ∗ P := by
  subst heq
  exact ProofLib.Satisfies.of_rodata_loads himg hdo hsec hoff hlen hdlen hrel hro hP

end EncryptCoreFacts

open ProofLib.ProgramReflection in
theorem rodata_encrypt_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556))) ↦ᵣ utf8 "encrypt") ∗ P :=
  EncryptCoreFacts.of_rodata_loads_eq himg
    (secOff := num% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556))) (secLen := 7) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) rodata_0x453ee_eq hro hP

theorem rodata_encrypt_sepWPp {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : img.RoDataLoaded s.mem)
    (h : SepWPp prog ret s (((img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556))) ↦ᵣ utf8 "encrypt") ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact rodata_encrypt_intro himg hro hm

theorem drop_left_sepWPp {prog : Program} {ret : BitVec 64}
    {s : State} {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL


theorem adrp_0x453ee_eq (base entry : BitVec 64)
    (halign : base &&& 0xfff#64 = 0#64) (hentry : base + bv% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>") = entry) :
    ((entry + bv% (552) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556) - page% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 500))) = base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556)) := by
  subst hentry
  rw [BitVec.add_assoc, adrp_page_of_aligned halign, BitVec.add_assoc]
  rfl

/-- Fold the `Err(InvalidState("encrypt", msg))` sret written on `spqr::send = None` (`0x34030..0x3405c`). -/
theorem errResultAt_invalidState_pack (A : RustAlloc) (ret : BitVec 64)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) (roBase entry : BitVec 64)
    (hadrp : ((entry + bv% (552) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556) - page% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 500))) = roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556))) :
    ((ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
      ((ret + 8#64) ↦₆₄ 9223372036854775809#64) ∗
      ((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
      ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((ret + 40#64) ↦₆₄ ((entry + bv% (552) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556) - page% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 500)))) ∗
      ((ret + 48#64) ↦₆₄ 7#64) ∗
      memRegion (ret + 56#64) 64 ∗
      vecU8Buf A cap ptr bs ∗
      ((roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556))) ↦ᵣ utf8 "encrypt")) ⊢
    signalMessageResultAt A (utf8 "encrypt") ret (.error .invalidState) := by
  rw [hadrp]
  change ((ret ↦₆₄ errTag) ∗
      ((ret + 8#64) ↦₆₄ speWord 1) ∗
      ((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
      ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((ret + 40#64) ↦₆₄ (roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556)))) ∗
      ((ret + 48#64) ↦₆₄ 7#64) ∗
      memRegion (ret + 56#64) 64 ∗
      vecU8Buf A cap ptr bs ∗
      ((roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556))) ↦ᵣ utf8 "encrypt")) ⊢
    signalMessageResultAt A (utf8 "encrypt") ret (.error .invalidState)
  unfold signalMessageResultAt errResultAt speAt strRefAt
  have hvec :
      (((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
        ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs) ⊢
      (∃∗ bs' : List (BitVec 8), vecU8 A (ret + 8#64 + 8#64) bs') := by
    refine Entails.sepExists_right bs ?_
    unfold vecU8
    refine Entails.sepExists_right cap ?_
    refine Entails.sepExists_right ptr ?_
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc]
    exact Entails.refl _
  have hstr :
      (((ret + 40#64) ↦₆₄ (roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556)))) ∗
        ((ret + 48#64) ↦₆₄ 7#64) ∗
        ((roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556))) ↦ᵣ utf8 "encrypt")) ⊢
      (∃∗ p : BitVec 64,
        ((ret + 8#64 + 32#64) ↦₆₄ p) ∗
          ((ret + 8#64 + 32#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "encrypt").length) ∗
          (p ↦ᵣ utf8 "encrypt")) := by
    refine Entails.sepExists_right (roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556))) ?_
    have hlen : BitVec.ofNat 64 (utf8 "encrypt").length = 7#64 := by decide +kernel
    simp only [hlen, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _
  have hpull :
      ((ret ↦₆₄ errTag) ∗
        ((ret + 8#64) ↦₆₄ speWord 1) ∗
        ((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
        ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ret + 40#64) ↦₆₄ (roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556)))) ∗
        ((ret + 48#64) ↦₆₄ 7#64) ∗
        memRegion (ret + 56#64) 64 ∗
        vecU8Buf A cap ptr bs ∗
        ((roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556))) ↦ᵣ utf8 "encrypt")) =
      ((ret ↦₆₄ errTag) ∗
        (((ret + 8#64) ↦₆₄ speWord 1) ∗
          (((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
            ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            vecU8Buf A cap ptr bs) ∗
          (((ret + 40#64) ↦₆₄ (roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556)))) ∗
            ((ret + 48#64) ↦₆₄ 7#64) ∗
            ((roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 556))) ↦ᵣ utf8 "encrypt"))) ∗
        memRegion (ret + 56#64) 64) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono hvec hstr)))

/-! ## Relocatable `[LibsignalPlacement]` `.rodata` `"encrypt"` and Callee Helpers -/

theorem rodata_encrypt_placed_sepWPp [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {roSym : String} (hchk : lsroCheck roSym (utf8 "encrypt") = true)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWPp prog ret s (((lsmpl.ρ roSym) ↦ᵣ utf8 "encrypt") ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact lsro_intro_chk hro hchk hm

theorem errResultAt_invalidState_placed_pack (A : RustAlloc) (ret : BitVec 64)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) (roPtr : BitVec 64) :
    ((ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
      ((ret + 8#64) ↦₆₄ 9223372036854775809#64) ∗
      ((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
      ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((ret + 40#64) ↦₆₄ roPtr) ∗
      ((ret + 48#64) ↦₆₄ 7#64) ∗
      memRegion (ret + 56#64) 64 ∗
      vecU8Buf A cap ptr bs ∗
      (roPtr ↦ᵣ utf8 "encrypt")) ⊢
    signalMessageResultAt A (utf8 "encrypt") ret (.error .invalidState) := by
  change ((ret ↦₆₄ errTag) ∗
      ((ret + 8#64) ↦₆₄ speWord 1) ∗
      ((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
      ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((ret + 40#64) ↦₆₄ roPtr) ∗
      ((ret + 48#64) ↦₆₄ 7#64) ∗
      memRegion (ret + 56#64) 64 ∗
      vecU8Buf A cap ptr bs ∗
      (roPtr ↦ᵣ utf8 "encrypt")) ⊢
    signalMessageResultAt A (utf8 "encrypt") ret (.error .invalidState)
  unfold signalMessageResultAt errResultAt speAt strRefAt
  have hvec :
      (((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
        ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs) ⊢
      (∃∗ bs' : List (BitVec 8), vecU8 A (ret + 8#64 + 8#64) bs') := by
    refine Entails.sepExists_right bs ?_
    unfold vecU8
    refine Entails.sepExists_right cap ?_
    refine Entails.sepExists_right ptr ?_
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc]
    exact Entails.refl _
  have hstr :
      (((ret + 40#64) ↦₆₄ roPtr) ∗
        ((ret + 48#64) ↦₆₄ 7#64) ∗
        (roPtr ↦ᵣ utf8 "encrypt")) ⊢
      (∃∗ p : BitVec 64,
        ((ret + 8#64 + 32#64) ↦₆₄ p) ∗
          ((ret + 8#64 + 32#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "encrypt").length) ∗
          (p ↦ᵣ utf8 "encrypt")) := by
    refine Entails.sepExists_right roPtr ?_
    have hlen : BitVec.ofNat 64 (utf8 "encrypt").length = 7#64 := by decide +kernel
    simp only [hlen, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _
  have hpull :
      ((ret ↦₆₄ errTag) ∗
        ((ret + 8#64) ↦₆₄ speWord 1) ∗
        ((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
        ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ret + 40#64) ↦₆₄ roPtr) ∗
        ((ret + 48#64) ↦₆₄ 7#64) ∗
        memRegion (ret + 56#64) 64 ∗
        vecU8Buf A cap ptr bs ∗
        (roPtr ↦ᵣ utf8 "encrypt")) =
      ((ret ↦₆₄ errTag) ∗
        (((ret + 8#64) ↦₆₄ speWord 1) ∗
          (((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
            ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            vecU8Buf A cap ptr bs) ∗
          (((ret + 40#64) ↦₆₄ roPtr) ∗
            ((ret + 48#64) ↦₆₄ 7#64) ∗
            (roPtr ↦ᵣ utf8 "encrypt"))) ∗
        memRegion (ret + 56#64) 64) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono hvec hstr)))

abbrev lsAesEncSym : String :=
  "_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_encrypt"

abbrev lsFormatInnerSym : String :=
  "_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_inner"

abbrev lsSpqrSendCoinsName : String :=
  "spqr::send::<libsignal_cli_ratchet::Coins>"

abbrev lsOtrEncryptRoSym : String :=
  "libsignal_session:.rodata..Lanon.81"

abbrev lsOtrEncryptCoinsRoSym : String :=
  "libsignal_cli_ratchet:.rodata..Lanon.81"

theorem lsroCheck_otrEncryptRoSym : lsroCheck lsOtrEncryptRoSym (utf8 "encrypt") = true := by
  decide +kernel

theorem lsroCheck_otrEncryptCoinsRoSym :
    lsroCheck lsOtrEncryptCoinsRoSym (utf8 "encrypt") = true := by
  decide +kernel

theorem aesEnc_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {C : Crypto} {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsAesEncSym) (aesEncSpec C.E A) :=
  keys_ls_hook_ok_of_mem h_aes (by decide) hi hunmut

theorem formatInner_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsFormatInnerSym) (formatInnerSpec A) :=
  keys_ls_hook_ok_of_mem h_fmt (by decide) hi hunmut

theorem dealloc_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSym) (rustDeallocSpec A) :=
  keys_ls_hook_ok_of_mem h_dealloc (by decide) hi hunmut

end CryptoVerification.LibsignalTripleRatchet.Encrypt
