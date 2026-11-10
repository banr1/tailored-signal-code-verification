/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Rodata
import ProofLib.SepLogic.WPp

/-!
# Callee Addresses and `.rodata` Helpers for `OutgoingTripleRatchet::encrypt`

Callee/hook address equalities and `.rodata` `"encrypt"` string-literal lemmas for
`OutgoingTripleRatchet::encrypt::<Coins>` in the CLI image.
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


/-! ## Callee and Hook Address Lemmas -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.spqrSend_addr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% (2 ^ 64 + (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")) := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>"), (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.spqrSend_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName =
      (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% (2 ^ 64 + (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.spqrSend_addr_eq_ext b (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.messageKeys_addr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr messageKeysName =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::message_keys") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")) := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::message_keys"), (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.messageKeys_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr messageKeysName =
      (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::message_keys") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.messageKeys_addr_eq_ext b (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.generateKeys_addr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr generateKeysName =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")) := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys"), (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.generateKeys_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr generateKeysName =
      (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.generateKeys_addr_eq_ext b (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.signalMessageNew_addr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")) := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::new"), (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.signalMessageNew_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName =
      (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.signalMessageNew_addr_eq_ext b (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.nextChainKey_addr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr nextChainKeyName =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")) := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key"), (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.nextChainKey_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr nextChainKeyName =
      (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>")) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.nextChainKey_addr_eq_ext b (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.aesEnc_ok_at_encrypt_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (b : BitVec 64) (hC : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% ((2^64 + ls_off% "signal_crypto::aes_cbc::aes_256_cbc_encrypt" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>") % 2^64)) (aesEncSpec C.E A) :=
  hC.aes_enc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_encrypt" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.aesEnc_ok_at_encrypt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (b : BitVec 64) (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% ((2^64 + ls_off% "signal_crypto::aes_cbc::aes_256_cbc_encrypt" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>") % 2^64)) (aesEncSpec C.E A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.aesEnc_ok_at_encrypt_ext C A ctl S (tripleRatchetExterns C ctl abs) b
    (Stage2Contracts.of_tripleRatchetProgAt b C A ctl S abs hS)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.formatInner_ok_at_encrypt_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (b : BitVec 64) (hC : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% ((2^64 + ls_off% "alloc::fmt::format::format_inner" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>") % 2^64)) (formatInnerSpec A) :=
  hC.format_inner_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.formatInner_ok_at_encrypt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (b : BitVec 64) (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% ((2^64 + ls_off% "alloc::fmt::format::format_inner" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>") % 2^64)) (formatInnerSpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.formatInner_ok_at_encrypt_ext C A ctl S (tripleRatchetExterns C ctl abs) b
    (Stage2Contracts.of_tripleRatchetProgAt b C A ctl S abs hS)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.dealloc_ok_at_encrypt_ext (A : RustAlloc) (ext : String → Option (State → State))
    (b : BitVec 64) (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>") % 2^64)) (rustDeallocSpec A) :=
  hA.dealloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.dealloc_ok_at_encrypt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (b : BitVec 64) (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>") % 2^64)) (rustDeallocSpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.dealloc_ok_at_encrypt_ext A (tripleRatchetExterns C ctl abs) b
    (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hS.alloc)

/-! ## `.rodata` literal `"encrypt"` (`0x4f3ee`, 7 bytes) -/

open ProofLib.ProgramReflection in
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.rodata_0x453ee_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 7 = utf8 "encrypt" := by
  rfl_kernel

namespace EncryptCoreFacts

end EncryptCoreFacts

open ProofLib.ProgramReflection in
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.rodata_encrypt_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556))) ↦ᵣ utf8 "encrypt") ∗ P :=
  EncryptCoreFacts.of_rodata_loads_eq himg
    (secOff := num% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556))) (secLen := 7) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.rodata_0x453ee_eq hro hP

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.rodata_encrypt_sepWPp {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : img.RoDataLoaded s.mem)
    (h : SepWPp prog ret s (((img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556))) ↦ᵣ utf8 "encrypt") ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.rodata_encrypt_intro himg hro hm

/-- Page-aligned `adrp` address relation for the `.rodata` `"encrypt"` literal. -/
structure _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.AdrpFact (entry roBase : BitVec 64) : Prop where
  eq : ((entry + bv% (552) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556) - page% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 500))) =
    roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.adrp_0x453ee_eq (base entry : BitVec 64)
    (halign : base &&& 0xfff#64 = 0#64) (hentry : base + bv% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>") = entry) :
    ((entry + bv% (552) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556) - page% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 500))) = base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556)) := by
  subst hentry
  rw [BitVec.add_assoc, adrp_page_of_aligned halign, BitVec.add_assoc]
  rfl

/-- Folds the `Err(InvalidState("encrypt", msg))` return value written when `spqr::send` returns
`None`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.errResultAt_invalidState_pack (A : RustAlloc) (ret : BitVec 64)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) (roBase entry : BitVec 64)
    (hadrp : ((entry + bv% (552) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556) - page% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 500))) = roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556))) :
    ((ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
      ((ret + 8#64) ↦₆₄ 9223372036854775809#64) ∗
      ((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
      ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((ret + 40#64) ↦₆₄ ((entry + bv% (552) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556) - page% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 500)))) ∗
      ((ret + 48#64) ↦₆₄ 7#64) ∗
      memRegion (ret + 56#64) 64 ∗
      vecU8Buf A cap ptr bs ∗
      ((roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556))) ↦ᵣ utf8 "encrypt")) ⊢
    signalMessageResultAt A (utf8 "encrypt") ret (.error .invalidState) := by
  rw [hadrp]
  change ((ret ↦₆₄ errTag) ∗
      ((ret + 8#64) ↦₆₄ speWord 1) ∗
      ((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
      ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((ret + 40#64) ↦₆₄ (roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556)))) ∗
      ((ret + 48#64) ↦₆₄ 7#64) ∗
      memRegion (ret + 56#64) 64 ∗
      vecU8Buf A cap ptr bs ∗
      ((roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556))) ↦ᵣ utf8 "encrypt")) ⊢
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
      (((ret + 40#64) ↦₆₄ (roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556)))) ∗
        ((ret + 48#64) ↦₆₄ 7#64) ∗
        ((roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556))) ↦ᵣ utf8 "encrypt")) ⊢
      (∃∗ p : BitVec 64,
        ((ret + 8#64 + 32#64) ↦₆₄ p) ∗
          ((ret + 8#64 + 32#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "encrypt").length) ∗
          (p ↦ᵣ utf8 "encrypt")) := by
    refine Entails.sepExists_right (roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556))) ?_
    have hlen : BitVec.ofNat 64 (utf8 "encrypt").length = 7#64 := by decide +kernel
    simp only [hlen, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _
  have hpull :
      ((ret ↦₆₄ errTag) ∗
        ((ret + 8#64) ↦₆₄ speWord 1) ∗
        ((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
        ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ret + 40#64) ↦₆₄ (roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556)))) ∗
        ((ret + 48#64) ↦₆₄ 7#64) ∗
        memRegion (ret + 56#64) 64 ∗
        vecU8Buf A cap ptr bs ∗
        ((roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556))) ↦ᵣ utf8 "encrypt")) =
      ((ret ↦₆₄ errTag) ∗
        (((ret + 8#64) ↦₆₄ speWord 1) ∗
          (((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
            ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            vecU8Buf A cap ptr bs) ∗
          (((ret + 40#64) ↦₆₄ (roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556)))) ∗
            ((ret + 48#64) ↦₆₄ 7#64) ∗
            ((roBase + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 552) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 556))) ↦ᵣ utf8 "encrypt"))) ∗
        memRegion (ret + 56#64) 64) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono hvec hstr)))

end CryptoVerification.LibsignalTripleRatchet.Encrypt
