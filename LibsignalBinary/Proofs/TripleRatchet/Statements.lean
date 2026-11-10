/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Root
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Compute
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Verify
public import LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddresses
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecrypt
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchet
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKey
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeys
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepMain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecv
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Root
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMac
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Root
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.InImage.Spqr
import LibsignalBinary.Proofs.TripleRatchet.InImage.Uuid
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Proofs.TripleRatchet.Mac.Addresses
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main
import LibsignalBinary.Proofs.TripleRatchet.Record.SegClone
import LibsignalBinary.Proofs.TripleRatchet.RunAssembly.DecryptAssembly
import LibsignalBinary.Proofs.TripleRatchet.RunAssembly.RecordAssembly
import LibsignalBinary.Proofs.TripleRatchet.RunAssembly.TryFromAssembly
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Core
import LibsignalBinary.Proofs.TripleRatchet.Wire.New

/-!
# Top-Level Binary Refinement Theorems for Triple-Ratchet Session Entry Points

Composes the assembled subroutine and region proofs to establish the top-level specifications of
`Specifications/LibsignalTripleRatchet.lean` for session encryption (`otrFrom_run`, `otrEncrypt_run`,
`otrApply_run`), message parsing (`tryFrom_run`), state and record decryption (`tryDecrypt_run`,
`recordDecrypt_run`), and their empty-state and SPQR v1 specializations.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Statements

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- The 16 callee contracts of `try_decrypt_with_state` (`TryDecryptCalleesExt`) on `tripleRatchetProgAtExt`,
discharged from proved lemmas. -/
theorem tryDecryptCallees_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs ext : String → Option (State → State))
    (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    [HkdfHooks C.F ext]
    (hA : AllocHooks A abs)
    (hle : ∀ n f,
      Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics ext n = some f)
    (h_bb : Rust.withPanics ext "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook)
    (himg : Obj.Loads libsignalSessionImage img) :
    Decrypt.TryDecryptCalleesExt img C A uuidTryParse ext where
  localIk := Getters.local_identity_key_ok_ext _ _ _ (pkTryFrom_ok_ext img ext himg)
  remoteIk := Glue.remoteIdentityKeyOk_ext _ _ _ himg
  sameAcc := Glue.is_same_account_ok_ext _ h_bb
  clearUpk := Glue.clear_unacknowledged_pre_key_message_ok_of_tripleRatchetHooks_ext hC
  dropChain := Glue.drop_chain_ok_of_tripleRatchetHooks_ext hC
  chainKeyToPb := Glue.chain_key_to_pb_ok_of_tripleRatchetHooks_ext hC
  derivePk := derive_public_key_bytes_ok_ext hC
  trFrom := ReceiveRatchetFrom.trFrom_ok_ext himg hC.toAllocContracts (Glue.deserializeOk_ext _ _)
    (Glue.remoteIdentityKeyOk_ext _ _ _ himg) (Glue.dropSpeOk_of_tripleRatchetHooks_ext himg hC)
    (Glue.drop_vec_chain_ok_of_tripleRatchetHooks_ext hC)
  trApply := ReceiveRatchetApply.trApply_ok_ext hC.toAllocContracts
    (Glue.publicKeySerializeOk_of_tripleRatchetHooks_ext hC)
    (Glue.drop_vec_message_key_ok_of_tripleRatchetHooks_ext hC) (Glue.drop_vec_chain_ok_of_tripleRatchetHooks_ext hC)
  findReceiverChainKey := Glue.findReceiverChainKeyOk_ext hle himg
  createChain := Keys.createChain_ok_ext himg (ConsumeMessageKeyTransfer.ctEqRO_ok_ext img.base h_bb)
    (extract_ok_ext img C ext (ConsumeMessageKeyTransfer.new_from_slice_ok_ext img C.F himg hle))
    (expand_multi_info_ok_ext img.base C ext) hC
  genKeys := Keys.generateKeys_ok_ext himg
    (extract_ok_ext img C ext (ConsumeMessageKeyTransfer.new_from_slice_ok_ext img C.F himg hle))
    (expand_multi_info_ok_ext img.base C ext) hC.toAllocContracts
  pkSer := Glue.publicKeySerializeOk_of_tripleRatchetHooks_ext hC
  verifyMac := verifyMacWithAddresses_subroutine_ok_ext img himg C A ctl S ext hC
    (ConsumeMessageKeyTransfer.new_from_slice_ok_ext img C.F himg hle) (Glue.publicKeySerializeOk_of_tripleRatchetHooks_ext hC)
  cmk := ConsumeMessageKeyTransfer.cmk_ok_ext himg hA hle
  growOne := ConsumeMessageKeyTransfer.growOneChain_ok_ext himg hA hle

/-- `try_decrypt_with_state::<HookRng>` meets `tryDecryptSpec` on `tripleRatchetProgAtExt`,
given the unrestricted `spqr::recv` contract `hrecv`. -/
theorem tryDecrypt_run_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs ext : String → Option (State → State))
    (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hrecv : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName) (spqrRecvSpec A S img))
    [HkdfHooks C.F ext]
    (hA : AllocHooks A abs)
    (hle : ∀ n f,
      Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics ext n = some f)
    (h_bb : Rust.withPanics ext "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (Decrypt.tryDecryptEntry img)
      (tryDecryptSpec C A ctl uuidTryParse S img) := by
  rw [ofImage_eq_tripleRatchetProgAtExt ext himg]
  exact Decrypt.try_decrypt_ok_of_seams_ext himg hC
    (tryDecryptCallees_ext C A ctl S abs ext img hC hA hle h_bb himg)
    Decrypt.ChainLookup.identityKeys_ok_ext Decrypt.ChainLookup.loadRatchet_ok_ext Decrypt.ChainLookup.findChain_ok_ext
    (Decrypt.DhStep.s3_ok_ext img C A ctl S ext)
    (Decrypt.KeyDerive.consumeMsgKey_ok_ext img C A ctl S ext)
    (Decrypt.KeyDerive.pqRecv_ok_ext img C A ctl S ext hrecv)
    (Decrypt.KeyDerive.deriveKeys_ok_ext img C A ctl ext)
    (Decrypt.AuthDecrypt.verifyMac_ok_ext img C A ctl S ext)
    (Decrypt.AuthDecrypt.aesDecrypt_ok_ext img C A ctl S ext)
    (Decrypt.AuthDecrypt.applyRatchet_ok_ext img C A ctl S ext)
    Decrypt.ChainLookup.errTail_ok_ext

/-- `try_decrypt_with_state::<HookRng>` meets `tryDecryptSpec`. -/
theorem tryDecrypt_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) :
    TryDecryptRunStmt C A ctl S abs img :=
  DecryptAssembly.tryDecrypt_run_of_back C A ctl S abs img
    (Decrypt.AuthDecrypt.verifyMac_ok img C A ctl S abs) (Decrypt.AuthDecrypt.aesDecrypt_ok img C A ctl S abs)
    (Decrypt.AuthDecrypt.applyRatchet_ok img C A ctl S abs)

/-- The four callee contracts of `OTR::encrypt` on `tripleRatchetProgAtExt`. -/
theorem encryptCallees_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs ext : String → Option (State → State))
    (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    [HkdfHooks C.F ext]
    (hle : ∀ n f,
      Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics ext n = some f)
    (himg : Obj.Loads libsignalSessionImage img) :
    MessageKeysOkExt img C.F A ext ∧ GenerateKeysOkExt img C A ext ∧
      SignalMessageNewOkExt img C A uuidTryParse ext ∧ NextChainKeyOkExt img C.F ext :=
  ⟨Glue.messageKeysOk_of_tripleRatchetHooks_ext hC hle himg,
   Keys.generateKeys_ok_ext himg
     (extract_ok_ext img C ext (ConsumeMessageKeyTransfer.new_from_slice_ok_ext img C.F himg hle))
     (expand_multi_info_ok_ext img.base C ext) hC.toAllocContracts,
   signalMessageNew_ok_ext hC.toAllocContracts (Glue.publicKeySerializeOk_of_tripleRatchetHooks_ext hC)
     (Glue.encodedLenOk_ext _ _ _) (Glue.encode_varint_ok_of_tripleRatchetHooks_ext hC)
     (serializeAddresses_subroutine_ok_ext _ _ _ _ _ _ hC)
     (computeMac_subroutine_ok_ext img C A ctl S ext hC
       (ConsumeMessageKeyTransfer.new_from_slice_ok_ext img C.F himg hle) (Glue.publicKeySerializeOk_of_tripleRatchetHooks_ext hC)),
   Glue.nextChainKeyOk_ext hle himg⟩
/-- `try_decrypt_with_state::<HookRng>` meets `tryDecryptSpec` on an empty PQ state (via `spqrRecvEmpty_run`). -/
theorem tryDecryptEmpty_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) :
    TryDecryptEmptyRunStmt C A ctl S abs img :=
  DecryptAssembly.tryDecryptEmpty_run_of_back C A ctl S abs img
    (spqrRecvEmpty_run C A ctl S abs img)
    (Decrypt.AuthDecrypt.verifyMac_ok img C A ctl S abs) (Decrypt.AuthDecrypt.aesDecrypt_ok img C A ctl S abs)
    (Decrypt.AuthDecrypt.applyRatchet_ok img C A ctl S abs)

instance instHkdfHooks_trap (C : Crypto) (abs : String → Option (State → State)) :
    HkdfHooks C.F (trTrapExterns C abs) where
  memset := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact HkdfHooks.memset (F := C.F) (ext := tripleRatchetExterns C 0#64 abs)
  memcpy := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact HkdfHooks.memcpy (F := C.F) (ext := tripleRatchetExterns C 0#64 abs)
  compress256 := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact HkdfHooks.compress256 (F := C.F) (ext := tripleRatchetExterns C 0#64 abs)

theorem encryptCallees_trap (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    MessageKeysOkExt img C.F A (trTrapExterns C abs) ∧
      GenerateKeysOkExt img C A (trTrapExterns C abs) ∧
      SignalMessageNewOkExt img C A uuidTryParse (trTrapExterns C abs) ∧
      NextChainKeyOkExt img C.F (trTrapExterns C abs) :=
  ⟨Glue.messageKeysOk_of_tripleRatchetHooks_trap hH himg,
   Keys.generateKeys_ok_ext himg
     (extract_ok_ext img C (trTrapExterns C abs) (Glue.newFromSliceOk_trap himg))
     (expand_multi_info_ok_ext img.base C (trTrapExterns C abs))
     (AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hH.alloc),
   signalMessageNew_ok_ext (AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hH.alloc)
     (Glue.publicKeySerializeOk_of_tripleRatchetHooks_trap hH)
     (Glue.encodedLenOk_trap img.base C A abs)
     (Glue.encode_varint_ok_of_tripleRatchetHooks_trap hH)
     (serializeAddresses_subroutine_ok_trap img.base C A abs hH.alloc)
     (computeMac_subroutine_ok_trap img C A abs hH.alloc (Glue.newFromSliceOk_trap himg)
       (Glue.publicKeySerializeOk_of_tripleRatchetHooks_trap hH)),
   Glue.nextChainKeyOk_trap himg⟩

/-- The four callee contracts of `OTR::encrypt` (`message_keys`, `generate_keys`,
`SignalMessage::new`, `next_chain_key`), discharged from proved lemmas given only the hooks and the
image loading. -/
theorem encryptCallees (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    MessageKeysOk img C A ctl abs ∧ GenerateKeysOk img C A ctl abs ∧
      SignalMessageNewOk img C A ctl uuidTryParse abs ∧ NextChainKeyOk img C ctl abs :=
  let ⟨hMK, hGK, hNew, hNCK⟩ := encryptCallees_trap C A S abs img hH himg
  ⟨subroutine_ok_kit_of_trTrap hMK,
   subroutine_ok_kit_of_trTrap hGK,
   subroutine_ok_kit_of_trTrap hNew,
   subroutine_ok_kit_of_trTrap hNCK⟩

/-- `OutgoingTripleRatchet::from_session_state` meets `otrFromSpec` on `tripleRatchetProgAtExt`. -/
theorem otrFrom_run_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img otrFromName) (otrFromSpec A img) :=
  OutgoingRatchet.otrFrom_run_ext A ext img hC.toAllocContracts (Glue.deserializeOk_ext _ _)
    (Glue.remoteIdentityKeyOk_ext _ _ _ himg) (Glue.dropSpeOk_of_tripleRatchetHooks_ext himg hC) himg

theorem otrFrom_run_trap (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) :
    OtrFromRunStmt_trap C A S abs img :=
  fun hH himg => OutgoingRatchet.otrFrom_run_trap C A S abs img
    (Glue.deserializeOk_trap img.base C abs)
    (Glue.remoteIdentityKeyOk_trap img C A abs himg)
    (Glue.dropSpeOk_of_tripleRatchetHooks_trap himg hH) hH himg

/-- `OutgoingTripleRatchet::from_session_state` meets `otrFromSpec`. -/
theorem otrFrom_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) :
    OtrFromRunStmt C A ctl S abs img :=
  fun hH himg => subroutine_ok_prog_kit_of_trTrap himg (otrFrom_run_trap C A S abs img hH himg)

/-- `OutgoingTripleRatchet::encrypt::<HookRng>` meets `otrEncryptSpec` on `tripleRatchetProgAtExt`. -/
theorem otrEncrypt_run_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs ext : String → Option (State → State)) (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    [HkdfHooks C.F ext]
    (hle : ∀ n f,
      Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics ext n = some f)
    (hSend : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName) (spqrSendSpec A ctl S img))
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img otrEncryptName) (otrEncryptSpec C A ctl uuidTryParse S img) :=
  let ⟨hMK, hGK, hNew, hNCK⟩ := encryptCallees_ext C A ctl S abs ext img hC hle himg
  root_of_tripleRatchetProgAtExt himg
    (Encrypt.otrEncrypt_ext_ok C A ctl S ext img hC himg hSend hMK hGK hNew hNCK)

/-- `OutgoingTripleRatchet::encrypt::<HookRng>` meets `otrEncryptSpec` given `SpqrSendOk`. -/
theorem otrEncrypt_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) :
    OtrEncryptRunStmt C A ctl S abs img :=
  fun hH hSend himg =>
    let ⟨hMK, hGK, hNew, hNCK⟩ := encryptCallees C A ctl S abs img hH himg
    Encrypt.otrEncrypt_run C A ctl S abs img hMK hGK hNew hNCK hH hSend himg

/-- `OutgoingTripleRatchet::apply_to_session_state` meets `otrApplySpec` on `tripleRatchetProgAtExt`. -/
theorem otrApply_run_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img otrApplyName) (otrApplySpec A img) :=
  OutgoingRatchet.otrApply_run_ext A ext img hC.toAllocContracts himg

theorem otrApply_run_trap (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) :
    OtrApplyRunStmt_trap C A S abs img :=
  OutgoingRatchet.otrApply_run_trap C A S abs img

/-- `OutgoingTripleRatchet::apply_to_session_state` meets `otrApplySpec`. -/
theorem otrApply_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) :
    OtrApplyRunStmt C A ctl S abs img :=
  fun hH himg => subroutine_ok_prog_kit_of_trTrap himg (otrApply_run_trap C A S abs img hH himg)

/-- `<SignalMessage as TryFrom<&[u8]>>::try_from` meets `tryFromSpec` on `tripleRatchetProgAtExt`. -/
theorem tryFrom_run_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img tryFromName) (tryFromSpec A img) :=
  TryFromAssembly.tryFrom_run_ext hC himg

/-- `<SignalMessage as TryFrom<&[u8]>>::try_from` meets `tryFromSpec`. -/
theorem tryFrom_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) :
    TryFromRunStmt C A ctl S abs img :=
  TryFromAssembly.tryFrom_run_closed C A ctl S abs img

/-- `spqr::send::<HookRng>` meets `spqrSendEmptySpec` on `tripleRatchetProgAtExt`. -/
theorem spqrSendEmpty_run_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hEmpty : S.SendEmptyOk)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img spqrSendName) (spqrSendEmptySpec A ctl S img) :=
  root_of_tripleRatchetProgAtExt himg (SpqrSendEmpty.spqrSendEmpty_base_ext C A ctl S ext img hC hEmpty)

/-- `spqr::send::<HookRng>` meets `spqrSendEmptySpec` on an empty PQ state under `SpqrModel.SendEmptyOk`. -/
theorem spqrSendEmpty_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) :
    SpqrSendEmptyRunStmt C A ctl S abs img :=
  SpqrSendEmpty.spqrSendEmpty_run' C A ctl S abs img

/-- `OutgoingTripleRatchet::encrypt::<HookRng>` meets `otrEncryptSpec` on an empty PQ state (`tripleRatchetProgAtExt`). -/
theorem otrEncryptEmpty_run_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs ext : String → Option (State → State))
    (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    [HkdfHooks C.F ext]
    (hle : ∀ n f,
      Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics ext n = some f)
    (hEmpty : S.SendEmptyOk)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img otrEncryptName)
      { otrEncryptSpec C A ctl uuidTryParse S img with
        pre := fun x s => ⌜x.ot.pqrState = []⌝ ∗ (otrEncryptSpec C A ctl uuidTryParse S img).pre x s } :=
  let ⟨hMK, hGK, hNew, hNCK⟩ := encryptCallees_ext C A ctl S abs ext img hC hle himg
  root_of_tripleRatchetProgAtExt himg
    (Encrypt.otrEncryptEmpty_ext_ok C A ctl S ext img hC hEmpty himg hMK hGK hNew hNCK)

/-- `OutgoingTripleRatchet::encrypt::<HookRng>` meets `otrEncryptSpec` on an empty PQ state (via `spqrSendEmpty_run`). -/
theorem otrEncryptEmpty_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) :
    OtrEncryptEmptyRunStmt C A ctl S abs img :=
  fun hH hEmpty himg =>
    let ⟨hMK, hGK, hNew, hNCK⟩ := encryptCallees C A ctl S abs img hH himg
    Encrypt.otrEncryptEmpty_run C A ctl S abs img hMK hGK hNew hNCK hH hEmpty himg

/-- The `try_decrypt_from_record` region of `message_decrypt_signal::<HookRng>` meets `recordDecryptSpec`. -/
theorem recordDecrypt_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) :
    RecordDecryptRunStmt C A ctl S abs img :=
  RecordAssembly.recordDecrypt_run_of_clone C A ctl S abs img Record.segClone_ok

/-- The `try_decrypt_from_record` region meets `recordDecryptSpec` when the active session's PQ state is empty. -/
theorem recordDecryptEmpty_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) :
    RecordDecryptEmptyRunStmt C A ctl S abs img :=
  RecordAssembly.recordDecryptEmpty_run_of_clone C A ctl S abs img
    (spqrRecvEmpty_run C A ctl S abs img) Record.segClone_ok

theorem recordDecrypt_vregs_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : SpqrRecvOk C A ctl S abs img)
    (hloads : Obj.Loads libsignalSessionImage img) :
    region_ok (tripleRatchetProgAt img.base C ctl abs) (recordRegionEntry img) (recordRegionExit img)
      ((recordDecryptSpec C A ctl uuidTryParse S img).withVRegs.restrictPre (fun _ => True)) :=
  RecordAssembly.recordDecrypt_vregs_run_of_clone C A ctl S abs img Record.segClone_ok hhooks hrecv hloads

theorem recordDecryptEmpty_vregs_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hhooks : TripleRatchetHooks C A S abs)
    (hempty : S.RecvEmptyOk)
    (hloads : Obj.Loads libsignalSessionImage img) :
    region_ok (tripleRatchetProgAt img.base C ctl abs) (recordRegionEntry img) (recordRegionExit img)
      ((recordDecryptSpec C A ctl uuidTryParse S img).withVRegs.restrictPre (·.st.pqRatchetState = [])) :=
  RecordAssembly.recordDecryptEmpty_vregs_run_of_clone C A ctl S abs img
    (spqrRecvEmpty_run C A ctl S abs img) Record.segClone_ok hhooks hempty hloads

/-- `try_decrypt_with_state::<HookRng>` meets `tryDecryptSpecT` on SPQR v1 states via `SpqrRecvV1Stmt`. -/
theorem tryDecryptV1_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image)
    (hrecvV1 : LibsignalSpqrV1.SpqrRecvV1Stmt C A ctl K abs img) :
    LibsignalSpqrV1.TryDecryptV1RunStmt C A ctl K abs img :=
  DecryptAssembly.tryDecryptV1_run_of_back C A ctl K abs img hrecvV1
    (Decrypt.AuthDecrypt.verifyMac_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (Decrypt.AuthDecrypt.aesDecrypt_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (Decrypt.AuthDecrypt.applyRatchet_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)

/-- `OutgoingTripleRatchet::encrypt::<HookRng>` meets `otrEncryptSpecT` on SPQR v1 states via `SpqrSendV1Stmt`. -/
theorem otrEncryptV1_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image)
    (hSendV1 : LibsignalSpqrV1.SpqrSendV1Stmt C A ctl K abs img) :
    LibsignalSpqrV1.OtrEncryptV1RunStmt C A ctl K abs img :=
  fun hH hSpqr himg =>
    let ⟨hMK, hGK, hNew, hNCK⟩ :=
      encryptCallees C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg
    Encrypt.otrEncryptV1_run C A ctl K abs img hSendV1 hMK hGK hNew hNCK hH hSpqr himg

/-- The `try_decrypt_from_record` region meets `recordDecryptSpecT` on SPQR v1 states via `SpqrRecvV1Stmt`. -/
theorem recordDecryptV1_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image)
    (hrecvV1 : LibsignalSpqrV1.SpqrRecvV1Stmt C A ctl K abs img) :
    LibsignalSpqrV1.RecordDecryptV1RunStmt C A ctl K abs img :=
  RecordAssembly.recordDecryptV1_run_of_clone C A ctl K abs img hrecvV1 Record.segClone_ok

/-! ## Stacked 32-bit `black_box` and `compress256` (`extHookStack = 16384`) corollaries -/

section Ext32Statements

open CryptoVerification.InImageLift
open ProofLib.ProgramReflection

/-- Lift `uuidTryParseCodeSpec uuidTryParse` (`uuidTryParseStack` = 192 B) to
`withStack (uuidTryParseSpec uuidTryParse) hookStack` for `192 ≤ hookStack ≤ 2^64`. -/
theorem uuidTryParseWithStack_of_code {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (h : subroutine_ok P addr (uuidTryParseCodeSpec uuidTryParse))
    (hle : uuidTryParseStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (withStack (uuidTryParseSpec uuidTryParse) hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs, out⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗
        stackAt s0.sp uuidTryParseStack := by
    have h1 := stackAt_split_bottom s0.sp uuidTryParseStack (hookStack - uuidTryParseStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗ R
  have hpre' : s0.mem ⊨ (uuidTryParseCodeSpec uuidTryParse).pre (p, bs, out) s0 ∗ R' := by
    dsimp only [withStack, uuidTryParseCodeSpec, uuidTryParseSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (p, bs, out) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, uuidTryParseCodeSpec, uuidTryParseSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · rcases hpan with ⟨_, hpan_sat⟩
    have h0 : (uuidTryParseCodeSpec uuidTryParse).onPanic (p, bs, out) s0 sf = ⌜False⌝ := rfl
    rw [h0, satisfies_pure_sepConj] at hpan_sat
    exact False.elim hpan_sat.1
  · rcases hex with ⟨code, _, hex_sat⟩ | ⟨_, hoom_sat⟩
    · have h0 : (uuidTryParseCodeSpec uuidTryParse).onExit (p, bs, out) code s0 sf = ⌜False⌝ := rfl
      rw [h0, satisfies_pure_sepConj] at hex_sat
      exact False.elim hex_sat.1
    · have h0 : (uuidTryParseCodeSpec uuidTryParse).onOom (p, bs, out) s0 sf = ⌜False⌝ := rfl
      rw [h0, satisfies_pure_sepConj] at hoom_sat
      exact False.elim hoom_sat.1

/-- Unconditional in-image `<uuid::Uuid>::try_parse` at any `hookStack ≥ 192` (default `extHookStack = 16384`)
on `tripleRatchetProgAtExt img.base ext` for arbitrary `ext`. -/
theorem uuidTryParseWithStack_inImage_ok (img : Obj.Image)
    (ext : String → Option (State → State))
    {hookStack : Nat}
    (hle : uuidTryParseStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName)
      ((withStack (uuidTryParseSpec uuidTryParse) hookStack).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img
    (uuidTryParseWithStack_of_code (uuidTryParse_ok_F img.base (Rust.withPanics ext)) hle hmax)

/-- Lift `HookSat ext compress256Name (withStack (compress256Spec F) extHookStack)`
(definitionally `CliExt.compress256Spec C`) to `inImage img` on `tripleRatchetProgAtExt`. -/
theorem compress256WithStack_inImage_ok_ext32 (img : Obj.Image) (F : ShaCompress)
    {ext : String → Option (State → State)}
    (h_comp : HookSat ext compress256Name (withStack (compress256Spec F) extHookStack)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr compress256Name)
      ((withStack (compress256Spec F) extHookStack).inImage img) := by
  refine subroutine_ok_inImage_of_subroutine_ok img ?_
  have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (k := 0)
    (ls_stub% "sha2::sha256::compress256") (Nat.add_zero _) (by decide)
    (ls_hook% "sha2::sha256::compress256")
    (by simp [Rust.isPanicSymbol]) h_comp
  simpa only [BitVec.add_zero] using h

/-- `SignalMessage::compute_mac` meets `ComputeMacOkX img C A ext` (`16912` B) under
`AllocContractsX img A ext`, `HookSat ext compress256Name ...`, and `NewFromSliceOkExt`. -/
theorem computeMac_subroutine_ok_ext32 (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (h_comp : HookSat ext compress256Name (withStack (compress256Spec C.F) extHookStack))
    (hnew : NewFromSliceOkExt img C ext) :
    ComputeMacOkX img C A ext :=
  computeMac_subroutine_ok_of_contracts_x img C A ext hA
    (compress256WithStack_inImage_ok_ext32 img C.F h_comp)
    hnew
    (public_key_serialize_ok_ext_x hA)

/-- `SignalMessage::verify_mac_with_addresses` meets `VerifyMacWithAddressesOkX img C A uuidTryParse ext`
(`17200` B) under `AllocContractsX`, 32-bit stacked `CliExt.blackBoxSpec`, stacked `compress256Spec`,
and `NewFromSliceOkExt` (`uuidTryParse` and `publicKeySerialize` discharged internally). -/
theorem verifyMacWithAddresses_subroutine_ok_ext32
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (h_bb : HookSat ext blackBoxName CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    (h_comp : HookSat ext compress256Name (withStack (compress256Spec C.F) extHookStack))
    (hnew : NewFromSliceOkExt img C ext) :
    VerifyMacWithAddressesOkX img C A uuidTryParse ext :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_subroutine_ok_ext32 img himg C A ext hA h_bb
    (uuidTryParseWithStack_inImage_ok img ext)
    (computeMac_subroutine_ok_ext32 img C A ext hA h_comp hnew)

/-- Callee stack budget inside `compute_mac` when `Hmac<Sha256>::new_from_slice` also uses
`extHookStack` (`544 + 16384 = 16928` B). -/
abbrev computeMacPkStackExt32 : Nat := newFromSliceStack + extHookStack

/-- Total `compute_mac` stack budget (`16928 + 496 = 17424` B) under stacked `new_from_slice`. -/
abbrev computeMacStackExt32 : Nat := computeMacPkStackExt32 + 496

private theorem stackAt_16928_eq_16416 (sp : BitVec 64) :
    stackAt sp computeMacPkStackExt32 =
      stackAt sp publicKeySerializeStackX ∗ memRegion (sp - 16928#64) 512 := by
  simp only [stackAt, computeMacPkStackExt32, newFromSliceStack, publicKeySerializeStackX, extHookStack]
  rw [show (544 + 2 ^ 14 : Nat) = 512 + (2 ^ 14 + 32) by decide,
    memRegion_split _ 512 (2 ^ 14 + 32) (by decide)]
  have e1 : sp - BitVec.ofNat 64 (512 + (2 ^ 14 + 32)) = sp - 16928#64 := by bv_arith
  have e2 : sp - 16928#64 + BitVec.ofNat 64 512 = sp - BitVec.ofNat 64 (2 ^ 14 + 32) := by bv_arith
  rw [e1, e2, sepConj_comm]

private theorem stackAt_16928_eq_16384 (sp : BitVec 64) :
    stackAt sp computeMacPkStackExt32 =
      stackAt sp extHookStack ∗ memRegion (sp - 16928#64) 544 := by
  simp only [stackAt, computeMacPkStackExt32, newFromSliceStack, extHookStack]
  rw [memRegion_split _ 544 (2 ^ 14) (by decide)]
  have e1 : sp - BitVec.ofNat 64 (544 + 2 ^ 14) = sp - 16928#64 := by bv_arith
  have e2 : sp - 16928#64 + BitVec.ofNat 64 544 = sp - BitVec.ofNat 64 (2 ^ 14) := by bv_arith
  rw [e1, e2, sepConj_comm]

private theorem newFromSlice_at_computeMac_ext32 (img : Obj.Image) (C : Crypto)
    (ext : String → Option (State → State))
    (hnew_x : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr newFromSliceName)
      ((newFromSlicePkStackSpecAt C.F computeMacPkStackExt32).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName +
        bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" -
          ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      ((newFromSlicePkStackSpecAt C.F computeMacPkStackExt32).inImage img) :=
  sub_ok_at_of_fnAddr hnew_x computeMacName
    (num% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" -
      ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
    (by fnoff_eq)

private theorem publicKeySerialize_at_computeMac_ext32 (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName +
        bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
          ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      ((publicKeySerializeSpecAt A computeMacPkStackExt32).inImage img) := by
  have hpk := sub_ok_at_of_fnAddr (public_key_serialize_ok_ext_x hA) computeMacName
    (num% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
      ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
    (by fnoff_eq)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine hpk.mono_outcome x (memRegion (s0.sp - 16928#64) 512 ∗ R) s0 hpc hrun
    (by simpa only [Spec.inImage, publicKeySerializeSpecX, publicKeySerializeSpecAt,
      stackAt_16928_eq_16416, sepConj_assoc] using hpre) hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpan_sat⟩ | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [Spec.inImage, publicKeySerializeSpecX, publicKeySerializeSpecAt,
      stackAt_16928_eq_16416, sepConj_assoc] using hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    simp only [Spec.inImage, publicKeySerializeSpecX, publicKeySerializeSpecAt,
      satisfies_pure_sepConj, sepConj_assoc] at hpan_sat ⊢
    refine ⟨hpan_sat.1, ?_⟩
    have h1 : anyHeap ∗ memRegion (s0.sp - 16928#64) 512 ∗ R ⊢ anyHeap ∗ R := by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)
    exact Satisfies.mono h1 hpan_sat.2
  · rcases hex with ⟨_, _, hfalse⟩ | ⟨_, hfalse⟩
    · simp only [Spec.inImage, publicKeySerializeSpecX, satisfies_pure_sepConj, false_and] at hfalse
    · simp only [Spec.inImage, publicKeySerializeSpecX, satisfies_pure_sepConj, false_and] at hfalse

private theorem memcpy_at_computeMac_ext32 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (sp_cur : BitVec 64)
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")))
      ((session2MemcpyPkStackSpecAt computeMacPkStackExt32 sp_cur).inImage img) := by
  have hm := hA.session_memcpy_region_ok_at computeMacName
    (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
    computeMacPkStackExt32 (by decide) (by decide) (by fnoff_eq)
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, session2MemcpyPkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hsp_eq⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((withStack sessionMemcpyRegionSpec computeMacPkStackExt32).inImage img).pre
      (dst, src, bs) s0 ∗ R := by
    simp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec,
      hsp_eq, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2⟩, hmem⟩
  refine hm.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  unfold SubroutineOutcome at hout ⊢
  simpa only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec,
    session2MemcpyPkStackSpecAt, hsp_eq, satisfies_pure_sepConj, false_and, sepConj_assoc] using hout

private theorem compress256_at_computeMac_ext32 {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} (sp_cur : BitVec 64)
    (h_comp : HookSat ext compress256Name (withStack (compress256Spec F) extHookStack)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName +
        BitVec.ofNat 64 (num% (ls_off% "sha2::sha256::compress256" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")))
      ((session2Compress256PkStackSpecAt F computeMacPkStackExt32 sp_cur).inImage img) := by
  have hc := sub_ok_at_of_fnAddr (compress256WithStack_inImage_ok_ext32 img F h_comp) computeMacName
    (num% (ls_off% "sha2::sha256::compress256" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
    (by fnoff_eq)
  refine subroutine_ok_outcome_intro fun ⟨stA, st, blkA, blk, n⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, session2Compress256PkStackSpecAt, stackAt_16928_eq_16384,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hblk, hsp_eq⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((withStack (compress256Spec F) extHookStack).inImage img).pre
      (stA, st, blkA, blk, n) s0 ∗ (memRegion (sp_cur - 16928#64) 544 ∗ R) := by
    simp only [Spec.inImage, withStack, compress256Spec,
      hsp_eq, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hblk⟩, hmem⟩
  refine hc.mono_outcome (stA, st, blkA, blk, n) (memRegion (sp_cur - 16928#64) 544 ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  unfold SubroutineOutcome at hout ⊢
  simpa only [Spec.inImage, withStack, compress256Spec,
    session2Compress256PkStackSpecAt, hsp_eq, stackAt_16928_eq_16384,
    satisfies_pure_sepConj, false_and, sepConj_assoc] using hout

private theorem dealloc_at_computeMac_ext32 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")))
      ((rustDeallocPkStackSpecAt A computeMacPkStackExt32).inImage img) := by
  have hdeel := hA.dealloc_ok_at (name := computeMacName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
    (by fnoff_eq)
  refine subroutine_ok_outcome_intro fun ⟨p, bs⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ ((rustDeallocExternSpecWithStack A extHookStack).inImage img).pre
      (p, bs.length, 1) s0 ∗ (memRegion (s0.sp - 16928#64) 544 ∗ R) := by
    simp only [Spec.inImage, rustDeallocExternSpecWithStack, rustDeallocPkStackSpecAt,
      stackAt_16928_eq_16384, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hbs⟩, hmem⟩
    have hlay : LayoutOk bs.length 1 := by
      rw [hbs]; exact ⟨by decide, ⟨0, rfl⟩, by decide⟩
    refine ⟨hinv, ⟨hx0, hx1, hx2, hlay⟩, ?_⟩
    have hm : s0.mem ⊨ (p ↦ₛ bs) ∗ (A.pool ∗ A.live p bs.length 1 ∗
        stackAt s0.sp extHookStack ∗ memRegion (s0.sp - 16928#64) 544 ∗ R) := by
      refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hmem
      ac_rfl
    have hm2 := Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion p bs)) hm
    refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hm2
    ac_rfl
  refine hdeel.mono_outcome (p, bs.length, 1) (memRegion (s0.sp - 16928#64) 544 ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  unfold SubroutineOutcome at hout ⊢
  simpa only [Spec.inImage, rustDeallocExternSpecWithStack, rustDeallocPkStackSpecAt,
    stackAt_16928_eq_16384, satisfies_pure_sepConj, false_and, sepConj_assoc] using hout

private theorem memset_at_computeMac_ext32 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (sp_cur : BitVec 64)
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName +
        BitVec.ofNat 64 (num% (ls_off% "memset" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")))
      ((session2MemsetPkStackSpecAt computeMacPkStackExt32 sp_cur).inImage img) := by
  have hm := hA.session_memset_region_ok_at computeMacName
    (num% (ls_off% "memset" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
    computeMacPkStackExt32 (by decide) (by decide) (by fnoff_eq)
  refine subroutine_ok_outcome_intro fun ⟨dst, val, n⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, session2MemsetPkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hsp_eq⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((withStack sessionMemsetRegionSpec computeMacPkStackExt32).inImage img).pre
      (dst, val, n) s0 ∗ R := by
    simp only [Spec.inImage, withStack, sessionMemsetRegionSpec, memsetRegionSpec,
      hsp_eq, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ⟨hx0, ?_, hx2, by rw [← hx2]; exact Nat.le_of_lt (s0.readReg64 .x2).isLt⟩, hmem⟩
    rw [← hx1]; dsimp [State.readReg32]; bv_bits
  refine hm.mono_outcome (dst, val, n) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  unfold SubroutineOutcome at hout ⊢
  simpa only [Spec.inImage, withStack, sessionMemsetRegionSpec, memsetRegionSpec,
    session2MemsetPkStackSpecAt, hsp_eq, satisfies_pure_sepConj, false_and, sepConj_assoc] using hout

/-- `SignalMessage::compute_mac` at `computeMacStackExt32 = 17424` B (when `new_from_slice` also
uses `extHookStack = 16384` B, so `pkStack = 16928` B). -/
theorem computeMac_subroutine_ok_stacked_ext32 (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (h_comp : HookSat ext compress256Name (withStack (compress256Spec C.F) extHookStack))
    (hnew_x : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr newFromSliceName)
      ((newFromSlicePkStackSpecAt C.F computeMacPkStackExt32).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((Mac.VerifyMacWithAddresses.computeMacSpecWithStack C.F A computeMacStackExt32).inImage img) :=
  computeMac_ok_of_hooks_gen computeMacPkStackExt32 (by decide) img C A ext
    (newFromSlice_at_computeMac_ext32 img C ext hnew_x)
    (publicKeySerialize_at_computeMac_ext32 img A ext hA)
    (fun sp_cur => memcpy_at_computeMac_ext32 sp_cur hA)
    (fun sp_cur => compress256_at_computeMac_ext32 sp_cur h_comp)
    (dealloc_at_computeMac_ext32 hA)
    (fun sp_cur => memset_at_computeMac_ext32 sp_cur hA)

/-- `SignalMessage::verify_mac_with_addresses` at `17712` B (`computeMacStackExt32 + 288`), when
`new_from_slice` also uses `extHookStack = 16384` B (`16928` B total in `new_from_slice`), under
`AllocContractsX`, 32-bit stacked `CliExt.blackBoxSpec`, and stacked `compress256Spec`. -/
theorem verifyMacWithAddresses_subroutine_ok_stacked_ext32
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (h_bb : HookSat ext blackBoxName CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    (h_comp : HookSat ext compress256Name (withStack (compress256Spec C.F) extHookStack))
    (hnew_x : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr newFromSliceName)
      ((newFromSlicePkStackSpecAt C.F computeMacPkStackExt32).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((Mac.VerifyMacWithAddresses.verifyMacWithAddressesSpecWithStack img C.F A uuidTryParse computeMacStackExt32).inImage img) :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_subroutine_ok_at_ext32
    computeMacStackExt32 (by decide) (by decide) img C A ext (base_aligned_of_loads himg) hA h_bb
    (uuidTryParseWithStack_inImage_ok img ext)
    (computeMac_subroutine_ok_stacked_ext32 img C A ext hA h_comp hnew_x)

end Ext32Statements

end CryptoVerification.LibsignalTripleRatchet.Statements
