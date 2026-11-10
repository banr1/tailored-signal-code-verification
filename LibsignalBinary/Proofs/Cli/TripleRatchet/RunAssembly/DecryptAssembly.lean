/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Root
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.FindChain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ConsumeMsgKey
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DeriveKeys
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepMain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.PqRecv
import LibsignalBinary.Proofs.Cli.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Proofs.TripleRatchet.Mac.Verify
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main

/-!
# Top-Level `try_decrypt_with_state` Assembly for the CLI Image

Assembles `DecryptCallees` and the front/back decrypt segment proofs into `TryDecryptRunStmt`,
`TryDecryptEmptyRunStmt`, and `TryDecryptV1RunStmt` for the CLI image.
-/

@[expose] public section

open Arm64 CryptoGames.LibsignalSession CryptoVerification.RustHeap

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

namespace CryptoVerification.LibsignalTripleRatchet.DecryptAssembly

local instance instHkdfHooks_decryptAssembly_trap (C : Crypto) (abs : String → Option (State → State)) :
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

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptCallees_trap
    (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptCallees_trap img C A uuidTryParse abs where
  localIk := Getters.local_identity_key_ok_trap img C A abs himg
  remoteIk := Glue.remoteIdentityKeyOk_trap img C A abs himg
  sameAcc := Glue.is_same_account_ok_trap img.base C abs
  clearUpk := Glue.clear_unacknowledged_pre_key_message_ok_of_tripleRatchetHooks_trap hH
  dropChain := CryptoVerification.Cli.LibsignalTripleRatchet.Glue.drop_chain_ok_of_tripleRatchetHooks_trap hH
  chainKeyToPb := Glue.chain_key_to_pb_ok_of_tripleRatchetHooks_trap hH
  derivePk := derive_public_key_bytes_ok_trap
  trFrom := ReceiveRatchetFrom.trFrom_ok_ext himg
    (AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hH.alloc)
    (Glue.deserializeOk_trap img.base C abs)
    (Glue.remoteIdentityKeyOk_trap img C A abs himg)
    (Glue.dropSpeOk_of_tripleRatchetHooks_trap himg hH)
    (Glue.drop_vec_chain_ok_of_tripleRatchetHooks_trap hH)
  trApply := ReceiveRatchetApply.trApply_ok_ext
    (AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hH.alloc)
    (Glue.publicKeySerializeOk_of_tripleRatchetHooks_trap hH)
    (Glue.drop_vec_message_key_ok_of_tripleRatchetHooks_trap hH)
    (Glue.drop_vec_chain_ok_of_tripleRatchetHooks_trap hH)
  findReceiverChainKey := Glue.findReceiverChainKeyOk_trap himg
  createChain := Keys.createChain_ok_of_contracts himg
    (Keys.calculateAgreement_ok_trap himg (ConsumeMessageKeyTransfer.ctEqRO_ok_trap img.base C abs) hH.alloc)
    (extract_ok_ext img C (trTrapExterns C abs) (Glue.newFromSliceOk_trap himg))
    (expand_multi_info_ok_ext img.base C (trTrapExterns C abs))
    ((AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hH.alloc).dealloc_ok_at createChainName
      (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"))
      (by rw [(ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"),
            (ls_stub% "__rustc::__rust_dealloc")]))
  genKeys := Keys.generateKeys_ok_ext himg
    (extract_ok_ext img C (trTrapExterns C abs) (Glue.newFromSliceOk_trap himg))
    (expand_multi_info_ok_ext img.base C (trTrapExterns C abs))
    (AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hH.alloc)
  pkSer := Glue.publicKeySerializeOk_of_tripleRatchetHooks_trap hH
  verifyMac := verifyMacWithAddresses_subroutine_ok_trap img himg C A abs hH.alloc
    (Glue.newFromSliceOk_trap himg) (Glue.publicKeySerializeOk_of_tripleRatchetHooks_trap hH)
  cmk := ConsumeMessageKeyTransfer.cmk_ok_trap himg hH.alloc
  growOne := ConsumeMessageKeyTransfer.growOneChain_ok_trap himg hH.alloc

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptCallees (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptCallees img C A ctl uuidTryParse abs :=
  let hc := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptCallees_trap C A S abs img hH himg
  { localIk := subroutine_ok_kit_of_trTrap hc.localIk
    remoteIk := subroutine_ok_kit_of_trTrap hc.remoteIk
    sameAcc := subroutine_ok_kit_of_trTrap hc.sameAcc
    clearUpk := subroutine_ok_kit_of_trTrap hc.clearUpk
    dropChain := subroutine_ok_kit_of_trTrap hc.dropChain
    chainKeyToPb := subroutine_ok_kit_of_trTrap hc.chainKeyToPb
    derivePk := subroutine_ok_kit_of_trTrap hc.derivePk
    trFrom := subroutine_ok_kit_of_trTrap hc.trFrom
    trApply := subroutine_ok_kit_of_trTrap hc.trApply
    findReceiverChainKey := subroutine_ok_kit_of_trTrap hc.findReceiverChainKey
    createChain := subroutine_ok_kit_of_trTrap hc.createChain
    genKeys := subroutine_ok_kit_of_trTrap hc.genKeys
    pkSer := subroutine_ok_kit_of_trTrap hc.pkSer
    verifyMac := subroutine_ok_kit_of_trTrap hc.verifyMac
    cmk := subroutine_ok_kit_of_trTrap hc.cmk
    growOne := subroutine_ok_kit_of_trTrap hc.growOne }

end CryptoVerification.LibsignalTripleRatchet.DecryptAssembly

/-! ## Top-Level `try_decrypt_with_state` Run Theorems -/

namespace CryptoVerification.LibsignalTripleRatchet.DecryptAssembly

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecrypt_run_of_back (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacSpec img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptSpec img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetSpec img C A ctl uuidTryParse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptRunStmt C A ctl S abs img :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecrypt_run_of_seams C A ctl S abs img
    (fun hH himg => CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptCallees C A ctl S abs img hH himg)
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_ok CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_ok CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.pqRecv_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.deriveKeys_ok img C A ctl abs)
    hs7 hs8 hs9
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecrypt_run_of_back_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacSpec_trap img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptSpec_trap img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetSpec_trap img C A ctl uuidTryParse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptRunStmt_trap C A ctl S abs img :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecrypt_run_of_seams_trap C A ctl S abs img
    (fun hH himg => CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptCallees_trap C A S abs img hH himg)
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_ok_trap
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_ok_trap
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok_trap
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_ok_trap img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok_trap img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.pqRecv_ok_trap img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.deriveKeys_ok_trap img C A ctl abs)
    hs7 hs8 hs9
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok_trap

/-- Empty-PQ specialization of `tryDecrypt_run_of_back`: establishes `TryDecryptEmptyRunStmt` from
`SpqrRecvEmptyRunStmt` without `SpqrRecvOk`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptEmpty_run_of_back (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hrecvEmpty : SpqrRecvEmptyRunStmt C A ctl S abs img)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacSpec img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptSpec img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetSpec img C A ctl uuidTryParse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptEmptyRunStmt C A ctl S abs img :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEmpty_run_of_seams C A ctl S abs img hrecvEmpty
    (fun hH himg => CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptCallees C A ctl S abs img hH himg)
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_ok CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_ok CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.pqRecv_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.deriveKeys_ok img C A ctl abs)
    hs7 hs8 hs9
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptEmpty_run_of_back_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hrecvEmpty : SpqrRecvEmptyRunStmt_trap C A S abs img)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacSpec_trap img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptSpec_trap img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetSpec_trap img C A ctl uuidTryParse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptEmptyRunStmt_trap C A ctl S abs img :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEmpty_run_of_seams_trap C A ctl S abs img hrecvEmpty
    (fun hH himg => CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptCallees_trap C A S abs img hH himg)
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_ok_trap
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_ok_trap
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok_trap
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_ok_trap img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok_trap img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.pqRecv_ok_trap img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.deriveKeys_ok_trap img C A ctl abs)
    hs7 hs8 hs9
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok_trap

/-- SPQR v1 specialization of `tryDecrypt_run_of_back`: establishes `TryDecryptV1RunStmt` from
`SpqrRecvV1Stmt` without `SpqrRecvOk`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptV1_run_of_back (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hrecvV1 : LibsignalSpqrV1.SpqrRecvV1Stmt C A ctl K abs img)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs) :
    CryptoVerification.Cli.LibsignalSpqrV1.TryDecryptV1RunStmt C A ctl K abs img :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptV1_run_of_seams C A ctl K abs img hrecvV1
    (fun hH himg => CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptCallees C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg)
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_ok CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_ok
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.pqRecv_okQF img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.deriveKeys_ok img C A ctl abs)
    hs7 hs8 hs9
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptV1_run_of_back_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hrecvV1 : LibsignalSpqrV1.SpqrRecvV1Stmt_trap C A K abs img)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacSpec_trap img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptSpec_trap img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetSpec_trap img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs) :
    CryptoVerification.Cli.LibsignalSpqrV1.TryDecryptV1RunStmt_trap C A ctl K abs img :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptV1_run_of_seams_trap C A ctl K abs img hrecvV1
    (fun hH himg => CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptCallees_trap C A (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg)
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_ok_trap
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_ok_trap
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok_trap
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_ok_trap img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok_trap img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.pqRecv_okQF_trap img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.deriveKeys_ok_trap img C A ctl abs)
    hs7 hs8 hs9
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok_trap

end CryptoVerification.LibsignalTripleRatchet.DecryptAssembly
