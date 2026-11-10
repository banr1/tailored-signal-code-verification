/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKey
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeys
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepMain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecv
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Root
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Proofs.TripleRatchet.Mac.Verify
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStep -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDerive -- shake: keep

/-!
# Assembly of `try_decrypt_with_state`

Discharges the 16 callee contracts (`tryDecryptCallees`) of `try_decrypt_with_state` and composes
them with the front and error-tail segments (`tryDecrypt_run_of_back`), plus empty-state and SPQR v1
specializations.
-/

@[expose] public section

open Arm64 CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

namespace CryptoVerification.LibsignalTripleRatchet.DecryptAssembly

theorem tryDecryptCallees (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    Decrypt.TryDecryptCallees img C A ctl uuidTryParse abs where
  localIk := Getters.local_identity_key_ok _ _ _ _ _ himg
  remoteIk := Glue.remoteIdentityKeyOk _ _ _ _ _ himg
  sameAcc := Glue.is_same_account_ok _ _ _ _
  clearUpk := Glue.clear_unacknowledged_pre_key_message_ok_of_tripleRatchetHooks hH
  dropChain := Glue.drop_chain_ok_of_tripleRatchetHooks hH
  chainKeyToPb := Glue.chain_key_to_pb_ok_of_tripleRatchetHooks hH
  derivePk := derive_public_key_bytes_ok
  trFrom := ReceiveRatchetFrom.trFrom_ok himg hH (Glue.deserializeOk _ _ _ _)
    (Glue.remoteIdentityKeyOk _ _ _ _ _ himg) (Glue.dropSpeOk_of_tripleRatchetHooks himg hH)
    (Glue.drop_vec_chain_ok_of_tripleRatchetHooks hH)
  trApply := ReceiveRatchetApply.trApply_ok hH (Glue.publicKeySerializeOk_of_tripleRatchetHooks hH)
    (Glue.drop_vec_message_key_ok_of_tripleRatchetHooks hH) (Glue.drop_vec_chain_ok_of_tripleRatchetHooks hH)
  findReceiverChainKey := Glue.findReceiverChainKeyOk himg
  createChain := Keys.createChain_ok himg (Glue.ctEqROOk _ _ _ _)
    (extract_ok img C ctl abs (Glue.newFromSliceOk himg))
    (expand_multi_info_ok img.base C ctl abs) hH.alloc
  genKeys := Keys.generateKeys_ok himg (extract_ok img C ctl abs (Glue.newFromSliceOk himg))
    (expand_multi_info_ok img.base C ctl abs) hH.alloc
  pkSer := Glue.publicKeySerializeOk_of_tripleRatchetHooks hH
  verifyMac := verifyMacWithAddresses_subroutine_ok img himg C A ctl abs hH.alloc
    (Glue.newFromSliceOk himg) (Glue.publicKeySerializeOk_of_tripleRatchetHooks hH)
  cmk := ConsumeMessageKeyTransfer.cmk_ok himg hH.alloc
  growOne := ConsumeMessageKeyTransfer.growOneChain_ok himg hH.alloc


end CryptoVerification.LibsignalTripleRatchet.DecryptAssembly

namespace CryptoVerification.LibsignalTripleRatchet.DecryptAssembly

theorem tryDecrypt_run_of_back (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hs7 : Decrypt.VerifyMacSpec img C A ctl uuidTryParse S abs)
    (hs8 : Decrypt.AesDecryptSpec img C A ctl uuidTryParse S abs)
    (hs9 : Decrypt.ApplyRatchetSpec img C A ctl uuidTryParse S abs) :
    TryDecryptRunStmt C A ctl S abs img :=
  Decrypt.tryDecrypt_run_of_seams C A ctl S abs img
    (fun hH himg => tryDecryptCallees C A ctl S abs img hH himg)
    Decrypt.ChainLookup.identityKeys_ok Decrypt.ChainLookup.loadRatchet_ok Decrypt.ChainLookup.findChain_ok
    (Decrypt.DhStep.dhStep_ok img C A ctl S abs)
    (Decrypt.KeyDerive.consumeMsgKey_ok img C A ctl S abs)
    (Decrypt.KeyDerive.pqRecv_ok img C A ctl S abs)
    (Decrypt.KeyDerive.deriveKeys_ok img C A ctl abs)
    hs7 hs8 hs9
    Decrypt.ChainLookup.errTail_ok

/-- `tryDecrypt_run_of_back` on an empty pq state: `TryDecryptEmptyRunStmt` from the empty-state recv
contract (`SpqrRecvEmptyRunStmt`) instead of `SpqrRecvOk`. -/
theorem tryDecryptEmpty_run_of_back (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hrecvEmpty : SpqrRecvEmptyRunStmt C A ctl S abs img)
    (hs7 : Decrypt.VerifyMacSpec img C A ctl uuidTryParse S abs)
    (hs8 : Decrypt.AesDecryptSpec img C A ctl uuidTryParse S abs)
    (hs9 : Decrypt.ApplyRatchetSpec img C A ctl uuidTryParse S abs) :
    TryDecryptEmptyRunStmt C A ctl S abs img :=
  Decrypt.tryDecryptEmpty_run_of_seams C A ctl S abs img hrecvEmpty
    (fun hH himg => tryDecryptCallees C A ctl S abs img hH himg)
    Decrypt.ChainLookup.identityKeys_ok Decrypt.ChainLookup.loadRatchet_ok Decrypt.ChainLookup.findChain_ok
    (Decrypt.DhStep.dhStep_ok img C A ctl S abs)
    (Decrypt.KeyDerive.consumeMsgKey_ok img C A ctl S abs)
    (Decrypt.KeyDerive.pqRecv_ok img C A ctl S abs)
    (Decrypt.KeyDerive.deriveKeys_ok img C A ctl abs)
    hs7 hs8 hs9
    Decrypt.ChainLookup.errTail_ok

/-- Specialization of `tryDecrypt_run_of_back` to SPQR v1 states via `SpqrRecvV1Stmt`. -/
theorem tryDecryptV1_run_of_back (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hrecvV1 : LibsignalSpqrV1.SpqrRecvV1Stmt C A ctl K abs img)
    (hs7 : Decrypt.VerifyMacSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs8 : Decrypt.AesDecryptSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs9 : Decrypt.ApplyRatchetSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs) :
    LibsignalSpqrV1.TryDecryptV1RunStmt C A ctl K abs img :=
  Decrypt.tryDecryptV1_run_of_seams C A ctl K abs img hrecvV1
    (fun hH himg => tryDecryptCallees C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg)
    Decrypt.ChainLookup.identityKeys_ok Decrypt.ChainLookup.loadRatchet_ok
    Decrypt.ChainLookup.findChain_ok
    (Decrypt.DhStep.dhStep_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (Decrypt.KeyDerive.consumeMsgKey_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (Decrypt.KeyDerive.pqRecv_okQF img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (Decrypt.KeyDerive.deriveKeys_ok img C A ctl abs)
    hs7 hs8 hs9
    Decrypt.ChainLookup.errTail_ok


end CryptoVerification.LibsignalTripleRatchet.DecryptAssembly
