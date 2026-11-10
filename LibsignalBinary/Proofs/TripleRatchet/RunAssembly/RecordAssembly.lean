/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecrypt
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchet
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMac
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetState
import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.Clone
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Record.SegDecrypt
import LibsignalBinary.Proofs.TripleRatchet.Record.SegExit
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch
import LibsignalBinary.Proofs.TripleRatchet.Record.SegTail
import LibsignalBinary.Proofs.TripleRatchet.RunAssembly.DecryptAssembly

/-!
# Assembly of `try_decrypt_from_record`

Discharges the 6 callee contracts (`recordCallees`) of `try_decrypt_from_record` and composes them
with `tryDecrypt_run_of_back` and the proved record segments (`segDecrypt_ok`, `segMismatch_ok`,
`segTail_ok`, `segExit_ok`), leaving `Record.SegCloneSpec` as a parameter.
-/

@[expose] public section

open Arm64 CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

namespace CryptoVerification.LibsignalTripleRatchet.RecordAssembly

theorem recordCallees (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    Record.RecordCallees img C A ctl abs where
  chainClone := FromRecordChainClone.chain_clone_ok hH.alloc
  senderClone := FromRecordChainClone.senderChain_clone_ok hH.alloc
  dropLocal2 := FromRecordCallees.drop_session_structure_local2_ok hH.alloc (Glue.drop_chain_ok_of_tripleRatchetHooks hH)
  setState := FromRecordCallees.set_session_state_ok
    (FromRecordCallees.drop_session_structure_local1_ok hH.alloc (Glue.drop_vec_message_key_ok_of_tripleRatchetHooks hH)
      (Glue.drop_vec_chain_ok_of_tripleRatchetHooks hH))
  growSpe := FromRecordCallees.grow_one_spe_ok hH.alloc
  closure := FromRecordCallees.log_closure_ok himg

theorem recordDecrypt_run_of_clone (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hclone : Record.SegCloneSpec img C A ctl uuidTryParse S abs) :
    RecordDecryptRunStmt C A ctl S abs img :=
  Record.recordDecrypt_run_of_seams C A ctl S abs img
    (fun hH himg => recordCallees C A ctl S abs img hH himg)
    (DecryptAssembly.tryDecrypt_run_of_back C A ctl S abs img
      (Decrypt.AuthDecrypt.verifyMac_ok img C A ctl S abs) (Decrypt.AuthDecrypt.aesDecrypt_ok img C A ctl S abs)
      (Decrypt.AuthDecrypt.applyRatchet_ok img C A ctl S abs))
    hclone Record.segDecrypt_ok Record.segMismatch_ok Record.segTail_ok Record.segExit_ok

/-- `recordDecrypt_run_of_clone` on an empty pq state: `RecordDecryptEmptyRunStmt` from the
empty-state recv contract (`SpqrRecvEmptyRunStmt`) instead of `SpqrRecvOk`. -/
theorem recordDecryptEmpty_run_of_clone (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hrecvEmpty : SpqrRecvEmptyRunStmt C A ctl S abs img)
    (hclone : Record.SegCloneSpec img C A ctl uuidTryParse S abs) :
    RecordDecryptEmptyRunStmt C A ctl S abs img :=
  Record.recordDecryptEmpty_run_of_seams C A ctl S abs img
    (fun hH himg => recordCallees C A ctl S abs img hH himg)
    (DecryptAssembly.tryDecryptEmpty_run_of_back C A ctl S abs img hrecvEmpty
      (Decrypt.AuthDecrypt.verifyMac_ok img C A ctl S abs) (Decrypt.AuthDecrypt.aesDecrypt_ok img C A ctl S abs)
      (Decrypt.AuthDecrypt.applyRatchet_ok img C A ctl S abs))
    hclone Record.segDecrypt_ok Record.segMismatch_ok Record.segTail_ok Record.segExit_ok

theorem recordDecrypt_vregs_run_of_clone (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hclone : Record.SegCloneSpec img C A ctl uuidTryParse S abs)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : SpqrRecvOk C A ctl S abs img)
    (hloads : Obj.Loads libsignalSessionImage img) :
    region_ok (tripleRatchetProgAt img.base C ctl abs) (recordRegionEntry img) (recordRegionExit img)
      ((recordDecryptSpec C A ctl uuidTryParse S img).withVRegs.restrictPre (fun _ => True)) :=
  Record.recordDecrypt_region_vregs_ok_of_seams (Q := fun _ => True)
    hloads hhooks (recordCallees C A ctl S abs img hhooks hloads)
    (Record.tryDecryptOkAtImageBase_of_run
      (DecryptAssembly.tryDecrypt_run_of_back C A ctl S abs img
        (Decrypt.AuthDecrypt.verifyMac_ok img C A ctl S abs) (Decrypt.AuthDecrypt.aesDecrypt_ok img C A ctl S abs)
        (Decrypt.AuthDecrypt.applyRatchet_ok img C A ctl S abs))
      hhooks hrecv hloads)
    hclone Record.segDecrypt_ok Record.segMismatch_ok Record.segTail_ok Record.segExit_ok

theorem recordDecryptEmpty_vregs_run_of_clone (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hrecvEmpty : SpqrRecvEmptyRunStmt C A ctl S abs img)
    (hclone : Record.SegCloneSpec img C A ctl uuidTryParse S abs)
    (hhooks : TripleRatchetHooks C A S abs)
    (hempty : S.RecvEmptyOk)
    (hloads : Obj.Loads libsignalSessionImage img) :
    region_ok (tripleRatchetProgAt img.base C ctl abs) (recordRegionEntry img) (recordRegionExit img)
      ((recordDecryptSpec C A ctl uuidTryParse S img).withVRegs.restrictPre (·.st.pqRatchetState = [])) :=
  Record.recordDecrypt_region_vregs_ok_of_seams (Q := (· = []))
    hloads hhooks (recordCallees C A ctl S abs img hhooks hloads)
    (Record.tryDecryptOktripleRatchetProgAt_of_emptyRun
      (DecryptAssembly.tryDecryptEmpty_run_of_back C A ctl S abs img hrecvEmpty
        (Decrypt.AuthDecrypt.verifyMac_ok img C A ctl S abs) (Decrypt.AuthDecrypt.aesDecrypt_ok img C A ctl S abs)
        (Decrypt.AuthDecrypt.applyRatchet_ok img C A ctl S abs))
      hhooks hempty hloads)
    hclone Record.segDecrypt_ok Record.segMismatch_ok Record.segTail_ok Record.segExit_ok

/-- Specialization of `recordDecrypt_run_of_clone` to SPQR v1 states via `SpqrRecvV1Stmt`. -/
theorem recordDecryptV1_run_of_clone (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hrecvV1 : LibsignalSpqrV1.SpqrRecvV1Stmt C A ctl K abs img)
    (hclone : Record.SegCloneSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs) :
    LibsignalSpqrV1.RecordDecryptV1RunStmt C A ctl K abs img :=
  Record.recordDecryptV1_run_of_seams C A ctl K abs img
    (fun hH himg => recordCallees C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg)
    (DecryptAssembly.tryDecryptV1_run_of_back C A ctl K abs img hrecvV1
      (Decrypt.AuthDecrypt.verifyMac_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
      (Decrypt.AuthDecrypt.aesDecrypt_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
      (Decrypt.AuthDecrypt.applyRatchet_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs))
    hclone Record.segDecrypt_okQF Record.segMismatch_ok Record.segTail_ok Record.segExit_ok

end CryptoVerification.LibsignalTripleRatchet.RecordAssembly
