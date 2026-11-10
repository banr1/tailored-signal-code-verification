/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Root
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegBackS7
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegBackS8
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegBackS9
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhMain
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegFront.ErrTailProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegFront.S0B
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegFront.S1Proof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegFront.S2B
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegMidS4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegMidS5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegMidS6
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Recv.Final
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.InImage.Spqr
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Proofs.TripleRatchet.Mac.Verify
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Assembly -- shake: keep

/-!
# CLI `try_decrypt_with_state::<Coins>` Top-Level Assembly

Top-level verification theorems assembling the segment contracts for
`libsignal_protocol::session_management::try_decrypt_with_state::<signal_session_handshake::Coins>`
in `libsignalSessionImage` (unconditional, empty-PQ, and SPQR v1 specializations).
-/

@[expose] public section

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPqAssembly

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.tryDecryptPqCallees (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees img C A ctl uuidTryParse abs where
  localIk := Getters.local_identity_key_ok _ _ _ _ _ himg
  remoteIk := Glue.remoteIdentityKeyOk _ _ _ _ _ himg
  sameAcc := Glue.is_same_account_ok _ _ _ _
  clearUpk := Glue.clear_unacknowledged_pre_key_message_ok_of_tripleRatchetHooks hH
  dropChain := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain2_ok hH.alloc
  chainKeyToPb := Glue.chain_key_to_pb_ok_of_tripleRatchetHooks hH
  derivePk := derive_public_key_bytes_ok
  trFrom := ReceiveRatchetFrom.trFrom_ok himg hH (Glue.deserializeOk _ _ _ _)
    (Glue.remoteIdentityKeyOk _ _ _ _ _ himg) (Glue.dropSpeOk_of_tripleRatchetHooks himg hH)
    (Glue.drop_vec_chain_ok_of_tripleRatchetHooks hH)
  trApply := ReceiveRatchetApply.trApply_ok hH (Glue.publicKeySerializeOk_of_tripleRatchetHooks hH)
    (Glue.drop_vec_message_key_ok_of_tripleRatchetHooks hH)
    (Glue.drop_vec_chain_ok_of_tripleRatchetHooks hH)
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

/-- `try_decrypt_with_state::<signal_session_handshake::Coins>` satisfies `CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.tryDecryptPq_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqRunStmt C A ctl S abs img :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecrypt_run_of_seams C A ctl S abs img
    (fun hH himg => CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.tryDecryptPqCallees C A ctl S abs img hH himg)
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_ok CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s4_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s5_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s6_ok img C A ctl abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s8_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s9_ok img C A ctl S abs)
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_ok

/-- Specialization of `tryDecryptPq_run` to an empty post-quantum ratchet state. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.tryDecryptPqEmpty_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqEmptyRunStmt C A ctl S abs img :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEmpty_run_of_seams C A ctl S abs img
    (spqrRecvEmpty_run C A ctl S abs img)
    (fun hH himg => CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.tryDecryptPqCallees C A ctl S abs img hH himg)
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_ok CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s4_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s5_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s6_ok img C A ctl abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s8_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s9_ok img C A ctl S abs)
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_ok

/-- Specialization of `tryDecryptPq_run` to SPQR v1 states given `SpqrRecvV1Stmt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.tryDecryptPqV1_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image)
    (hrecvV1 : LibsignalSpqrV1.SpqrRecvV1Stmt C A ctl K abs img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmt C A ctl K abs img :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptV1_run_of_seams C A ctl K abs img hrecvV1
    (fun hH himg => CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.tryDecryptPqCallees C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg)
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_ok CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s4_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s5_okQF img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s6_ok img C A ctl abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s8_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s9_ok img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_ok

/-- Unconditional SPQR v1 `try_decrypt_with_state::<signal_session_handshake::Coins>` contract discharging `SpqrRecvV1Stmt` via `spqr_recv_ok`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.tryDecryptPqV1_ok (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmt C A ctl K abs img :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.tryDecryptPqV1_run C A ctl K abs img (CryptoVerification.Cli.SpqrV1.Top.Recv.spqr_recv_ok C A ctl K abs img)

end CryptoVerification.LibsignalTripleRatchet.DecryptPqAssembly
