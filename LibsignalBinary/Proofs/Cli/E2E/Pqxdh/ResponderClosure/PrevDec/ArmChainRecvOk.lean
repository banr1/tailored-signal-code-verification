/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Kit.BytesMerge6 -- shake: keep
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecv
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPush
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.ArmChain
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Callees

/-!
# Unconditional Tag 6 (`sender_chain`) and Tag 7 (`receiver_chains`) Decode Arms

Instantiates `chain3CalleeKit_cli` from `decodeVarint5_ok` and `bytes_merge_6_ok_ext_of_alloc`, and
proves unconditional `OverDecArmStmtTR` specifications for tag 6 (`overDecArmSender_cli`) and tag 7
(`overDecArmRecv_cli`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

private theorem kit_decodeVarint2SpecX_eq_chain3 (A : RustAlloc) :
    Kit.decodeVarint2SpecX A =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.decodeVarint2SpecX A := by
  unfold Kit.decodeVarint2SpecX
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.decodeVarint2SpecX
  congr 1

private theorem kit_bytesMerge3RawSpec_eq_chain3 (A : RustAlloc) :
    Kit.bytesMerge3RawSpec A =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.bytesMerge3RawSpec A := by
  unfold Kit.bytesMerge3RawSpec
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.bytesMerge3RawSpec
  congr 1

private theorem kit_bytesMerge3Spec_eq_chain3 (A : RustAlloc) (img : Obj.Image) :
    Kit.bytesMerge3Spec A img =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.bytesMerge3Spec A img := by
  unfold Kit.bytesMerge3Spec
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.bytesMerge3Spec
  rw [kit_bytesMerge3RawSpec_eq_chain3]

/-- Allocator-polymorphic `Chain3CalleeKitExt` instantiated from `decodeVarint5_ok` and
`bytes_merge_6_ok_ext_of_alloc`. -/
theorem chain3CalleeKit_cli_ext {A : RustAlloc} : Chain3CalleeKitExt A where
  dv := fun img ext _himg hAlloc => by
    have h := Kit.decodeVarint5_ok hAlloc
    unfold Kit.DecodeVarint5OkExtX at h
    rw [kit_decodeVarint2SpecX_eq_chain3] at h
    exact h
  bm := fun img ext himg hAlloc => by
    have h := Kit.bytes_merge_6_ok_ext_of_alloc himg hAlloc
    unfold Kit.BytesMerge6OkExt at h
    rw [kit_bytesMerge3Spec_eq_chain3] at h
    exact h

theorem chain3CalleeKit_cli : Chain3CalleeKit :=
  chain3CalleeKit_cli_ext

/-- Unconditional `message::merge<Chain> [local#5]` contract (`Chain5OkAtW img ext`) under
`Obj.Loads` and `AllocContractsX`. -/
theorem chainMerge5_cli_ok (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A0 ext) :
    Chain5OkAtW img ext :=
  chainMerge5_ok chain3CalleeKit_cli img ext himg hAlloc

theorem overDecArm_recv_of_chain3_ext {A : RustAlloc}
    (hChain3 : ∀ img ext, Obj.Loads libsignalSessionImage img →
      CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext →
      Chain3OkAtWExt A img ext) :
    OverDecArmStmtTRExt A OverDecRecvField :=
  overDecArm_recv_of_segB_chain3_ext overDecRecv_segB_ok_ext hChain3

theorem overDecArmRecv_cli_of_kit (kit : Chain3CalleeKit) :
    OverDecArmStmtTR OverDecRecvField :=
  overDecArm_recv_of_chain3 overDecRecv_segB_ok (chainMerge5_ok kit)

/-- Unconditional tag 6 (`sender_chain`) decode arm (`+0x2214 → +0x2160`). -/
theorem overDecArmSender_cli : OverDecArmStmtTR OverDecSenderField :=
  overDecArmSender_cli_of_kit chain3CalleeKit_cli

/-- Unconditional tag 7 (`receiver_chains`) decode arm (`+0x22e0 → +0x2160`). -/
theorem overDecArmRecv_cli : OverDecArmStmtTR OverDecRecvField :=
  overDecArmRecv_cli_of_kit chain3CalleeKit_cli

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
