/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpoch
public import LibsignalBinary.Proofs.SpqrV1.Drop.States2
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: Callee Address Bridges & `decode_state` Post-Call Dispatch

**Checked by Lean.** Relative callee `fnOff` bridges, `SepWPpI` prologue entry (`+0..+312`),
stack-frame splits, and post-`spqr::decode_state` error/success steps (`+328..+408`) for
`spqr::recv` (`0x5462c`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. `fnOff` Facts & Relative Address Bridges for `spqr::recv` Callees -/

private theorem spqrDecodeState_fnOff :
    libsignalSessionCode.fnOff DecodeState.decodeStateName = num% (ls_off% "spqr::decode_state") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "spqr::decode_state")

private theorem spqrInitInner_fnOff :
    libsignalSessionCode.fnOff initInnerName = num% (ls_off% "spqr::init_inner") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "spqr::init_inner")

private theorem spqrChainFrom_fnOff :
    libsignalSessionCode.fnOff chainFromName = num% (ls_off% "spqr::chain_from") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "spqr::chain_from")

private theorem spqrChainFromPb_fnOff :
    libsignalSessionCode.fnOff chainFromPbName = num% (ls_off% "<spqr::chain::Chain>::from_pb") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<spqr::chain::Chain>::from_pb")

private theorem spqrChainNew_fnOff :
    libsignalSessionCode.fnOff chainNewName = num% (ls_off% "<spqr::chain::Chain>::new") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<spqr::chain::Chain>::new")

private theorem spqrChainAddEpoch_fnOff :
    libsignalSessionCode.fnOff chainAddEpochName = num% (ls_off% "<spqr::chain::Chain>::add_epoch") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<spqr::chain::Chain>::add_epoch")

private theorem spqrChainRecvKey_fnOff :
    libsignalSessionCode.fnOff chainRecvKeyName = num% (ls_off% "<spqr::chain::Chain>::recv_key") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<spqr::chain::Chain>::recv_key")

private theorem spqrChainIntoPb_fnOff :
    libsignalSessionCode.fnOff chainIntoPbName = num% (ls_off% "<spqr::chain::Chain>::into_pb") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<spqr::chain::Chain>::into_pb")

private theorem spqrMessageDeserialize_fnOff :
    libsignalSessionCode.fnOff messageDeserializeName =
      num% (ls_off% "<spqr::v1::chunked::states::Message>::deserialize") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<spqr::v1::chunked::states::Message>::deserialize")

private theorem spqrStatesFromPb_fnOff :
    libsignalSessionCode.fnOff statesFromPbName =
      num% (ls_off% "<spqr::v1::chunked::states::States>::from_pb") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::from_pb")

private theorem spqrStatesRecv_fnOff :
    libsignalSessionCode.fnOff statesRecvName =
      num% (ls_off% "<spqr::v1::chunked::states::States>::recv") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv")

private theorem spqrStatesIntoPb_fnOff :
    libsignalSessionCode.fnOff statesIntoPbName =
      num% (ls_off% "<spqr::v1::chunked::states::States>::into_pb") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::into_pb")

private theorem spqrEncodeToVec_fnOff :
    libsignalSessionCode.fnOff spqrEncodeToVecName =
      num% (ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem spqrRecv_decodeState_ok {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (2 ^ 64 - ls_rel% "spqr::decode_state" "spqr::recv"))
      ((decodeStateSpecX H_inner img.base A).inImage img) := by
  have hrel : (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName =
      (tripleRatchetProgAtExt img.base ext).fnAddr DecodeState.decodeStateName +
        bv% (ls_rel% "spqr::decode_state" "spqr::recv") :=
    Program.fnAddr_rel (k := num% (ls_rel% "spqr::decode_state" "spqr::recv"))
      (b := img.base) (X := Rust.withPanics ext)
      spqrDecodeState_fnOff (ls_lemma% fnOff "spqr::recv") (by decide)
  refine sub_ok_of_addr_eq ?_ hC.decodeState_ok
  rw [hrel, BitVec.add_assoc]; simp

theorem spqrRecv_initInner_ok {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (2 ^ 64 - ls_rel% "spqr::init_inner" "spqr::recv"))
      ((initInnerSpecX A F img.base).inImage img) := by
  have hrel : (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName =
      (tripleRatchetProgAtExt img.base ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "spqr::recv") :=
    Program.fnAddr_rel (k := num% (ls_rel% "spqr::init_inner" "spqr::recv"))
      (b := img.base) (X := Rust.withPanics ext)
      spqrInitInner_fnOff (ls_lemma% fnOff "spqr::recv") (by decide)
  refine sub_ok_of_addr_eq ?_ hC.initInner_ok
  rw [hrel, BitVec.add_assoc]; simp

theorem spqrRecv_chainFrom_ok {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (2 ^ 64 - ls_rel% "spqr::chain_from" "spqr::recv"))
      ((chainFromSpecX (spqrHkdfWith F) A).inImage img) := by
  have hrel : (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName =
      (tripleRatchetProgAtExt img.base ext).fnAddr chainFromName +
        bv% (ls_rel% "spqr::chain_from" "spqr::recv") :=
    Program.fnAddr_rel (k := num% (ls_rel% "spqr::chain_from" "spqr::recv"))
      (b := img.base) (X := Rust.withPanics ext)
      spqrChainFrom_fnOff (ls_lemma% fnOff "spqr::recv") (by decide)
  refine sub_ok_of_addr_eq ?_ hC.chainFrom_ok
  rw [hrel, BitVec.add_assoc]; simp

theorem spqrRecv_chainFromPb_ok {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::from_pb"))
      ((chainFromPbSpecX A).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::from_pb"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrChainFromPb_fnOff (by decide))
    hC.chainFromPb_ok

theorem spqrRecv_chainNew_ok {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::new"))
      ((chainNewSpecX (spqrHkdfWith F) A).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::new"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrChainNew_fnOff (by decide))
    hC.chainNew_ok

theorem spqrRecv_chainAddEpoch_ok {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::add_epoch"))
      ((chainAddEpochSpecX (spqrHkdfWith F) A).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::add_epoch"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrChainAddEpoch_fnOff (by decide))
    hC.chainAddEpoch_ok

theorem spqrRecv_chainRecvKey_ok {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::recv_key"))
      ((chainRecvKeySpecX (spqrHkdfWith F) A).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::recv_key"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrChainRecvKey_fnOff (by decide))
    hC.chainRecvKey_ok

theorem spqrRecv_chainIntoPb_ok {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::into_pb"))
      ((chainIntoPbSpecX A).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::into_pb"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrChainIntoPb_fnOff (by decide))
    hC.chainIntoPb_ok

theorem spqrRecv_messageDeserialize_ok {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::v1::chunked::states::Message>::deserialize"))
      ((messageDeserializeSpecX spqrPolyApi A).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "spqr::recv" "<spqr::v1::chunked::states::Message>::deserialize"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrMessageDeserialize_fnOff (by decide))
    hC.messageDeserialize_ok

theorem spqrRecv_statesFromPb_ok {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::v1::chunked::states::States>::from_pb"))
      ((statesFromPbSpecX A F img.base).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "spqr::recv" "<spqr::v1::chunked::states::States>::from_pb"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrStatesFromPb_fnOff (by decide))
    hC.statesFromPb_ok

theorem spqrRecv_statesRecv_ok {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::v1::chunked::states::States>::recv"))
      (statesRecvSpecX A F K img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "spqr::recv" "<spqr::v1::chunked::states::States>::recv"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrStatesRecv_fnOff (by decide))
    hC.statesRecv_ok

theorem spqrRecv_statesIntoPb_ok {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::v1::chunked::states::States>::into_pb"))
      ((statesIntoPbSpecX A F img.base).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "spqr::recv" "<spqr::v1::chunked::states::States>::into_pb"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrStatesIntoPb_fnOff (by decide))
    hC.statesIntoPb_ok

theorem spqrRecv_encodeToVec_ok {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      ((pqRatchetStateEncodeToVecSpecX A).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "spqr::recv" "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrEncodeToVec_fnOff (by decide))
    hC.encodeToVec_ok

theorem spqrRecv_dropOptProtoChain_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrRecvName +
        bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>" "spqr::recv"))
      (CryptoVerification.SpqrV1.Drop.dropOptProtoSpqrChainSpec A) := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.SpqrV1.Drop.dropOptProtoSpqrChainName +
        bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>" "spqr::recv") :=
    Program.fnAddr_rel
      (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>" "spqr::recv"))
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>")
      (ls_lemma% fnOff "spqr::recv") (by decide)
  refine sub_ok_of_addr_eq ?_ (drop_opt_proto_spqr_chain_ok_ext hdealloc)
  rw [hrel, BitVec.add_assoc]; simp

theorem spqrRecv_dropChain_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrRecvName +
        bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<spqr::chain::Chain>" "spqr::recv"))
      (CryptoVerification.SpqrV1.Drop.dropSpqrChainSpec A) := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.SpqrV1.Drop.dropSpqrChainName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::chain::Chain>" "spqr::recv") :=
    Program.fnAddr_rel
      (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::chain::Chain>" "spqr::recv"))
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::chain::Chain>")
      (ls_lemma% fnOff "spqr::recv") (by decide)
  refine sub_ok_of_addr_eq ?_ (drop_spqr_chain_ok_ext hdealloc)
  rw [hrel, BitVec.add_assoc]; simp

theorem spqrRecv_dropPqRatchetState_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrRecvName +
        bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" "spqr::recv"))
      (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStateSpec A b) := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStateName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" "spqr::recv") :=
    Program.fnAddr_rel
      (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" "spqr::recv"))
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>")
      (ls_lemma% fnOff "spqr::recv") (by decide)
  refine sub_ok_of_addr_eq ?_ (drop_proto_pq_ratchet_state_ok_ext hdealloc)
  rw [hrel, BitVec.add_assoc]; simp

theorem spqrRecv_dropStates_ok {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrRecvName +
        bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "spqr::recv"))
      (CryptoVerification.SpqrV1.Drop.dropChunkedStatesLocal2Spec A F b) := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.SpqrV1.Drop.dropChunkedStatesLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "spqr::recv") :=
    Program.fnAddr_rel
      (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "spqr::recv"))
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]")
      (ls_lemma% fnOff "spqr::recv") (by decide)
  refine sub_ok_of_addr_eq ?_ (drop_chunked_states_local2_ok_ext hdealloc)
  rw [hrel, BitVec.add_assoc]; simp

/-! ## 2. Prologue + `msg_preamble` Entry Bridge to `SepWPpI` (`+0 .. +312`) -/

/-- Lift `step_prologue_preamble` (`+0 .. +312`) into `SepWPpI`:
    - When `msgPreamble msg.bytes = .error e`, steps through `step_err_msgDecode` (`+276..+288`) and
    `step_epilogue` (`+1040..+1072`) directly to `s0.readReg64 .x30`.
    - When `msgPreamble msg.bytes = .ok pre`, steps to `entry + 312#64` and invokes `hok_tail`. -/
theorem step_prologue_to_312 {img : Obj.Image} (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (P R : SepProp)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = st.v)
    (hx1 : s0.readReg64 .x1 = msg.v)
    (hx8 : s0.readReg64 .x8 = ret)
    (hP : P =
      spqrRecvRoAt img.base ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt s0.sp spqrRecvStack)
    (hok_tail : ∀ (pre : MsgPreamble) (msgPtr : BitVec 64) (s1 : State) (P1 : SepProp),
      msgPreamble msg.bytes = .ok pre →
      MsgRemValid msg msgPtr pre.remaining →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 312#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 4992#64 →
      TraceVRegs s1 s0 →
      s1.readReg64 .x0 = st.v →
      s1.readReg64 .x19 = ret →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 →
      s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
      s1.readReg64 .x24 = msgPtr →
      s1.readReg64 .x25 = pre.version.zeroExtend 64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = spqrRecvPreambleFrame img.base A st msg ret s0 →
      SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s0 P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  cases hpre : msgPreamble msg.bytes with
  | error err =>
    apply SepWPpI.of_sepWPp
    apply SepWPp.of_sepWP_ret
    refine step_prologue_preamble img.base A ext st msg ret (s0.readReg64 .x30) s0 P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R) ?_ ?_ hpc hrun hsp_align hx0 hx1 hx8 hP
    · intro s1 P1 herr hpc1 hrun1 hsp1 htr1 hx19_1 hP1
      have hrecv : (spqrV1Recv F K).recv st.bytes msg.bytes = .error false :=
        spqrV1Recv_recv_of_err (recv_of_msgPreamble_error (spqrDeps F K) (spqrHkdfWith F) herr)
      have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
        spqrV1Recv_noPanic_of_err (recv_of_msgPreamble_error (spqrDeps F K) (spqrHkdfWith F) herr)
      exact sepWP_spqrRecvPost_of_post0 hnp
        (step_err_msgDecode img.base A (spqrV1Recv F K) ext st msg ret s0 s1 P1 R
          _ rfl hrecv hpc1 hrun1 hsp1 hsp_align htr1 hx19_1 hP1)
    · intro pre' _ _ _ hok'
      rw [hpre] at hok'
      cases hok'
  | ok pre =>
    apply SepWPpI.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 312#64)
    refine step_prologue_preamble img.base A ext st msg ret
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 312#64) s0 P
      (fun sm Pm =>
        SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sm Pm
          (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
          (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R))
      ?_ ?_ hpc hrun hsp_align hx0 hx1 hx8 hP
    · intro s1 P1 herr
      rw [hpre] at herr
      cases herr
    · intro pre' msgPtr s1 P1 hok' hvalid hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1
      apply SepWP.done hpc1 hrun1
      exact hok_tail pre' msgPtr s1 P1 hok' hvalid hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1

/-! ## 3. Frame Split/Join Helpers for `spqr::decode_state` (`+312 .. +496`) -/

/-- Split `memRegion (sp0 - 4992#64) 0x1320` (`4896`B) for `+312 .. +408`:
    - `32`B (`4` words at `sp0 - 4992#64 .. sp0 - 4960#64`),
    - `320`B (`memRegion (sp0 - 4960#64) 320` for `memcpy` destination),
    - `1584`B (`memRegion (sp0 - 4640#64) 1584`),
    - `352`B (`memRegion (sp0 - 3056#64) 352` for `decode_state` sret at `sp + 0x790`),
    - `608`B (`memRegion (sp0 - 2704#64) 608`),
    - `24`B (`3` words at `sp0 - 2096#64 .. sp0 - 2072#64` = `sp + 0xb50 .. sp + 0xb68`),
    - `1976`B (`memRegion (sp0 - 2072#64) 1976`). -/
theorem ownFrame_split_for_decode (sp0 : BitVec 64) :
    memRegion (sp0 - 4992#64) 0x1320 ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
      ∃∗ b0 : BitVec 64, ∃∗ b1 : BitVec 64, ∃∗ b2 : BitVec 64,
        ((sp0 - 4992#64) ↦₆₄ d0) ∗ ((sp0 - 4984#64) ↦₆₄ d1) ∗
        ((sp0 - 4976#64) ↦₆₄ d2) ∗ ((sp0 - 4968#64) ↦₆₄ d3) ∗
        memRegion (sp0 - 4960#64) 320 ∗
        memRegion (sp0 - 4640#64) 1584 ∗
        memRegion (sp0 - 3056#64) 352 ∗
        memRegion (sp0 - 2704#64) 608 ∗
        ((sp0 - 2096#64) ↦₆₄ b0) ∗ ((sp0 - 2088#64) ↦₆₄ b1) ∗ ((sp0 - 2080#64) ↦₆₄ b2) ∗
        memRegion (sp0 - 2072#64) 1976 := by
  have h1 : memRegion (sp0 - 4992#64) 0x1320 =
      memRegion (sp0 - 4992#64) 8 ∗ memRegion (sp0 - 4984#64) 8 ∗
      memRegion (sp0 - 4976#64) 8 ∗ memRegion (sp0 - 4968#64) 8 ∗
      memRegion (sp0 - 4960#64) 320 ∗
      memRegion (sp0 - 4640#64) 1584 ∗
      memRegion (sp0 - 3056#64) 352 ∗
      memRegion (sp0 - 2704#64) 608 ∗
      memRegion (sp0 - 2096#64) 8 ∗ memRegion (sp0 - 2088#64) 8 ∗ memRegion (sp0 - 2080#64) 8 ∗
      memRegion (sp0 - 2072#64) 1976 := by
    rw [show (0x1320 : Nat) = 8 + (8 + (8 + (8 + (320 + (1584 + (352 + (608 + (8 + (8 + (8 + 1976)))))))))) by decide,
        memRegion_split (sp0 - 4992#64) 8 _ (by decide), bv_sub_add_lit sp0 4992 8,
        memRegion_split (sp0 - 4984#64) 8 _ (by decide), bv_sub_add_lit sp0 4984 8,
        memRegion_split (sp0 - 4976#64) 8 _ (by decide), bv_sub_add_lit sp0 4976 8,
        memRegion_split (sp0 - 4968#64) 8 _ (by decide), bv_sub_add_lit sp0 4968 8,
        memRegion_split (sp0 - 4960#64) 320 _ (by decide), bv_sub_add_lit sp0 4960 320,
        memRegion_split (sp0 - 4640#64) 1584 _ (by decide), bv_sub_add_lit sp0 4640 1584,
        memRegion_split (sp0 - 3056#64) 352 _ (by decide), bv_sub_add_lit sp0 3056 352,
        memRegion_split (sp0 - 2704#64) 608 _ (by decide), bv_sub_add_lit sp0 2704 608,
        memRegion_split (sp0 - 2096#64) 8 _ (by decide), bv_sub_add_lit sp0 2096 8,
        memRegion_split (sp0 - 2088#64) 8 _ (by decide), bv_sub_add_lit sp0 2088 8,
        memRegion_split (sp0 - 2080#64) 8 1976 (by decide), bv_sub_add_lit sp0 2080 8]
  rw [h1,
      ProofLib.memRegion_eight (sp0 - 4992#64),
      ProofLib.memRegion_eight (sp0 - 4984#64),
      ProofLib.memRegion_eight (sp0 - 4976#64),
      ProofLib.memRegion_eight (sp0 - 4968#64),
      ProofLib.memRegion_eight (sp0 - 2096#64),
      ProofLib.memRegion_eight (sp0 - 2088#64),
      ProofLib.memRegion_eight (sp0 - 2080#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b2
  apply Entails.sepExists_elim; intro b1
  apply Entails.sepExists_elim; intro b0
  apply Entails.sepExists_elim; intro d3
  apply Entails.sepExists_elim; intro d2
  apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d0
  refine Entails.sepExists_right d0 (Entails.sepExists_right d1
    (Entails.sepExists_right d2 (Entails.sepExists_right d3
      (Entails.sepExists_right b0 (Entails.sepExists_right b1
        (Entails.sepExists_right b2 ?_))))))
  exact Entails.of_eq (by ac_rfl)

theorem ownFrame_join_4544_after_decode (sp0 w0 w1 w2 w3 b0 b1 b2 : BitVec 64)
    (bs320 : List (BitVec 8)) (hbs320 : bs320.length = 320) :
    memRegion (sp0 - 4640#64) 1584 ∗
      ((sp0 - 3056#64) ↦₆₄ w0) ∗ ((sp0 - 3048#64) ↦₆₄ w1) ∗
      ((sp0 - 3040#64) ↦₆₄ w2) ∗ ((sp0 - 3032#64) ↦₆₄ w3) ∗
      ((sp0 - 3024#64) ↦ₛ bs320) ∗
      memRegion (sp0 - 2704#64) 608 ∗
      ((sp0 - 2096#64) ↦₆₄ b0) ∗ ((sp0 - 2088#64) ↦₆₄ b1) ∗ ((sp0 - 2080#64) ↦₆₄ b2) ∗
      memRegion (sp0 - 2072#64) 1976 ⊢
    memRegion (sp0 - 4640#64) 4544 := by
  have h1 : memRegion (sp0 - 4640#64) 4544 =
      memRegion (sp0 - 4640#64) 1584 ∗
      memRegion (sp0 - 3056#64) 8 ∗ memRegion (sp0 - 3048#64) 8 ∗
      memRegion (sp0 - 3040#64) 8 ∗ memRegion (sp0 - 3032#64) 8 ∗
      memRegion (sp0 - 3024#64) 320 ∗
      memRegion (sp0 - 2704#64) 608 ∗
      memRegion (sp0 - 2096#64) 8 ∗ memRegion (sp0 - 2088#64) 8 ∗ memRegion (sp0 - 2080#64) 8 ∗
      memRegion (sp0 - 2072#64) 1976 := by
    rw [show (4544 : Nat) = 1584 + (8 + (8 + (8 + (8 + (320 + (608 + (8 + (8 + (8 + 1976))))))))) by decide,
        memRegion_split (sp0 - 4640#64) 1584 _ (by decide), bv_sub_add_lit sp0 4640 1584,
        memRegion_split (sp0 - 3056#64) 8 _ (by decide), bv_sub_add_lit sp0 3056 8,
        memRegion_split (sp0 - 3048#64) 8 _ (by decide), bv_sub_add_lit sp0 3048 8,
        memRegion_split (sp0 - 3040#64) 8 _ (by decide), bv_sub_add_lit sp0 3040 8,
        memRegion_split (sp0 - 3032#64) 8 _ (by decide), bv_sub_add_lit sp0 3032 8,
        memRegion_split (sp0 - 3024#64) 320 _ (by decide), bv_sub_add_lit sp0 3024 320,
        memRegion_split (sp0 - 2704#64) 608 _ (by decide), bv_sub_add_lit sp0 2704 608,
        memRegion_split (sp0 - 2096#64) 8 _ (by decide), bv_sub_add_lit sp0 2096 8,
        memRegion_split (sp0 - 2088#64) 8 _ (by decide), bv_sub_add_lit sp0 2088 8,
        memRegion_split (sp0 - 2080#64) 8 1976 (by decide), bv_sub_add_lit sp0 2080 8]
  rw [h1, ← hbs320]
  exact sepConj_mono_right
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsToBytes_entails_memRegion _ _)
              (sepConj_mono_right
                (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                    (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))))))))))

theorem ownFrame_join_4896_err_decode (sp0 d0 d1 d2 d3 w0 w1 w2 w3 b0 b1 b2 : BitVec 64) :
    ((sp0 - 4992#64) ↦₆₄ d0) ∗ ((sp0 - 4984#64) ↦₆₄ d1) ∗
      ((sp0 - 4976#64) ↦₆₄ d2) ∗ ((sp0 - 4968#64) ↦₆₄ d3) ∗
      memRegion (sp0 - 4960#64) 320 ∗
      memRegion (sp0 - 4640#64) 1584 ∗
      ((sp0 - 3056#64) ↦₆₄ w0) ∗ ((sp0 - 3048#64) ↦₆₄ w1) ∗
      ((sp0 - 3040#64) ↦₆₄ w2) ∗ ((sp0 - 3032#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 3024#64) 320 ∗
      memRegion (sp0 - 2704#64) 608 ∗
      ((sp0 - 2096#64) ↦₆₄ b0) ∗ ((sp0 - 2088#64) ↦₆₄ b1) ∗ ((sp0 - 2080#64) ↦₆₄ b2) ∗
      memRegion (sp0 - 2072#64) 1976 ⊢
    memRegion (sp0 - 4992#64) 0x1320 := by
  have h1 : memRegion (sp0 - 4992#64) 0x1320 =
      memRegion (sp0 - 4992#64) 8 ∗ memRegion (sp0 - 4984#64) 8 ∗
      memRegion (sp0 - 4976#64) 8 ∗ memRegion (sp0 - 4968#64) 8 ∗
      memRegion (sp0 - 4960#64) 320 ∗
      memRegion (sp0 - 4640#64) 1584 ∗
      memRegion (sp0 - 3056#64) 8 ∗ memRegion (sp0 - 3048#64) 8 ∗
      memRegion (sp0 - 3040#64) 8 ∗ memRegion (sp0 - 3032#64) 8 ∗
      memRegion (sp0 - 3024#64) 320 ∗
      memRegion (sp0 - 2704#64) 608 ∗
      memRegion (sp0 - 2096#64) 8 ∗ memRegion (sp0 - 2088#64) 8 ∗ memRegion (sp0 - 2080#64) 8 ∗
      memRegion (sp0 - 2072#64) 1976 := by
    rw [show (0x1320 : Nat) = 8 + (8 + (8 + (8 + (320 + (1584 + (8 + (8 + (8 + (8 + (320 + (608 + (8 + (8 + (8 + 1976)))))))))))))) by decide,
        memRegion_split (sp0 - 4992#64) 8 _ (by decide), bv_sub_add_lit sp0 4992 8,
        memRegion_split (sp0 - 4984#64) 8 _ (by decide), bv_sub_add_lit sp0 4984 8,
        memRegion_split (sp0 - 4976#64) 8 _ (by decide), bv_sub_add_lit sp0 4976 8,
        memRegion_split (sp0 - 4968#64) 8 _ (by decide), bv_sub_add_lit sp0 4968 8,
        memRegion_split (sp0 - 4960#64) 320 _ (by decide), bv_sub_add_lit sp0 4960 320,
        memRegion_split (sp0 - 4640#64) 1584 _ (by decide), bv_sub_add_lit sp0 4640 1584,
        memRegion_split (sp0 - 3056#64) 8 _ (by decide), bv_sub_add_lit sp0 3056 8,
        memRegion_split (sp0 - 3048#64) 8 _ (by decide), bv_sub_add_lit sp0 3048 8,
        memRegion_split (sp0 - 3040#64) 8 _ (by decide), bv_sub_add_lit sp0 3040 8,
        memRegion_split (sp0 - 3032#64) 8 _ (by decide), bv_sub_add_lit sp0 3032 8,
        memRegion_split (sp0 - 3024#64) 320 _ (by decide), bv_sub_add_lit sp0 3024 320,
        memRegion_split (sp0 - 2704#64) 608 _ (by decide), bv_sub_add_lit sp0 2704 608,
        memRegion_split (sp0 - 2096#64) 8 _ (by decide), bv_sub_add_lit sp0 2096 8,
        memRegion_split (sp0 - 2088#64) 8 _ (by decide), bv_sub_add_lit sp0 2088 8,
        memRegion_split (sp0 - 2080#64) 8 1976 (by decide), bv_sub_add_lit sp0 2080 8]
  rw [h1]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                      (sepConj_mono_right
                        (sepConj_mono_right
                          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                              (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))))))))))))))

/-- When `Proto.spqrDecodeState st.bytes = .error e`, steps from `+328` (`0x54774`, right after
    `bl spqr::decode_state`) through `+356..+380` (`b +1040`) and `step_epilogue`
    (`+1040..+1072`) to `s0.readReg64 .x30`. -/
theorem step_decode_err_328 (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (e : LibsignalSpqrV1.Error)
    (d0 d1 d2 d3 b0 b1 b2 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .error e)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost A b (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 328#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
      ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
      memRegion (s0.sp - 4960#64) 320 ∗
      memRegion (s0.sp - 4640#64) 1584 ∗
      decodeStateResultAt H_inner A (s0.sp - 3056#64) (.error e) ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ b0) ∗ ((s0.sp - 2088#64) ↦₆₄ b1) ∗ ((s0.sp - 2080#64) ↦₆₄ b2) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  have ⟨hd_err, he_eq⟩ :=
    CryptoVerification.SpqrV1.Top.Send.decodeState_spqrDeps_of_spqrDecodeState_error F K hdec
  subst he_eq
  have hrecv : (spqrV1Recv F K).recv st.bytes msg.bytes = .error true :=
    spqrV1Recv_recv_of_err (recv_of_decodeState_error (spqrDeps F K) (spqrHkdfWith F) hpre hd_err)
  have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
    spqrV1Recv_noPanic_of_recv_err_true hrecv
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, decodeStateResultAt,
    DecodeState.spqrErrorTag, DecodeState.none2Cap] at hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 328 56
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  have hexp := err_payload_expose (s0.sp - 3056#64) 0#8 343 (by decide) (by decide)
  simp only [bv_sub_add_lit, Nat.reduceSub] at hexp ⊢
  refine SepWP.focus_weaken hexp (by sep_focus) ?_
  wp_pull_exists; rename_i w1 w2 w3
  wp_focus_pure; intro hw1_ent
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r3 r2 r1 r0
  wp_steps 14
  have hfold := recv_err_words_foldX A ret w1 w2 w3 0#8 true (by decide) hw1_ent
  rw [← hrecv] at hfold
  refine SepWP.fold hfold (by sep_focus) ?_
  refine SepWP.focus_weaken
    (ownFrame_join_4896_err_decode s0.sp d0 d1 d2 d3 0xFFFFFFFFFFFFFFFE#64 w1 w2 w3 w1 w2 w3)
    (by sep_focus) ?_
  subst hpost
  exact sepWP_spqrRecvPost_of_post0 hnp
    (step_epilogue b A (spqrV1Recv F K) ext st msg ret s0 _ _ R _ rfl
      (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hs0_align (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; ac_rfl))

/-- When `Proto.spqrDecodeState st.bytes = .ok pre_pb`, steps from `+328` (`0x54774`, right
    after `bl spqr::decode_state`) through `+352` (`b.ne +384`) and `+384..+404` (`bl memcpy` of
    `320`B) to `+408` (`0x547c4`). -/
theorem step_decode_ok_328_to_408 (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState)
    (d0 d1 d2 d3 b0 b1 b2 : BitVec 64)
    (s0 s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 328#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx26 : s.readReg64 .x26 = s0.sp - 3056#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
      ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
      memRegion (s0.sp - 4960#64) 320 ∗
      memRegion (s0.sp - 4640#64) 1584 ∗
      decodeStateResultAt H_inner A (s0.sp - 3056#64) (.ok pre_pb) ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ b0) ∗ ((s0.sp - 2088#64) ↦₆₄ b1) ∗ ((s0.sp - 2080#64) ↦₆₄ b2) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (htail : ∀ (w0 w1 w2 w3 : BitVec 64) (bs96 : List (BitVec 8)) (sm : State) (Pm : SepProp),
      w0 ≠ DecodeState.none2Cap →
      bs96.length = 96 →
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 408#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 4992#64 →
      TraceVRegs sm s0 →
      sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = w0 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s0.sp - 3056#64 →
      sm.readReg64 .x28 = s0.sp - 4288#64 →
      sm.readReg64 .x29 = s.readReg64 .x29 →
      Pm = (spqrRecvRoAt b ∗
        st.at A ∗
        msg.at A ∗
        memRegion ret 48 ∗
        A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
        ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
        ((s0.sp - 4960#64) ↦ₛ bs96) ∗
        (relocVnTailAndChainAt A w0 w1 pre_pb).1 (unpack64 w2 ++ unpack64 w3 ++ bs96) ∗
        Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
        ((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗
        (∃∗ P_tail : SepProp,
          ⌜((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗ P_tail ⊢
            memRegion (s0.sp - 4640#64) 4544⌝ ∗ P_tail) ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 408#64) sm Pm post) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 408#64) s P post := by
  have hmemcpy_raw := spqrRecv_memcpy_ok hA spqrRecvCalleeStackX
  simp only [sessionMemcpySpec] at hmemcpy_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, decodeStateResultAt,
    BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc htail ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 328 80
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  have hsplit := protoPqRatchetStateAt_entails_head32_bs96_bs224 H_inner A (s0.sp - 3056#64) pre_pb
  rw [bv_sub_add_lit s0.sp 3056 8, bv_sub_add_lit s0.sp 3056 16,
      bv_sub_add_lit s0.sp 3056 24, bv_sub_add_lit s0.sp 3056 32] at hsplit
  refine SepWP.focus_weaken hsplit (by sep_focus) ?_
  wp_pull_exists; rename_i w0 w1 w2 w3 bs96 bs224
  wp_focus_pure; rintro ⟨hw0_ne, hbs96, hbs224, hbs320⟩
  have hw0_cmn : (w0 + 2#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    apply hw0_ne
    change w0 = -2#64
    revert w0 heq; bv_kernel
  have hlen_lt : (bs96 ++ bs224).length < 2 ^ 64 := by rw [hbs320]; decide
  have hlen_eq : (320#64 : BitVec 64).toNat = (bs96 ++ bs224).length := hbs320.symm
  have hdst_eq : memRegion (s0.sp - 4960#64) (bs96 ++ bs224).length =
      memRegion (s0.sp - 4960#64) 320 := by rw [hbs320]
  rw [← hdst_eq]
  wp_steps 13
  wp_call hmemcpy_raw ⟨s0.sp - 4960#64, s0.sp - 3024#64, bs96 ++ bs224⟩
  have hsp_eq : stackAt s.sp spqrRecvCalleeStackX = stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX := by rw [hsp]
  rw [hsp_eq]
  have hbs_inner := bs320_entails_bs96_inner H_inner A (s0.sp - 4992#64) bs96 bs224 pre_pb hbs96 hbs224
  rw [bv_sub_add_lit s0.sp 4992 32, bv_sub_add_lit s0.sp 4992 128,
      optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at hbs_inner
  refine SepWP.focus_weaken hbs_inner (by sep_focus) ?_
  let P_tail : SepProp :=
    memRegion (s0.sp - 4640#64) 1584 ∗
      ((s0.sp - 3056#64) ↦₆₄ w0) ∗ ((s0.sp - 3048#64) ↦₆₄ w1) ∗
      ((s0.sp - 3040#64) ↦₆₄ w2) ∗ ((s0.sp - 3032#64) ↦₆₄ w3) ∗
      ((s0.sp - 3024#64) ↦ₛ (bs96 ++ bs224)) ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      memRegion (s0.sp - 2072#64) 1976
  have hP_tail_join :
      ((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗ P_tail ⊢
        memRegion (s0.sp - 4640#64) 4544 := by
    refine Entails.trans (Entails.of_eq ?_)
      (ownFrame_join_4544_after_decode s0.sp w0 w1 w2 w3 w1 w2 w3 (bs96 ++ bs224) hbs320)
    unfold P_tail; ac_rfl
  have hP_tail_intro :
      P_tail ⊢
        ∃∗ P_t : SepProp,
          ⌜((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗ P_t ⊢
            memRegion (s0.sp - 4640#64) 4544⌝ ∗ P_t :=
    Entails.sepExists_right P_tail (Entails.pure_right hP_tail_join (Entails.refl _))
  refine SepWP.focus_weaken hP_tail_intro (by unfold P_tail; sep_focus) ?_
  exact htail w0 w1 w2 w3 bs96 _ _ hw0_ne hbs96
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Recv

