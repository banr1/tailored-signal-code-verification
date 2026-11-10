/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: Extended Hook-Stack (`*Ext`) Callee Bundle & Bridges

**Checked by Lean.** Defines `SpqrRecvContractsExt`, upgrading the six HKDF-backed callees of
`spqr::recv` to `extHookStack` (`+16384` B) contracts within `spqrRecvCalleeStackX` (`126080` B),
along with relative call-site address and monotonicity bridges.
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
open CryptoVerification.SpqrV1.Drop
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

/-! ## 1. Contract-Parameterized (`*Ext`) Callee Bundle `SpqrRecvContractsExt` -/

/-- Contract-parameterized (`*Ext`, `+ 16384` B extern-hook stack headroom) callee bundle for
    `spqr::recv` (`0x5462c..0x55208`, 759 instructions). Upgrades the 6 HKDF-backed callees
    (`init_inner`, `chain_from`, `Chain::new`, `Chain::add_epoch`, `Chain::recv_key`,
    `States::recv`) to their `*OkExt` / `*OkXExt` contracts; all other 7 callees and all
    drop-glue callees do not invoke `hkdf_to_slice` and retain their exact `*OkX` contracts.
    Top-level `spqrRecvStack = 131072` B (`spqrRecvCalleeStackX = 126080` B) is unchanged
    (`40176 ≤ 126080`). -/
structure SpqrRecvContractsExt (H_inner : V1InnerHeapPred) (img : Obj.Image) (A : RustAlloc)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  base_aligned : img.base &&& 0xfff#64 = 0#64
  himg : Obj.Loads libsignalSessionImage img
  hAx : AllocContractsX img A ext
  hdealloc : DeallocOkExt img.base A ext
  decodeState_ok : DecodeStateOkX H_inner img A ext
  initInner_ok : InitInnerOkXExt img A F ext
  chainFrom_ok : ChainFromOkExt img (spqrHkdfWith F) A ext
  chainFromPb_ok : ChainFromPbOkX img A ext
  chainNew_ok : ChainNewOkExt img (spqrHkdfWith F) A ext
  chainAddEpoch_ok : ChainAddEpochOkExt img (spqrHkdfWith F) A ext
  chainRecvKey_ok : ChainRecvKeyOkExt img (spqrHkdfWith F) A ext
  chainIntoPb_ok : ChainIntoPbOkX img A ext
  messageDeserialize_ok : MessageDeserializeOkX spqrPolyApi img A ext
  statesFromPb_ok : StatesFromPbOkX img A F ext
  statesRecv_ok : StatesRecvOkXExt img A F K ext
  statesIntoPb_ok : StatesIntoPbOkX img A F ext
  encodeToVec_ok : PqRatchetStateEncodeToVecOkX img A ext
  /-- Representation equivalence between `DecodeState.optProtoInnerStateAt H_inner A a opt` and
      `Drop.optProtoInnerStateAt A a opt`. -/
  h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt

/-! ## 2. Relative Call-Site Address Bridges (`spqrRecv_*_ok_ext`) -/

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

theorem spqrRecv_decodeState_ok_ext {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
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

theorem spqrRecv_initInner_ok_ext {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (2 ^ 64 - ls_rel% "spqr::init_inner" "spqr::recv"))
      ((initInnerSpecExt A F img.base).inImage img) := by
  have hrel : (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName =
      (tripleRatchetProgAtExt img.base ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "spqr::recv") :=
    Program.fnAddr_rel (k := num% (ls_rel% "spqr::init_inner" "spqr::recv"))
      (b := img.base) (X := Rust.withPanics ext)
      spqrInitInner_fnOff (ls_lemma% fnOff "spqr::recv") (by decide)
  refine sub_ok_of_addr_eq ?_ hC.initInner_ok
  rw [hrel, BitVec.add_assoc]; simp

theorem spqrRecv_chainFrom_ok_ext {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (2 ^ 64 - ls_rel% "spqr::chain_from" "spqr::recv"))
      ((chainFromSpecExt (spqrHkdfWith F) A).inImage img) := by
  have hrel : (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName =
      (tripleRatchetProgAtExt img.base ext).fnAddr chainFromName +
        bv% (ls_rel% "spqr::chain_from" "spqr::recv") :=
    Program.fnAddr_rel (k := num% (ls_rel% "spqr::chain_from" "spqr::recv"))
      (b := img.base) (X := Rust.withPanics ext)
      spqrChainFrom_fnOff (ls_lemma% fnOff "spqr::recv") (by decide)
  refine sub_ok_of_addr_eq ?_ hC.chainFrom_ok
  rw [hrel, BitVec.add_assoc]; simp

theorem spqrRecv_chainFromPb_ok_ext {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::from_pb"))
      ((chainFromPbSpecX A).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::from_pb"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrChainFromPb_fnOff (by decide))
    hC.chainFromPb_ok

theorem spqrRecv_chainNew_ok_ext {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::new"))
      ((chainNewSpecExt (spqrHkdfWith F) A).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::new"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrChainNew_fnOff (by decide))
    hC.chainNew_ok

theorem spqrRecv_chainAddEpoch_ok_ext {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::add_epoch"))
      ((chainAddEpochSpecExt (spqrHkdfWith F) A).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::add_epoch"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrChainAddEpoch_fnOff (by decide))
    hC.chainAddEpoch_ok

theorem spqrRecv_chainRecvKey_ok_ext {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::recv_key"))
      ((chainRecvKeySpecExt (spqrHkdfWith F) A).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::recv_key"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrChainRecvKey_fnOff (by decide))
    hC.chainRecvKey_ok

theorem spqrRecv_chainIntoPb_ok_ext {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::into_pb"))
      ((chainIntoPbSpecX A).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::into_pb"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrChainIntoPb_fnOff (by decide))
    hC.chainIntoPb_ok

theorem spqrRecv_messageDeserialize_ok_ext {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
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

theorem spqrRecv_statesFromPb_ok_ext {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
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

theorem spqrRecv_statesRecv_ok_ext {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_rel% "spqr::recv" "<spqr::v1::chunked::states::States>::recv"))
      (statesRecvSpecXExt A F K img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "spqr::recv" "<spqr::v1::chunked::states::States>::recv"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::recv") spqrStatesRecv_fnOff (by decide))
    hC.statesRecv_ok

theorem spqrRecv_statesIntoPb_ok_ext {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
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

theorem spqrRecv_encodeToVec_ok_ext {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
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

/-! ## 3. Monotonicity Bridges (`*OkX → *OkExt`, `SpqrRecvContracts.toExt`) -/

private theorem stackAt_split_grow_top (sp : BitVec 64) (nX nExt : Nat)
    (hle : nX ≤ nExt := by decide) (hbd : nExt ≤ 131072 := by decide) :
    stackAt sp nExt = memRegion (sp - BitVec.ofNat 64 nExt) (nExt - nX) ∗ stackAt sp nX := by
  have hbd' : nX + (nExt - nX) ≤ 2 ^ 64 := by omega
  have h := ProofLib.stackAt_split_bottom sp nX (nExt - nX) hbd'
  rwa [Nat.add_sub_of_le hle] at h

private theorem sub_ok_inImage_grow_stack_top {α : Type} {prog : Program} {img : Obj.Image}
    {entry : BitVec 64} {specX specExt : Spec α} (nX nExt : Nat)
    (hpre_imp : ∀ x s,
      specExt.pre x s ⊢
        specX.pre x s ∗ memRegion (s.sp - BitVec.ofNat 64 nExt) (nExt - nX))
    (hpost_imp : ∀ x s sf,
      specX.post x s sf ∗ memRegion (s.sp - BitVec.ofNat 64 nExt) (nExt - nX) ⊢
        specExt.post x s sf)
    (hpan_eq : ∀ x s sf, ∃ φ : Prop,
      specX.onPanic x s sf = (⌜φ⌝ ∗ anyHeap) ∧ specExt.onPanic x s sf = (⌜φ⌝ ∗ anyHeap))
    (hexit : ∀ x code s sf, specX.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ x s sf, specX.onOom x s sf = ⌜False⌝)
    (h : subroutine_ok prog entry (specX.inImage img)) :
    subroutine_ok prog entry (specExt.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let Fr := memRegion (s0.sp - BitVec.ofNat 64 nExt) (nExt - nX)
  have hpre' : s0.mem ⊨ (specX.inImage img).pre x s0 ∗ (Fr ∗ R) := by
    change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ specExt.pre x s0) ∗ R at hpre
    change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ specX.pre x s0) ∗ (Fr ∗ R)
    refine Satisfies.mono ?_ hpre
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (hpre_imp x s0))) ?_
    exact Entails.of_eq (by dsimp only [Fr]; ac_rfl)
  refine h.mono_outcome x (Fr ∗ R) s0 hpc hrun hpre' hsp ?_
  intro sf hout
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    change sf.mem ⊨ specX.post x s0 sf ∗ (Fr ∗ R) at hpost
    change sf.mem ⊨ specExt.post x s0 sf ∗ R
    refine Satisfies.mono ?_ hpost
    exact Entails.trans (Entails.of_eq (by dsimp only [Fr]; ac_rfl))
      (sepConj_mono_left (hpost_imp x s0 sf))
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    obtain ⟨φ, hpX, hpE⟩ := hpan_eq x s0 sf
    change sf.mem ⊨ specX.onPanic x s0 sf ∗ (Fr ∗ R) at hpost
    change sf.mem ⊨ specExt.onPanic x s0 sf ∗ R
    rw [hpX] at hpost; rw [hpE]
    refine Satisfies.mono ?_ hpost
    exact Entails.trans
      (Entails.of_eq (show (⌜φ⌝ ∗ anyHeap) ∗ (Fr ∗ R) = (⌜φ⌝ ∗ (anyHeap ∗ Fr)) ∗ R by ac_rfl))
      (sepConj_mono_left (sepConj_mono_right (entails_anyHeap (anyHeap ∗ Fr))))
  · change sf.mem ⊨ specX.onExit x code s0 sf ∗ (Fr ∗ R) at hpost
    rw [hexit] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · change sf.mem ⊨ specX.onOom x s0 sf ∗ (Fr ∗ R) at hpost
    rw [hoom] at hpost; exact (not_satisfies_false_sepConj hpost).elim

theorem initInnerOkXExt_of_okX {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} (h : InitInnerOkX img A F ext) :
    InitInnerOkXExt img A F ext := by
  refine sub_ok_inImage_grow_stack_top initInnerStack initInnerStackExt ?_ ?_
    (fun _ _ _ => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro x s; dsimp only [initInnerSpecExt, initInnerSpecX, initInnerSpec]
    rw [stackAt_split_grow_top s.sp initInnerStack initInnerStackExt]
    exact Entails.of_eq (by ac_rfl)
  · intro x s sf; dsimp only [initInnerSpecExt, initInnerSpecX, initInnerSpec]
    rw [stackAt_split_grow_top s.sp initInnerStack initInnerStackExt]
    exact Entails.of_eq (by ac_rfl)

theorem chainFromOkExt_of_okX {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : ChainFromOkX img hkdf A ext) :
    ChainFromOkExt img hkdf A ext := by
  refine sub_ok_inImage_grow_stack_top chainFromStackX chainFromStackExt ?_ ?_
    (fun _ _ _ => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro x s; dsimp only [chainFromSpecExt, chainFromSpecX]
    rw [stackAt_split_grow_top s.sp chainFromStackX chainFromStackExt]
    exact Entails.of_eq (by ac_rfl)
  · intro x s sf; dsimp only [chainFromSpecExt, chainFromSpecX]
    rw [stackAt_split_grow_top s.sp chainFromStackX chainFromStackExt]
    exact Entails.of_eq (by ac_rfl)

theorem chainNewOkExt_of_okX {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : ChainNewOkX img hkdf A ext) :
    ChainNewOkExt img hkdf A ext := by
  refine sub_ok_inImage_grow_stack_top chainNewStackX chainNewStackExt ?_ ?_
    (fun _ _ _ => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro x s
    dsimp only [chainNewSpecExt, chainNewSpecX]
    simp only [sepConj_assoc]
    refine Entails.pure_left fun ⟨h0, h1, h2, h3, h4, h5, hlen, _⟩ => ?_
    rw [stackAt_split_grow_top s.sp chainNewStackX chainNewStackExt]
    exact Entails.pure_right ⟨h0, h1, h2, h3, h4, h5, hlen⟩ (Entails.of_eq (by ac_rfl))
  · intro x s sf; dsimp only [chainNewSpecExt, chainNewSpecX]
    rw [stackAt_split_grow_top s.sp chainNewStackX chainNewStackExt]
    exact Entails.of_eq (by ac_rfl)

theorem chainAddEpochOkExt_of_okX_recv {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : ChainAddEpochOkX img hkdf A ext) :
    ChainAddEpochOkExt img hkdf A ext := by
  refine sub_ok_inImage_grow_stack_top chainAddEpochStackX chainAddEpochStackExt ?_ ?_
    (fun _ _ _ => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro x s; dsimp only [chainAddEpochSpecExt, chainAddEpochSpecX]
    rw [stackAt_split_grow_top s.sp chainAddEpochStackX chainAddEpochStackExt]
    exact Entails.of_eq (by ac_rfl)
  · intro x s sf; dsimp only [chainAddEpochSpecExt, chainAddEpochSpecX]
    cases Chain.addEpoch hkdf x.self x.epochSecret
    · dsimp only
      apply Entails.pure_left; exact False.elim
    · dsimp only
      rw [stackAt_split_grow_top s.sp chainAddEpochStackX chainAddEpochStackExt]
      exact Entails.of_eq (by ac_rfl)

theorem chainRecvKeyOkExt_of_okX {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : ChainRecvKeyOkX img hkdf A ext) :
    ChainRecvKeyOkExt img hkdf A ext := by
  refine sub_ok_inImage_grow_stack_top chainRecvKeyStackX chainRecvKeyStackExt ?_ ?_
    (fun _ _ _ => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro x s; dsimp only [chainRecvKeySpecExt, chainRecvKeySpecX, chainRecvKeySpecCore]
    rw [stackAt_split_grow_top s.sp chainRecvKeyStackX chainRecvKeyStackExt]
    exact Entails.of_eq (by ac_rfl)
  · intro x s sf; dsimp only [chainRecvKeySpecExt, chainRecvKeySpecX, chainRecvKeySpecCore]
    rw [stackAt_split_grow_top s.sp chainRecvKeyStackX chainRecvKeyStackExt]
    exact Entails.of_eq (by ac_rfl)

theorem statesRecvOkXExt_of_okX {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)} (h : StatesRecvOkX img A F K ext) :
    StatesRecvOkXExt img A F K ext := by
  refine sub_ok_inImage_grow_stack_top statesRecvStackX statesRecvStackXExt ?_ ?_
    (fun _ _ _ => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro x s; dsimp only [statesRecvSpecExt, statesRecvSpec]
    rw [stackAt_split_grow_top s.sp statesRecvStackX statesRecvStackXExt]
    exact Entails.of_eq (by ac_rfl)
  · intro x s sf; dsimp only [statesRecvSpecExt, statesRecvSpec]
    rw [stackAt_split_grow_top s.sp statesRecvStackX statesRecvStackXExt]
    exact Entails.of_eq (by ac_rfl)

theorem SpqrRecvContracts.toExt {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (h : SpqrRecvContracts H_inner img A F K ext) :
    SpqrRecvContractsExt H_inner img A F K ext where
  base_aligned := h.base_aligned
  himg := h.himg
  hAx := AllocContractsX.of_AllocContracts h.hA
  hdealloc := h.hA.dealloc
  decodeState_ok := h.decodeState_ok
  initInner_ok := initInnerOkXExt_of_okX h.initInner_ok
  chainFrom_ok := chainFromOkExt_of_okX h.chainFrom_ok
  chainFromPb_ok := h.chainFromPb_ok
  chainNew_ok := chainNewOkExt_of_okX h.chainNew_ok
  chainAddEpoch_ok := chainAddEpochOkExt_of_okX_recv h.chainAddEpoch_ok
  chainRecvKey_ok := chainRecvKeyOkExt_of_okX h.chainRecvKey_ok
  chainIntoPb_ok := h.chainIntoPb_ok
  messageDeserialize_ok := h.messageDeserialize_ok
  statesFromPb_ok := h.statesFromPb_ok
  statesRecv_ok := statesRecvOkXExt_of_okX h.statesRecv_ok
  statesIntoPb_ok := h.statesIntoPb_ok
  encodeToVec_ok := h.encodeToVec_ok
  h_inner_eq := h.h_inner_eq

end CryptoVerification.SpqrV1.Top.Recv
