/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.Defs
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncodedLen
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerHeader
import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.Encode1
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParams1
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1Sent1
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1Received1
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirection1
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSent
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPoly
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainEncode
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncode
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodedLen
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked2
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3a
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeader
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesPolyDecExact
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesPolyExact
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncode
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridges
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerDispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<signal_session_ratchet::Coins>` Phase 3e Dispatch & Master `PqRatchetState` Encode

Dispatches all 11 `V1State` variants at `+6616` and composes full `PqRatchetState`
encoded-length, buffer allocation, and encoding (`+4288/+4364 -> +6216`) for the CLI image.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr hiding tripleRatchetProgAtExt
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Auth hiding SepWPp.pure_elim
open CryptoVerification.SpqrV1.Prost.MessageEncode
open CryptoVerification.SpqrV1.Prost.EncodeToVec hiding allowPanic_not_exited

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  Prost.EncodeToVec.noneCap2_add_two_beq_zero Prost.EncodeToVec.noneCap2_add_two_bne_zero
  ProtoRepr.noneCap_add_two_beq_zero ProtoRepr.noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

/-! ## 1. `.rodata` Jump-Table Loader and `[local#1]` Callee `subroutine_ok` Bridges -/

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.rodata_spqrSendEncodeJumpTable_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 340) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 344) + 22)) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 340) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 344) + 22)) (n := 22) (bs := spqrSendEncodeJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chainEncodedLen_call_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (chainEncodedLenPinnedSpec A)) := by
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chainEncodedLen_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chainEncodedLen1_ok b A ext s0

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_epochEncodedLen_call_ok {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)) := by
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_epochEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_epochEncodedLen1_ok hres b A ext s0

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeVarint_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStack A)) := by
  apply etv_encodeVarint_exact_of_fit (by decide)
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeVarint2_fnAddr_eq b ext hfn]
  exact subroutine_ok_withStepInv s0 (CryptoVerification.Cli.SpqrV1.Varint.encode_varint2_fit_ok_ext hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeVarint_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStackX A)) := by
  apply etv_encodeVarint_exact_of_fit (by decide)
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeVarint2_fnAddr_eq img.base ext hfn]
  exact subroutine_ok_withStepInv_x img s0 hinv0
    (CryptoVerification.Cli.SpqrV1.Varint.encodeVarint2_fit_ok_ext_x img A ext (CryptoVerification.Cli.SpqrV1.Varint.do_reserve2_ok_ext_x (img := img) hA))

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeChainParams_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStack A)) := by
  apply etv_encodeChainParams_exact_of_spec (by decide)
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeChainParams1_fnAddr_eq b ext hfn]
  exact subroutine_ok_withStepInv s0 (CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_chainParams_1_ok_ext hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeChainParams_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStackX A)) := by
  apply etv_encodeChainParams_exact_of_spec (by decide)
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeChainParams1_fnAddr_eq img.base ext hfn]
  exact subroutine_ok_withStepInv_x img s0 hinv0 (CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_chainParams_1_ok_ext_x hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeEpochDirection_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStack A)) := by
  apply etv_encodeEpochDirection_exact_of_spec (by decide)
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeEpochDirection1_fnAddr_eq b ext hfn]
  exact subroutine_ok_withStepInv s0 (CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_epochDirection_1_pinned_ok_ext hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeEpochDirection_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStackX A)) := by
  apply etv_encodeEpochDirection_exact_of_spec (by decide)
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeEpochDirection1_fnAddr_eq img.base ext hfn]
  exact subroutine_ok_withStepInv_x img s0 hinv0 (CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_epochDirection_1_pinned_ok_ext_x hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_authEncode_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (authEncodeExactSpecOf doReserveStack A)) := by
  apply etv_authEncode_exact_of_spec (by decide)
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_authEncode1_fnAddr_eq b ext hfn]
  exact subroutine_ok_withStepInv s0 (CryptoVerification.Cli.SpqrV1.Auth.auth_encode_1_pinned_ok_ext hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_authEncode_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (authEncodeExactSpecOf doReserveStackX A)) := by
  apply etv_authEncode_exact_of_spec (by decide)
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_authEncode1_fnAddr_eq img.base ext hfn]
  exact subroutine_ok_withStepInv_x img s0 hinv0 (CryptoVerification.Cli.SpqrV1.Auth.auth_encode_1_pinned_ok_ext_x hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyEncoderEncode_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (etvPolyEncoderExactSpecOf doReserveStack A)) := by
  apply etv_polyEncoderEncode_exact_of_spec
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyEncoderEncode1_fnAddr_eq b ext hfn]
  exact subroutine_ok_withStepInv s0 (CryptoVerification.Cli.SpqrV1.Top.Send.encode_polyEncoder_1_exact_pinned_ok_ext hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyEncoderEncode_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (etvPolyEncoderExactSpecOf doReserveStackX A)) := by
  apply etv_polyEncoderEncode_exact_of_spec
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyEncoderEncode1_fnAddr_eq img.base ext hfn]
  exact subroutine_ok_withStepInv_x img s0 hinv0 (CryptoVerification.Cli.SpqrV1.Top.Send.encode_polyEncoder_1_exact_pinned_ok_ext_x hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyDecoderEncode_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (etvPolyDecoderExactSpecOf doReserveStack A)) := by
  apply etv_polyDecoderEncode_exact_of_spec
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyDecoderEncode1_fnAddr_eq b ext hfn]
  exact subroutine_ok_withStepInv s0 (CryptoVerification.Cli.SpqrV1.Top.Send.encode_polyDecoder_1_exact_pinned_ok_ext hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyDecoderEncode_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (etvPolyDecoderExactSpecOf doReserveStackX A)) := by
  apply etv_polyDecoderEncode_exact_of_spec
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyDecoderEncode1_fnAddr_eq img.base ext hfn]
  exact subroutine_ok_withStepInv_x img s0 hinv0 (CryptoVerification.Cli.SpqrV1.Top.Send.encode_polyDecoder_1_exact_pinned_ok_ext_x hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentCt1ReceivedEncode_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf doReserveStack A)) := by
  apply etv_ekSentCt1ReceivedEncode_of_spec
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentCt1ReceivedEncode1_fnAddr_eq b ext hfn]
  exact subroutine_ok_withStepInv s0 (CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ek_sent_ct1_received_encode_1_pinned_ok_ext hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentCt1ReceivedEncode_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf doReserveStackX A)) := by
  apply etv_ekSentCt1ReceivedEncode_of_spec
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentCt1ReceivedEncode1_fnAddr_eq img.base ext hfn]
  exact subroutine_ok_withStepInv_x img s0 hinv0 (CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ek_sent_ct1_received_encode_1_pinned_ok_ext_x hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEncode_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (etvCt1SentEncodeSpecOf doReserveStack A)) := by
  apply etv_ct1SentEncode_of_spec
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEncode1_fnAddr_eq b ext hfn]
  exact subroutine_ok_withStepInv s0 (CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ct1_sent_encode_1_pinned_ok_ext hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEncode_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (etvCt1SentEncodeSpecOf doReserveStackX A)) := by
  apply etv_ct1SentEncode_of_spec
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEncode1_fnAddr_eq img.base ext hfn]
  exact subroutine_ok_withStepInv_x img s0 hinv0 (CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ct1_sent_encode_1_pinned_ok_ext_x hA)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_keysUnsampledEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64}
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::KeysUnsampled as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen)) := by
  apply etv_leafEncLen16_withStepInv; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_keysUnsampledEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.ProtoRepr.keysUnsampledEncodedLen_local1_pinned_ok_ext b A ext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_headerSentEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64}
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderSent as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A) headerSentPBEncodedLen)) := by
  apply etv_leafEncLen16_withStepInv; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_headerSentEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_pinned_ok_ext b A ext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chunkedHeaderSentEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64}
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (leafEncLen48Spec (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen)) := by
  apply etv_leafEncLen48_withStepInv; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chunkedHeaderSentEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.ProtoRepr.chunkedHeaderSentEncodedLen_local1_pinned_ok_ext b A ext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64}
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSent as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A) ekSentPBEncodedLen)) := by
  apply etv_leafEncLen16_withStepInv; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentEncodedLen_local1_pinned_ok_ext b A ext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentCt1ReceivedEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64}
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)) := by
  apply etv_leafEncLen16_withStepInv; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentCt1ReceivedEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_pinned_ok_ext b A ext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64}
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)) := by
  apply etv_leafEncLen16_withStepInv; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_pinned_ok_ext b A ext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_noHeaderReceivedEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64}
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::NoHeaderReceived as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen)) := by
  apply etv_leafEncLen16_withStepInv; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_noHeaderReceivedEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.ProtoRepr.noHeaderReceivedEncodedLen_local1_pinned_ok_ext b A ext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_headerReceivedEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64}
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)) := by
  apply etv_leafEncLen16_withStepInv; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_headerReceivedEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.ProtoRepr.headerReceivedEncodedLen_local1_pinned_ok_ext b A ext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chunkedCt1SampledEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64}
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Sampled as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (chunkedCt1SampledEncodedLenPinnedSpec A)) := by
  apply etv_leafEncLen48_withStepInv; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chunkedCt1SampledEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLen_local1_pinned_ok_ext b A ext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEkReceivedEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64}
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen)) := by
  apply etv_leafEncLen16_withStepInv; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEkReceivedEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_pinned_ok_ext b A ext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct2SentEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64}
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A) ct2SentPBEncodedLen)) := by
  apply etv_leafEncLen16_withStepInv; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct2SentEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.ProtoRepr.ct2SentEncodedLen_local1_pinned_ok_ext b A ext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyDecoderEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64}
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)) := by
  apply etv_leafEncLen16_withStepInv; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyDecoderEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_pinned_ok_ext b A ext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyEncoderEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64}
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) (s0 : State) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)) := by
  apply etv_leafEncLen16_withStepInv; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyEncoderEncodedLen1_fnAddr_eq b ext hfn]
  exact CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_pinned_ok_ext b A ext

/-! ## 2. `StepSendInnerStateAt6616` Dispatch Across All 11 Variants (`+6616 -> +6216`) -/

/-- Parametric 11-variant dispatch at `entry + 6616#64` over `withStack etvMemcpyRegionSpec` and a
pluggable `.headerSent` handler (shared by 0-stack and 4K-stack instantiations). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_inner_at_6616_of_variants_gen {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64) (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    {s0 : State}
    (hHeaderSent : ∀ v, StepSendInnerStateAt6616 resStack b A ext entry roBase s0 (.headerSent v))
    (hkuLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::KeysUnsampled as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen)))
    (hhs16Len : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderSent as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A) headerSentPBEncodedLen)))
    (hekLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)))
    (hnhrLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::NoHeaderReceived as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen)))
    (hhrLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)))
    (hct1SampledLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Sampled as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (chunkedCt1SampledEncodedLenPinnedSpec A)))
    (hct1SentEkLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen)))
    (hct1SentLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)))
    (hct2Len : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A) ct2SentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")) (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack)))
    (hekEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hpolyEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (is : V1State.InnerState) :
    StepSendInnerStateAt6616 resStack b A ext entry roBase s0 is := by
  cases is with
  | keysUnsampled v => exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_keysUnsampled_at_6616 hres b A ext hfn hkuLen hvarint hauthEnc v
  | keysSampled v => exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_keysSampled_at_6616_4k hres b A ext hfn hhs16Len hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | headerSent v => exact hHeaderSent v
  | ct1Received v => exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_ct1Received_at_6616 hres b A ext hfn hekLen hpolyEncLen hvarint hekEnc hpolyEnc v
  | ekSentCt1Received v => exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_ekSentCt1Received_at_6616 hres b A ext hfn hekLen hpolyDecLen hvarint hekEnc hpolyDec v
  | noHeaderReceived v => exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_noHeaderReceived_at_6616 hres b A ext hfn hnhrLen hpolyDecLen hvarint hauthEnc hpolyDec v
  | headerReceived v => exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_headerReceived_at_6616_4k hres b A ext hfn hhrLen hpolyDecLen hvarint hauthEnc hmemcpy hpolyDec v
  | ct1Sampled v => exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_ct1Sampled_at_6616 hres b A ext hfn hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec v
  | ekReceivedCt1Sampled v => exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_ekReceivedCt1Sampled_at_6616_4k hres b A ext hfn hct1SentEkLen hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | ct1Acknowledged v => exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_ct1Acknowledged_at_6616 hres b A ext hfn hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec v
  | ct2Sampled v => exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_ct2Sampled_at_6616 hres b A ext hfn hct2Len hpolyEncLen hvarint hauthEnc hpolyEnc v

/-- `doReserveStack` instantiation of `step_send_inner_at_6616_of_variants_gen` discharging all
11 `V1State.InnerState` variant callees from `hA : AllocContracts b A ext`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_inner_at_6616
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    {entry roBase : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) (is : V1State.InnerState) :
    StepSendInnerStateAt6616 doReserveStack b A ext entry roBase s0 is :=
  CryptoVerification.Cli.SpqrV1.Top.Send.step_send_inner_at_6616_of_variants_gen (by decide) b A ext hfn
    (fun v => CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_headerSent_at_6616 (by decide) b A ext hfn
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chunkedHeaderSentEncodedLen_ok b A ext hfn s0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentEncodedLen_ok b A ext hfn s0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeVarint_ok hA hfn s0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_authEncode_ok hA hfn s0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_etvMemcpy_ok hA hfn)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyEncoderEncode_ok hA hfn s0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyDecoderEncode_ok hA hfn s0) v)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_keysUnsampledEncodedLen_ok b A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_headerSentEncodedLen_ok b A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentCt1ReceivedEncodedLen_ok b A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_noHeaderReceivedEncodedLen_ok b A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_headerReceivedEncodedLen_ok b A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chunkedCt1SampledEncodedLen_ok b A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEkReceivedEncodedLen_ok b A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEncodedLen_ok b A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct2SentEncodedLen_ok b A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyEncoderEncodedLen_ok b A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyDecoderEncodedLen_ok b A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeVarint_ok hA hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_authEncode_ok hA hfn s0)
    (subroutine_ok_withStack_of_subroutine_ok
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_etvMemcpy_ok hA hfn)
      (encodeToVecCalleeStackOf doReserveStack))
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentCt1ReceivedEncode_ok hA hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEncode_ok hA hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyEncoderEncode_ok hA hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyDecoderEncode_ok hA hfn s0)
    is

/-- `doReserveStackX` (`Obj.Image`) instantiation of `step_send_inner_at_6616_of_variants_gen`
discharging all 11 `V1State.InnerState` variant callees from `hA : AllocContracts img.base A ext`
and `hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_inner_at_6616_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {entry roBase : BitVec 64} (hfn : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (s0 : State) (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab)
    (is : V1State.InnerState) :
    StepSendInnerStateAt6616 doReserveStackX img.base A ext entry roBase s0 is :=
  CryptoVerification.Cli.SpqrV1.Top.Send.step_send_inner_at_6616_of_variants_gen (by decide) img.base A ext hfn
    (fun v => CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_headerSent_at_6616 (by decide) img.base A ext hfn
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chunkedHeaderSentEncodedLen_ok img.base A ext hfn s0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentEncodedLen_ok img.base A ext hfn s0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeVarint_ok_x hA hfn s0 hinv0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_authEncode_ok_x hA hfn s0 hinv0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_etvMemcpy_ok hA hfn)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyEncoderEncode_ok_x hA hfn s0 hinv0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyDecoderEncode_ok_x hA hfn s0 hinv0) v)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_keysUnsampledEncodedLen_ok img.base A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_headerSentEncodedLen_ok img.base A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentCt1ReceivedEncodedLen_ok img.base A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_noHeaderReceivedEncodedLen_ok img.base A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_headerReceivedEncodedLen_ok img.base A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chunkedCt1SampledEncodedLen_ok img.base A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEkReceivedEncodedLen_ok img.base A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEncodedLen_ok img.base A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct2SentEncodedLen_ok img.base A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyEncoderEncodedLen_ok img.base A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyDecoderEncodedLen_ok img.base A ext hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeVarint_ok_x hA hfn s0 hinv0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_authEncode_ok_x hA hfn s0 hinv0)
    (subroutine_ok_withStack_of_subroutine_ok
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_etvMemcpy_ok hA hfn)
      (encodeToVecCalleeStackOf doReserveStackX))
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ekSentCt1ReceivedEncode_ok_x hA hfn s0 hinv0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_ct1SentEncode_ok_x hA hfn s0 hinv0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyEncoderEncode_ok_x hA hfn s0 hinv0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyDecoderEncode_ok_x hA hfn s0 hinv0)
    is

/-! ## 3. Parametric `step_send_inner_len_31b48_roV1` and Combined Field Encoding (`+4996..`) -/

/-- `entry + 4844#64` to `entry + 4920#64`, parametric in `roV1`
(instantiated to `roV1 = b + 0x9d53a#64` for `CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLenLocal1Name`):
Computes `Option<pq_ratchet_state::Inner>::encoded_len` and sets
`x20 = optPqRatchetInnerCap g.inner st.inner`,
`x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_inner_len_31b48_roV1 (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry roV1 : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    {s0 s2 : State}
    (hV1StateLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (sp : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s2.pc = entry + 4844#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = sp) (htr : s2.trace = s0.trace)
    (hx22 : s2.readReg64 .x22 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen st.chain))
    (hx24 : s2.readReg64 .x24 = sp + 4704#64)
    (hinv2 : StepInv s0 s2)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt sp spqrSendCalleeStack) ∗ F)
    (hnext : ∀ s3 : State,
      s3.pc = entry + 4920#64 → s3.status = .Running → s3.sp = sp →
      s3.trace = s0.trace →
      s3.readReg64 .x19 = s2.readReg64 .x19 →
      s3.readReg64 .x20 = optPqRatchetInnerCap g.inner st.inner →
      s3.readReg64 .x21 = s2.readReg64 .x21 →
      s3.readReg64 .x22 = s2.readReg64 .x22 →
      s3.readReg64 .x23 = s2.readReg64 .x23 →
      s3.readReg64 .x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      s3.readReg64 .x25 = s2.readReg64 .x25 →
      s3.readReg64 .x26 = s2.readReg64 .x26 →
      s3.readReg64 .x27 = s2.readReg64 .x27 →
      s3.readReg64 .x28 = s2.readReg64 .x28 →
      s3.readReg64 .fp = s2.readReg64 .fp → StepInv s0 s3 →
      SepWPp (tripleRatchetProgAtExt b ext) ret s3
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt sp spqrSendCalleeStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s2 P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4844 76
  subst hfn
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hV1StateLen ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches; subst hP
  refine sepWPp_extract_pure
    ((optPqRatchetInnerCap g.inner st.inner + 3#64 == 0#64) = !st.inner.isSome ∧
     (optPqRatchetInnerCap g.inner st.inner + 3#64 != 0#64) = st.inner.isSome)
    (fun R' hm => ?_) (fun hin_cap => ?_)
  · apply optPqRatchetInnerPBPinnedAt_cap_bounds (A := A) (p := (sp + 4704#64) + 0x80#64)
      (R := optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
        optChainPBPinnedAt A g.chain ((sp + 4704#64) + 0x30#64) st.chain ∗
        (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
        stackAt sp spqrSendCalleeStack ∗ F ∗ R')
    rw [pqRatchetStatePBPinnedAt] at hm
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq]
    cases hin : st.inner with
    | none =>
      rw [hin] at hin_cap
      simp only [Option.isSome_none, Bool.not_false] at hin_cap
      have ⟨hadd1, hadd2⟩ := EncodedLen.adds_no_overflow_of_eq (a := 0)
        (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
          optChainPBFieldEncodedLen st.chain)
        (c := pqRatchetStatePBEncodedLen st)
        (by unfold pqRatchetStatePBEncodedLen; rw [hin]; dsimp [optPqRatchetInnerPBFieldEncodedLen])
        (by omega)
      apply SepWPp.of_sepWP_cs (mid := entry + 4920#64); wp_steps
      apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre ?_
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hin]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv2.trans hinv))
      rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq, hin]
      exact Entails.of_eq (by ac_rfl)
    | some innerVal =>
      cases innerVal with
      | v1 v1s =>
        rw [hin] at hin_cap
        simp only [Option.isSome_some, Bool.not_true] at hin_cap
        have ⟨hfit, hopt_lt, hvar_lt⟩ := v1StatePBEncodedLen_lt_of_state hin hlen
        have hls := EncodedLen.cmp_ls_false_of_lt hvar_lt hopt_lt
        have hopt_in := bv_optInner_some_eq v1s
        have ⟨hadd1, hadd2⟩ := EncodedLen.adds_no_overflow_of_eq
          (a := optPqRatchetInnerPBFieldEncodedLen (some (.v1 v1s)))
          (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
            optChainPBFieldEncodedLen st.chain)
          (c := pqRatchetStatePBEncodedLen st)
          (by unfold pqRatchetStatePBEncodedLen; rw [hin])
          (by omega)
        apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps
        apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_bl
        refine SepWPp.call_cs (x := PinnedEncLenGhost.mk ((sp + 4704#64) + 0x80#64) g.inner v1s)
          (F := optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
            optChainPBPinnedAt A g.chain ((sp + 4704#64) + 0x30#64) st.chain ∗
            memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - v1StateEncodedLenStack) ∗ F)
          hV1StateLen (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
          (ret_pc := entry + 4872#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
        · intro R' hm
          rw [← optPqRatchetInnerPBPinnedAt_eq A g.inner ((sp + 4704#64) + 0x80#64) (some (.v1 v1s)),
            optPqRatchetInnerPBPinnedAt,
            stackAt_spqrSendCallee_split_enc sp v1StateEncodedLenStack (by decide)] at hm
          simp only [arm64_norm] at hm
          simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, arm64_norm, hsp, hx24,
            sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hinv2.trans hinv_bl, hfit⟩, ?_⟩
          exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
        · intro sf code R' _ hm
          exact allowPanic_not_exited hm
        · intro sf _ hm
          simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
          exact hm.1.elim
        · intro sm hpcm hrunm hspm hcsm hinv_call
          simp only [arm64_norm, hsp] at hspm
          dsimp only [withStepInv, v1StateEncodedLenRoPinnedSpec]
          rw [sepConj_assoc]
          refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
          simp only [arm64_norm, htr] at htrm
          rcases hcsm with ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, _⟩
          simp only [arm64_norm, hx22, hx24] at hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm
          apply SepWPp.of_sepWP_cs (mid := entry + 4920#64); wp_steps
          apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_post
          refine SepWPp.weaken_pre ?_
            (hnext _
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by rw [hin]; simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (((hinv2.trans hinv_bl).trans hinv_call).trans hinv_post))
          rw [pqRatchetStatePBPinnedAt, hin, optPqRatchetInnerPBPinnedAt,
            stackAt_spqrSendCallee_split_enc sp v1StateEncodedLenStack (by decide)]
          simp only [arm64_norm, hsp]
          exact Entails.of_eq (by ac_rfl)

/-- Continuation-style contract for the `chain` field-encoding step (`+5604 -> +6140`) inside
`spqr::send`, abstracting over `step_send_chain_31e40` (0-stack) and `step_send_chain_31e40_ext` (4K). -/
def _root_.CryptoVerification.Cli.SpqrV1.Top.Send.StepSendChainAt31e40
    (resStack : Nat) (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (entry : BitVec 64) (s0 : State) (sp ptr : BitVec 64)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState) : Prop :=
  ∀ {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop},
    s.pc = entry + 5604#64 → s.status = .Running → s.sp = sp → s.trace = s0.trace →
    s.readReg64 .x25 = optChainCap g.chain st.chain → StepInv s0 s →
    P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
      vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
        (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation) ∗
      A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F →
    (∀ sm : State,
      sm.pc = entry + 6140#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = optChainCap g.chain st.chain → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation ++
              Proto.encodeOptMessage ChainPB.encodeRaw 2#32 st.chain) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) →
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))

/-- Parametric combined field-encoding step (`+4996/+5604 -> +6216`) over `withStack etvMemcpyRegionSpec`
and a pluggable `StepSendChainAt31e40` continuation. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_encode_fields_31be0_gen {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64) (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roV1 roBase : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (hjt : HasSendEncodeJumpTableAddr b ext entry roBase) {s0 s : State}
    (hv1Len : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")) (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack)))
    (hcp_call : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (hInnerAt6616 : ∀ is : V1State.InnerState, StepSendInnerStateAt6616 resStack b A ext entry roBase s0 is)
    (sp ptr v0 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    (hChain : CryptoVerification.Cli.SpqrV1.Top.Send.StepSendChainAt31e40 resStack b A ext entry s0 sp ptr g st)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (if st.versionNegotiation.isSome then entry + 4996#64 else entry + 5604#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx0 : st.versionNegotiation.isSome → s.readReg64 .x0 = ptr)
    (hx20 : s.readReg64 .x20 = optPqRatchetInnerCap g.inner st.inner)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx28 : s.readReg64 .x28 = sp + 4192#64) (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗ (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
      A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
    (hnext : ∀ (sm : State) (w0 : BitVec 64),
      sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗ (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr (PqRatchetState.encodeRaw st) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  refine CryptoVerification.Cli.SpqrV1.Top.Send.step_send_versionNeg_31be0_ext b A ext hfn hvarint hmemcpy hcp_call
    sp ptr v0 g st hlen halign
    (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ F)
    hpc hrun hsp htr hx0 hx25 hx28 hinv0 (by ac_rfl) ?_
  intro s1 w0 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_23 hs1_25 hs1_27 hs1_28 hs1_fp hinv1
  rw [hx20] at hs1_20
  refine hChain (s := s1) (R := R) (ret := ret) (Q := Q)
    (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ (sp ↦₆₄ w0) ∗ F)
    hpcs1 hruns1 hsps1 htrs1 hs1_25 hinv1 (by ac_rfl) ?_
  intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_19 hs2_20 hs2_21 hs2_23 hs2_25 hs2_27 hs2_28 hs2_fp hinv2
  rw [hs1_19] at hs2_19; rw [hs1_20] at hs2_20; rw [hs1_21] at hs2_21
  rw [hs1_23] at hs2_23; rw [hs1_27] at hs2_27; rw [hs1_28] at hs2_28; rw [hs1_fp] at hs2_fp
  refine CryptoVerification.Cli.SpqrV1.Top.Send.step_send_inner_32058 hres b A ext hfn hjt hv1Len hvarint hInnerAt6616
    sp ptr (optChainCap g.chain st.chain) g st hlen halign (F := (sp ↦₆₄ w0) ∗ F)
    hpcs2 hruns2 hsps2 htrs2 hs2_20 hs2_25 hinv2 (by ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  rw [hs2_19] at hm19; rw [hs2_21] at hm21; rw [hs2_23] at hm23
  rw [hs2_27] at hm27; rw [hs2_28] at hm28; rw [hs2_fp] at hmfp
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)

/-! ## 4. Full Phase 3 Encode Step (`+4288/+4364 -> +6216`) -/

/-- Parametric Phase 3 step from `entry + 4768#64` (`+4768 -> +6216`) over `withStack etvMemcpyRegionSpec`
and a pluggable `StepSendChainAt31e40` continuation. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_encode_from_31afc_gen {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64) (hle_stack : encodeToVecCalleeStackOf resStack ≤ spqrSendCalleeStack)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roV1 roBase : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (hjt : HasSendEncodeJumpTableAddr b ext entry roBase) {s0 s1 : State}
    (hChainLen1 : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1Name) (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (hv1Len : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) (withStepInv s0 spqrSendShimStackSpec))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_alloc")) (withStepInv s0 (spqrSendRustAllocStackSpec A)))
    (hhandle : (tripleRatchetProgAtExt b ext).externAt? (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "alloc::raw_vec::handle_error")) = some Rust.panicked)
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")) (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack)))
    (hcp_call : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (hInnerAt6616 : ∀ is : V1State.InnerState, StepSendInnerStateAt6616 resStack b A ext entry roBase s0 is)
    (sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 : BitVec 64)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    (hChain : ∀ ptr, CryptoVerification.Cli.SpqrV1.Top.Send.StepSendChainAt31e40 resStack b A ext entry s0 sp ptr g st)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s1.pc = entry + 4768#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = sp) (htr : s1.trace = s0.trace)
    (hx20 : s1.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation))
    (hx22 : s1.readReg64 .x22 = msg_cap) (hx24 : s1.readReg64 .x24 = sp + 4704#64)
    (hx25 : s1.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s1.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hx28 : s1.readReg64 .x28 = sp + 4192#64) (hinv1 : StepInv s0 s1)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗ (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr w0 : BitVec 64),
      sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s1.readReg64 .x19 → sm.readReg64 .x21 = s1.readReg64 .x21 →
      sm.readReg64 .x23 = s1.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s1.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s1.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗ (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr (PqRatchetState.encodeRaw st) ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ ((sp + 24#64) ↦₆₄ msg_cap)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s1 P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  refine CryptoVerification.Cli.SpqrV1.Top.Send.step_send_chain_len_31afc b A ext hfn hChainLen1
    sp msg_cap v_sp18 g st hlen halign
    (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ A.pool ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 1424#64) ↦₆₄ v_590) ∗
      ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F)
    hpc hrun hsp htr hx20 hx22 hx24 hx25 hinv1 (by ac_rfl) ?_
  intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_19 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25 hs2_26 hs2_27 hs2_28 hs2_fp hinv2
  rw [hx26] at hs2_26; rw [hx28] at hs2_28
  refine CryptoVerification.Cli.SpqrV1.Top.Send.step_send_inner_len_31b48_roV1 b A ext hfn hv1Len sp g st hlen halign
    (F := (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ A.pool ∗ (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗
      ((sp + 24#64) ↦₆₄ msg_cap) ∗ ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F)
    hpcs2 hruns2 hsps2 htrs2 hs2_22 hs2_24 hinv2 (by ac_rfl) ?_
  intro s3 hpcs3 hruns3 hsps3 htrs3 hs3_19 hs3_20 hs3_21 hs3_22 hs3_23 hs3_24 hs3_25 hs3_26 hs3_27 hs3_28 hs3_fp hinv3
  rw [hs2_19] at hs3_19; rw [hs2_21] at hs3_21; rw [hs2_23] at hs3_23
  rw [hs2_25] at hs3_25; rw [hs2_26] at hs3_26; rw [hs2_27] at hs3_27; rw [hs2_28] at hs3_28; rw [hs2_fp] at hs3_fp
  refine CryptoVerification.Cli.SpqrV1.Top.Send.step_send_alloc_31b94 b A ext hfn hshim halloc hhandle
    sp v_sp10 v_590 v_598 v_5a0 g st hpos hlen halign
    (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ (sp ↦₆₄ v0) ∗ ((sp + 24#64) ↦₆₄ msg_cap) ∗ F)
    hpcs3 hruns3 hsps3 htrs3 hs3_24 hs3_25 hs3_26 hinv3 (by ac_rfl) ?_
  intro s4 ptr hpcs4 hruns4 hsps4 htrs4 hs4_0 hs4_19 hs4_20 hs4_21 hs4_22 hs4_23 hs4_24 hs4_25 hs4_26 hs4_27 hs4_28 hs4_fp hinv4
  rw [hs3_19] at hs4_19; rw [hs3_20] at hs4_20; rw [hs3_21] at hs4_21
  rw [hs3_23] at hs4_23; rw [hs3_27] at hs4_27; rw [hs3_28] at hs4_28; rw [hs3_fp] at hs4_fp
  let F_stack := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack)
    (spqrSendCalleeStack - encodeToVecCalleeStackOf resStack)
  refine CryptoVerification.Cli.SpqrV1.Top.Send.step_send_encode_fields_31be0_gen hres b A ext hfn hjt
    hv1Len hvarint hmemcpy hcp_call hInnerAt6616 sp ptr v0 g st hlen halign (hChain ptr)
    (F := F_stack ∗ ((sp + 24#64) ↦₆₄ msg_cap) ∗ F)
    hpcs4 hruns4 hsps4 htrs4 (fun _ => hs4_0) hs4_20 hs4_25 hs4_28 hinv4
    (by rw [stackAt_spqrSendCallee_split_enc sp (encodeToVecCalleeStackOf resStack) hle_stack]
        dsimp only [F_stack]; ac_rfl) ?_
  intro sm w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  rw [hs4_19] at hm19; rw [hs4_21] at hm21; rw [hs4_23] at hm23; rw [hs4_27] at hm27; rw [hs4_fp] at hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm ptr w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  rw [stackAt_spqrSendCallee_split_enc sp (encodeToVecCalleeStackOf resStack) hle_stack]
  dsimp only [F_stack]; exact Entails.of_eq (by ac_rfl)

/-- Full Phase 3 step from `entry + (if st.versionNegotiation.isSome then 4288#64 else 4364#64)`
(`+4288 / +4364`) to `entry + 6216#64` (`+6216`):
chains `CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_unified` (`+4288 / +4364 -> +4768`) + `CryptoVerification.Cli.SpqrV1.Top.Send.step_send_encode_from_31afc` (`+4768 -> +6216`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_some_3191c_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4288#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : vn.authKey.length < 2 ^ 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4768#64) s
      (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
      (fun s' P' => VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn)) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)) := by
  refine SepWP.seq (CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_authKey_3191c_vregs A s g vn F hpc hrun hsp_align hlen) ?_
  intro s1 P1 hpc1 _ ⟨hv1, hrun1, hsp1, htr1, hx8_1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp1, hP1⟩
  rw [← hsp1] at hP1
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.seq (CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_dir_31940_vregs A s1 g vn F hpc1 hrun1 (by rw [hsp1]; exact hsp_align)) ?_
  intro s2 P2 hpc2 _ ⟨hv2, hrun2, hsp2, htr2, hx8_2, hx9_2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp2, hP2⟩
  rw [← hsp2] at hP2
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.seq (CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_minVer_31974_vregs A s2 g vn F hpc2 hrun2 (by rw [hsp2, hsp1]; exact hsp_align)) ?_
  intro s3 P3 hpc3 _ ⟨hv3, hrun3, hsp3, htr3, hx8_3, hx9_3, hx10_3, hx19_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp3, hP3⟩
  rw [← hsp3] at hP3
  refine SepWP.weaken_pre hP3 ?_
  refine SepWP.seq (CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_chainParams_319a0_vregs A s3 g vn F hpc3 hrun3 (by rw [hsp3, hsp2, hsp1]; exact hsp_align)) ?_
  intro s4 P4 hpc4 _ ⟨hv4, hrun4, hsp4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hfp4, hP4⟩
  have hsp3_eq : s3.sp = s.sp := hsp3.trans (hsp2.trans hsp1)
  rw [hsp3_eq] at hP4
  refine SepWP.weaken_pre hP4 ?_
  refine SepWP.mono (CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_combine_31ad4_vregs s4 vn (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
    hpc4 hrun4 (hx8_4.trans (hx8_3.trans (hx8_2.trans hx8_1)))
    (hx9_4.trans (hx9_3.trans hx9_2)) (hx10_4.trans hx10_3) hx11_4) ?_
  intro s5 P5 _ _ ⟨hv5, hrun5, hsp5, htr5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hfp5, hP5⟩
  exact ⟨⟨hv5.eq.trans (hv4.eq.trans (hv3.eq.trans (hv2.eq.trans hv1.eq)))⟩, hrun5, hsp5.trans (hsp4.trans hsp3_eq),
    htr5.trans (htr4.trans (htr3.trans (htr2.trans htr1))),
    hx19_5.trans (hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_1))),
    hx20_5,
    hx21_5.trans (hx21_4.trans (hx21_3.trans (hx21_2.trans hx21_1))),
    hx22_5.trans (hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_1))),
    hx23_5.trans (hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_1))),
    hx24_5.trans (hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_1))),
    hx25_5.trans (hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_1))),
    hx26_5.trans (hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_1))),
    hx27_5.trans (hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_1))),
    hx28_5.trans (hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_1))),
    hfp5.trans (hfp4.trans (hfp3.trans (hfp2.trans hfp1))),
    hP5⟩

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_unified_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : PqRatchetStatePBGhost) (st : PqRatchetState) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName +
      (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4768#64) s
      (optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) st.versionNegotiation ∗ F)
      (fun s' P' => VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) st.versionNegotiation ∗ F)) := by
  cases hvn : st.versionNegotiation with
  | none =>
    rw [hvn] at hpc
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    exact CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_none_31968_vregs s (optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) none ∗ F) hpc hrun
  | some vn =>
    rw [hvn] at hpc
    simp only [Option.isSome_some, ↓reduceIte] at hpc
    have hlen_vn := vn_authKey_len_lt_of_state hvn hlen
    have hpre_eq :
        optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) (some vn) ∗ F =
        versionNegotiationRest A g.vn (s.sp + 4704#64) vn ∗
          (((s.sp + 4704#64) ↦₆₄ optVersionNegCap g.vn (some vn)) ∗ F) := by
      rw [optVersionNegotiationPBPinnedAt_eq A g.vn (s.sp + 4704#64) (some vn)]
      dsimp only [optVersionNegRest]
      ac_rfl
    refine SepWP.weaken_pre (Entails.of_eq hpre_eq) ?_
    refine SepWP.mono (CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_some_3191c_vregs A s g.vn vn
      (((s.sp + 4704#64) ↦₆₄ optVersionNegCap g.vn (some vn)) ∗ F) hpc hrun hsp_align hlen_vn) ?_
    intro s' P' _ _ ⟨hv', hrun', hsp', htr', hx19', hx20', hx21', hx22', hx23', hx24', hx25', hx26', hx27', hx28', hfp', hP'⟩
    refine ⟨hv', hrun', hsp', htr', hx19', hx20', hx21', hx22', hx23', hx24', hx25', hx26', hx27', hx28', hfp', ?_⟩
    exact Entails.trans hP' (Entails.of_eq hpre_eq.symm)

/-- Parametric Phase 3 step from `entry + (if st.versionNegotiation.isSome then 4288#64 else 4364#64)`
to `entry + 6216#64` over `withStack etvMemcpyRegionSpec` and a pluggable `StepSendChainAt31e40` continuation. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_encode_from_vn_len_gen {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64) (hle_stack : encodeToVecCalleeStackOf resStack ≤ spqrSendCalleeStack)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roV1 roBase : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    (hjt : HasSendEncodeJumpTableAddr b ext entry roBase) {s0 s : State}
    (hChainLen1 : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLenLocal1Name) (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (hv1Len : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) (withStepInv s0 spqrSendShimStackSpec))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_alloc")) (withStepInv s0 (spqrSendRustAllocStackSpec A)))
    (hhandle : (tripleRatchetProgAtExt b ext).externAt? (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "alloc::raw_vec::handle_error")) = some Rust.panicked)
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")) (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack)))
    (hcp_call : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (hInnerAt6616 : ∀ is : V1State.InnerState, StepSendInnerStateAt6616 resStack b A ext entry roBase s0 is)
    (sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 : BitVec 64)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    (hChain : ∀ ptr, CryptoVerification.Cli.SpqrV1.Top.Send.StepSendChainAt31e40 resStack b A ext entry s0 sp ptr g st)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msg_cap) (hx24 : s.readReg64 .x24 = sp + 4704#64)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hx28 : s.readReg64 .x28 = sp + 4192#64) (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗ (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr w0 : BitVec 64),
      sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗ (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr (PqRatchetState.encodeRaw st) ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ ((sp + 24#64) ↦₆₄ msg_cap)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  have hpc' : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName +
      (if st.versionNegotiation.isSome then 4288#64 else 4364#64) := by rw [hfn]; exact hpc
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := by rw [hsp, beq_iff_eq]; exact halign
  let F_vn : SepProp :=
    optChainPBPinnedAt A g.chain ((sp + 4704#64) + 48#64) st.chain ∗
      optPqRatchetInnerPBPinnedAt A g.inner ((sp + 4704#64) + 128#64) st.inner ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool ∗ stackAt sp spqrSendCalleeStack ∗ (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F
  have hP_eq :
      (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗ (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
        (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
        ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F =
      optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) st.versionNegotiation ∗ F_vn := by
    rw [hsp]; unfold pqRatchetStatePBPinnedAt; dsimp only [F_vn]; ac_rfl
  rw [hP_eq]
  apply SepWPp.of_sepWP_cs (mid := (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4768#64)
  refine SepWP.mono (CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_unified_vregs A s g st F_vn hpc' hrun hsp_align hlen) ?_
  intro s1 P1 hpc1 _ ⟨hv1, hrun1, hsp1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp1, hP1⟩
  refine ⟨hv1, fun hinv_s1 => ?_⟩
  rw [hfn] at hpc1; rw [hsp] at hsp1
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx28] at hx28_1
  refine SepWPp.weaken_pre (Entails.trans hP1 (Entails.of_eq hP_eq.symm)) ?_
  refine CryptoVerification.Cli.SpqrV1.Top.Send.step_send_encode_from_31afc_gen hres hle_stack b A ext hfn hjt
    hChainLen1 hv1Len hshim halloc hhandle hvarint hmemcpy hcp_call hInnerAt6616
    sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 g st hpos hlen halign hChain
    hpc1 hrun1 hsp1 htr1' hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 (hinv0.trans hinv_s1) rfl ?_
  intro sm ptr w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  rw [hx19_1] at hm19; rw [hx21_1] at hm21; rw [hx23_1] at hm23; rw [hx27_1] at hm27; rw [hfp1] at hmfp
  exact hnext sm ptr w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m

/-- Self-contained `doReserveStack` version of `step_send_encode_from_vn_len_gen`, discharging all
callee `subroutine_ok` obligations from `hA : AllocContracts b A ext` and `hb : b &&& 0xfff#64 = 0#64`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_encode_from_vn_len_self_contained
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    {s0 s : State}
    (sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 : BitVec 64)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msg_cap) (hx24 : s.readReg64 .x24 = sp + 4704#64)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hx28 : s.readReg64 .x28 = sp + 4192#64) (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      ((b + bv% (ls_xref% (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 56) (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 60))) ↦ᵣ v1StateJumpTableBytes) ∗
      ((b + bv% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 340) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 344) + 22)) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr w0 : BitVec 64),
      sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          ((b + bv% (ls_xref% (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 56) (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 60))) ↦ᵣ v1StateJumpTableBytes) ∗
          ((b + bv% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 340) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 344) + 22)) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr (PqRatchetState.encodeRaw st) ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ ((sp + 24#64) ↦₆₄ msg_cap)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hjt : HasSendEncodeJumpTableAddr b ext entry (b + bv% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 340) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 344) + 22)) := by
    rw [← hfn]; exact CryptoVerification.Cli.SpqrV1.Top.Send.hasSendEncodeJumpTableAddr b ext hb
  have hChainLen_entry : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (chainEncodedLenPinnedSpec A)) := by
    rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chainEncodedLen_fnAddr_eq b ext hfn]
    exact CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chainEncodedLen1_ok b A ext s0
  exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_encode_from_vn_len_gen (by decide) (by decide) b A ext hfn hjt
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chainEncodedLen1_ok b A ext s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_v1StateEncodedLen1_ok b A ext hb hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_shim_ok_enc hA hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_rustAlloc_ok hA hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_handle_alloc_error b ext hfn)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeVarint_ok hA hfn s0)
    (subroutine_ok_withStack_of_subroutine_ok
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_etvMemcpy_ok hA hfn)
      (encodeToVecCalleeStackOf doReserveStack))
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeChainParams_ok hA hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.step_send_inner_at_6616 hA hfn s0)
    sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 g st hpos hlen halign
    (fun ptr {s1 R1 ret1 P1 F1 Q1} => CryptoVerification.Cli.SpqrV1.Top.Send.step_send_chain_31e40 (by decide) b A ext hfn
      (s := s1) hChainLen_entry
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_epochEncodedLen_call_ok (by decide) b A ext hfn s0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeVarint_ok hA hfn s0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_etvMemcpy_ok hA hfn)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeEpochDirection_ok hA hfn s0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeChainParams_ok hA hfn s0)
      sp ptr g st hlen halign (R := R1) (ret := ret1) (P := P1) (F := F1) (Q := Q1))
    hpc hrun hsp htr hx22 hx24 hx25 hx26 hx28 hinv0 hP hnext

/-- Self-contained `doReserveStackX` (`Obj.Image`) version of `step_send_encode_from_vn_len_gen`,
discharging all callee `subroutine_ok` obligations from `hA : AllocContracts img.base A ext`,
`himg : Obj.Loads libsignalSessionImage img`, and `hinv_img : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_encode_from_vn_len_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) (himg : Obj.Loads libsignalSessionImage img)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    {s0 s : State} (hinv_img : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab)
    (sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 : BitVec 64)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msg_cap) (hx24 : s.readReg64 .x24 = sp + 4704#64)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hx28 : s.readReg64 .x28 = sp + 4192#64) (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      ((img.base + bv% (ls_xref% (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 56) (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 60))) ↦ᵣ v1StateJumpTableBytes) ∗
      ((img.base + bv% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 340) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 344) + 22)) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr w0 : BitVec 64),
      sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          ((img.base + bv% (ls_xref% (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 56) (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 60))) ↦ᵣ v1StateJumpTableBytes) ∗
          ((img.base + bv% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 340) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 344) + 22)) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr (PqRatchetState.encodeRaw st) ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ ((sp + 24#64) ↦₆₄ msg_cap)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hjt : HasSendEncodeJumpTableAddr img.base ext entry (img.base + bv% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 340) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 344) + 22)) := by
    rw [← hfn]; exact CryptoVerification.Cli.SpqrV1.Top.Send.hasSendEncodeJumpTableAddr img.base ext hb
  have hChainLen_entry : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (chainEncodedLenPinnedSpec A)) := by
    rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chainEncodedLen_fnAddr_eq img.base ext hfn]
    exact CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chainEncodedLen1_ok img.base A ext s0
  exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_encode_from_vn_len_gen (by decide) (by decide) img.base A ext hfn hjt
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_chainEncodedLen1_ok img.base A ext s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_v1StateEncodedLen1_ok img.base A ext hb hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_shim_ok_enc hA hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_rustAlloc_ok hA hfn s0)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_handle_alloc_error img.base ext hfn)
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeVarint_ok_x hA hfn s0 hinv_img)
    (subroutine_ok_withStack_of_subroutine_ok
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_etvMemcpy_ok hA hfn)
      (encodeToVecCalleeStackOf doReserveStackX))
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeChainParams_ok_x hA hfn s0 hinv_img)
    (CryptoVerification.Cli.SpqrV1.Top.Send.step_send_inner_at_6616_x hA hfn s0 hinv_img)
    sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 g st hpos hlen halign
    (fun ptr {s1 R1 ret1 P1 F1 Q1} => CryptoVerification.Cli.SpqrV1.Top.Send.step_send_chain_31e40 (by decide) img.base A ext hfn
      (s := s1) hChainLen_entry
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_epochEncodedLen_call_ok (by decide) img.base A ext hfn s0)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeVarint_ok_x hA hfn s0 hinv_img)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_etvMemcpy_ok hA hfn)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeEpochDirection_ok_x hA hfn s0 hinv_img)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeChainParams_ok_x hA hfn s0 hinv_img)
      sp ptr g st hlen halign (R := R1) (ret := ret1) (P := P1) (F := F1) (Q := Q1))
    hpc hrun hsp htr hx22 hx24 hx25 hx26 hx28 hinv0 hP hnext

end CryptoVerification.SpqrV1.Top.Send
