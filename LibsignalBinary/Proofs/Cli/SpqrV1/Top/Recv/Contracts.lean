/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsExt
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.EncodeToVec.Final
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrow
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPb
import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPb
import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKey
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Top
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Contracts
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import ProofLib.SepLogic.WPp

/-!
# Top-Level `spqr::recv` Contract Assembly (`DEV-SPQR4`)

Assembles `SpqrRecvContracts` and `SpqrRecvContractsExt` for `canonicalV1InnerHeap` on the
CLI image from leaf `OkX` / `OkExt` contracts and `TripleRatchetHooks` + `SpqrHooks`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession (Crypto ShaCompress)

open CryptoVerification

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchet



open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.Auth

open CryptoVerification.SpqrV1.ChainProofs

open CryptoVerification.SpqrV1.Kdf

open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

open CryptoVerification.SpqrV1.GF.UnacceleratedMul

open CryptoVerification.SpqrV1.GF.Mul2U16

open CryptoVerification.SpqrV1.Poly

open CryptoVerification.SpqrV1.Poly.EncodeBytes

open CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.Prost.MessageMerge

open CryptoVerification.SpqrV1.Prost.EncodeToVec

open CryptoVerification.SpqrV1.Top

open CryptoVerification.SpqrV1.Top.DecodeState

open CryptoVerification.SpqrV1.Top.InitInner

open CryptoVerification.SpqrV1.Top.ChainFrom

open CryptoVerification.SpqrV1.Top.MessageDeserialize

open CryptoVerification.SpqrV1.States.FromPb

open CryptoVerification.SpqrV1.States.Leaves

open CryptoVerification.SpqrV1.States.Recv

open CryptoVerification.SpqrV1.States.IntoPb


open CryptoVerification.CodeLayout

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Assemble `SpqrRecvContracts canonicalV1InnerHeap img A F K ext` from the already-proved
    callee `OkX` theorems and remaining leaf contracts. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecvContracts_of_okX
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hDecodeState : DecodeStateOkX canonicalV1InnerHeap img A ext)
    (hAuthNew : AuthNewOkX img F A ext)
    (hChainNew : ChainNewOkX img (spqrHkdfWith F) A ext)
    (hChainAddEpoch : ChainAddEpochOkX img (spqrHkdfWith F) A ext)
    (hChainRecvKey : ChainRecvKeyOkX img (spqrHkdfWith F) A ext)
    (hMsgDeser : MessageDeserializeOkX spqrPolyApi img A ext)
    (hStatesFromPb : StatesFromPbOkX img A F ext)
    (hStatesRecv : StatesRecvOkX img A F K ext) :
    SpqrRecvContracts canonicalV1InnerHeap img A F K ext where
  base_aligned := ProofLib.ObjectLoad.base_aligned_of_loads himg
  himg := himg
  hA := hA
  decodeState_ok := hDecodeState
  initInner_ok := init_inner_ok_x himg hA hAuthNew
  chainFrom_ok :=
    chainFrom_ok_of_contracts_x
      (chain_from_pb_ok hA.dealloc)
      hChainNew
  chainFromPb_ok := chain_from_pb_ok hA.dealloc
  chainNew_ok := hChainNew
  chainAddEpoch_ok := hChainAddEpoch
  chainRecvKey_ok := hChainRecvKey
  chainIntoPb_ok := chain_into_pb_ok hA
  messageDeserialize_ok := hMsgDeser
  statesFromPb_ok := hStatesFromPb
  statesRecv_ok := hStatesRecv
  statesIntoPb_ok := states_into_pb_ok_x hA
  encodeToVec_ok := CryptoVerification.Cli.SpqrV1.Prost.EncodeToVec.pqRatchetStateEncodeToVec_okX hA himg
  h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A

/-- Assemble `SpqrRecvContracts canonicalV1InnerHeap img A C.F K (tripleRatchetExterns C ctl abs)`
from `TripleRatchetHooks`, `SpqrHooks`, `Obj.Loads`, `StatesFromPbOkX`, and `StatesRecvOkX`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecvContracts_of_hooks
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (_hSH : SpqrHooks C A K abs)
    (hFromPb : StatesFromPbOkX img A C.F (tripleRatchetExterns C ctl abs))
    (hStatesRecv : StatesRecvOkX img A C.F K (tripleRatchetExterns C ctl abs)) :
    SpqrRecvContracts canonicalV1InnerHeap img A C.F K (tripleRatchetExterns C ctl abs) := by
  let ext := tripleRatchetExterns C ctl abs
  have hStage2 : Stage2Contracts img.base C A ctl uuidTryParse (spqrV1 C.F K) ext :=
    Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl (spqrV1 C.F K) abs hTH
  have hA : AllocContracts img.base A ext := hStage2.toAllocContracts
  have hAX : AllocContractsX img A ext := AllocContractsX.of_AllocContracts hA
  have hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith C.F) ext :=
    hkdf_to_slice_spqr_ok_ext img C himg
      (ConsumeMessageKeyTransfer.sessionExterns_le C ctl abs)
  have hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec :=
    hookSat_memcpy_ro_tripleRatchetExterns C ctl abs
  have hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A) :=
    hookSat_allocZeroed_tripleRatchetExterns hTH.allocZeroed
  exact CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecvContracts_of_okX himg hA
    (decode_state_ok_x himg hStage2)
    (auth_new_ok_x himg hhkdf hA hRO hZero)
    (chainNew_ok_ext_x himg hhkdf (vec_deque_grow_ok_x hA) hAX)
    (chainAddEpoch_ok_ext_x himg hhkdf (vec_deque_grow_ok_x hA) hAX)
    (chainRecvKey_ok_alloc_x himg (slice_concat_2_ok_x hA hRO) hhkdf hA)
    (messageDeserialize_spqrPolyApi_ok_of_contracts_x img A ext hA hStage2.format_inner)
    hFromPb
    hStatesRecv

/-- Assemble `SpqrRecvContractsExt canonicalV1InnerHeap img A F K ext` from `AllocContractsX`,
`DeallocOkExt`, and the individual `*OkX` / `*OkExt` callee contracts. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecvContractsExt_of_okX
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hDecodeState : DecodeStateOkX canonicalV1InnerHeap img A ext)
    (hInitInner : InitInnerOkXExt img A F ext)
    (hChainNew : ChainNewOkExt img (spqrHkdfWith F) A ext)
    (hChainAddEpoch : ChainAddEpochOkExt img (spqrHkdfWith F) A ext)
    (hChainRecvKey : ChainRecvKeyOkExt img (spqrHkdfWith F) A ext)
    (hChainIntoPb : ChainIntoPbOkX img A ext)
    (hMsgDeser : MessageDeserializeOkX spqrPolyApi img A ext)
    (hStatesFromPb : StatesFromPbOkX img A F ext)
    (hStatesRecv : StatesRecvOkXExt img A F K ext)
    (hStatesIntoPb : StatesIntoPbOkX img A F ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecOkX img A ext) :
    SpqrRecvContractsExt canonicalV1InnerHeap img A F K ext where
  base_aligned := ProofLib.ObjectLoad.base_aligned_of_loads himg
  himg := himg
  hAx := hAx
  hdealloc := hdealloc
  decodeState_ok := hDecodeState
  initInner_ok := hInitInner
  chainFrom_ok :=
    chainFrom_ok_of_contracts_ext
      (chain_from_pb_ok hdealloc)
      hChainNew
  chainFromPb_ok := chain_from_pb_ok hdealloc
  chainNew_ok := hChainNew
  chainAddEpoch_ok := hChainAddEpoch
  chainRecvKey_ok := hChainRecvKey
  chainIntoPb_ok := hChainIntoPb
  messageDeserialize_ok := hMsgDeser
  statesFromPb_ok := hStatesFromPb
  statesRecv_ok := hStatesRecv
  statesIntoPb_ok := hStatesIntoPb
  encodeToVec_ok := hEncodeToVec
  h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A

end CryptoVerification.SpqrV1.Top.Recv
