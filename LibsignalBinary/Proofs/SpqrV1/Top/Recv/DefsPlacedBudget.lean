/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.States2Budget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget

/-!
# Budget-Threaded Relocatable Callee Specs & Contracts for `spqr::recv`

Envelope-parametric and default budget-threaded relocatable callee specifications and contract
bundles (`SpqrRecvPlacedContractsOfEnv`, `SpqrRecvPlacedContracts`) for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (MlKem V1State spqrAuthApi spqrHkdfWith spqrPolyApi)
open CryptoVerification.SpqrV1.Drop (chunkedStatesAt chunkedStatesSize)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost V1InnerHeapPred)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.MessageSerialize (messageAt)
open CryptoVerification.SpqrV1.States.FromPb (StatesFromPbGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Recv
  (StatesRecvGhost resultV1RecvAt statesRecvPreInv statesRecvStackX v1RecvSize)
open CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS seq_clean_lscl spqrRecvPlacedEntry spqrRecvPlacedProg spqrRecvRoPlacedAt
   statesFromPbJumpTablePlacedAt statesIntoPbJumpTablePlacedAt statesRecvJumpTablePlacedAt
   statesRecvRoPlacedAt subroutine_ok_withMemEq_of_lscl)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (chainAddEpochSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (chainNewSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (chainIntoPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (chainRecvKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropSpqrChainSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
  (dropOptProtoSpqrChainSpec dropProtoEpochSliceSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
  (dropOptProtoInnerStatePlacedSpec dropProtoPqRatchetStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.States2Budget (dropChunkedStatesLocal2PlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (pqRatchetStateEncodeToVecSpecX)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (chainFromPbSpecX chainFromSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (spqrDecodeStatePlacedSpec spqrDecodeStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (InitInnerEnv SpqrBoundedEvs StatesIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsBudget (messageDeserializeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget (framelessMemcpyBudgetSpec)

variable [LibsignalPlacement]

/-! ## 1. Re-Exports of `RustAlloc`-Free Block `329` Helpers from `DefsPlaced` -/

export CryptoVerification.SpqrV1.Top.Recv
  (spqrRecvPlacedProg spqrRecvPlacedEntry SepWPpLS subroutine_ok_withMemEq_of_lscl seq_clean_lscl
   statesFromPbJumpTablePlacedAt statesRecvJumpTablePlacedAt statesRecvRoPlacedAt
   statesIntoPbJumpTablePlacedAt spqrRecvRoPlacedAt)

/-! ## 2. Budget-Threaded Relocatable Callee Specifications for Block `329` (`spqr::recv`) -/

/-- Envelope-parametric relocatable budget specification for `spqr::decode_state` (Block `325`). -/
abbrev decodeStatePlacedSpecXOfEnv {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop) :
    Spec (DecodeStateGhost × M.σ) :=
  spqrDecodeStatePlacedSpecOfEnv H_inner A lim PreEnv PostEnv

abbrev decodeStatePlacedSpecX {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DecodeStateGhost × M.σ) :=
  spqrDecodeStatePlacedSpec H_inner A lim

/-- Envelope-parametric relocatable budget specification for `spqr::init_inner` (Block `324`). -/
abbrev initInnerPlacedSpecXOfEnv (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : InitInnerGhost → List AllocEvent → Prop) :
    Spec (InitInnerGhost × M.σ) :=
  LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.initInnerPlacedSpecOfEnv
    M A lim F Env

abbrev initInnerPlacedSpecX (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (InitInnerGhost × M.σ) :=
  LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.initInnerPlacedSpec M A lim F

/-- Envelope-parametric relocatable budget specification for `<States>::from_pb` (Block `333`). -/
abbrev statesFromPbPlacedSpecXOfEnv (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : V1State → List AllocEvent → Prop) :
    Spec (StatesFromPbGhost × M.σ) :=
  LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv
    M A lim F Env

abbrev statesFromPbPlacedSpecX (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (StatesFromPbGhost × M.σ) :=
  LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecX M A lim F

/-- Default bounded allocation-event envelope of `<spqr::v1::chunked::states::States>::recv`
    (Block `332`), bounded linearly in the serialized input `V1State` and `Message` byte
    lengths. -/
def StatesRecvEnv {F : ShaCompress} (x : StatesRecvGhost F) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 128
    (4 * (V1State.encodeRaw x.self.into_pb).length + 4 * (x.msg.serialize 0).length + 8192) evs

omit [LibsignalPlacement] in
theorem StatesRecvEnv.nil {F : ShaCompress} (x : StatesRecvGhost F) : StatesRecvEnv x [] :=
  SpqrBoundedEvs.nil _ _

/-- Budget-form panic postcondition of `<States>::recv` (Block `332`): retains the genuine pure
    model panic `(x.self.recv K x.msg).isPanic = true` while dropping `allocFailedIn s0 sf`. -/
def statesRecvBudgetOnPanic {F : ShaCompress} (K : MlKem) (x : StatesRecvGhost F)
    (s0 sf : State) : SepProp :=
  ⌜(x.self.recv K x.msg).isPanic = true ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Envelope-parametric relocatable budget specification for `<States>::recv` (Block `332`). -/
def statesRecvPlacedSpecOfEnv (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) (K : MlKem)
    (Env : StatesRecvGhost F → List AllocEvent → Prop) :
    Spec (StatesRecvGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.msgA ∧
      statesRecvPreInv x.self ∧
      FitsEnv M lim st (Env x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA v1RecvSize ∗
      chunkedStatesAt A.repAlloc x.selfA x.self ∗
      messageAt spqrPolyApi x.msgA x.msg ∗
      statesRecvRoPlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp statesRecvStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      resultV1RecvAt A.repAlloc (F := F) x.outA (x.self.recv K x.msg) ∗
      memRegion x.selfA chunkedStatesSize ∗
      messageAt spqrPolyApi x.msgA x.msg ∗
      statesRecvRoPlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesRecvStackX
  onPanic := fun (x, _) s0 sf => statesRecvBudgetOnPanic K x s0 sf

abbrev statesRecvPlacedSpec (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) (K : MlKem) :
    Spec (StatesRecvGhost F × M.σ) :=
  statesRecvPlacedSpecOfEnv M A lim F K StatesRecvEnv

/-- Envelope-parametric relocatable budget specification for `<States>::into_pb` (Block `334`). -/
abbrev statesIntoPbPlacedSpecXOfEnv (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : StatesIntoPbGhost F → List AllocEvent → Prop) :
    Spec (StatesIntoPbGhost F × M.σ) :=
  LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.statesIntoPbPlacedSpecXOfEnv
    M A lim F Env

abbrev statesIntoPbPlacedSpecX (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (StatesIntoPbGhost F × M.σ) :=
  LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.statesIntoPbPlacedSpecX M A lim F

/-! ## 3. Budget-Threaded Relocatable Callee Contract Bundle (`SpqrRecvPlacedContracts`) -/

structure SpqrRecvPlacedContractsOfEnv {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop)
    (InitEnv : InitInnerGhost → List AllocEvent → Prop)
    (FromPbEnv : V1State → List AllocEvent → Prop)
    (RecvEnv : StatesRecvGhost F → List AllocEvent → Prop)
    (IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop where
  dealloc_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim)
  memcpy_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "memcpy") framelessMemcpyBudgetSpec
  dropEpochSlice_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim))
  dropOptProtoInnerState_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim))
  dropOptProtoChain_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 266) (withLsCodeLoaded lsmpl (dropOptProtoSpqrChainSpec M A lim))
  dropChain_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 269) (withLsCodeLoaded lsmpl (dropSpqrChainSpec M A lim))
  dropPqRatchetState_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim))
  dropStates_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 273) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedSpec M A lim F))
  decodeState_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfEnv H_inner A lim DecodePreEnv DecodePostEnv))
  initInner_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 324)
      (withLsCodeRoLoaded lsmpl (initInnerPlacedSpecXOfEnv M A lim F InitEnv))
  chainFrom_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 323)
      (withLsCodeRoLoaded lsmpl (chainFromSpecX (spqrHkdfWith F) M A lim))
  chainFromPb_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (chainFromPbSpecX M A lim))
  chainNew_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 363)
      (withLsCodeRoLoaded lsmpl (chainNewSpecX (spqrHkdfWith F) M A lim))
  chainAddEpoch_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith F) M A lim))
  chainRecvKey_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 366)
      (withLsCodeRoLoaded lsmpl (chainRecvKeySpecX M A lim (spqrHkdfWith F)))
  chainIntoPb_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim))
  messageDeserialize_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 351)
      (withLsCodeRoLoaded lsmpl (messageDeserializeSpecX spqrPolyApi M A lim))
  statesFromPb_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F FromPbEnv))
  statesRecv_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl (statesRecvPlacedSpecOfEnv M A lim F K RecvEnv))
  statesIntoPb_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F IntoPbEnv))
  encodeToVec_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 426)
      (withLsCodeRoLoaded lsmpl (pqRatchetStateEncodeToVecSpecX A lim))
  /-- Representation equivalence between `DecodeState.optProtoInnerStateAt H_inner A.repAlloc a
      opt` and `Drop.optProtoInnerStateAt A.repAlloc a opt`. -/
  h_inner_eq :
    ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc a opt

abbrev SpqrRecvPlacedContracts {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State)) : Prop :=
  SpqrRecvPlacedContractsOfEnv H_inner A lim F K
    DecodeStateEnv DecodeStateEnv (InitInnerEnv F) StatesFromPbEnv StatesRecvEnv StatesIntoPbEnv ext

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
