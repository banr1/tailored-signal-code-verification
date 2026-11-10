/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Placed
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Version Tail Contracts & `none` Dispatch for `spqr::recv`

Cost-state-generic and default `SpqrRecvEnv` tail contracts (`V0ChainPlacedTailGen`,
`InitInnerPlacedTailGen`, `V1RatchetPlacedTailLSGen`), `Ordering::Equal` `SepWPpLS` lift, and
`versionNegotiation = none` dispatch (`+744..+952`) for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.LibsignalSpqrV1
  (MlKem MsgPreamble PqRatchetState V1State Version VersionNegotiationPB msgPreamble
   spqrDecodeState spqrDeps spqrHkdfWith spqrV1Recv stateVersion)
open CryptoVerification.LibsignalTripleRatchet (VecArg)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (none3Cap' optProtoInnerStateAt optProtoPqRatchetInnerAt)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (TraceVRegs V1InnerHeapPred none2Cap optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.Recv
  (InnerWordInv MsgRemValid SepWPpLS one_ule_zeroExtend64_of_gt optProtoPqRatchetInnerAt_eq_drop
   optProtoPqRatchetInnerAt_expose_word pinnedPqRatchetStateAt pqRatchetStateToPb_inner_none
   pqRatchetStateToPb_inner_some recv_vn_none_inner_none recv_vn_none_inner_some_gt recv_vn_none_lt
   relocPinnedPqRatchetStateAt sp_sub_4992_aligned spqrRecvCalleeStackX spqrRecvPlacedEntry
   spqrRecvPlacedProg spqrRecvRoPlacedAt spqrRecvSavedRegs spqrV1Recv_noPanic_of_err
   spqrV1Recv_noPanic_of_recv_ok spqrV1Recv_recv_of_err spqrV1Recv_recv_of_ok
   version_eq_zero_of_lt_one version_trichotomy vnHeader_sub4992_entails_memRegion_48
   zeroExtend32_bne_one_of_gt zeroExtend32_bne_zero_of_ne)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open CryptoVerification.SpqrV1.Top.Send (decodeState_spqrDeps_of_spqrDecodeState_ok)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv sepWP_spqrRecvPlacedPostOfEnv_of_post0
   spqrRecvBudgetPanicPost spqrRecvPlacedPost spqrRecvPlacedPostOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
  (SpqrRecvDropContractsBudget SpqrRecvEnv.append_freeOnly seq_vm_clean)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
  (step_err_minVersion_752_placed_ofEnv step_err_versionMismatch_892_placed_ofEnv
   step_ok_none_912_placed_ofEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (framelessMemcpyBudgetSpec framelessMemcpySpec)

export CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS.of_sepWP_ret SepWPpLS.pre_mono SepWPpLS.focus_weaken SepWPpLS.focus_pure)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

private theorem align_pre_wp {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (hwp : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ hwp

/-! ## 1. Continuation Contracts for the Three Version Branches (`+496`, `+1076`, `+1532`) -/

/-- Cost-state- and postcondition-generic continuation contract at `+496` for the V0
    chain-ratchet path (`Ordering::Greater`: `pre_pb.versionNegotiation = some vn`,
    `pre_pb.inner = some (.v1 pb)`, `pre.version ≥ vn.minVersion.truncate 8`, and `pre.version >
    1#8`). -/
def V0ChainPlacedTailGen {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cur : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (post : State → SepProp → Prop) (R : SepProp) : Prop :=
  ∀ (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 w26 : BitVec 64) (s : State) (P : SepProp),
    msgPreamble msg.bytes = .ok pre →
    MsgRemValid msg remPtr pre.remaining →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    w0 ≠ none2Cap →
    InnerWordInv pre_pb.inner w26 →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version > 1#8 →
    s.pc = spqrRecvPlacedEntry + 496#64 →
    s.status = .Running →
    s.sp = s0.sp - 4992#64 →
    TraceVRegs s s0 →
    s.readReg64 .x19 = ret →
    s.readReg64 .x20 = w0 →
    s.readReg64 .x21 = pre.index.zeroExtend 64 →
    s.readReg64 .x22 = pre.epoch →
    s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
    s.readReg64 .x24 = remPtr →
    s.readReg64 .x26 = w26 →
    s.readReg64 .x27 = s0.sp - 3056#64 →
    s.readReg64 .x28 = s0.sp - 4288#64 →
    s.readReg64 .x29 = s0.sp - 96#64 →
    P = (spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cur s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      post
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)

abbrev V0ChainPlacedTail {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (evs0 : List AllocEvent)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (R : SepProp) : Prop :=
  V0ChainPlacedTailGen A lim (MC.stepEvents evs0 st_cost) F K ext st msg ret s0
    (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R) R

/-- Cost-state- and postcondition-generic continuation contract at `+1076` for the `init_inner`
    path (`Ordering::Less`: `pre_pb.versionNegotiation = some vn`, `pre_pb.inner = some (.v1
    pb)`, `pre.version ≥ vn.minVersion.truncate 8`, and `pre.version < 1#8`). -/
def InitInnerPlacedTailGen {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cur : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (post : State → SepProp → Prop) (R : SepProp) : Prop :=
  ∀ (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 w26 : BitVec 64) (s : State) (P : SepProp),
    msgPreamble msg.bytes = .ok pre →
    MsgRemValid msg remPtr pre.remaining →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    w0 ≠ none2Cap →
    InnerWordInv pre_pb.inner w26 →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version < 1#8 →
    s.pc = spqrRecvPlacedEntry + 1076#64 →
    s.status = .Running →
    s.sp = s0.sp - 4992#64 →
    TraceVRegs s s0 →
    s.readReg64 .x19 = ret →
    s.readReg64 .x20 = w0 →
    s.readReg64 .x21 = pre.index.zeroExtend 64 →
    s.readReg64 .x22 = pre.epoch →
    s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
    s.readReg64 .x24 = remPtr →
    s.readReg64 .x25 = pre.version.zeroExtend 64 →
    s.readReg64 .x26 = w26 →
    s.readReg64 .x27 = s0.sp - 3056#64 →
    s.readReg64 .x28 = s0.sp - 4288#64 →
    s.readReg64 .x29 = s0.sp - 96#64 →
    P = (spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cur s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      post
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)

abbrev InitInnerPlacedTail {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (evs0 : List AllocEvent)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (R : SepProp) : Prop :=
  InitInnerPlacedTailGen A lim (MC.stepEvents evs0 st_cost) F K ext st msg ret s0
    (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R) R

/-- Cost-state- and postcondition-generic `SepWPpLS` continuation contract at `+1532` for the V1
    ratchet path (`Ordering::Equal`). -/
def V1RatchetPlacedTailLSGen {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cur : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (post : State → SepProp → Prop) (R : SepProp) : Prop :=
  ∀ (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64) (s : State) (P : SepProp),
    msgPreamble msg.bytes = .ok pre →
    MsgRemValid msg remPtr pre.remaining →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    w0 ≠ none2Cap →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    s.pc = spqrRecvPlacedEntry + 1532#64 →
    s.status = .Running →
    s.sp = s0.sp - 4992#64 →
    TraceVRegs s s0 →
    s.readReg64 .x19 = ret →
    s.readReg64 .x20 = w0 →
    s.readReg64 .x21 = pre.index.zeroExtend 64 →
    s.readReg64 .x22 = pre.epoch →
    s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
    s.readReg64 .x24 = remPtr →
    s.readReg64 .x26 = 0#64 →
    s.readReg64 .x27 = s0.sp - 3056#64 →
    s.readReg64 .x28 = s0.sp - 4288#64 →
    s.readReg64 .x29 = s0.sp - 96#64 →
    P = (spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cur s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
      memRegion (s0.sp - 4288#64) 4192 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      post
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)

abbrev V1RatchetPlacedTailLS {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (evs0 : List AllocEvent)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (R : SepProp) : Prop :=
  V1RatchetPlacedTailLSGen A lim (MC.stepEvents evs0 st_cost) F K ext st msg ret s0
    (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R) R

/-! ## 2. `Ordering::Equal` Transition (`+792 .. +820 -> +1532`) in `SepWPpLS` -/

/-- Cost-state- and postcondition-generic `SepWPpLS` transition at `+792 .. +820 -> +1532`. -/
theorem step_equal_792_pLS_gen {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cur : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpySpec)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        optProtoInnerStateAt A.repAlloc a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw0_ne : w0 ≠ none2Cap)
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (htail : V1RatchetPlacedTailLSGen A lim st_cur F K ext st msg ret s0 post R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 792#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cur s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      post
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hmemcpy_raw := hmemcpy_ok
  simp only [framelessMemcpySpec, framelessMemcpyBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec] at hmemcpy_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  rcases htr with ⟨htr_eq, hvregs⟩
  subst hP
  have hto :
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
        ((s0.sp - 4984#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
        optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ⊢
      ∃∗ bs352 : List (BitVec 8),
        ⌜bs352.length = 352⌝ ∗
        ((s0.sp - 4992#64) ↦ₛ bs352) ∗
        (relocPinnedPqRatchetStateAt H_inner A.repAlloc w0 w1 pre_pb).1 bs352 := by
    have h := (relocPinnedPqRatchetStateAt H_inner A.repAlloc w0 w1 pre_pb).2.to_bytes (s0.sp - 4992#64)
    unfold pinnedPqRatchetStateAt at h
    rw [optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at h
    have h8 : (s0.sp - 4992#64) + 8#64 = s0.sp - 4984#64 := bv_sub_add_lit s0.sp 4992 8
    have h16 : (s0.sp - 4992#64) + 16#64 = s0.sp - 4976#64 := bv_sub_add_lit s0.sp 4992 16
    have h48 : (s0.sp - 4992#64) + 48#64 = s0.sp - 4944#64 := bv_sub_add_lit s0.sp 4992 48
    have h128 : (s0.sp - 4992#64) + 128#64 = s0.sp - 4864#64 := bv_sub_add_lit s0.sp 4992 128
    rw [h8, h16, h48, h128] at h
    exact h
  have hsplit_4544 :
      memRegion (s0.sp - 4640#64) 4544 =
        memRegion (s0.sp - 4640#64) 352 ∗ memRegion (s0.sp - 4288#64) 4192 :=
    ProofLib.memRegion_split' (b := s0.sp - 4640#64) (n := 352) (k := 4192)
      (b' := s0.sp - 4288#64) rfl (by bv_omega) (by decide)
  apply SepWPpLS.of_sepWP (mid := (blkPl_329).base + 1532#64)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc ⊢
  refine SepWP.focus_weaken hto (by sep_focus) ?_
  wp_pull_exists; rename_i bs352
  wp_focus_pure; intro hlen352
  rw [hsplit_4544]
  have hof :
      ((s0.sp - 4640#64) ↦ₛ bs352) ∗
        (relocPinnedPqRatchetStateAt H_inner A.repAlloc w0 w1 pre_pb).1 bs352 ⊢
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
        ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4512#64) pre_pb.inner := by
    have h := (relocPinnedPqRatchetStateAt H_inner A.repAlloc w0 w1 pre_pb).2.of_bytes (s0.sp - 4640#64) bs352 hlen352
    unfold pinnedPqRatchetStateAt at h
    rw [optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at h
    have h8 : (s0.sp - 4640#64) + 8#64 = s0.sp - 4632#64 := bv_sub_add_lit s0.sp 4640 8
    have h16 : (s0.sp - 4640#64) + 16#64 = s0.sp - 4624#64 := bv_sub_add_lit s0.sp 4640 16
    have h48 : (s0.sp - 4640#64) + 48#64 = s0.sp - 4592#64 := bv_sub_add_lit s0.sp 4640 48
    have h128 : (s0.sp - 4640#64) + 128#64 = s0.sp - 4512#64 := bv_sub_add_lit s0.sp 4640 128
    rw [h8, h16, h48, h128] at h
    exact h
  have hsrc_mem : ((s0.sp - 4992#64) ↦ₛ bs352) ⊢ memRegion (s0.sp - 4992#64) 352 := by
    rw [← hlen352]
    exact ProofLib.pointsToBytes_entails_memRegion (s0.sp - 4992#64) bs352
  have hdst_mem : memRegion (s0.sp - 4640#64) 352 = memRegion (s0.sp - 4640#64) bs352.length := by
    rw [hlen352]
  have hlen_lt : bs352.length < 2 ^ 64 := by rw [hlen352]; decide
  have hlen_eq : (352#64 : BitVec 64).toNat = bs352.length := hlen352.symm
  refine seq_vm_clean (mid := lsρ "memcpy")
    (P_mid :=
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cur s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦ₛ bs352) ∗
      (relocPinnedPqRatchetStateAt H_inner A.repAlloc w0 w1 pre_pb).1 bs352 ∗
      memRegion (s0.sp - 4640#64) bs352.length ∗
      memRegion (s0.sp - 4288#64) 4192 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun s1 =>
      s1.sp = s0.sp - 4992#64 ∧
      TraceVRegs s1 s0 ∧
      s1.readReg64 .x0 = s0.sp - 4640#64 ∧
      s1.readReg64 .x1 = s0.sp - 4992#64 ∧
      s1.readReg64 .x2 = 352#64 ∧
      s1.readReg64 .x30 = (blkPl_329).base + 808#64 ∧
      s1.readReg64 .x19 = ret ∧
      s1.readReg64 .x20 = w0 ∧
      s1.readReg64 .x21 = pre.index.zeroExtend 64 ∧
      s1.readReg64 .x22 = pre.epoch ∧
      s1.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length ∧
      s1.readReg64 .x24 = remPtr ∧
      s1.readReg64 .x27 = s0.sp - 3056#64 ∧
      s1.readReg64 .x28 = s0.sp - 4288#64 ∧
      s1.readReg64 .x29 = s0.sp - 96#64)
    ?_ ?_
  · rw [hdst_mem]
    by_vm_steps (
      wp_steps 4
      refine align_pre_wp (by sep_ac_rfl) ?_
      wp_done
    )
  · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, ⟨htr1, hvregs1⟩, hx0_1, hx1_1, hx2_1, hlr1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1, hx28_1, hx29_1⟩
    rw [← A.pool_transport lim st_cur s s1 hvm1]
    have hs1_align : s1.spAligned = true := by
      rw [State.spAligned, hsp1]; exact hfsp_align
    wp_call hmemcpy_raw ⟨s0.sp - 4640#64, s0.sp - 4992#64, bs352⟩
    have hvm2 := ‹VmPreserved s1 _›
    let s2 : State := (fun {a b : State} (_ : VmPreserved a b) => b) hvm2
    have hvm2' : VmPreserved s1 s2 := hvm2
    rw [← A.pool_transport lim st_cur s1 s2 hvm2']
    refine SepWP.focus_weaken hsrc_mem (by sep_focus) ?_
    refine SepWP.focus_weaken hof (by sep_focus) ?_
    refine SepWP.focus_weaken
      (optProtoPqRatchetInnerAt_expose_word A.repAlloc (s0.sp - 4512#64) pre_pb.inner)
      (by sep_focus) ?_
    wp_pull_exists; rename_i w8 P_inner
    wp_focus_pure; intro hw8
    wp_focus_pure; intro hunexp
    have hw8_bne3 : (w8 + 3#64 != 0#64) = true := by
      rw [hinner] at hw8
      dsimp [InnerWordInv] at hw8
      simp [bne, hw8]
    have hinner_eq_pb : optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4512#64) pre_pb.inner =
        optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState := by
      rw [hinner]; rfl
    refine seq_vm_clean (mid := (blkPl_329).base + 1532#64)
      (P_mid :=
        spqrRecvRoPlacedAt ∗
        st.at A.repAlloc ∗
        msg.at A.repAlloc ∗
        memRegion ret 48 ∗
        A.pool lim st_cur s2 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗
        ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
        memRegion (s0.sp - 4288#64) 4192 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun s3 =>
        s3.sp = s0.sp - 4992#64 ∧
        TraceVRegs s3 s0 ∧
        s3.readReg64 .x19 = ret ∧
        s3.readReg64 .x20 = w0 ∧
        s3.readReg64 .x21 = pre.index.zeroExtend 64 ∧
        s3.readReg64 .x22 = pre.epoch ∧
        s3.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length ∧
        s3.readReg64 .x24 = remPtr ∧
        s3.readReg64 .x26 = 0#64 ∧
        s3.readReg64 .x27 = s0.sp - 3056#64 ∧
        s3.readReg64 .x28 = s0.sp - 4288#64 ∧
        s3.readReg64 .x29 = s0.sp - 96#64)
      ?_ ?_
    · by_vm_steps (
        wp_steps 4
        refine SepWP.focus_weaken hunexp (by sep_focus) ?_
        rw [hinner_eq_pb]
        refine align_pre_wp (by sep_ac_rfl) ?_
        wp_done
      )
    · intro s3 hpc3 hrun3 hvm3 ⟨hsp3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
        hx26_3, hx27_3, hx28_3, hx29_3⟩
      rw [← A.pool_transport lim st_cur s2 s3 hvm3]
      apply SepWP.done hpc3 hrun3
      exact htail pre remPtr pre_pb pb w0 w1 s3 _ hpre hvalid hdec hinner hw0_ne hmv hmin
        hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx26_3 hx27_3 hx28_3 hx29_3 rfl

/-- Envelope-parametric `SepWPpLS` transition at `+792 .. +820 -> +1532`. -/
theorem step_equal_792_pLS_ofEnv {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpySpec)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        optProtoInnerStateAt A.repAlloc a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw0_ne : w0 ≠ none2Cap)
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (s0 s : State) (P R : SepProp)
    (htail : V1RatchetPlacedTailLSGen A lim (MC.stepEvents evs0 st_cost) F K ext st msg ret s0
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 792#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_equal_792_pLS_gen H_inner A lim (MC.stepEvents evs0 st_cost) F K ext hmemcpy_ok h_inner_eq
    st msg ret pre remPtr pre_pb pb w0 w1 hpre hvalid hdec hinner hw0_ne hmv hmin
    s0 s P R _ htail hs0_align hpc hrun hsp htr
    hx19 hx20 hx21 hx22 hx23 hx24 hx27 hx28 hx29 hP

theorem step_equal_792_pLS {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (evs0 : List AllocEvent)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpySpec)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        optProtoInnerStateAt A.repAlloc a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw0_ne : w0 ≠ none2Cap)
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (s0 s : State) (P R : SepProp)
    (htail : V1RatchetPlacedTailLS A lim st_cost evs0 F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 792#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_equal_792_pLS_ofEnv H_inner A lim st_cost (SpqrRecvEnv st msg) evs0 F K ext
    hmemcpy_ok h_inner_eq st msg ret pre remPtr pre_pb pb w0 w1
    hpre hvalid hdec hinner hw0_ne hmv hmin s0 s P R htail hs0_align hpc hrun hsp htr
    hx19 hx20 hx21 hx22 hx23 hx24 hx27 hx28 hx29 hP

/-! ## 3. Version Dispatch at `+744` (`pre_pb.versionNegotiation = none`) -/

/-- Envelope-parametric dispatch at `+744` when `pre_pb.versionNegotiation = none` (`w0 =
    noneCap`). -/
theorem step_vn_none_744_placed_ofEnv {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpySpec)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        optProtoInnerStateAt A.repAlloc a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (w1 w26 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = none)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp)
    (htail_eq : V1RatchetPlacedTailLSGen A lim (MC.stepEvents evs0 st_cost) F K ext st msg ret s0
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 744#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = if (w26 + 3#64 != 0#64) = true then 1#64 else 0#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = noneCap)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ noneCap) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc noneCap w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hd_ok := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  subst hP
  cases hinner : pre_pb.inner with
  | none =>
    have hw26_eq : w26 = none3Cap' := by
      rw [hinner] at hw26; exact hw26
    subst hw26_eq
    have hx8_0 : s.readReg64 .x8 = 0#64 := by
      rw [hx8]; rfl
    have hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none) :=
      spqrV1Recv_recv_of_ok
        (recv_vn_none_inner_none (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn
          (pqRatchetStateToPb_inner_none hinner))
    apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    by_cases hv0 : pre.version = 0#8
    · rw [hv0] at hx25
      wp_steps 5
      refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
      exact step_ok_none_912_placed_ofEnv A lim st_cost Env evs0 hevs_free
        (spqrV1Recv F K) ext hC st msg ret pre_pb noneCap w1 none3Cap'
        hw26 hok s0 _ _ R _ rfl hs0_align
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [← hinner]; simp only [wp_norm, arm64_norm, *]) hcl
    · have hne0 := zeroExtend32_bne_zero_of_ne hv0
      wp_steps 5
      refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
      exact step_ok_none_912_placed_ofEnv A lim st_cost Env evs0 hevs_free
        (spqrV1Recv F K) ext hC st msg ret pre_pb noneCap w1 none3Cap'
        hw26 hok s0 _ _ R _ rfl hs0_align
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [← hinner]; simp only [wp_norm, arm64_norm, *]) hcl
  | some inn =>
    cases inn with
    | v1 pb =>
      have hw26_ne : ¬((w26 + 3#64 == 0#64) = true) := by
        rw [hinner] at hw26; exact hw26
      have hw26_bne : (w26 + 3#64 != 0#64) = true := by
        simp [bne, hw26_ne]
      have hx8_1 : s.readReg64 .x8 = 1#64 := by
        rw [hx8, hw26_bne]; rfl
      rcases version_trichotomy pre.version with hlt | heq | hgt
      · have hv0 : pre.version = 0#8 := version_eq_zero_of_lt_one hlt
        have hrust : CryptoVerification.LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F)
            st.bytes msg.bytes = .error (.err .minimumVersion) := by
          refine recv_vn_none_lt (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn ?_
          simp [stateVersion, pqRatchetStateToPb_inner_some hinner, Version.toU8, hlt]
        have herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error false :=
          spqrV1Recv_recv_of_err hrust
        have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
          spqrV1Recv_noPanic_of_err hrust
        apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
        dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
        rw [hv0] at hx25
        wp_steps 2
        refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 hnp ?_
        exact step_err_minVersion_752_placed_ofEnv A lim st_cost Env evs0 hevs_free
          (spqrV1Recv F K) ext hC st msg ret pre_pb noneCap w1 w26
          hw26 herr s0 _ _ R _ rfl hs0_align
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hinner]; simp only [wp_norm, arm64_norm, *]) hcl
      · apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 792#64)
        dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
        rw [heq] at hx25
        wp_steps 5
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        exact step_equal_792_pLS_ofEnv H_inner A lim st_cost Env evs0 F K ext hmemcpy_ok h_inner_eq
          st msg ret pre remPtr pre_pb pb noneCap w1
          hpre hvalid hdec hinner (by decide) heq
          (by intro vn hvn'; rw [hvn] at hvn'; cases hvn')
          s0 _ _ R htail_eq hs0_align
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hinner]; simp only [wp_norm, arm64_norm, *])
      · have herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error false :=
          spqrV1Recv_recv_of_err
            (recv_vn_none_inner_some_gt (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn
              (pqRatchetStateToPb_inner_some hinner) hgt)
        have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
          spqrV1Recv_noPanic_of_err
            (recv_vn_none_inner_some_gt (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn
              (pqRatchetStateToPb_inner_some hinner) hgt)
        have hule1 := one_ule_zeroExtend64_of_gt hgt
        have hbne1 := zeroExtend32_bne_one_of_gt hgt
        apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
        dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
        rw [hvn]
        dsimp only [optVersionNegotiationPBTailAt]
        wp_focus_pure; intro _
        wp_steps 5
        refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
        refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 hnp ?_
        exact step_err_versionMismatch_892_placed_ofEnv A lim st_cost Env evs0 hevs_free
          (spqrV1Recv F K) ext hC st msg ret pre_pb w26
          hw26 herr s0 _ _ R _ rfl hs0_align
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [← hinner]; simp only [wp_norm, arm64_norm, *]; sep_ac_rfl) hcl

theorem step_vn_none_744_placed {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpySpec)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        optProtoInnerStateAt A.repAlloc a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (w1 w26 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = none)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp)
    (htail_eq : V1RatchetPlacedTailLS A lim st_cost evs0 F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 744#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = if (w26 + 3#64 != 0#64) = true then 1#64 else 0#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = noneCap)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ noneCap) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc noneCap w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_vn_none_744_placed_ofEnv H_inner A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC hmemcpy_ok h_inner_eq st msg ret pre remPtr pre_pb w1 w26
    hpre hvalid hdec hvn hw26 s0 s P R htail_eq hs0_align hpc hrun hsp htr
    hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudgetAux
