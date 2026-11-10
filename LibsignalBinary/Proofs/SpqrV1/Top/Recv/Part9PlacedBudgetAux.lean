/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9Placed
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable `Ordering::Greater` Substeps for `spqr::recv`

Envelope-parametric and default `SpqrRecvEnv` proofs of `step_v0_after_chainFrom_604_placed`
(`+604..+740`) and `step_v0_chain_none_2108_placed` (`+2108..+2948`) for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl sepWP_seq_lscl withMemEq)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain ChainPB ChainParamsPB Direction Error MlKem MsgPreamble PqRatchetState V1State
   VersionNegotiationPB chainFrom chainFromVersionNegotiation msgPreamble recvResultExactKeyAt
   spqrDecodeState spqrHkdfWith spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainGhost ChainRecvKeyGhost RecvPrevFits chainAt chainNewStackX chainNewVal
   chainRecvKeyStackX chainRepr chainSize recvKeyOkAt recvKeyPostAt)
open CryptoVerification.SpqrV1.Drop (dropSpqrChainStack optProtoPqRatchetInnerAt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (extractLsb_hi_append64 extractLsb_lo_append64)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
  (add_one_beq_zero_of_ne_noneCap chainAtHeap)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation (optChainParamsPBAt spqrErrorTag)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm
  (chainNew_post_entails_chainRepr direction_fromI32_or ult_one_toI32)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS byte_memRegion79_sub2096_to_v0_err chainRepr_sub_entails_words11 chainWords11
   encodeRaw_v0_state_len_lt err_payload_expose fp_sub_32_add_eq fp_sub_48_add_eq
   frame1912_split_err_2388 frame2544_join_v0 frame4544_join_err_740 frame_pure_pre
   hsp_add_544_eq' hsp_add_560_eq' memRegion_872_sub2968_split_ok_680
   memRegion_88_sub2096_split_byte8 memRegion_88_sub3056_split_32_56
   memRegion_88_sub_entails_words11 recvKeyErrAt_entails_code_memRegion23 recvPrevFits_of_chainFrom
   recv_err_words_foldX ret_48_split sp_setPState sp_sub_4992_aligned sp_writeVReg128
   spqrErrorTag_eq_zero_iff spqrRecvCalleeStackX spqrRecvPlacedEntry spqrRecvPlacedProg
   spqrRecvRoPlacedAt spqrRecvSavedRegs spqrV1Recv_gt_chainFrom_err spqrV1Recv_gt_recvKey_err
   spqrV1Recv_gt_recvKey_ok spqrV1Recv_gt_recvKey_panic stackAt_spqrRecvCallee_split
   subroutine_ok_withMemEq_of_lscl tail680_join_1952 vecU8At_sub4992_repack vecU8At_sub4992_unpack
   vecU8_sub_entails_header_buf vn_some_unpack_sub4992 words11SubAt words11SubAt_entails_chainAt)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkLib_eq_329 blkPC_329 blkPl_329)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (ChainNewEnv chainNewSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (ChainIntoPbAllocEnv ChainIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
  (ChainRecvKeyEnv chainRecvKeyEvents chainRecvKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropSpqrChainSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
  (ChainFromAllocEnv ChainFromEnv ChainFromVersionNegotiationEnv
   chainFromAllocEnv_imp_chainFromEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContracts SpqrRecvPlacedContractsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv sepWP_spqrRecvPlacedPostOfEnv_of_post0 spqrRecvBudgetPanicPost spqrRecvPlacedPost
   spqrRecvPlacedPostOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
  (SpqrRecvEnv.append_freeOnly freeOnlyWitness)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
  (SepWPpLS.call_lscro step_drop_pre_2540_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8PlacedBudget
  (SpqrRecvPlacedContractsOfEnv.toDropContracts step_v0_err_2388_placed_ofEnv
   step_v0_recvKey_ok_2184_placed_ofEnv)

@[simp] private theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

@[simp] private theorem pure_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (pure x >>= f) = f x := rfl

@[simp] private theorem ok_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64 ult_one_toI32
attribute [local simp, local arm64_norm, local wp_norm]
  fp_sub_32_add_eq hsp_add_560_eq' fp_sub_48_add_eq hsp_add_544_eq'

omit [LibsignalPlacement] in
theorem onPanic_false_entails {Q : Prop} {H : SepProp} :
    (⌜False⌝ : SepProp) ⊢ (⌜Q⌝ ∗ H) :=
  Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm) (Entails.pure_left False.elim)

omit [LibsignalPlacement] in
private theorem onPanic_of_chainRecvKey_budget {F : ShaCompress} {K : MlKem}
    {st msg : VecArg} {pre : MsgPreamble} {pre_pb : PqRatchetState}
    {vn : VersionNegotiationPB} {pb : V1State} {chain0 : Chain}
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_gt : pre.version > 1#8)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0)
    (s sm : State) :
    (⌜(Chain.recvKey (spqrHkdfWith F) chain0 0#64 pre.index).isPanic = true ∧ sm.trace = s.trace⌝ ∗
        anyHeap : SepProp) ⊢
      ⌜(spqrV1Recv F K).recvPanics st.bytes msg.bytes ∧ s.trace <+: sm.trace⌝ ∗ anyHeap := by
  apply Entails.pure_left
  rintro ⟨hpan, htr⟩
  exact Entails.pure_right
    ⟨spqrV1Recv_gt_recvKey_panic (F := F) (K := K) hpre hdec hvn hinner hmin hver_gt hcf hpan,
      htr ▸ List.prefix_refl _⟩
    (Entails.refl _)

omit [LibsignalPlacement] in
private theorem chainNewEvents_eq_chainFrom :
    LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.chainNewEvents =
      LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget.chainNewEvents := rfl

omit [LibsignalPlacement] in
private theorem chainNewEnv_imp_chainFromAllocEnv {pb_ch : Option ChainPB}
    {vn : VersionNegotiationPB} {dir : Direction} {cp : ChainParamsPB} {evs : List AllocEvent}
    (hchain : pb_ch = none)
    (hdir : Direction.fromI32? vn.direction = some dir)
    (hcp : vn.chainParams = some cp)
    (h : ChainNewEnv evs) :
    ChainFromAllocEnv pb_ch (some vn) evs := by
  subst hchain
  dsimp only [ChainFromAllocEnv, ChainFromVersionNegotiationEnv, ChainNewEnv] at h ⊢
  simp only [hdir, hcp, Option.isSome_some, Bool.and_self, ↓reduceIte]
  exact h.trans chainNewEvents_eq_chainFrom

omit [LibsignalPlacement] in
private theorem chainNewEnv_imp_chainFromEnv {pb_ch : Option ChainPB}
    {vn : VersionNegotiationPB} {dir : Direction} {cp : ChainParamsPB} {evs : List AllocEvent}
    (hchain : pb_ch = none)
    (hdir : Direction.fromI32? vn.direction = some dir)
    (hcp : vn.chainParams = some cp)
    (h : ChainNewEnv evs) :
    ChainFromEnv pb_ch (some vn) evs :=
  chainFromAllocEnv_imp_chainFromEnv (chainNewEnv_imp_chainFromAllocEnv hchain hdir hcp h)

/-! ## 1. `step_v0_after_chainFrom_604_placed` (`+604 .. +740 -> +2184 / +2540`) -/

/-- Envelope-parametric shared continuation after `chain_from` succeeds in `Ordering::Greater`
    (`+604 .. +740`): moves `chain0 : Chain` (`88`B) into `s0.sp - 4288#64`, calls
    `Chain::recv_key(0, pre.index)` (`lsmpl.base 366`), and branches to
    `step_v0_recvKey_ok_2184_placed_ofEnv` (`+2184`) on `Ok` or drops `chain0` (`lsmpl.base
    269`) and jumps to `step_drop_pre_2540_placed_ofEnv` (`+2540`) on `Err`. -/
theorem step_v0_after_chainFrom_604_placed_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    (st_cost : MC.σ) (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (G_c0 : ChainGhost) (chain0 : Chain) (pad_c0 : BitVec 32)
    (w0 w1 d880 d888 d896 d2896 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_gt : pre.version > 1#8)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0)
    (s0 s : State) (P R : SepProp)
    (hfits_rk : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainRecvKeyEnv (spqrHkdfWith F)
        ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩))
    (hfits_into : ∀ (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost),
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩)
          st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩))
    (hfits_enc : ∀ (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost)
        (evs_into : List AllocEvent),
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_into)
          st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }))
    (hevs_rk_err : ∀ (e : Error) (evs_d : List AllocEvent),
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .error (.err e) →
      FreeOnlyEvs evs_d →
      Env
        (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_d))
    (hevs_rk_ok : ∀ (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost)
        (evs_into evs_enc evs_d : List AllocEvent),
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }
        evs_enc →
      FreeOnlyEvs evs_d →
      Env
        (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++
          evs_into ++ evs_enc ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 604#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = G_c0.linksCap)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = s0.sp - 2096#64)
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
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 352 ∗
      memRegion (s0.sp - 4288#64) 88 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d880) ∗
      ((s0.sp - 4104#64) ↦₆₄ d888) ∗
      ((s0.sp - 4096#64) ↦₆₄ d896) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      memRegion (s0.sp - 3056#64) 88 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      words11SubAt s0.sp 2096 { chainWords11 G_c0 chain0 pad_c0 with w0 := d2896 } ∗
      chainAtHeap A.repAlloc G_c0 chain0 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hrk_ok := hC.chainRecvKey_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have hfits : RecvPrevFits chain0 :=
    recvPrevFits_of_chainFrom (F := F) (K := K) hst_len hdec hcf
  let x_rk : ChainRecvKeyGhost :=
    ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩
  subst hP
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 366)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine SepWP.focus_weaken (memRegion_88_sub_entails_words11 s0.sp 4288) (by sep_focus) ?_
  wp_pull_exists; rename_i u4288
  rw [memRegion_88_sub3056_split_32_56 s0.sp, frame1912_split_err_2388 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i d48 d40 d32
  have hchainAt := words11SubAt_entails_chainAt A.repAlloc s0.sp 4288 G_c0 chain0 pad_c0
  dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hchainAt ⊢
  simp only [sepConj_assoc]
  apply sepWP_seg_ls_vm
    (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_329 (mid := lsmpl.base 366)
  intro _m_strip
  wp_steps 19
  refine SepWP.focus_weaken hchainAt (by sep_focus) ?_
  refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainRecvKeyStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro hrk_ok
    (x_rk, MC.stepEvents evs0 st_cost)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (show _ = spqrRecvPlacedEntry + 680#64 by simp only [spqrRecvPlacedEntry, arm64_norm, *])
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun sm => by
      dsimp only [chainRecvKeySpecX, x_rk]
      exact onPanic_of_chainRecvKey_budget (F := F) (K := K)
        hpre hdec hvn hinner hmin hver_gt hcf _ sm)
    (fun _ _ => rfl)
    (by
      dsimp only [chainRecvKeySpecX, x_rk]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *],
          by simp only [arm64_norm, *],
          by simp only [arm64_norm, *],
          by simp only [arm64_norm, *],
          hfits, hfits_rk⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, _, _, _, _, hx27_c, hx28_c, hxfp_c, _⟩
  dsimp only [chainRecvKeySpecX, x_rk]
  simp only [sepConj_assoc]
  refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sm, _⟩
  have htr_sm' : TraceVRegs sm s0 :=
    ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by
    rw [hx20_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = s0.sp - 3056#64 := by
    rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = s0.sp - 2096#64 := by
    rw [hx22_c]; simp only [arm64_norm, *]
  have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by
    rw [hx27_c]; simp only [arm64_norm, *]
  have hx28_sm : sm.readReg64 .x28 = s0.sp - 4288#64 := by
    rw [hx28_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64
    rw [hxfp_c]; simp only [arm64_norm, *]
  rw [← MC.stepEvents_append]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainRecvKeyStackX (by decide)).symm)
    (by sep_focus) ?_
  cases hrk : chain0.recvKey (spqrHkdfWith F) 0#64 pre.index with
  | error ce =>
    cases ce with
    | panic p =>
      dsimp only [recvKeyPostAt]
      exact SepWPpLS.focus_pure (by sep_focus) False.elim
    | err e =>
      obtain ⟨herr_recv, hnp⟩ : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode) ∧
          ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
        spqrV1Recv_gt_recvKey_err hpre hdec hvn hinner hmin hver_gt hcf hrk
      apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
      dsimp only [recvKeyPostAt]
      refine SepWP.focus_weaken (recvKeyErrAt_entails_code_memRegion23 (s0.sp - 3056#64) e) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (err_payload_expose (s0.sp - 3056#64) (spqrErrorTag e) 23 (by decide) (by decide))
        (by sep_focus) ?_
      wp_pull_exists; rename_i w3_err w2_err w1_err
      wp_focus_pure; intro hret8_err
      dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
      rw [memRegion_zero, emp_sepConj]
      unfold chainRepr
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      wp_pull_exists; rename_i G_c1
      rw [ret_48_split ret]
      wp_pull_exists; rename_i r3 r2 r1 r0
      apply sepWP_seq_lscl hcl (mid := lsmpl.base 269)
      apply sepWP_seg_ls_vm
        (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
        blkLib_eq_329 (mid := lsmpl.base 269)
      intro _m_strip
      wp_steps 15
      refine ProofLib.SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        fun _m_real _hnsp => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
      refine ProofLib.SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        fun hcl1 => ?_
      have hret_fold :
          ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
            ((ret + 8#64) ↦₆₄ w3_err) ∗
            ((ret + 16#64) ↦₆₄ w2_err) ∗
            ((ret + 24#64) ↦₆₄ w1_err) ∗
            memRegion (ret + 32#64) 16) ⊢
          recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
        rw [herr_recv]
        exact recv_err_words_foldX A.repAlloc ret w3_err w2_err w1_err
          (spqrErrorTag e) (e == .stateDecode)
          (spqrErrorTag_eq_zero_iff e).to_iff hret8_err
      apply sepWP_seq_lscl hcl1 (mid := (blkPl_329).base + 2540#64)
      refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropSpqrChainStack (by decide)))
        (by sep_focus) ?_
      have hdrop_chain := subroutine_ok_withMemEq_of_lscl hC.dropChain_ok hcl1
      simp only [withMemEq, dropSpqrChainSpec] at hdrop_chain
      dsimp only [spqrRecvPlacedProg, BitVec.ofNat_eq_ofNat] at hdrop_chain
      wp_call hdrop_chain
        (⟨s0.sp - 4288#64, G_c1, chain0⟩,
          MC.stepEvents
            (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
              ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩)
            st_cost)
      have hevs_dc := ‹FreeOnlyEvs _›
      simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
        sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropSpqrChainStack (by decide)).symm)
        (by sep_focus) ?_
      wp_steps 1
      refine ProofLib.SepWP.done (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) fun hcl2 => ?_
      refine SepWP.focus_weaken
        (tail680_join_1952 s0.sp G_c0.linksPtr G_c0.linksHead d48 (chainWords11 G_c0 chain0 pad_c0))
        (by dsimp only [chainWords11]; sep_focus) ?_
      dsimp only [chainSize]
      refine SepWP.focus_weaken
        (frame4544_join_err_740 s0.sp d880 d888 d896 1#64 w3_err w2_err w1_err
          w3_err w2_err w1_err (BitVec.ofNat 64 (G_c0.epochs.zip chain0.links).length)
          G_c0.nextRoot.cap G_c0.nextRoot.ptr)
        (by sep_focus) ?_
      refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 hnp ?_
      exact step_drop_pre_2540_placed_ofEnv A lim st_cost Env
        (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++
          freeOnlyWitness hevs_dc)
        (fun evs_d hd => by
          rw [List.append_assoc]
          exact hevs_rk_err e (freeOnlyWitness hevs_dc ++ evs_d) hrk (hevs_dc.append hd))
        (spqrV1Recv F K) ext (SpqrRecvPlacedContractsOfEnv.toDropContracts hC)
        st msg ret vn pb w0 w1 s0 _ _ R _ rfl hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, htr_sm'.1, *],
          by simp only [wp_norm, arm64_norm, htr_sm'.2, *]⟩
        (by simp only [arm64_norm, *])
        (by
          simp only [← MC.stepEvents_append, List.append_assoc, freeOnlyWitness, wp_norm,
            arm64_norm, *]
          sep_ac_rfl)
        hcl2
  | ok res =>
    rcases res with ⟨chain1, rawKey⟩
    have hok_recv :=
      spqrV1Recv_gt_recvKey_ok (F := F) (K := K) hpre hdec hvn hinner hmin hver_gt hcf hrk
    have henc_len :=
      encodeRaw_v0_state_len_lt (F := F) (K := K) hst_len hpre hdec hvn hinner hmin hver_gt hcf hrk
    apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 2184#64)
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
    dsimp only [recvKeyPostAt, recvKeyOkAt]
    rw [bv_sub_add_lit s0.sp 3056 8 (by decide) (by decide)]
    dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
    refine SepWP.focus_weaken (vecU8_sub_entails_header_buf A.repAlloc s0.sp 3048 rawKey) (by sep_focus) ?_
    wp_pull_exists; rename_i cap_rk ptr_rk
    dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
    apply sepWP_seg_ls_vm
      (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
      blkLib_eq_329 (mid := (blkPl_329).base + 2184#64)
    intro _m_strip
    wp_steps 7
    refine SepWP.focus_weaken
      (tail680_join_1952 s0.sp G_c0.linksPtr G_c0.linksHead d48 (chainWords11 G_c0 chain0 pad_c0))
      (by dsimp only [chainWords11]; sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (memRegion_872_sub2968_split_ok_680 s0.sp))
      (by sep_focus) ?_
    wp_pull_exists; rename_i u5 u4
    refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
    apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact step_v0_recvKey_ok_2184_placed_ofEnv st_cost Env
      (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
        ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩)
      hC st msg ret vn pb chain1 rawKey w0 w1 cap_rk ptr_rk
      d880 d888 d896 0#64 cap_rk ptr_rk (BitVec.ofNat 64 rawKey.length) u4 u5
      (BitVec.ofNat 64 (G_c0.epochs.zip chain0.links).length) G_c0.nextRoot.cap G_c0.nextRoot.ptr
      henc_len hok_recv s0 _ _ R
      (fun gChain => hfits_into chain1 rawKey gChain hrk)
      (fun gChain evs_into hinto => hfits_enc chain1 rawKey gChain evs_into hrk hinto)
      (fun gChain evs_into evs_enc evs_drop hinto henc hd =>
        hevs_rk_ok chain1 rawKey gChain evs_into evs_enc evs_drop hrk hinto henc hd)
      hs0_align
      (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, htr_sm'.1, *],
        by simp only [wp_norm, arm64_norm, htr_sm'.2, *]⟩
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by sep_ac_rfl)

theorem step_v0_after_chainFrom_604_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    (st_cost : MC.σ) (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (G_c0 : ChainGhost) (chain0 : Chain) (pad_c0 : BitVec 32)
    (w0 w1 d880 d888 d896 d2896 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_gt : pre.version > 1#8)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0)
    (s0 s : State) (P R : SepProp)
    (hfits_rk : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainRecvKeyEnv (spqrHkdfWith F)
        ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩))
    (hfits_into : ∀ (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost),
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩)
          st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩))
    (hfits_enc : ∀ (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost)
        (evs_into : List AllocEvent),
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_into)
          st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }))
    (hevs_rk_err : ∀ (e : Error) (evs_d : List AllocEvent),
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .error (.err e) →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg
        (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_d))
    (hevs_rk_ok : ∀ (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost)
        (evs_into evs_enc evs_d : List AllocEvent),
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }
        evs_enc →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg
        (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++
          evs_into ++ evs_enc ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 604#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = G_c0.linksCap)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = s0.sp - 2096#64)
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
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 352 ∗
      memRegion (s0.sp - 4288#64) 88 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d880) ∗
      ((s0.sp - 4104#64) ↦₆₄ d888) ∗
      ((s0.sp - 4096#64) ↦₆₄ d896) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      memRegion (s0.sp - 3056#64) 88 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      words11SubAt s0.sp 2096 { chainWords11 G_c0 chain0 pad_c0 with w0 := d2896 } ∗
      chainAtHeap A.repAlloc G_c0 chain0 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_v0_after_chainFrom_604_placed_ofEnv st_cost (SpqrRecvEnv st msg) evs0 hC
    st msg ret pre pre_pb vn pb G_c0 chain0 pad_c0 w0 w1 d880 d888 d896 d2896
    hst_len hpre hdec hvn hinner hmin hver_gt hcf s0 s P R
    hfits_rk hfits_into hfits_enc hevs_rk_err hevs_rk_ok
    hs0_align hpc hrun hsp htr hx8 hx19 hx20 hx21 hx22 hx27 hx28 hx29 hP

/-! ## 2. `step_v0_chain_none_2108_placed` (`+2108 .. +2140`, `+2384 .. +2388`, `+2920 .. +2948`) -/

/-- Envelope-parametric `pre_pb.chain = none` dispatch in `Ordering::Greater` (`+2108`):
    - Invalid `vn.direction` (`> 1`): jumps to `+2384` (`Error::StateDecode`) ->
    `step_v0_err_2388_placed_ofEnv`.
    - `vn.chainParams = none`: writes `15#8` (`Error::ChainNotAvailable`) at `+2132..+2140` ->
    `step_v0_err_2388_placed_ofEnv`.
    - `vn.chainParams = some cp`: jumps to `+2920`, calls `Chain::new` (`lsmpl.base 363`), and
    jumps to `+604` (`step_v0_after_chainFrom_604_placed_ofEnv`). -/
theorem step_v0_chain_none_2108_placed_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    (st_cost : MC.σ) (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 d880 d888 d896 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hchain : pre_pb.chain = none)
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_gt : pre.version > 1#8)
    (s0 s : State) (P R : SepProp)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (hfits_cf : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainFromAllocEnv pre_pb.chain (some vn)))
    (hfits_rk : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cf) st_cost)
        (ChainRecvKeyEnv (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩))
    (hfits_into : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩)
          st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩))
    (hfits_enc : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost) (evs_into : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_into)
          st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }))
    (hevs_rk_err : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (e : Error) (evs_d : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .error (.err e) →
      FreeOnlyEvs evs_d →
      Env
        (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_d))
    (hevs_rk_ok : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost)
        (evs_into evs_enc evs_d : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }
        evs_enc →
      FreeOnlyEvs evs_d →
      Env
        (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++
          evs_into ++ evs_enc ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
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
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 352 ∗
      memRegion (s0.sp - 4288#64) 88 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d880) ∗
      ((s0.sp - 4104#64) ↦₆₄ d888) ∗
      ((s0.sp - 4096#64) ↦₆₄ d896) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      memRegion (s0.sp - 3056#64) 88 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      memRegion (s0.sp - 2096#64) 88 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hnew_ok := hC.chainNew_ok
  subst hP
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (vn_some_unpack_sub4992 A.repAlloc s0.sp w0 w1 vn))
    (by sep_focus) ?_
  rcases direction_fromI32_or vn.direction with
    ⟨dir, hdir_val, hdir_opt, hcond_hi⟩ | ⟨hdir_opt, hcond_hi⟩
  · cases hcp : vn.chainParams with
    | none =>
      have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .error .chainNotAvailable := by
        simp [chainFrom, chainFromVersionNegotiation, hchain, hdir_opt, hcp]
      obtain ⟨herr_recv, hnp⟩ : (spqrV1Recv F K).recv st.bytes msg.bytes =
          .error (Error.chainNotAvailable == .stateDecode) ∧
          ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
        spqrV1Recv_gt_chainFrom_err hpre hdec hvn hinner hmin hver_gt hcf
      apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 2388#64)
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
      dsimp only [optChainParamsPBAt]
      rw [memRegion_88_sub2096_split_byte8 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      wp_pull_exists; rename_i b0_err d2896
      apply sepWP_seg_ls_vm
        (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
        blkLib_eq_329 (mid := (blkPl_329).base + 2388#64)
      intro _m_strip
      wp_steps 9
      have hcp_fold :
          ((s0.sp - 4968#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 4968#64 + 4#64) 8 =
            optChainParamsPBAt (s0.sp - 4968#64) vn.chainParams := by
        rw [hcp]; rfl
      refine SepWP.focus_weaken (Entails.of_eq hcp_fold) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (vn_some_unpack_sub4992 A.repAlloc s0.sp w0 w1 vn).symm)
        (by sep_focus) ?_
      have htag_cna : (15#8 : BitVec 8) = spqrErrorTag .chainNotAvailable := rfl
      rw [htag_cna]
      refine SepWP.focus_weaken
        (byte_memRegion79_sub2096_to_v0_err s0.sp .chainNotAvailable)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (frame2544_join_v0 s0.sp d880 d888 d896) (by sep_focus) ?_
      refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        fun _m_real _hnsp => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
      apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      exact step_v0_err_2388_placed_ofEnv A lim st_cost Env evs0 hevs_free F K ext
        (SpqrRecvPlacedContractsOfEnv.toDropContracts hC)
        st msg ret vn pb .chainNotAvailable w0 w1 d2896 herr_recv hnp s0 _ _ R hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, htr.1, *],
          by simp only [wp_norm, arm64_norm, htr.2, *]⟩
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by sep_ac_rfl)
    | some cp =>
      let chain0 := chainNewVal (spqrHkdfWith F) vn.authKey dir cp
      have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 := by
        simp [chainFrom, chainFromVersionNegotiation, hchain, hdir_opt, hcp]; rfl
      have hfits_new : FitsEnv MC lim (MC.stepEvents evs0 st_cost) ChainNewEnv :=
        FitsEnv.mono (fun _ => chainNewEnv_imp_chainFromAllocEnv hchain hdir_opt hcp) hfits_cf
      apply SepWPpLS.of_sepWP (mid := lsmpl.base 363)
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
      refine SepWP.focus_weaken (vecU8At_sub4992_unpack A.repAlloc s0.sp w0 w1 vn.authKey) (by sep_focus) ?_
      wp_focus_pure; intro hlen64
      dsimp only [optChainParamsPBAt]
      rw [bv_sub_add_lit s0.sp 4968 4 (by decide) (by decide),
          bv_sub_add_lit s0.sp 4968 8 (by decide) (by decide)]
      dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
      apply sepWP_seg_ls_vm
        (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
        blkLib_eq_329 (mid := lsmpl.base 363)
      intro _m_strip
      wp_steps 10
      refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        fun _m_real _hnsp => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
      apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPpLS.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainNewStackX (by decide)))
        (by sep_focus) ?_
      refine SepWPpLS.call_lscro hnew_ok
        (⟨s0.sp - 2096#64, false, w1, vn.authKey, dir, cp⟩, MC.stepEvents evs0 st_cost)
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
        (show _ = spqrRecvPlacedEntry + 2936#64 by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
        (fun _ => onPanic_false_entails)
        (fun _ _ => rfl)
        (by
          dsimp only [chainNewSpecX]
          refine frame_pure_pre
            ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
              by simp only [arm64_norm, *],
              by simp only [arm64_norm, *],
              by simp only [arm64_norm, *],
              by simp only [arm64_norm, *],
              hlen64, hfits_new⟩
            (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
                sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
        ?_
      intro sm hpcm hrunm hspm hcsm
      have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
      rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, _, _, _, _, hx27_c, hx28_c, hxfp_c, _⟩
      dsimp only [chainNewSpecX]
      rw [sepExists_sepConj_left]
      apply SepWPpLS.exists_elim; intro evs_new
      simp only [sepConj_assoc]
      refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sm, _, hevs_new⟩
      have hevs_cf : ChainFromEnv pre_pb.chain (some vn) evs_new :=
        chainNewEnv_imp_chainFromEnv hchain hdir_opt hcp hevs_new
      have htr_sm' : TraceVRegs sm s0 :=
        ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
      have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm]; simp only [arm64_norm, *]
      have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
      have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c]; simp only [arm64_norm, *]
      have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by
        rw [hx21_c]; simp only [arm64_norm, *]
      have hx22_sm : sm.readReg64 .x22 = s0.sp - 2096#64 := by rw [hx22_c]; simp only [arm64_norm, *]
      have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c]; simp only [arm64_norm, *]
      have hx28_sm : sm.readReg64 .x28 = s0.sp - 4288#64 := by rw [hx28_c]; simp only [arm64_norm, *]
      have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
        change sm.readReg64 Reg.fp = s0.sp - 96#64
        rw [hxfp_c]; simp only [arm64_norm, *]
      rw [← MC.stepEvents_append]
      simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
        sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
      refine SepWPpLS.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainNewStackX (by decide)).symm)
        (by sep_focus) ?_
      refine SepWPpLS.focus_weaken (vecU8At_sub4992_repack A.repAlloc s0.sp w0 w1 vn.authKey) (by sep_focus) ?_
      have hcp_fold :
          ((s0.sp - 4968#64) ↦₃₂ 1#32) ∗
            ((s0.sp - 4964#64) ↦₃₂ cp.maxJump) ∗
            ((s0.sp - 4960#64) ↦₃₂ cp.maxOooKeys) =
          optChainParamsPBAt (s0.sp - 4968#64) vn.chainParams := by
        rw [hcp]
        dsimp only [optChainParamsPBAt]
        rw [bv_sub_add_lit s0.sp 4968 4 (by decide) (by decide),
            bv_sub_add_lit s0.sp 4968 8 (by decide) (by decide)]
      refine SepWPpLS.focus_weaken (Entails.of_eq hcp_fold) (by sep_focus) ?_
      refine SepWPpLS.focus_weaken
        (Entails.of_eq (vn_some_unpack_sub4992 A.repAlloc s0.sp w0 w1 vn).symm)
        (by sep_focus) ?_
      refine SepWPpLS.focus_weaken
        (Entails.trans (chainNew_post_entails_chainRepr A.repAlloc (s0.sp - 2096#64) chain0)
          (chainRepr_sub_entails_words11 A.repAlloc s0.sp 2096 chain0))
        (by sep_focus) ?_
      apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 604#64)
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
      wp_pull_exists; rename_i G_c0 pad_c0
      wp_focus_pure; intro hcap_c0_ne
      have hz_c0 : (G_c0.linksCap + 1#64 == 0#64) = false :=
        add_one_beq_zero_of_ne_noneCap hcap_c0_ne
      have hnz_c0 : (G_c0.linksCap + 1#64 != 0#64) = true := by
        simp [bne, hz_c0]
      dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
      simp only [sepConj_assoc]
      apply sepWP_seg_ls_vm
        (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
        blkLib_eq_329 (mid := (blkPl_329).base + 604#64)
      intro _m_strip
      wp_steps 4
      refine ProofLib.SepWP.done (by simp only [arm64_norm, bne, *]) (by simp only [arm64_norm, *])
        fun _m_real _hnsp => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
      apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      exact step_v0_after_chainFrom_604_placed_ofEnv st_cost Env (evs0 ++ evs_new) hC
        st msg ret pre pre_pb vn pb G_c0 chain0 pad_c0 w0 w1 d880 d888 d896 G_c0.linksCap
        hst_len hpre hdec hvn hinner hmin hver_gt hcf s0 _ _ R
        (hfits_rk evs_new chain0 G_c0 hevs_cf hcf)
        (fun chain1 rawKey gChain hrk =>
          hfits_into evs_new chain0 G_c0 chain1 rawKey gChain hevs_cf hcf hrk)
        (fun chain1 rawKey gChain evs_into hrk hinto =>
          hfits_enc evs_new chain0 G_c0 chain1 rawKey gChain evs_into hevs_cf hcf hrk hinto)
        (fun e evs_d hrk hd =>
          hevs_rk_err evs_new chain0 G_c0 e evs_d hevs_cf hcf hrk hd)
        (fun chain1 rawKey gChain evs_into evs_enc evs_d hrk hinto henc hd =>
          hevs_rk_ok evs_new chain0 G_c0 chain1 rawKey gChain evs_into evs_enc evs_d
            hevs_cf hcf hrk hinto henc hd)
        hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, htr_sm'.1, *],
          by simp only [wp_norm, arm64_norm, htr_sm'.2, *]⟩
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]; sep_ac_rfl)
  · have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .error .stateDecode := by
      simp [chainFrom, chainFromVersionNegotiation, hchain, hdir_opt]
    obtain ⟨herr_recv, hnp⟩ : (spqrV1Recv F K).recv st.bytes msg.bytes =
        .error (Error.stateDecode == .stateDecode) ∧
        ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
      spqrV1Recv_gt_chainFrom_err hpre hdec hvn hinner hmin hver_gt hcf
    apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 2388#64)
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    rw [memRegion_88_sub2096_split_byte8 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists; rename_i b0_err d2896
    apply sepWP_seg_ls_vm
      (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
      blkLib_eq_329 (mid := (blkPl_329).base + 2388#64)
    intro _m_strip
    wp_steps 5
    refine SepWP.focus_weaken
      (Entails.of_eq (vn_some_unpack_sub4992 A.repAlloc s0.sp w0 w1 vn).symm)
      (by sep_focus) ?_
    have htag_sd : (0#8 : BitVec 8) = spqrErrorTag .stateDecode := rfl
    rw [htag_sd]
    refine SepWP.focus_weaken
      (byte_memRegion79_sub2096_to_v0_err s0.sp .stateDecode)
      (by sep_focus) ?_
    refine SepWP.focus_weaken (frame2544_join_v0 s0.sp d880 d888 d896) (by sep_focus) ?_
    refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
    apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact step_v0_err_2388_placed_ofEnv A lim st_cost Env evs0 hevs_free F K ext
      (SpqrRecvPlacedContractsOfEnv.toDropContracts hC)
      st msg ret vn pb .stateDecode w0 w1 d2896 herr_recv hnp s0 _ _ R hs0_align
      (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, htr.1, *],
        by simp only [wp_norm, arm64_norm, htr.2, *]⟩
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by sep_ac_rfl)

theorem step_v0_chain_none_2108_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    (st_cost : MC.σ) (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (hevs0 : SpqrRecvEnv st msg evs0)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 d880 d888 d896 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hchain : pre_pb.chain = none)
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_gt : pre.version > 1#8)
    (s0 s : State) (P R : SepProp)
    (hfits_cf : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainFromAllocEnv pre_pb.chain (some vn)))
    (hfits_rk : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cf) st_cost)
        (ChainRecvKeyEnv (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩))
    (hfits_into : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩)
          st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩))
    (hfits_enc : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost) (evs_into : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      FitsEnv MC lim
        (MC.stepEvents
          (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_into)
          st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }))
    (hevs_rk_err : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (e : Error) (evs_d : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .error (.err e) →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg
        (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_d))
    (hevs_rk_ok : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
        (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost)
        (evs_into evs_enc evs_d : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
      chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }
        evs_enc →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg
        (evs0 ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++
          evs_into ++ evs_enc ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
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
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 352 ∗
      memRegion (s0.sp - 4288#64) 88 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d880) ∗
      ((s0.sp - 4104#64) ↦₆₄ d888) ∗
      ((s0.sp - 4096#64) ↦₆₄ d896) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      memRegion (s0.sp - 3056#64) 88 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      memRegion (s0.sp - 2096#64) 88 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_v0_chain_none_2108_placed_ofEnv st_cost (SpqrRecvEnv st msg) evs0 hC
    st msg ret pre pre_pb vn pb w0 w1 d880 d888 d896
    hst_len hpre hdec hvn hinner hchain hmin hver_gt s0 s P R
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    hfits_cf hfits_rk hfits_into hfits_enc hevs_rk_err hevs_rk_ok
    hs0_align hpc hrun hsp htr hx19 hx20 hx21 hx27 hx28 hx29 hP

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9PlacedBudgetAux
