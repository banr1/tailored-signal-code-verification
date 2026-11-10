/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7Placed
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable `Ordering::Less` (`InitInnerPlacedTail`) for `spqr::recv`

Envelope-parametric and default `SpqrRecvEnv` proofs of the `Ordering::Less` (`+1076..+1420`)
branch of `spqr::recv` (Block `329`), discharging `InitInnerPlacedTailGen` and `InitInnerPlacedTail`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl sepWP_seq_lscl)
open CryptoVerification.LibsignalSpqrV1
  (Chain Direction MlKem MsgPreamble PqRatchetState V1State VersionNegotiationPB chainFrom
   msgPreamble spqrDecodeState spqrHkdfWith spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainGhost ChainIntoPbCall chainIntoPbStackX chainRepr)
open CryptoVerification.SpqrV1.Drop
  (optProtoInnerStateSize optProtoPqRatchetInnerAt vecCapPtrDealloc)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Top.ChainFrom
  (ChainFromCall chainFromStackX optChainPBAt_protoRepr_eq_exists optVersionNegotiationRefAt)
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm (add_one_beq_zero_of_ne_noneCap)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
  (chainResultAt versionNegotiationPBAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.InitInner
  (InitInnerGhost initInnerResultAt_v0 initInnerStack)
open CryptoVerification.SpqrV1.Top.Recv
  (InnerWordInv SepWPpLS chainRepr_sub_entails_words11 chainWords11
   direction_fromI32_of_two_ule direction_fromI32_of_ult_two frame1584_split_ok_1320
   frame4544_join_1076 frame4544_join_1320
   frame4544_split_1076 frame_pure_pre hsp_add_544 memRegion_88_sub_entails_words11
   not_ult_two_imp_two_ule optVersionNegotiationPBTailAt_some_expose_direction recv_err_byte_foldX
   ret_48_split_byte8 sp_setPState sp_sub_96_sub_48 sp_writeVReg128 spqrRecvCalleeStackX
   spqrRecvPlacedEntry spqrRecvPlacedProg spqrRecvRoPlacedAt spqrRecvRoPlacedAt_expose_logOff
   spqrRecvRoPlacedAt_expose_statesIntoPb spqrRecvSavedRegs spqrV1Recv_lt_one_chainFrom_err
   spqrV1Recv_lt_one_chainFrom_ok spqrV1Recv_lt_one_dir_none spqrV1Recv_noPanic_of_recv_err_true
   stackAt_spqrRecvCallee_split ult_two_imp_two_ule_false vnHeader_sub4992_entails_memRegion_48
   vnTail_some_entails_dealloc vn_authKey_len_bound_of_spqrDecodeState
   vn_some_expose_dir_and_initInner words11SubAt words11SubAt_entails_chainAt
   words11SubAt_to_memRegion_88 zeroExtend64_eq_zero_of_lt_one)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkLib_eq_329 blkPC_329 blkPl_329)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEnv.nil FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
  (ChainIntoPbAllocEnv ChainIntoPbEnv chainIntoPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
  (ChainFromAllocEnv ChainFromEnv chainFromSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (InitInnerEnv initInnerPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContracts SpqrRecvPlacedContractsOfEnv initInnerPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv sepWP_spqrRecvPlacedPostOfEnv_of_post0 spqrRecvBudgetPanicPost spqrRecvPlacedPost
   spqrRecvPlacedPostOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
  (SpqrRecvDropContractsBudget SpqrRecvEnv.append_freeOnly step_drop_pre_952_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget (SepWPpLS.call_lscro)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudgetAux (step_drop_vn_936_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudgetAux
  (InitInnerPlacedTail InitInnerPlacedTailGen)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6PlacedBudget
  (step_initInner_chainFrom_err_1320_placed_ofEnv step_initInner_chainFrom_ok_1424_placed_ofEnv)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm, local wp_norm] sp_sub_96_sub_48 hsp_add_544

private theorem toDropContracts {MC : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext) :
    SpqrRecvDropContractsBudget A lim F ext :=
  ⟨hC.dealloc_ok, hC.dropEpochSlice_ok, hC.dropOptProtoInnerState_ok,
   hC.dropOptProtoChain_ok, hC.dropChain_ok, hC.dropPqRatchetState_ok, hC.dropStates_ok⟩

private theorem onPanic_false_entails {Q : Prop} {H : SepProp} :
    (⌜False⌝ : SepProp) ⊢ (⌜Q⌝ ∗ H) :=
  Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm) (Entails.pure_left False.elim)

private theorem statesIntoPbJumpTablePlacedAt_eq_initInner :
    CryptoVerification.SpqrV1.Top.Recv.statesIntoPbJumpTablePlacedAt =
      CryptoVerification.SpqrV1.Top.InitInner.statesIntoPbJumpTablePlacedAt := by
  unfold CryptoVerification.SpqrV1.Top.Recv.statesIntoPbJumpTablePlacedAt
    CryptoVerification.SpqrV1.Top.InitInner.statesIntoPbJumpTablePlacedAt
  rfl

/-! ## 1. Success Path of `spqr::chain_from` in `Ordering::Less` (`+1320 .. +1420 -> +1424`) -/

/-- Envelope-parametric success path of `spqr::chain_from` in `Ordering::Less` (`+1320 .. +1420
    -> +1424`): copies `ch : Chain` (`88`B) from `s0.sp - 2096#64` (`sp + 0xb50`) to `s0.sp -
    4200#64` (`sp + 0x318`), calls `Chain::into_pb` (Block `365`) writing to `s0.sp - 4592#64`
    (`sp + 0x190`), and continues via `step_initInner_chainFrom_ok_1424_placed_ofEnv`. -/
theorem step_initInner_chainFrom_ok_1320_placed_ofEnv {MC : AllocCostModel}
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
    (vn : VersionNegotiationPB) (pb : V1State) (ch : Chain)
    (w0 w1 : BitVec 64)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none))
    (s0 s : State) (P R : SepProp)
    (hfits_into : ∀ G : ChainGhost,
      FitsEnv MC lim (MC.stepEvents evs0 st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩))
    (hevs_done : ∀ G evs_into evs_d,
      ChainIntoPbEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩ evs_into →
      FreeOnlyEvs evs_d →
      Env (evs0 ++ evs_into ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1320#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      versionNegotiationPBAt A.repAlloc ⟨w0, w1⟩ (s0.sp - 4992#64) vn ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 1584 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 3056#64) none ∗
      memRegion (s0.sp - 2832#64) 736 ∗
      chainRepr A.repAlloc (s0.sp - 2096#64) ch ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hinto_pb := hC.chainIntoPb_ok
  subst hP
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 365)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [frame1584_split_ok_1320 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i d2 d1 d0 w160
  refine SepWP.focus_weaken (chainRepr_sub_entails_words11 A.repAlloc s0.sp 2096 ch) (by sep_focus) ?_
  wp_pull_exists; rename_i G pad
  wp_focus_pure; intro hcap_ne
  have hz_ch : (G.linksCap + 1#64 == 0#64) = false := add_one_beq_zero_of_ne_noneCap hcap_ne
  refine SepWP.focus_weaken (memRegion_88_sub_entails_words11 s0.sp 4200) (by sep_focus) ?_
  wp_pull_exists; rename_i dDst
  have hjoin_src := words11SubAt_to_memRegion_88 s0.sp 2096 (chainWords11 G ch pad)
  dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hjoin_src
  have hpack_dst := words11SubAt_entails_chainAt A.repAlloc s0.sp 4200 G ch pad
  dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hpack_dst
  dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  simp only [sepConj_assoc]
  apply sepWP_seg_ls_vm
    (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_329 (mid := lsmpl.base 365)
  intro _m_strip
  wp_steps 26
  refine SepWP.focus_weaken hjoin_src (by sep_focus) ?_
  refine SepWP.focus_weaken hpack_dst (by sep_focus) ?_
  refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro hinto_pb
    (⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩, MC.stepEvents evs0 st_cost)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = spqrRecvPlacedEntry + 1424#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_false_entails)
    (fun _ _ => rfl)
    (by
      dsimp only [chainIntoPbSpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], hfits_into G⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_c, hx20_c, _⟩
  dsimp only [chainIntoPbSpecX]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPpLS.exists_elim; intro evs_into
  refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨hevs_into, htr_sm, _⟩
  have htr_sm' : TraceVRegs sm s0 :=
    ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by
    rw [hx20_c]; simp only [arm64_norm, *]
  simp only [arm64_norm, hsp]
  rw [← MC.stepEvents_append]
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)).symm)
    (by sep_focus) ?_
  exact step_initInner_chainFrom_ok_1424_placed_ofEnv A lim st_cost Env (evs0 ++ evs_into)
    (fun evs_d hd => hevs_done G evs_into evs_d hevs_into hd)
    F K ext (toDropContracts hC)
    st msg ret vn pb ch w0 w1 w160
    G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
    hok s0 sm _ R hs0_align
    hpcm hrunm hspm' htr_sm' hx19_sm hx20_sm (by sep_ac_rfl)

theorem step_initInner_chainFrom_ok_1320_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    (st_cost : MC.σ) (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State) (ch : Chain)
    (w0 w1 : BitVec 64)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none))
    (s0 s : State) (P R : SepProp)
    (hfits_into : ∀ G : ChainGhost,
      FitsEnv MC lim (MC.stepEvents evs0 st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩))
    (hevs_done : ∀ G evs_into evs_d,
      ChainIntoPbEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩ evs_into →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg (evs0 ++ evs_into ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1320#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      versionNegotiationPBAt A.repAlloc ⟨w0, w1⟩ (s0.sp - 4992#64) vn ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 1584 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 3056#64) none ∗
      memRegion (s0.sp - 2832#64) 736 ∗
      chainRepr A.repAlloc (s0.sp - 2096#64) ch ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_initInner_chainFrom_ok_1320_placed_ofEnv st_cost (SpqrRecvEnv st msg) evs0 hC
    st msg ret vn pb ch w0 w1 hok s0 s P R hfits_into hevs_done
    hs0_align hpc hrun hsp htr hx19 hx20 hP

/-! ## 2. `Ordering::Less` (`InitInnerPlacedTail`, `+1076 .. +1320`) -/

/-- Envelope-parametric invalid-direction path (`¬(vn.direction.ult 2#32 = true)`) of
    `Ordering::Less` (`+1076 .. +1280`): stores `Err(InvalidStateEncoding)` (`tag = 0#8`) at
    `ret` and drops `pre_pb` via `step_drop_vn_936_placed_ofEnv` /
    `step_drop_pre_952_placed_ofEnv`. -/
theorem step_ordering_less_dir_none_placed_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 w26 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw26 : InnerWordInv pre_pb.inner w26)
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_lt : pre.version < 1#8)
    (hdir_ge : ¬(vn.direction.ult 2#32 = true))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
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
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hx25' : s.readReg64 .x25 = 0#64 := by
    rw [hx25, zeroExtend64_eq_zero_of_lt_one hver_lt]
  clear hx25
  have hule : (2#32).ule vn.direction = true := not_ult_two_imp_two_ule hdir_ge
  have hdir_none : Direction.fromI32? vn.direction = none := direction_fromI32_of_two_ule hule
  have herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error true :=
    spqrV1Recv_lt_one_dir_none F K hpre hdec hvn hinner hmin hver_lt hdir_none
  have hvn_dealloc :
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ⊢
      ⌜w0.toNat < 2 ^ 63⌝ ∗
        ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗ memRegion (s0.sp - 4976#64) 32 ∗
        vecCapPtrDealloc A.repAlloc w0 w1 := by
    have h8 : (s0.sp - 4992#64) + 8#64 = s0.sp - 4984#64 := bv_sub_add_lit s0.sp 4992 8
    have h16 : (s0.sp - 4992#64) + 16#64 = s0.sp - 4976#64 := bv_sub_add_lit s0.sp 4992 16
    rw [← h8, ← h16]
    exact vnTail_some_entails_dealloc A.repAlloc (s0.sp - 4992#64) w0 w1 vn
  apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
  subst hP
  rw [← hinner]
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [frame4544_split_1076 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i w30_slot b0_slot
  refine SepWP.focus_weaken spqrRecvRoPlacedAt_expose_logOff (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro
  wp_focus_pure; intro hP_ro
  refine SepWP.focus_weaken
    (optVersionNegotiationPBTailAt_some_expose_direction A.repAlloc s0.sp w0 w1 vn)
    (by sep_focus) ?_
  wp_pull_exists; rename_i P_dir
  wp_focus_pure; intro hP_dir
  refine SepWP.focus_weaken (ret_48_split_byte8 ret) (by sep_focus) ?_
  wp_pull_exists; rename_i r0 b8 r2 r3
  have hfold := recv_err_byte_foldX A.repAlloc ret r2 r3 0#8 true (by decide)
  rw [← herr] at hfold
  by_cases hc0 : (w0 == 0#64) = true
  · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
    apply sepWP_seq_lscl (mid := (blkPl_329).base + 952#64) hcl
    apply sepWP_seg_ls_vm
      (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
      blkLib_eq_329 (mid := (blkPl_329).base + 952#64)
    intro _m_strip
    wp_steps 14
    refine SepWP.focus_weaken hP_ro (by sep_focus) ?_
    refine SepWP.focus_weaken hP_dir (by sep_focus) ?_
    refine SepWP.focus_weaken (frame4544_join_1076 s0.sp 0#8 0#32) (by sep_focus) ?_
    refine SepWP.fold hfold (by sep_focus) ?_
    refine SepWP.focus_weaken hvn_dealloc (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc]
    simp only [hc0, ↓reduceIte, emp_sepConj, sepConj_emp]
    subst hw0
    wp_steps 2
    refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
    refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
    refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      fun hcl1 => ?_
    refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 (spqrV1Recv_noPanic_of_recv_err_true herr) ?_
    exact step_drop_pre_952_placed_ofEnv A lim st_cost Env evs0 hevs_free
      (spqrV1Recv F K) ext (toDropContracts hC) st msg ret pre_pb w26 hw26
      s0 _ _ R _ rfl hs0_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (⟨by simp only [arm64_norm, htr.1], by simp only [arm64_norm, htr.2]⟩)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; sep_ac_rfl) hcl1
  · apply sepWP_seq_lscl (mid := (blkPl_329).base + 936#64) hcl
    apply sepWP_seg_ls_vm
      (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
      blkLib_eq_329 (mid := (blkPl_329).base + 936#64)
    intro _m_strip
    wp_steps 14
    refine SepWP.focus_weaken hP_ro (by sep_focus) ?_
    refine SepWP.focus_weaken hP_dir (by sep_focus) ?_
    refine SepWP.focus_weaken (frame4544_join_1076 s0.sp 0#8 0#32) (by sep_focus) ?_
    refine SepWP.fold hfold (by sep_focus) ?_
    refine SepWP.focus_weaken hvn_dealloc (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc]
    simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    wp_steps 1
    refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
    refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      fun hcl1 => ?_
    refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 (spqrV1Recv_noPanic_of_recv_err_true herr) ?_
    exact step_drop_vn_936_placed_ofEnv A lim st_cost Env evs0 hevs_free
      (spqrV1Recv F K) ext (toDropContracts hC) st msg ret pre_pb w0 w1 w26 hw26
      s0 _ _ R _ rfl hs0_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (⟨by simp only [arm64_norm, htr.1], by simp only [arm64_norm, htr.2]⟩)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; sep_ac_rfl) hcl1

theorem step_ordering_less_dir_none_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 w26 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw26 : InnerWordInv pre_pb.inner w26)
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_lt : pre.version < 1#8)
    (hdir_ge : ¬(vn.direction.ult 2#32 = true))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
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
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_ordering_less_dir_none_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC st msg ret pre pre_pb vn pb w0 w1 w26
    hpre hdec hvn hinner hw26 hmin hver_lt hdir_ge
    s0 s P R hs0_align hpc hrun hsp htr hx19 hx20 hx25 hx26 hx29 hP

/-- Envelope-parametric valid-direction path (`vn.direction.ult 2#32 = true`,
    `Direction.fromI32? vn.direction = some dir`) of `Ordering::Less` (`+1076 .. +1320`): calls
    `spqr::init_inner` (`+1296`) with `v = .v0`, calls `spqr::chain_from` (`+1316`), and
    continues to `step_initInner_chainFrom_err_1320_placed_ofEnv` or
    `step_initInner_chainFrom_ok_1320_placed_ofEnv`. -/
theorem step_ordering_less_dir_some_placed_ofEnv {MC : AllocCostModel}
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
    (w0 w1 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_lt : pre.version < 1#8)
    (hdir_lt : vn.direction.ult 2#32 = true)
    (s0 s : State) (P R : SepProp)
    (hfits_init : ∀ dir : Direction,
      Direction.fromI32? vn.direction = some dir →
      FitsEnv MC lim (MC.stepEvents evs0 st_cost)
        (InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩))
    (hfits_cf : ∀ (dir : Direction) (evs_init : List AllocEvent),
      Direction.fromI32? vn.direction = some dir →
      InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_init) st_cost)
        (ChainFromAllocEnv pre_pb.chain (some vn)))
    (hfits_into : ∀ (dir : Direction) (evs_init evs_cf : List AllocEvent) (ch : Chain)
        (G : ChainGhost),
      Direction.fromI32? vn.direction = some dir →
      InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_init ++ evs_cf) st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩))
    (hevs_err : ∀ (dir : Direction) (evs_init evs_cf evs_d : List AllocEvent),
      Direction.fromI32? vn.direction = some dir →
      InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      FreeOnlyEvs evs_d →
      Env (evs0 ++ evs_init ++ evs_cf ++ evs_d))
    (hevs_ok : ∀ (dir : Direction) (evs_init evs_cf : List AllocEvent) (ch : Chain)
        (G : ChainGhost) (evs_into evs_d : List AllocEvent),
      Direction.fromI32? vn.direction = some dir →
      InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
      ChainIntoPbEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩ evs_into →
      FreeOnlyEvs evs_d →
      Env (evs0 ++ evs_init ++ evs_cf ++ evs_into ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hsp_ne : s0.sp - 4992#64 ≠ 0#64)
    (hpc : s.pc = spqrRecvPlacedEntry + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
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
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hx25' : s.readReg64 .x25 = 0#64 := by
    rw [hx25, zeroExtend64_eq_zero_of_lt_one hver_lt]
  clear hx25
  obtain ⟨dir, hdir_some, hdir_eq⟩ := direction_fromI32_of_ult_two hdir_lt
  have hule : (2#32).ule vn.direction = false := ult_two_imp_two_ule_false hdir_lt
  have hak_len : 32 + vn.authKey.length < 2 ^ 63 :=
    vn_authKey_len_bound_of_spqrDecodeState (F := F) (K := K) hst_len hdec hvn
  have hinit_ok := hC.initInner_ok
  have hcf_ok := hC.chainFrom_ok
  subst hP
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 324)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [frame4544_split_1076 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i w30_slot b0_slot
  refine SepWP.focus_weaken spqrRecvRoPlacedAt_expose_logOff (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro_log
  wp_focus_pure; intro hP_ro_log
  refine SepWP.focus_weaken (vn_some_expose_dir_and_initInner A.repAlloc s0.sp w0 w1 vn)
    (by sep_focus) ?_
  wp_pull_exists; rename_i P_vn
  wp_focus_pure; intro hw1_ne
  wp_focus_pure; intro hP_vn
  have hsplit3967 :
      memRegion (s0.sp - 4111#64) 3967 =
        memRegion (s0.sp - 4111#64) 1055 ∗
        memRegion (s0.sp - 3056#64) optProtoInnerStateSize ∗
        memRegion (s0.sp - 2832#64) 736 ∗
        memRegion (s0.sp - 2096#64) 88 ∗
        memRegion (s0.sp - 2008#64) 1864 := by
    unfold optProtoInnerStateSize
    rw [ProofLib.memRegion_split' (b := s0.sp - 4111#64) (n := 1055) (k := 2912)
        (b' := s0.sp - 3056#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 3056#64) (n := 224) (k := 2688)
        (b' := s0.sp - 2832#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 2832#64) (n := 736) (k := 1952)
        (b' := s0.sp - 2096#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 2096#64) (n := 88) (k := 1864)
        (b' := s0.sp - 2008#64) (by decide) (by bv_omega) (by decide)]
  apply sepWP_seg_ls_vm
    (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_329 (mid := lsmpl.base 324)
  intro _m_strip
  wp_steps 15
  refine SepWP.focus_weaken hP_ro_log (by sep_focus) ?_
  refine SepWP.focus_weaken spqrRecvRoPlacedAt_expose_statesIntoPb (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro_into
  wp_focus_pure; intro hP_ro_into
  rw [hsplit3967]
  simp only [sepConj_assoc]
  refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) initInnerStack (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro hinit_ok
    (⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩, MC.stepEvents evs0 st_cost)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = spqrRecvPlacedEntry + 1300#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_false_entails)
    (fun _ _ => rfl)
    (by
      dsimp only [initInnerPlacedSpecXOfEnv, initInnerPlacedSpecOfEnv]
      rw [← statesIntoPbJumpTablePlacedAt_eq_initInner]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]; rfl,
          by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          hw1_ne, hak_len, hfits_init dir hdir_eq⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_c, hx20_c, _⟩
  dsimp only [initInnerPlacedSpecXOfEnv, initInnerPlacedSpecOfEnv, initInnerResultAt_v0]
  rw [← statesIntoPbJumpTablePlacedAt_eq_initInner]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPpLS.exists_elim; intro evs_init
  refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sm, hevs_init⟩
  have htr_sm' : TraceVRegs sm s0 :=
    ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by
    rw [hx20_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
  rw [← MC.stepEvents_append]
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) initInnerStack (by decide)).symm)
    (by sep_focus) ?_
  refine SepWPpLS.focus_weaken hP_vn (by sep_focus) ?_
  refine SepWPpLS.focus_weaken hP_ro_into (by sep_focus) ?_
  refine SepWPpLS.focus_weaken (frame4544_join_1320 s0.sp 0#8 0#32) (by sep_focus) ?_
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 323)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
  rw [optChainPBAt_protoRepr_eq_exists A.repAlloc (s0.sp - 4944#64) pre_pb.chain]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i gPb
  have hvn_ref :
      versionNegotiationPBAt A.repAlloc ⟨w0, w1⟩ (s0.sp - 4992#64) vn ⊢
      optVersionNegotiationRefAt A.repAlloc ⟨w0, w1⟩ (s0.sp - 4992#64) (some vn) :=
    Entails.pure_right hsp_ne (Entails.refl _)
  refine SepWP.focus_weaken hvn_ref (by sep_focus) ?_
  apply sepWP_seg_ls_vm
    (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_329 (mid := lsmpl.base 323)
  intro _m_strip_cf
  wp_steps 5
  refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    fun _m_real_cf _hnsp_cf => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp_cf.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro hcf_ok
    (⟨s0.sp - 2096#64, s0.sp - 4944#64, s0.sp - 4992#64, gPb, ⟨w0, w1⟩, pre_pb.chain, some vn⟩,
      MC.stepEvents (evs0 ++ evs_init) st_cost)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hspm']; exact hs0_align)
    (rfl : _ = spqrRecvPlacedEntry + 1320#64)
    (by simp only [arm64_norm, htr_sm']; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_false_entails)
    (fun _ _ => rfl)
    (by
      dsimp only [chainFromSpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], hfits_cf dir evs_init hdir_eq hevs_init⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']; sep_focus))
    ?_
  intro sn hpcn hrunn hspn hcsn
  have hvregs_cn := hcsn.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsn with ⟨hx19_cn, hx20_cn, _⟩
  dsimp only [chainFromSpecX, optVersionNegotiationRefAt]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPpLS.exists_elim; intro evs_cf
  refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sn, hevs_cf⟩
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro _
  have htr_sn' : TraceVRegs sn s0 :=
    ⟨by rw [htr_sn]; simp only [arm64_norm, *], by rw [hvregs_cn]; simp only [arm64_norm, *]⟩
  have hspn' : sn.sp = s0.sp - 4992#64 := by
    rw [hspn]; simp only [arm64_norm, *]
  have hx19_sn : sn.readReg64 .x19 = ret := by
    rw [hx19_cn]; simp only [arm64_norm, *]
  have hx20_sn : sn.readReg64 .x20 = w0 := by
    rw [hx20_cn]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']
  rw [← MC.stepEvents_append]
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromStackX (by decide)).symm)
    (by sep_focus) ?_
  cases hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) with
  | error err =>
    obtain ⟨herr, hnp⟩ :=
      spqrV1Recv_lt_one_chainFrom_err F K hpre hdec hvn hinner hmin hver_lt hdir_eq hcf
    exact step_initInner_chainFrom_err_1320_placed_ofEnv A lim st_cost Env
      (evs0 ++ evs_init ++ evs_cf)
      (fun evs_d hd => hevs_err dir evs_init evs_cf evs_d hdir_eq hevs_init hevs_cf hd)
      F K ext (toDropContracts hC)
      st msg ret vn pb err w0 w1 herr hnp s0 sn _ R hs0_align
      hpcn hrunn hspn' htr_sn' hx19_sn hx20_sn (by dsimp only [chainResultAt]; sep_ac_rfl)
  | ok ch =>
    have hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none) :=
      spqrV1Recv_lt_one_chainFrom_ok F K hpre hdec hvn hinner hmin hver_lt hdir_eq hcf
    exact step_initInner_chainFrom_ok_1320_placed_ofEnv st_cost Env
      (evs0 ++ evs_init ++ evs_cf) hC st msg ret vn pb ch w0 w1 hok
      s0 sn _ R
      (fun G => hfits_into dir evs_init evs_cf ch G hdir_eq hevs_init hevs_cf hcf)
      (fun G evs_into evs_d hinto hd =>
        hevs_ok dir evs_init evs_cf ch G evs_into evs_d hdir_eq hevs_init hevs_cf hcf hinto hd)
      hs0_align hpcn hrunn hspn' htr_sn' hx19_sn hx20_sn (by dsimp only [chainResultAt]; sep_ac_rfl)

/-- `SpqrRecvEnv` specialization of `step_ordering_less_dir_some_placed_ofEnv`; `InitInnerEnv F`
    on `.v0` is `[[]]`, so `FitsEnv` for `init_inner` holds via `FitsEnv.nil`. -/
theorem step_ordering_less_dir_some_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    (st_cost : MC.σ) (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_lt : pre.version < 1#8)
    (hdir_lt : vn.direction.ult 2#32 = true)
    (s0 s : State) (P R : SepProp)
    (hfits_cf : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainFromAllocEnv pre_pb.chain (some vn)))
    (hfits_into : ∀ (evs_cf : List AllocEvent) (ch : Chain) (G : ChainGhost),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cf) st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩))
    (hevs_err : ∀ evs_cf evs_d : List AllocEvent,
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg (evs0 ++ evs_cf ++ evs_d))
    (hevs_ok : ∀ (evs_cf : List AllocEvent) (ch : Chain) (G : ChainGhost)
        (evs_into evs_d : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
      ChainIntoPbEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩ evs_into →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg (evs0 ++ evs_cf ++ evs_into ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hsp_ne : s0.sp - 4992#64 ≠ 0#64)
    (hpc : s.pc = spqrRecvPlacedEntry + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
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
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_ordering_less_dir_some_placed_ofEnv st_cost (SpqrRecvEnv st msg) evs0 hC
    st msg ret pre pre_pb vn pb w0 w1 hst_len hpre hdec hvn hinner hmin hver_lt hdir_lt
    s0 s P R
    (fun _ _ => FitsEnv.nil)
    (fun _ evs_init _ hinit => by
      dsimp only [InitInnerEnv] at hinit; subst hinit; rw [List.append_nil]; exact hfits_cf)
    (fun _ evs_init evs_cf ch G _ hinit hcf_env hcf_ok => by
      dsimp only [InitInnerEnv] at hinit; subst hinit; rw [List.append_nil]
      exact hfits_into evs_cf ch G hcf_env hcf_ok)
    (fun _ evs_init evs_cf evs_d _ hinit hcf_env hd => by
      dsimp only [InitInnerEnv] at hinit; subst hinit; rw [List.append_nil]
      exact hevs_err evs_cf evs_d hcf_env hd)
    (fun _ evs_init evs_cf ch G evs_into evs_d _ hinit hcf_env hcf_ok hinto hd => by
      dsimp only [InitInnerEnv] at hinit; subst hinit; rw [List.append_nil]
      exact hevs_ok evs_cf ch G evs_into evs_d hcf_env hcf_ok hinto hd)
    hs0_align hsp_ne hpc hrun hsp htr hx19 hx20 hx25 hx29 hP

/-- Combined envelope-parametric `Ordering::Less` (`+1076 .. +1420`) tail contract when `s0.sp -
    4992#64 ≠ 0#64`. -/
theorem step_ordering_less_placed_ofEnv {MC : AllocCostModel}
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
    (w0 w1 w26 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw26 : InnerWordInv pre_pb.inner w26)
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_lt : pre.version < 1#8)
    (s0 s : State) (P R : SepProp)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (hfits_init : ∀ dir : Direction,
      Direction.fromI32? vn.direction = some dir →
      FitsEnv MC lim (MC.stepEvents evs0 st_cost)
        (InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩))
    (hfits_cf : ∀ (dir : Direction) (evs_init : List AllocEvent),
      Direction.fromI32? vn.direction = some dir →
      InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_init) st_cost)
        (ChainFromAllocEnv pre_pb.chain (some vn)))
    (hfits_into : ∀ (dir : Direction) (evs_init evs_cf : List AllocEvent) (ch : Chain)
        (G : ChainGhost),
      Direction.fromI32? vn.direction = some dir →
      InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_init ++ evs_cf) st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩))
    (hevs_err : ∀ (dir : Direction) (evs_init evs_cf evs_d : List AllocEvent),
      Direction.fromI32? vn.direction = some dir →
      InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      FreeOnlyEvs evs_d →
      Env (evs0 ++ evs_init ++ evs_cf ++ evs_d))
    (hevs_ok : ∀ (dir : Direction) (evs_init evs_cf : List AllocEvent) (ch : Chain)
        (G : ChainGhost) (evs_into evs_d : List AllocEvent),
      Direction.fromI32? vn.direction = some dir →
      InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
      ChainIntoPbEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩ evs_into →
      FreeOnlyEvs evs_d →
      Env (evs0 ++ evs_init ++ evs_cf ++ evs_into ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hsp_ne : s0.sp - 4992#64 ≠ 0#64)
    (hpc : s.pc = spqrRecvPlacedEntry + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
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
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  by_cases hdir_lt : vn.direction.ult 2#32 = true
  · exact step_ordering_less_dir_some_placed_ofEnv st_cost Env evs0 hC
      st msg ret pre pre_pb vn pb w0 w1
      hst_len hpre hdec hvn hinner hmin hver_lt hdir_lt
      s0 s P R hfits_init hfits_cf hfits_into hevs_err hevs_ok
      hs0_align hsp_ne hpc hrun hsp htr hx19 hx20 hx25 hx29 hP
  · exact step_ordering_less_dir_none_placed_ofEnv A lim st_cost Env evs0 hevs_free
      F K ext hC st msg ret pre pre_pb vn pb w0 w1 w26
      hpre hdec hvn hinner hw26 hmin hver_lt hdir_lt
      s0 s P R hs0_align hpc hrun hsp htr hx19 hx20 hx25 hx26 hx29 hP

theorem step_ordering_less_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    (st_cost : MC.σ) (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (hevs0 : SpqrRecvEnv st msg evs0)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 w26 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw26 : InnerWordInv pre_pb.inner w26)
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_lt : pre.version < 1#8)
    (s0 s : State) (P R : SepProp)
    (hfits_cf : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainFromAllocEnv pre_pb.chain (some vn)))
    (hfits_into : ∀ (evs_cf : List AllocEvent) (ch : Chain) (G : ChainGhost),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cf) st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩))
    (hevs_err : ∀ evs_cf evs_d : List AllocEvent,
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg (evs0 ++ evs_cf ++ evs_d))
    (hevs_ok : ∀ (evs_cf : List AllocEvent) (ch : Chain) (G : ChainGhost)
        (evs_into evs_d : List AllocEvent),
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
      ChainIntoPbEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩ evs_into →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg (evs0 ++ evs_cf ++ evs_into ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hsp_ne : s0.sp - 4992#64 ≠ 0#64)
    (hpc : s.pc = spqrRecvPlacedEntry + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
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
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  by_cases hdir_lt : vn.direction.ult 2#32 = true
  · exact step_ordering_less_dir_some_placed st_cost evs0 hC st msg ret
      pre pre_pb vn pb w0 w1 hst_len hpre hdec hvn hinner hmin hver_lt hdir_lt
      s0 s P R hfits_cf hfits_into hevs_err hevs_ok
      hs0_align hsp_ne hpc hrun hsp htr hx19 hx20 hx25 hx29 hP
  · exact step_ordering_less_dir_none_placed A lim st_cost F K ext hC
      st msg ret evs0 hevs0 pre pre_pb vn pb w0 w1 w26
      hpre hdec hvn hinner hw26 hmin hver_lt hdir_lt
      s0 s P R hs0_align hpc hrun hsp htr hx19 hx20 hx25 hx26 hx29 hP

/-! ## 3. Packaging as `InitInnerPlacedTailGen` and `InitInnerPlacedTail` -/

/-- Package `step_ordering_less_placed_ofEnv` as `InitInnerPlacedTailGen`
    (`Part5PlacedBudgetAux`). -/
theorem initInnerPlacedTailGen_of_contracts {MC : AllocCostModel}
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
    (hst_len : st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hsp_ne : s0.sp - 4992#64 ≠ 0#64)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (hfits_init : ∀ (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (w1 : BitVec 64) (dir : Direction),
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      Direction.fromI32? vn.direction = some dir →
      FitsEnv MC lim (MC.stepEvents evs0 st_cost)
        (InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩))
    (hfits_cf : ∀ (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (w1 : BitVec 64) (dir : Direction) (evs_init : List AllocEvent),
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      Direction.fromI32? vn.direction = some dir →
      InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_init) st_cost)
        (ChainFromAllocEnv pre_pb.chain (some vn)))
    (hfits_into : ∀ (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (w1 : BitVec 64) (dir : Direction) (evs_init evs_cf : List AllocEvent)
        (ch : Chain) (G : ChainGhost),
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      Direction.fromI32? vn.direction = some dir →
      InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_init ++ evs_cf) st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩))
    (hevs_err : ∀ (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (w1 : BitVec 64) (dir : Direction) (evs_init evs_cf evs_d : List AllocEvent),
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      Direction.fromI32? vn.direction = some dir →
      InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      FreeOnlyEvs evs_d →
      Env (evs0 ++ evs_init ++ evs_cf ++ evs_d))
    (hevs_ok : ∀ (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (w1 : BitVec 64) (dir : Direction) (evs_init evs_cf : List AllocEvent)
        (ch : Chain) (G : ChainGhost) (evs_into evs_d : List AllocEvent),
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      Direction.fromI32? vn.direction = some dir →
      InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
      ChainIntoPbEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩ evs_into →
      FreeOnlyEvs evs_d →
      Env (evs0 ++ evs_init ++ evs_cf ++ evs_into ++ evs_d)) :
    InitInnerPlacedTailGen A lim (MC.stepEvents evs0 st_cost) F K ext st msg ret s0
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R := by
  intro pre _remPtr pre_pb vn pb w0 w1 w26 s P
    hpre _hvalid hdec hvn hinner _hw0_ne hw26 hmin hver_lt
    hpc hrun hsp htr hx19 hx20 _hx21 _hx22 _hx23 _hx24 hx25 hx26 _hx27 _hx28 hx29 hP
  exact step_ordering_less_placed_ofEnv st_cost Env evs0 hC
    st msg ret pre pre_pb vn pb w0 w1 w26
    hst_len hpre hdec hvn hinner hw26 hmin hver_lt
    s0 s P R hevs_free
    (fun dir => hfits_init pre_pb vn w1 dir hdec hvn)
    (fun dir evs_init => hfits_cf pre_pb vn w1 dir evs_init hdec hvn)
    (fun dir evs_init evs_cf ch G => hfits_into pre_pb vn w1 dir evs_init evs_cf ch G hdec hvn)
    (fun dir evs_init evs_cf evs_d => hevs_err pre_pb vn w1 dir evs_init evs_cf evs_d hdec hvn)
    (fun dir evs_init evs_cf ch G evs_into evs_d =>
      hevs_ok pre_pb vn w1 dir evs_init evs_cf ch G evs_into evs_d hdec hvn)
    hs0_align hsp_ne hpc hrun hsp htr hx19 hx20 hx25 hx26 hx29 hP

theorem initInnerPlacedTail_of_contracts {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    (st_cost : MC.σ) (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (hevs0 : SpqrRecvEnv st msg evs0)
    (hst_len : st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hsp_ne : s0.sp - 4992#64 ≠ 0#64)
    (hfits_cf : ∀ (pre_pb : PqRatchetState) (vn : VersionNegotiationPB),
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      FitsEnv MC lim (MC.stepEvents evs0 st_cost)
        (ChainFromAllocEnv pre_pb.chain (some vn)))
    (hfits_into : ∀ (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (evs_cf : List AllocEvent) (ch : Chain) (G : ChainGhost),
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cf) st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩))
    (hevs_err : ∀ (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (evs_cf evs_d : List AllocEvent),
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg (evs0 ++ evs_cf ++ evs_d))
    (hevs_ok : ∀ (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
        (evs_cf : List AllocEvent) (ch : Chain) (G : ChainGhost)
        (evs_into evs_d : List AllocEvent),
      spqrDecodeState st.bytes = .ok pre_pb →
      pre_pb.versionNegotiation = some vn →
      ChainFromEnv pre_pb.chain (some vn) evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
      ChainIntoPbEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩ evs_into →
      FreeOnlyEvs evs_d →
      SpqrRecvEnv st msg (evs0 ++ evs_cf ++ evs_into ++ evs_d)) :
    InitInnerPlacedTail A lim st_cost evs0 F K ext st msg ret s0 R :=
  initInnerPlacedTailGen_of_contracts st_cost (SpqrRecvEnv st msg) evs0 hC
    st msg ret hst_len s0 R hs0_align hsp_ne
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    (fun _ _ _ _ _ _ _ => FitsEnv.nil)
    (fun pre_pb vn _ _ evs_init hdec hvn _ hinit => by
      dsimp only [InitInnerEnv] at hinit; subst hinit; rw [List.append_nil]
      exact hfits_cf pre_pb vn hdec hvn)
    (fun pre_pb vn _ _ evs_init evs_cf ch G hdec hvn _ hinit hcf_env hcf_ok => by
      dsimp only [InitInnerEnv] at hinit; subst hinit; rw [List.append_nil]
      exact hfits_into pre_pb vn evs_cf ch G hdec hvn hcf_env hcf_ok)
    (fun pre_pb vn _ _ evs_init evs_cf evs_d hdec hvn _ hinit hcf_env hd => by
      dsimp only [InitInnerEnv] at hinit; subst hinit; rw [List.append_nil]
      exact hevs_err pre_pb vn evs_cf evs_d hdec hvn hcf_env hd)
    (fun pre_pb vn _ _ evs_init evs_cf ch G evs_into evs_d hdec hvn _ hinit hcf_env hcf_ok hinto hd => by
      dsimp only [InitInnerEnv] at hinit; subst hinit; rw [List.append_nil]
      exact hevs_ok pre_pb vn evs_cf ch G evs_into evs_d hdec hvn hcf_env hcf_ok hinto hd)

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7PlacedBudget
