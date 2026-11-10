/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6Placed
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable `Ordering::Less` Continuations for `spqr::recv`

Envelope-parametric and default `SpqrRecvEnv` `spqr::chain_from` error (`+1320`) and
post-`Chain::into_pb` (`+1424`) continuations of `Ordering::Less` in `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement lsmpl sepWP_seq_lscl withMemEq)
open CryptoVerification.LibsignalSpqrV1
  (Chain Error MlKem V1State VersionNegotiationPB recvResultExactKeyAt spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg)
open CryptoVerification.SpqrV1.Drop
  (dropStack80 none3Cap' optProtoPqRatchetInnerAt)
open CryptoVerification.SpqrV1.ProtoRepr (chainPBAt chainPBSize optChainPBAt)
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
  (chainErrorAt_unpack_words4 extractLsb_hi_append64 extractLsb_lo_append64
   words4_rest_to_memRegion_88)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
  (chainErrorAt noneCap spqrErrorTag versionNegotiationPBAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (TraceVRegs optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS frame1584_split_err frame4544_join_err_2424 frame4544_join_ok_880
   memRegion_224_sub_entails_words28 optProtoPqRatchetInnerAt_none_sub_entails_words27
   recv_err_q0_foldX recv_ok_empty_foldX ret_48_split sp_sub_4992_aligned
   spqrRecvCalleeStackX spqrRecvPlacedEntry spqrRecvPlacedProg spqrRecvRoPlacedAt
   spqrRecvSavedRegs spqrV1Recv_noPanic_of_recv_ok stackAt_spqrRecvCallee_split
   subroutine_ok_withMemEq_of_lscl vnTail_some_eq_versionNegotiationPBAt words27SubAt
   words27SubAt_to_memRegion_224)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropOptProtoSpqrChainSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv sepWP_spqrRecvPlacedPostOfEnv_of_post0
   spqrRecvBudgetPanicPost spqrRecvPlacedPost spqrRecvPlacedPostOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
  (SpqrRecvDropContractsBudget SpqrRecvEnv.append_freeOnly freeOnlyWitness seq_vm_lscl)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
  (step_drop_pre_2540_placed_ofEnv)

export CryptoVerification.SpqrV1.Top.Recv
  (spqrRecvRoPlacedAt_expose_logOff spqrRecvRoPlacedAt_expose_statesIntoPb)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

private theorem align_pre_wp {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (hwp : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ hwp

/-- Envelope-parametric error path of `spqr::chain_from` in `Ordering::Less` (`+1320 .. +1348 ->
    +2424 .. +2456 -> +2540`). -/
theorem step_initInner_chainFrom_err_1320_placed_ofEnv {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State)
    (e : Error) (w0 w1 : BitVec 64)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode))
    (hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes)
    (s0 s : State) (P R : SepProp)
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
      chainErrorAt (s0.sp - 2096#64) e ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hnone3 : (none3Cap' + 3#64 == 0#64) = true := rfl
  have hnone1 : (noneCap + 1#64 == 0#64) = true := rfl
  rcases htr with ⟨htr_eq, hvregs⟩
  apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  have hnone_3056 :
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 3056#64) none =
        ((s0.sp - 3056#64) ↦₆₄ none3Cap') ∗ memRegion (s0.sp - 3048#64) 216 := by
    dsimp only [optProtoPqRatchetInnerAt]
    rw [bv_sub_add_lit s0.sp 3056 8]
  rw [← vnTail_some_eq_versionNegotiationPBAt A.repAlloc (s0.sp - 4992#64) w0 w1 vn,
      bv_sub_add_lit s0.sp 4992 8,
      bv_sub_add_lit s0.sp 4992 16,
      hnone_3056,
      chainErrorAt_unpack_words4 (s0.sp - 2096#64) e,
      bv_sub_add_lit s0.sp 2096 8,
      bv_sub_add_lit s0.sp 2096 16,
      bv_sub_add_lit s0.sp 2096 24,
      bv_sub_add_lit s0.sp 2096 32,
      frame1584_split_err s0.sp,
      ret_48_split ret]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i q0_err w3_err d0 d1 d2 r0 r1 r2 r3
  wp_focus_pure; intro htag_q0
  have htag_eq : BitVec.truncate 8 ((q0_err.extractLsb' 64 64) ++ (q0_err.extractLsb' 0 64)) =
      spqrErrorTag e := by
    have hq : (q0_err.extractLsb' 64 64) ++ (q0_err.extractLsb' 0 64) = q0_err := by bv_kernel
    rw [hq, htag_q0]
  have hret_fold :
      ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((ret + 8#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
        ((ret + 16#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((ret + 24#64) ↦₆₄ w3_err) ∗
        memRegion (ret + 32#64) 16) ⊢
      recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [herr]
    exact recv_err_q0_foldX A.repAlloc ret (q0_err.extractLsb' 64 64) w3_err q0_err e htag_q0
  have hw4_join := words4_rest_to_memRegion_88 (s0.sp - 2096#64)
    noneCap (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err
  rw [bv_sub_add_lit s0.sp 2096 8,
      bv_sub_add_lit s0.sp 2096 16,
      bv_sub_add_lit s0.sp 2096 24,
      bv_sub_add_lit s0.sp 2096 32] at hw4_join
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hw4_join
  refine seq_vm_lscl hcl (mid := (blkPl_329).base + 2540#64)
    (P_mid :=
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sm =>
      sm.sp = s0.sp - 4992#64 ∧
      TraceVRegs sm s0 ∧
      sm.readReg64 .x20 = w0)
    ?_ ?_
  · by_vm_steps (
      wp_steps 17
      refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
      refine SepWP.focus_weaken hw4_join (by sep_focus) ?_
      refine SepWP.focus_weaken
        (frame4544_join_err_2424 s0.sp (q0_err.extractLsb' 0 64)
          (q0_err.extractLsb' 64 64) w3_err none3Cap')
        (by sep_focus) ?_
      refine align_pre_wp (by sep_ac_rfl) ?_
      wp_done
    )
  · intro s1 hpc1 hrun1 hcl1 hvm ⟨hsp1, htr1, hx20_1⟩
    rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm]
    refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 hnp ?_
    exact step_drop_pre_2540_placed_ofEnv A lim st_cost Env evs0 hevs_free
      (spqrV1Recv F K) ext hC st msg ret vn pb w0 w1
      s0 s1 _ R _ rfl hs0_align hpc1 hrun1 hsp1 htr1 hx20_1 rfl hcl1

theorem step_initInner_chainFrom_err_1320_placed {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (vn : VersionNegotiationPB) (pb : V1State)
    (e : Error) (w0 w1 : BitVec 64)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode))
    (hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes)
    (s0 s : State) (P R : SepProp)
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
      chainErrorAt (s0.sp - 2096#64) e ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_initInner_chainFrom_err_1320_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC st msg ret vn pb e w0 w1 herr hnp s0 s P R hs0_align hpc hrun hsp htr hx19 hx20 hP

/-- Envelope-parametric continuation after `Chain::into_pb` in `Ordering::Less` (`+1424 .. +1528
    -> +824 .. +880 -> +2540`). -/
theorem step_initInner_chainFrom_ok_1424_placed_ofEnv {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State) (ch : Chain)
    (w0 w1 w160 d0 d1 d2 : BitVec 64)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1424#64)
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
      ((s0.sp - 4640#64) ↦₆₄ w160) ∗
      memRegion (s0.sp - 4632#64) 40 ∗
      chainPBAt A.repAlloc (s0.sp - 4592#64) ch.intoPb ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 88 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d0) ∗
      ((s0.sp - 4104#64) ↦₆₄ d1) ∗
      ((s0.sp - 4096#64) ↦₆₄ d2) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 3056#64) none ∗
      memRegion (s0.sp - 2832#64) 736 ∗
      memRegion (s0.sp - 2096#64) 88 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have hnone3 : (none3Cap' + 3#64 == 0#64) = true := rfl
  have hslt_m1 : BitVec.slt 0xFFFFFFFFFFFFFFFF#64 1#64 = true := rfl
  rcases htr with ⟨htr_eq, hvregs⟩
  apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  have hopt_some : chainPBAt A.repAlloc (s0.sp - 4592#64) ch.intoPb =
      optChainPBAt A.repAlloc (s0.sp - 4592#64) (some ch.intoPb) := rfl
  rw [← vnTail_some_eq_versionNegotiationPBAt A.repAlloc (s0.sp - 4992#64) w0 w1 vn,
      bv_sub_add_lit s0.sp 4992 8,
      bv_sub_add_lit s0.sp 4992 16,
      hopt_some]
  refine SepWP.focus_weaken (memRegion_224_sub_entails_words28 s0.sp 4512) (by sep_focus) ?_
  wp_pull_exists; rename_i u0 uDst
  refine SepWP.focus_weaken (optProtoPqRatchetInnerAt_none_sub_entails_words27 A.repAlloc s0.sp 3056)
    (by sep_focus) ?_
  wp_pull_exists; rename_i uSrc
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r0 r1 r2 r3
  have hret_fold :
      ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 1#64) ∗ ((ret + 16#64) ↦₆₄ 0#64) ∗
        ((ret + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (ret + 32#64) 16) ⊢
      recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [hok]
    exact recv_ok_empty_foldX A.repAlloc ret
  have hjoin_dst := words27SubAt_to_memRegion_224 s0.sp 4512 none3Cap' uSrc
  dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hjoin_dst
  have hjoin_src := words27SubAt_to_memRegion_224 s0.sp 3056 none3Cap' uSrc
  dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hjoin_src
  dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  simp only [sepConj_assoc]
  refine seq_vm_lscl hcl (mid := lsmpl.base 266)
    (P_mid :=
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      ((s0.sp - 4640#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      memRegion (s0.sp - 4632#64) 40 ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) (some ch.intoPb) ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 88 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d0) ∗
      ((s0.sp - 4104#64) ↦₆₄ d1) ∗
      ((s0.sp - 4096#64) ↦₆₄ d2) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      memRegion (s0.sp - 3056#64) 224 ∗
      memRegion (s0.sp - 2832#64) 736 ∗
      memRegion (s0.sp - 2096#64) 88 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun s1 =>
      s1.sp = s0.sp - 4992#64 ∧
      TraceVRegs s1 s0 ∧
      s1.readReg64 .x0 = s0.sp - 4592#64 ∧
      s1.readReg64 .x20 = w0 ∧
      (BitVec.zeroExtend 64 (BitVec.truncate 32 (s1.readReg64 (Reg.gpr 26#5))) == 0#64) = false ∧
      s1.readReg64 .x30 = (blkPl_329).base + 876#64)
    ?_ ?_
  · by_vm_steps (
      wp_steps 37
      refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin_dst (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin_src (by sep_focus) ?_
      refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl),
         by simp only [wp_norm, arm64_norm, *],
         ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
         by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *],
         by simp [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]⟩
    )
  · intro s1 hpc1 hrun1 hcl1 hvm1 ⟨hsp1, htr1, hx0_1, hx20_1, hx26_1, hlr1⟩
    rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm1]
    have hs1_align : s1.spAligned = true := by
      rw [State.spAligned, hsp1]; exact hfsp_align
    apply sepWP_seq_lscl hcl1 (mid := (blkPl_329).base + 2540#64)
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack80 (by decide)))
      (by sep_focus) ?_
    have hdrop_chain := subroutine_ok_withMemEq_of_lscl hC.dropOptProtoChain_ok hcl1
    simp only [withMemEq, dropOptProtoSpqrChainSpec] at hdrop_chain
    dsimp only [spqrRecvPlacedProg, chainPBSize, BitVec.ofNat_eq_ofNat] at hdrop_chain
    wp_call hdrop_chain (⟨s0.sp - 4592#64, some ch.intoPb⟩, MC.stepEvents evs0 st_cost)
    have hevs_ch := ‹FreeOnlyEvs _›
    have hsp_eq : stackAt s1.sp dropStack80 = stackAt (s0.sp - 4992#64) dropStack80 := by rw [hsp1]
    refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack80 (by decide)).symm)
      (by sep_focus) ?_
    wp_steps 2
    refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      fun hcl2 => ?_
    refine SepWP.focus_weaken (frame4544_join_ok_880 s0.sp 0xFFFFFFFFFFFFFFFF#64 d0 d1 d2)
      (by sep_focus) ?_
    refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
    exact step_drop_pre_2540_placed_ofEnv A lim st_cost Env
      (evs0 ++ freeOnlyWitness hevs_ch)
      (fun evs_d hd => by rw [List.append_assoc]; exact hevs_free _ (hevs_ch.append hd))
      (spqrV1Recv F K) ext hC st msg ret vn pb w0 w1
      s0 _ _ R _ rfl hs0_align
      (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by
        rw [MC.stepEvents_append]
        simp only [freeOnlyWitness, wp_norm, arm64_norm, *]
        sep_ac_rfl)
      hcl2

theorem step_initInner_chainFrom_ok_1424_placed {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (vn : VersionNegotiationPB) (pb : V1State) (ch : Chain)
    (w0 w1 w160 d0 d1 d2 : BitVec 64)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1424#64)
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
      ((s0.sp - 4640#64) ↦₆₄ w160) ∗
      memRegion (s0.sp - 4632#64) 40 ∗
      chainPBAt A.repAlloc (s0.sp - 4592#64) ch.intoPb ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 88 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d0) ∗
      ((s0.sp - 4104#64) ↦₆₄ d1) ∗
      ((s0.sp - 4096#64) ↦₆₄ d2) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 3056#64) none ∗
      memRegion (s0.sp - 2832#64) 736 ∗
      memRegion (s0.sp - 2096#64) 88 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_initInner_chainFrom_ok_1424_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC st msg ret vn pb ch w0 w1 w160 d0 d1 d2 hok s0 s P R hs0_align hpc hrun hsp htr hx19 hx20 hP

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6PlacedBudget
