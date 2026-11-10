/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1RatchetErr2500
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1RatchetErr2500Placed
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable V1 Ratchet Chain & Key Error Cleanup

Envelope-parametric and default `SpqrRecvEnv` error-cleanup steppers after `spqr::chain_from`
(`+1860 -> +2568..+2656`) and `<Chain>::recv_key` (`+2000..+2056 -> +2632`) in `spqr::recv`
(Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1RatchetErr2500PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded lsmpl sepWP_seq_lscl withMemEq)
open CryptoVerification.LibsignalSpqrV1
  (Chain EpochSecret Error Message MlKem PqRatchetState SpqrRecvModel V1Recv
   recvResultExactKeyAt spqrAuthApi spqrPolyApi spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.ChainProofs (ChainGhost chainAt chainSize recvKeyErrAt)
open CryptoVerification.SpqrV1.Drop
  (cap_ne_zero_lt_one_false cap_ne_zero_slt_one_false chunkedStatesAt chunkedStatesSize
   chunkedStatesLocal2JumpTablePlacedAt dropSpqrChainStack dropStack80 dropStackPoly64
   vecCapPtrDealloc)
open CryptoVerification.SpqrV1.States.Recv (optEpochSecretAt)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation (chainErrorAt)
open CryptoVerification.SpqrV1.Top.DecodeState (TraceVRegs optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.MessageSerialize (messageAt)
open CryptoVerification.SpqrV1.Top.Recv
  (cap_add_one_ult_sub_one_false cap_ne_zero_one_sle_true chainErrorAt_unpack_words4
   memRegion_2872_split_chainFrom_err memRegion_3920_join_chainFrom_err
   memRegion_4416_join_464_32_3920 memRegion_4416_join_recvKey_err memRegion_464_16_of_msg
   optEpochSecret_none_entails_of_hfold optEpochSecret_some_entails_of_hfold
   ownFrame_join_err_2524
   recvKeyErrAt_sub3056_expose_words4 recv_err_q0_foldX recv_err_words_foldX ret_48_split
   rodata_chunkedStatesLocal2JumpTablePlacedAt sp_sub_4992_aligned spqrErrorTag_eq_zero_iff
   spqrRecvCalleeStackX spqrRecvPlacedEntry spqrRecvPlacedProg spqrRecvRoPlacedAt
   spqrRecvSavedRegs stackAt_spqrRecvCallee_split subroutine_ok_withMemEq_of_lscl
   vnHeader_sub4640_entails_memRegion_48 vnTail_sub4640_some_entails_dealloc)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropSpqrChainSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.States2Budget (dropChunkedStatesLocal2PlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv spqrRecvPlacedPost0 spqrRecvPlacedPost0OfEnv step_epilogue_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
  (SpqrRecvDropContractsBudget SpqrRecvEnv.append_freeOnly close_free_step deallocFreeOnlySpec
   freeOnlyWitness seq_free_lscl seq_vm_lscl subroutine_ok_deallocFreeOnly)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

export CryptoVerification.SpqrV1.Top.Recv (rodata_chunkedStatesLocal2JumpTablePlacedAt)

/-! ## 1. Shared Error Cleanup Tail at `+2632 .. +2656 -> +1040` (`step_drop_vn_2632_placed`) -/

/-- Envelope-parametric shared error cleanup tail at `+2632 .. +2656` (`-> +1040` when `w26 =
    0`). -/
theorem step_drop_vn_2632_placed_ofEnv {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 4416 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hC.dealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  cases hvn : pre_pb.versionNegotiation with
  | none =>
    dsimp only [optVersionNegotiationPBTailAt]
    wp_focus_pure; intro hw0
    subst hw0
    have hsle : (1#64).sle noneCap = false := rfl
    wp_steps 3
    refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
    refine SepWP.focus_weaken (ownFrame_join_err_2524 s0.sp) (by sep_focus) ?_
    have hevs0 : Env evs0 := by
      simpa only [List.append_nil] using hevs_free [] FreeOnlyEvs.nil
    exact step_epilogue_placed_ofEnv A lim st_cost Env evs0 hevs0 M ext st msg ret s0 _ _ R post hpost
      (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0_align
      (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm]; sep_ac_rfl)
  | some vn =>
    refine SepWP.focus_weaken (vnTail_sub4640_some_entails_dealloc A.repAlloc s0.sp w0 w1 vn) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hc0 : (w0 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hw0
      wp_steps 3
      refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
      refine SepWP.focus_weaken (ownFrame_join_err_2524 s0.sp) (by sep_focus) ?_
      have hevs0 : Env evs0 := by
        simpa only [List.append_nil] using hevs_free [] FreeOnlyEvs.nil
      exact step_epilogue_placed_ofEnv A lim st_cost Env evs0 hevs0 M ext st msg ret s0 _ _ R post hpost
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0_align
        (by simp only [arm64_norm, *])
        (by simp only [wp_norm, arm64_norm]; sep_ac_rfl)
    · have hslt := cap_ne_zero_slt_one_false hcap_lt hc0
      have hsle := cap_ne_zero_one_sle_true hcap_lt hc0
      have hlt_false := cap_ne_zero_lt_one_false hcap_lt hc0
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)))
        (by sep_focus) ?_
      wp_steps 6
      wp_call hdealloc_fo (w1, w0.toNat, 1, MC.stepEvents evs0 st_cost)
      have hsp_eq : stackAt s.sp allocHookStack = stackAt (s0.sp - 4992#64) allocHookStack := by rw [hsp]
      refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm)
        (by sep_focus) ?_
      wp_steps 1
      refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp w0 w1) (by sep_focus) ?_
      refine SepWP.focus_weaken (ownFrame_join_err_2524 s0.sp) (by sep_focus) ?_
      exact step_epilogue_placed_ofEnv A lim st_cost Env
        (evs0 ++ rustDeallocEvents w0.toNat 1)
        (hevs_free _ (FreeOnlyEvs.singleton 1 w0.toNat))
        M ext st msg ret s0 _ _ R post hpost
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0_align
        (by simp only [arm64_norm, *])
        (by
          rw [MC.stepEvents_append]
          try simp only [wp_norm, arm64_norm, *]
          sep_ac_rfl)

theorem step_drop_vn_2632_placed {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)
    (hs0_align : s0.spAligned = true) (hpc : s.pc = spqrRecvPlacedEntry + 2632#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx23 : s.readReg64 .x23 = w0) (hx26 : s.readReg64 .x26 = 0#64)
    (hP : P = spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗ stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗ ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 4416 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_drop_vn_2632_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    M ext hC st msg ret pre_pb w0 w1 s0 s P R post hpost hs0_align
    hpc hrun hsp htr hx23 hx26 hP

/-! ## 2. Drop `v.key : Option EpochSecret` at `+2600 .. +2628 -> +2632` -/

/-- Envelope-parametric drop of `v.key : Option EpochSecret` at `+2600 .. +2628` (`-> +2632`). -/
theorem step_drop_optEpochSecret_2600_placed_ofEnv {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (key : Option EpochSecret) (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        optEpochSecretAt A.repAlloc dst key)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2600#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1)
    (hx28 : s.readReg64 .x28 = 0#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 464 ∗
      memRegion (s0.sp - 4048#64) 16 ∗
      (((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key) ∗
      memRegion (s0.sp - 4016#64) 3920 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hC.dealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  cases key with
  | none =>
    have hnone := optEpochSecret_none_entails_of_hfold A.repAlloc (s0.sp - 4048#64) kw0 kw1 kw2 kw3 P_key hfold_key
    rw [bv_sub_add_lit s0.sp 4048 16, bv_sub_add_lit s0.sp 4048 24] at hnone
    simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hnone
    refine SepWP.focus_weaken hnone (by sep_focus) ?_
    wp_focus_pure; intro hkw0
    subst hkw0
    refine SepWP.focus_weaken (memRegion_4416_join_464_32_3920 s0.sp) (by sep_focus) ?_
    wp_steps 4
    exact step_drop_vn_2632_placed_ofEnv A lim st_cost Env evs0 hevs_free M ext hC st msg ret
      pre_pb w0 w1 s0 _ _ R post hpost hs0_align
      (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm]; sep_ac_rfl)
  | some sec =>
    have hsome := optEpochSecret_some_entails_of_hfold A.repAlloc (s0.sp - 4048#64) kw0 kw1 kw2 kw3 P_key sec hfold_key
    rw [bv_sub_add_lit s0.sp 4048 16, bv_sub_add_lit s0.sp 4048 24] at hsome
    simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hsome
    refine SepWP.focus_weaken hsome (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    refine SepWP.focus_weaken (memRegion_4416_join_464_32_3920 s0.sp) (by sep_focus) ?_
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hc0 : (kw0 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hkw0 : kw0 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hkw0
      wp_steps 4
      exact step_drop_vn_2632_placed_ofEnv A lim st_cost Env evs0 hevs_free M ext hC st msg ret
        pre_pb w0 w1 s0 _ _ R post hpost hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [wp_norm, arm64_norm]; sep_ac_rfl)
    · have hult_false := cap_add_one_ult_sub_one_false hcap_lt hc0
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)))
        (by sep_focus) ?_
      wp_steps 8
      wp_call hdealloc_fo (kw1, kw0.toNat, 1, MC.stepEvents evs0 st_cost)
      have hsp_eq : stackAt s.sp allocHookStack = stackAt (s0.sp - 4992#64) allocHookStack := by rw [hsp]
      refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm)
        (by sep_focus) ?_
      exact step_drop_vn_2632_placed_ofEnv A lim st_cost Env
        (evs0 ++ rustDeallocEvents kw0.toNat 1)
        (fun evs_d hd => by
          rw [List.append_assoc]
          exact hevs_free _ ((FreeOnlyEvs.singleton 1 kw0.toNat).append hd))
        M ext hC st msg ret pre_pb w0 w1 s0 _ _ R post hpost hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by
          rw [MC.stepEvents_append]
          try simp only [wp_norm, arm64_norm, *]
          sep_ac_rfl)

theorem step_drop_optEpochSecret_2600_placed {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (key : Option EpochSecret) (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        optEpochSecretAt A.repAlloc dst key)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)
    (hs0_align : s0.spAligned = true) (hpc : s.pc = spqrRecvPlacedEntry + 2600#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx23 : s.readReg64 .x23 = w0) (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1) (hx28 : s.readReg64 .x28 = 0#64)
    (hP : P = spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗ stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗ ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 464 ∗
      memRegion (s0.sp - 4048#64) 16 ∗ (((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key) ∗
      memRegion (s0.sp - 4016#64) 3920 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_drop_optEpochSecret_2600_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    M ext hC st msg ret pre_pb w0 w1 key kw0 kw1 kw2 kw3 P_key hfold_key s0 s P R post
    hpost hs0_align hpc hrun hsp htr hx23 hx24 hx25 hx28 hP

/-! ## 3. Post-`chain_from` Error Cleanup at `+2568 .. +2600 -> +2632` and `+1860 -> +2568` -/

theorem step_chainFrom_err_2568_placed_ofEnv {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        optEpochSecretAt A.repAlloc dst v.key)
    (e : Error) (q0_err : BitVec 128) (w3_err : BitVec 64)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode))
    (htag_q0 : BitVec.truncate 8 q0_err =
      CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.spqrErrorTag e)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2568#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1)
    (hx28 : s.readReg64 .x28 = 0#64)
    (hP : P =
      chunkedStatesLocal2JumpTablePlacedAt ∗
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗
      ((s0.sp - 4032#64) ↦₆₄ kw2) ∗
      ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
      P_key ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.noneCap) ∗
      ((s0.sp - 3048#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
      ((s0.sp - 3040#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
      ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
      memRegion (s0.sp - 3024#64) 56 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      ((s0.sp - 2096#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
      ((s0.sp - 2088#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
      ((s0.sp - 2080#64) ↦₆₄ w3_err) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r3 r2 r1 r0
  have hret_fold :
      ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((ret + 8#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
        ((ret + 16#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((ret + 24#64) ↦₆₄ w3_err) ∗
        memRegion (ret + 32#64) 16) ⊢
      recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [herr]
    exact recv_err_q0_foldX A.repAlloc ret (q0_err.extractLsb' 64 64) w3_err q0_err e htag_q0
  refine seq_vm_lscl hcl (mid := lsmpl.base 273)
    (P_mid :=
      chunkedStatesLocal2JumpTablePlacedAt ∗
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      (ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      ((ret + 8#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
      ((ret + 16#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
      ((ret + 24#64) ↦₆₄ w3_err) ∗
      memRegion (ret + 32#64) 16 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗
      ((s0.sp - 4032#64) ↦₆₄ kw2) ∗
      ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
      P_key ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.noneCap) ∗
      ((s0.sp - 3048#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
      ((s0.sp - 3040#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
      ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
      memRegion (s0.sp - 3024#64) 56 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      ((s0.sp - 2096#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
      ((s0.sp - 2088#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
      ((s0.sp - 2080#64) ↦₆₄ w3_err) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun s1 =>
      s1.sp = s0.sp - 4992#64 ∧
      TraceVRegs s1 s0 ∧
      s1.readReg64 .x0 = s0.sp - 4016#64 ∧
      s1.readReg64 .lr = (blkPl_329).base + 2600#64 ∧
      s1.readReg64 .x23 = w0 ∧
      s1.readReg64 .x24 = kw0 ∧
      s1.readReg64 .x25 = kw1 ∧
      s1.readReg64 .x28 = 0#64)
    ?_ ?_
  · by_vm_steps (
      wp_steps 8
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm]; try rfl)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm],
         Entails.of_eq (by sep_ac_rfl), ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp only [wp_norm, arm64_norm, *]
    )
  · intro s1 hpc1 hrun1 hcl1 hvm ⟨hsp1, htr1, hx0_1, hlr1, hx23_1, hx24_1, hx25_1, hx28_1⟩
    refine SepWP.transport_budgetPool hvm (hnext := ?_)
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStackPoly64 (by decide)))
      (by sep_focus) ?_
    have hdrop_states := subroutine_ok_withMemEq_of_lscl hC.dropStates_ok hcl1
    simp only [withMemEq, dropChunkedStatesLocal2PlacedSpec] at hdrop_states
    dsimp only [spqrRecvPlacedProg, chunkedStatesSize, BitVec.ofNat_eq_ofNat] at hdrop_states
    wp_call hdrop_states (⟨s0.sp - 4016#64, v.state⟩, MC.stepEvents evs0 st_cost)
    have hevs_st := ‹FreeOnlyEvs _›
    have hsp_eq : stackAt s1.sp dropStackPoly64 = stackAt (s0.sp - 4992#64) dropStackPoly64 := by rw [hsp1]
    refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStackPoly64 (by decide)).symm)
      (by sep_focus) ?_
    refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
    refine SepWP.focus_weaken (memRegion_464_16_of_msg s0.sp sckaMsg) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (memRegion_3920_join_chainFrom_err s0.sp (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err)
      (by sep_focus) ?_
    refine CryptoVerification.SpqrV1.Top.Recv.SepWP.drop_ro chunkedStatesLocal2JumpTablePlacedAt
      (step_drop_optEpochSecret_2600_placed_ofEnv A lim st_cost Env
        (evs0 ++ freeOnlyWitness hevs_st)
        (fun evs_d hd => by
          rw [List.append_assoc]
          exact hevs_free _ (hevs_st.append hd))
        (spqrV1Recv F K) ext hC st msg ret pre_pb w0 w1
        v.key kw0 kw1 kw2 kw3 P_key hfold_key s0 _ _ R post hpost hs0_align
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) rfl)
      (by
        rw [MC.stepEvents_append]
        try simp only [freeOnlyWitness, wp_norm, arm64_norm, *]
        sep_ac_rfl)

theorem step_chainFrom_err_2568_placed {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F)) (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        optEpochSecretAt A.repAlloc dst v.key)
    (e : Error) (q0_err : BitVec 128) (w3_err : BitVec 64)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode))
    (htag_q0 : BitVec.truncate 8 q0_err =
      CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.spqrErrorTag e)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true) (hpc : s.pc = spqrRecvPlacedEntry + 2568#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = kw0) (hx25 : s.readReg64 .x25 = kw1) (hx28 : s.readReg64 .x28 = 0#64)
    (hP : P = chunkedStatesLocal2JumpTablePlacedAt ∗ spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗ stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗ ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 32 ∗
      ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.noneCap) ∗
      ((s0.sp - 3048#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗ ((s0.sp - 3040#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
      ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 3024#64) 56 ∗ memRegion (s0.sp - 2968#64) 872 ∗
      ((s0.sp - 2096#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗ ((s0.sp - 2088#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
      ((s0.sp - 2080#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_chainFrom_err_2568_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC st msg ret pre_pb w0 w1 sckaMsg v kw0 kw1 kw2 kw3 P_key hfold_key
    e q0_err w3_err herr htag_q0 s0 s P R post hpost hs0_align
    hpc hrun hsp htr hx19 hx23 hx24 hx25 hx28 hP hcl

theorem step_post_chainFrom_err_1860_placed_ofEnv {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        optEpochSecretAt A.repAlloc dst v.key)
    (e : Error)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1860#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = 0#64)
    (hP : P =
      chunkedStatesLocal2JumpTablePlacedAt ∗
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗
      ((s0.sp - 4032#64) ↦₆₄ kw2) ∗
      ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
      P_key ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      chainErrorAt (s0.sp - 3056#64) e ∗
      memRegion (s0.sp - 2968#64) 2872 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hnone1 : (CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.noneCap + 1#64 == 0#64) = true := rfl
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [chainErrorAt_unpack_words4 (s0.sp - 3056#64) e,
      bv_sub_add_lit s0.sp 3056 8,
      bv_sub_add_lit s0.sp 3056 16,
      bv_sub_add_lit s0.sp 3056 24,
      bv_sub_add_lit s0.sp 3056 32]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i q0_err w3_err
  wp_focus_pure; intro htag_q0
  refine SepWP.focus_weaken (memRegion_2872_split_chainFrom_err s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i d0 d1 d2
  refine seq_vm_lscl hcl (mid := (blkPl_329).base + 2568#64)
    (P_mid :=
      chunkedStatesLocal2JumpTablePlacedAt ∗
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗
      ((s0.sp - 4032#64) ↦₆₄ kw2) ∗
      ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
      P_key ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.noneCap) ∗
      ((s0.sp - 3048#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
      ((s0.sp - 3040#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
      ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
      memRegion (s0.sp - 3024#64) 56 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      ((s0.sp - 2096#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
      ((s0.sp - 2088#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
      ((s0.sp - 2080#64) ↦₆₄ w3_err) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun s1 =>
      s1.sp = s0.sp - 4992#64 ∧
      TraceVRegs s1 s0 ∧
      s1.readReg64 .x19 = ret ∧
      s1.readReg64 .x23 = w0 ∧
      s1.readReg64 .x24 = kw0 ∧
      s1.readReg64 .x25 = kw1 ∧
      s1.readReg64 .x28 = 0#64)
    ?_ ?_
  · by_vm_steps (
      wp_steps 7
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm]; try rfl)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm],
         Entails.of_eq (by sep_ac_rfl), ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp only [wp_norm, arm64_norm, *]
    )
  · intro s1 hpc1 hrun1 hcl1 hvm ⟨hsp1, htr1, hx19_1, hx23_1, hx24_1, hx25_1, hx28_1⟩
    refine SepWP.transport_budgetPool hvm (hnext := ?_)
    exact step_chainFrom_err_2568_placed_ofEnv A lim st_cost Env evs0 hevs_free F K ext hC st msg ret
      pre_pb w0 w1 sckaMsg v kw0 kw1 kw2 kw3 P_key hfold_key e q0_err w3_err herr htag_q0
      s0 s1 _ R post hpost hs0_align hpc1 hrun1 hsp1 htr1 hx19_1 hx23_1 hx24_1 hx25_1 hx28_1
      (by sep_ac_rfl) hcl1

theorem step_post_chainFrom_err_1860_placed {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F)) (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        optEpochSecretAt A.repAlloc dst v.key)
    (e : Error) (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true) (hpc : s.pc = spqrRecvPlacedEntry + 1860#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = kw0) (hx25 : s.readReg64 .x25 = kw1)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hP : P = chunkedStatesLocal2JumpTablePlacedAt ∗ spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗ stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗ ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 32 ∗
      ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
      chainErrorAt (s0.sp - 3056#64) e ∗ memRegion (s0.sp - 2968#64) 2872 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_post_chainFrom_err_1860_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC st msg ret pre_pb w0 w1 sckaMsg v kw0 kw1 kw2 kw3 P_key hfold_key
    e herr s0 s P R post hpost hs0_align hpc hrun hsp htr
    hx19 hx23 hx24 hx25 hx27 hx28 hP hcl

/-! ## 4. Post-`recv_key` Error Cleanup at `+2000 .. +2056 -> +2632` -/

theorem step_recvKey_err_2028_placed_ofEnv {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (g1 : ChainGhost) (chain1 : Chain)
    (err : Error) (w1_err w2_err w3_err : BitVec 64)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (err == .stateDecode))
    (hw1_err : ∀ r : BitVec 64,
      ((r + 8#64) ↦₆₄ w1_err) ⊢
        ((r + 8#64) ↦₈ CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.spqrErrorTag err) ∗
        memRegion (r + 9#64) 7)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2028#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = w1_err)
    (hx22 : s.readReg64 .x22 = w2_err)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = w3_err)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      chunkedStatesLocal2JumpTablePlacedAt ∗
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 48 ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ 1#64) ∗
      ((s0.sp - 3048#64) ↦₆₄ w1_err) ∗
      ((s0.sp - 3040#64) ↦₆₄ w2_err) ∗
      ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
      memRegion (s0.sp - 3024#64) 2792 ∗
      chainAt A.repAlloc (s0.sp - 232#64) g1 chain1 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have hfp : s.readReg64 .fp = s0.sp - 96#64 := hx29
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r3 r2 r1 r0
  have hret_fold :
      ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((ret + 8#64) ↦₆₄ w1_err) ∗
        ((ret + 16#64) ↦₆₄ w2_err) ∗
        ((ret + 24#64) ↦₆₄ w3_err) ∗
        memRegion (ret + 32#64) 16) ⊢
      recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [herr]
    exact recv_err_words_foldX A.repAlloc ret w1_err w2_err w3_err
      (CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.spqrErrorTag err) (err == .stateDecode)
      (Iff.of_eq (spqrErrorTag_eq_zero_iff err)) hw1_err
  let st0 := MC.stepEvents evs0 st_cost
  refine seq_vm_lscl hcl (mid := lsmpl.base 269)
    (P_mid :=
      chunkedStatesLocal2JumpTablePlacedAt ∗
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      (ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      ((ret + 8#64) ↦₆₄ w1_err) ∗
      ((ret + 16#64) ↦₆₄ w2_err) ∗
      ((ret + 24#64) ↦₆₄ w3_err) ∗
      memRegion (ret + 32#64) 16 ∗
      A.pool lim st0 s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 48 ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ 1#64) ∗
      ((s0.sp - 3048#64) ↦₆₄ w1_err) ∗
      ((s0.sp - 3040#64) ↦₆₄ w2_err) ∗
      ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
      memRegion (s0.sp - 3024#64) 2792 ∗
      chainAt A.repAlloc (s0.sp - 232#64) g1 chain1 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun s1 =>
      s1.sp = s0.sp - 4992#64 ∧
      TraceVRegs s1 s0 ∧
      s1.readReg64 .x0 = s0.sp - 232#64 ∧
      s1.readReg64 .lr = (blkPl_329).base + 2048#64 ∧
      s1.readReg64 .x23 = w0 ∧
      s1.readReg64 .x26 = 0#64)
    ?_ ?_
  · by_vm_steps (
      wp_steps 5
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm]; try rfl)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm],
         Entails.of_eq (by sep_ac_rfl), ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp only [wp_norm, arm64_norm, *]
    )
  · intro s1 hpc1 hrun1 hcl1 hvm ⟨hsp1, htr1, hx0_1, hlr1, hx23_1, hx26_1⟩
    refine SepWP.transport_budgetPool hvm (hnext := ?_)
    refine seq_free_lscl hcl1 (mid := lsmpl.base 273)
      (P_evs := fun evs_ch s2 =>
        chunkedStatesLocal2JumpTablePlacedAt ∗
        spqrRecvRoPlacedAt ∗
        st.at A.repAlloc ∗
        msg.at A.repAlloc ∗
        (ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((ret + 8#64) ↦₆₄ w1_err) ∗
        ((ret + 16#64) ↦₆₄ w2_err) ∗
        ((ret + 24#64) ↦₆₄ w3_err) ∗
        memRegion (ret + 32#64) 16 ∗
        A.pool lim (MC.stepEvents evs_ch st0) s2 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗
        ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗
        memRegion (s0.sp - 4512#64) 224 ∗
        memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 48 ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 32 ∗
        ((s0.sp - 3056#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 3048#64) ↦₆₄ w1_err) ∗
        ((s0.sp - 3040#64) ↦₆₄ w2_err) ∗
        ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
        memRegion (s0.sp - 3024#64) 2792 ∗
        memRegion (s0.sp - 232#64) 88 ∗
        memRegion (s0.sp - 144#64) 48 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun s2 =>
        s2.sp = s0.sp - 4992#64 ∧
        TraceVRegs s2 s0 ∧
        s2.readReg64 .x0 = s0.sp - 4016#64 ∧
        s2.readReg64 .lr = (blkPl_329).base + 2056#64 ∧
        s2.readReg64 .x23 = w0 ∧
        s2.readReg64 .x26 = 0#64)
      ?_ ?_
    · refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack80 (by decide)))
        (by sep_focus) ?_
      have hdrop_chain := subroutine_ok_withMemEq_of_lscl hC.dropChain_ok hcl1
      simp only [withMemEq, dropSpqrChainSpec] at hdrop_chain
      dsimp only [spqrRecvPlacedProg, dropSpqrChainStack, chainSize, BitVec.ofNat_eq_ofNat] at hdrop_chain
      wp_call hdrop_chain (⟨s0.sp - 232#64, g1, chain1⟩, st0)
      have hevs_ch := ‹FreeOnlyEvs _›
      have hsp_eq1 : stackAt s1.sp dropStack80 = stackAt (s0.sp - 4992#64) dropStack80 := by rw [hsp1]
      refine SepWP.focus_weaken (Entails.of_eq hsp_eq1) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack80 (by decide)).symm)
        (by sep_focus) ?_
      wp_steps 2
      refine close_free_step (freeOnlyWitness hevs_ch) hevs_ch
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (Entails.of_eq (by
          try simp only [freeOnlyWitness, wp_norm, arm64_norm, *]
          sep_ac_rfl))
        ?_
      rcases htr1 with ⟨htr1_t, hvregs1⟩
      refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      all_goals simp only [wp_norm, arm64_norm, *]
    · intro evs_ch s2 hevs_ch hpc2 hrun2 hcl3 ⟨hsp2, htr2, hx0_2, hlr_2, hx23_2, hx26_2⟩
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStackPoly64 (by decide)))
        (by sep_focus) ?_
      have hdrop_states := subroutine_ok_withMemEq_of_lscl hC.dropStates_ok hcl3
      simp only [withMemEq, dropChunkedStatesLocal2PlacedSpec] at hdrop_states
      dsimp only [spqrRecvPlacedProg, chunkedStatesSize, BitVec.ofNat_eq_ofNat] at hdrop_states
      wp_call hdrop_states (⟨s0.sp - 4016#64, v.state⟩, MC.stepEvents evs_ch st0)
      have hevs_st := ‹FreeOnlyEvs _›
      have hsp_eq2 : stackAt s2.sp dropStackPoly64 = stackAt (s0.sp - 4992#64) dropStackPoly64 := by rw [hsp2]
      refine SepWP.focus_weaken (Entails.of_eq hsp_eq2) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStackPoly64 (by decide)).symm)
        (by sep_focus) ?_
      wp_steps 1
      refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
      refine SepWP.focus_weaken
        (memRegion_4416_join_recvKey_err s0.sp w1_err w2_err w3_err sckaMsg)
        (by sep_focus) ?_
      refine CryptoVerification.SpqrV1.Top.Recv.SepWP.drop_ro chunkedStatesLocal2JumpTablePlacedAt
        (step_drop_vn_2632_placed_ofEnv A lim st_cost Env
          (evs0 ++ evs_ch ++ freeOnlyWitness hevs_st)
          (fun evs_d hd => by
            rw [List.append_assoc, List.append_assoc]
            exact hevs_free _ (hevs_ch.append (hevs_st.append hd)))
          (spqrV1Recv F K) ext hC st msg ret pre_pb w0 w1 s0 _ _ R post hpost hs0_align
          (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) rfl)
        (by
          dsimp only [st0]
          rw [MC.stepEvents_append, MC.stepEvents_append]
          try simp only [freeOnlyWitness, wp_norm, arm64_norm, *]
          sep_ac_rfl)

theorem step_recvKey_err_2028_placed {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F)) (g1 : ChainGhost) (chain1 : Chain)
    (err : Error) (w1_err w2_err w3_err : BitVec 64)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (err == .stateDecode))
    (hw1_err : ∀ r : BitVec 64,
      ((r + 8#64) ↦₆₄ w1_err) ⊢
        ((r + 8#64) ↦₈ CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.spqrErrorTag err) ∗
        memRegion (r + 9#64) 7)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true) (hpc : s.pc = spqrRecvPlacedEntry + 2028#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = w1_err)
    (hx22 : s.readReg64 .x22 = w2_err) (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = w3_err) (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = chunkedStatesLocal2JumpTablePlacedAt ∗ spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗ stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗ ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ 1#64) ∗ ((s0.sp - 3048#64) ↦₆₄ w1_err) ∗
      ((s0.sp - 3040#64) ↦₆₄ w2_err) ∗ ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
      memRegion (s0.sp - 3024#64) 2792 ∗ chainAt A.repAlloc (s0.sp - 232#64) g1 chain1 ∗
      memRegion (s0.sp - 144#64) 48 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_recvKey_err_2028_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC st msg ret pre_pb w0 w1 sckaMsg v g1 chain1 err w1_err w2_err w3_err
    herr hw1_err s0 s P R post hpost hs0_align hpc hrun hsp htr
    hx19 hx21 hx22 hx23 hx24 hx26 hx29 hP hcl

theorem step_recvKey_err_2000_placed_ofEnv {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (g1 : ChainGhost) (chain1 : Chain)
    (err : Error)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (err == .stateDecode))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2000#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = w0)
    (hx28 : s.readReg64 .x28 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      chunkedStatesLocal2JumpTablePlacedAt ∗
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 48 ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      recvKeyErrAt (s0.sp - 3056#64) err ∗
      memRegion (s0.sp - 3024#64) 2792 ∗
      chainAt A.repAlloc (s0.sp - 232#64) g1 chain1 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine SepWP.focus_weaken (recvKeyErrAt_sub3056_expose_words4 s0.sp err) (by sep_focus) ?_
  wp_pull_exists; rename_i w1_err w2_err w3_err
  wp_focus_pure; intro hw1_err
  apply sepWP_seq_lscl hcl
  wp_steps 7
  refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
  exact step_recvKey_err_2028_placed_ofEnv A lim st_cost Env evs0 hevs_free F K ext hC st msg ret
    pre_pb w0 w1 sckaMsg v g1 chain1 err w1_err w2_err w3_err herr hw1_err s0 _ _ R post
    hpost hs0_align
    (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm]; sep_ac_rfl) hcl1

theorem step_recvKey_err_2000_placed {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F)) (g1 : ChainGhost) (chain1 : Chain) (err : Error)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (err == .stateDecode))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true) (hpc : s.pc = spqrRecvPlacedEntry + 2000#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx23 : s.readReg64 .x23 = w0)
    (hx28 : s.readReg64 .x28 = 0#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = chunkedStatesLocal2JumpTablePlacedAt ∗ spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗ stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗ ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
      recvKeyErrAt (s0.sp - 3056#64) err ∗ memRegion (s0.sp - 3024#64) 2792 ∗
      chainAt A.repAlloc (s0.sp - 232#64) g1 chain1 ∗ memRegion (s0.sp - 144#64) 48 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_recvKey_err_2000_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC st msg ret pre_pb w0 w1 sckaMsg v g1 chain1 err herr s0 s P R post
    hpost hs0_align hpc hrun hsp htr hx19 hx23 hx28 hx29 hP hcl

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1RatchetErr2500PlacedBudget
