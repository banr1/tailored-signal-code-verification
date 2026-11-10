/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.DropsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.CallSpecs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `FdsGe3Closed`-Threaded Relocatable `last_resort` Error & Append Exits for `KpkMarkPoll`

Proves `FdsGe3Closed`-threaded `kpk_reused_230_placed_fd`, `kpk_malformed_2a4_placed_fd`, and
`kpk_append_37c_placed_fd` on Block `578` (`lsProg_578 H`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudgetFd

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall doReserveStackX extHookStack finishGrowStackX memcpyName reserveCap
   sessionMemcpyRegionSpec sessionShimSpec withStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession
  (lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGhost KpkMarkPollGhost dirAt kpkMarkBoxAt kpkMarkOutAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_578 blkPl_578 lsProg_578)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (CliPanicHooksPlaced)
open CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers
  (fs_advancePC fs_applyWriteback fs_setMem fs_setPC fs_setPState fs_writeReg fs_writeReg32
   fs_writeReg64 fs_writeVReg128)
open CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
  (bind_sepWP_state_mark bind_sepWPp_state_mark cs_vregs cs_x19 cs_x20 cs_x21 cs_x24 cs_x26 cs_x28
   cs_x29 epiloguePre fast_seen_cap_ge kpkMinStk kpkSubMax layoutOk_u8_of_ne_zero
   malformedStrAddrPlaced reserve_seen_bound reusedStrAddrPlaced savedCalleeSlots sepWPp_conseq
   sepWPp_of_sepWP_lscro setWidth_32_setWidth_64 slot_b0_24_24_merge spAligned_sub_f0 subStack_split
   vecU8Tail vecU8_free_ne vecU8_free_zero vecU8_of_bytes_tail write_14_overlap_done
   write_14_overlap_mid write_15_overlap_done write_15_overlap_mid)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   rustAllocEvents rustCliAllocNoOomExternSpecWithStack rustCliDeallocBudgetExternSpecWithStack
   rustDeallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocNoOomExternSpecWithStack rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (dealloc_keepsFs_lscro_of_fs session_memcpy_region_keepsFs_lscro_of_fs shim_keepsFs_lscro_of_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced dirPutSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudgetFd
  (allocNoOomExtern_keepsFs_lscro_of_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (optDeallocBufEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesPlacedBudgetFd
  (kpkReserve_at_keepsFs_caller_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.DropsPlacedBudgetFd
  (kpk_put_and_epilogue_b8_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudget
  (kpkErrCleanupEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudgetFd
  (kpk_err_cleanup_2e8_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudgetAux
  (kpkAppendPrePutEvents kpkAppendReserveEvents kpkDoReserveSpec kpkMalformedEvents kpkReusedEvents
   vecU8At_of_flat_p vecU8At_unpack_pos_p vecU8_of_grown_p)

private theorem bv_sub_add_lit_kpk (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit_kpk BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64
  fs_advancePC fs_applyWriteback fs_setMem fs_setPC fs_setPState
  fs_writeReg fs_writeReg32 fs_writeReg64 fs_writeVReg128
  State.fs_setStatus State.fs_appendTrace

local macro_rules
  | `(tactic| kpk_norm) =>
    `(tactic|
      ((try with_reducible rfl)
       (try simp +zetaDelta only [wp_norm])
       (try simp +zetaDelta only [arm64_norm])
       (try simp +zetaDelta only [*])
       (try with_reducible rfl)
       try bv_omega))

private theorem entails_withLsCodeRoLoaded_pre_res_fd [LibsignalPlacement]
    {s : State} {P Q F : SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : P ⊢ Q ∗ F) :
    P ⊢ (Q ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ F := by
  refine Entails.trans h ?_
  rw [sepConj_assoc]
  exact sepConj_mono_right (Entails.pure_right hcrl (Entails.refl F))

/-- `SepWPp` call wrapper for `.keepsFs` `kpkDoReserveSpec` under `withLsCodeRoLoaded lsmpl`. -/
private theorem kpk_call_reserve_at_placed_fd [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {resStack : Nat} {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim resStack).keepsFs))
    (xg : DoReserveCall) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.v) (hx1 : (s.readReg64 .x1).toNat = xg.bs.length)
    (hx2 : (s.readReg64 .x2).toNat = xg.additional)
    (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hbound : reserveCap xg.cap.toNat xg.bs.length xg.additional + 1 ≤ 2 ^ 63)
    (hfit : FitsEvents M lim st (doReserveEvents xg))
    (hpre : P ⊢ (vecU8At A.repAlloc xg.v xg.cap xg.ptr xg.bs ∗
      A.pool lim st s ∗ stackAt s.sp resStack) ∗ F)
    (hnext : ∀ (sm : State) (p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.fs = s.fs → sm.trace = s.trace → p' ≠ 0#64 →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc xg.v
            (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗ stackAt s.sp resStack) ∗ F)
        Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hpre' : P ⊢ (withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim resStack).keepsFs).pre (xg, st) s ∗ F := by
    refine Entails.trans hpre ?_
    unfold withLsCodeRoLoaded Spec.keepsFs kpkDoReserveSpec
    refine entails_withLsCodeRoLoaded_pre_res_fd hcrl ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbound, hfit⟩ (Entails.refl _)
  refine sepWPp_of_sepWP_lscro hcrl (mid := ret_pc) ?_
  exact ProofLib.SepWP.call_subroutine_frame hcall hpc hrun hsp_align hlr
    (fun R hm => by
      have hm' : s.mem ⊨
          ((withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim resStack).keepsFs).pre (xg, st) s ∗ F) ∗ R :=
        Satisfies.mono (sepConj_mono_left hpre') hm
      rwa [sepConj_assoc] at hm')
    (fun _ _ _ hp => by
      simp only [Spec.keepsFs, kpkDoReserveSpec] at hp
      exact not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => by
      simp only [Spec.keepsFs, kpkDoReserveSpec] at he
      exact not_satisfies_false_sepConj he)
    (fun sm hpcm hrunm hspm hcsm =>
      ProofLib.SepWP.done hpcm hrunm fun hcrlm => by
        simp only [Spec.keepsFs, kpkDoReserveSpec, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_elim fun p' => SepWPp.pure_elim fun hfsm =>
          SepWPp.pure_elim fun htrm => ?_
        have hp'_pull :
            vecU8At A.repAlloc xg.v
                (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
              (A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗
                (stackAt s.sp resStack ∗ F)) =
            (vecU8At A.repAlloc xg.v
                (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
              A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗ stackAt s.sp resStack) ∗ F := by
          sep_ac_rfl
        rw [hp'_pull]
        intro R' hm hL
        have hp'_ne : p' ≠ 0#64 := by
          have hm1 : sm.mem ⊨ vecU8At A.repAlloc xg.v
              (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
              ((A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗ stackAt s.sp resStack) ∗
                F ∗ R') := by
            simpa only [sepConj_assoc] using hm
          unfold vecU8At at hm1
          rw [sepConj_assoc] at hm1
          have hm2 := Satisfies.of_sep_left (Satisfies.of_sep_right hm1)
          rw [satisfies_pure_sepConj] at hm2
          exact hm2.1.2.2
        exact hnext sm p' hpcm hrunm hspm hcsm hcrlm hfsm htrm hp'_ne R' hm hL)
    (fun _ _ _ ho => by
      simp only [Spec.keepsFs, kpkDoReserveSpec] at ho
      exact (not_satisfies_false_sepConj ho).elim)

/-! ## 1. `reused` Exit (`+560 .. +628`, Cleanup `+744`) -/

/-- `reused` exit preserving `sf.fs = s.fs` under `AllocContractsFsPlaced`. -/
theorem kpk_reused_230_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFsAlloc : AllocContractsFsPlaced A lim H)
    (x : KpkMarkPollGhost) (st : M.σ) (s0 s : State)
    (wR0 wR7 : BitVec 64)
    (usedCap usedPtr : BitVec 64) (usedBs : List (BitVec 8))
    (seenCap seenPtr : BitVec 64) (seenBs : List (BitVec 8))
    (fileCap filePtr : BitVec 64) (fileBs : List (BitVec 8))
    (P F : SepProp) {Q Qp : State → SepProp → Prop}
    (hfit : FitsEvents M lim st (rustAllocEvents 15 1))
    (hu_len : usedBs.length ≤ usedCap.toNat) (hu_lt : usedCap.toNat < 2 ^ 63)
    (hu_ptr : usedPtr ≠ 0#64)
    (hs_len : seenBs.length ≤ seenCap.toNat) (hs_lt : seenCap.toNat < 2 ^ 63)
    (hs_ptr : seenPtr ≠ 0#64)
    (hf_len : fileBs.length ≤ fileCap.toNat) (hf_lt : fileCap.toNat < 2 ^ 63)
    (hf_ptr : filePtr ≠ 0#64)
    (hpc : s.pc = (blkPl_578).base + 560#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (htr : s.trace = s0.trace)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx27 : s.readReg64 .x27 = seenCap)
    (hfoc : P ⊢
      (reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
      ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
      ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
      ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
      ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
      bytesAt false usedPtr usedBs ∗
      vecU8Tail A.repAlloc usedCap usedPtr usedBs ∗
      bytesAt false seenPtr seenBs ∗
      vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
      ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
      ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
      bytesAt false filePtr fileBs ∗
      vecU8Tail A.repAlloc fileCap filePtr fileBs ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      epiloguePre s0 x ∗ A.pool lim st s ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s0.trace →
      sf.fs = s.fs →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkOutAt A.repAlloc x.out .reused ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗
        (reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        A.pool lim (M.stepEvents (kpkReusedEvents usedCap seenCap fileCap) st) sf ∗ F) →
      Q sf P_f) :
    SepWPp (lsProg_578 H) (s0.readReg64 .lr) s P Q Qp := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hrlay15 : RustLayoutOk 15 1 := ⟨⟨by decide, hpow1, by decide⟩, hal1⟩
  have hfit_dec := hfit
  rcases hfit_dec with ⟨⟨hwma, henf, hphys, hva⟩, -⟩
  have hshim := shim_keepsFs_lscro_of_fs (callerProg := lsProg_578 H) hFsAlloc
    (stk := extHookStack) (by decide) (by decide)
  have halloc := allocNoOomExtern_keepsFs_lscro_of_fs (callerProg := lsProg_578 H) hFsAlloc
  have hclean := @kpk_err_cleanup_2e8_placed_fd _ M A lim H hFsAlloc
  dsimp only [withLsCodeRoLoaded, Spec.keepsFs, withStack, sessionShimBudgetSpec,
    sessionShimSpec, lsProg_578] at hshim
  dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
    rustCliAllocNoOomExternSpecWithStack, rustCliAllocNoOomSpecWithStack, ↓reduceIte,
    lsProg_578] at halloc
  dsimp only [lsProg_578] at hclean
  clear hFsAlloc
  let st_al : M.σ := M.stepEvents (rustAllocEvents 15 1) st
  have hst_reused :
      M.stepEvents (kpkErrCleanupEvents usedCap seenCap fileCap) st_al =
        M.stepEvents (kpkReusedEvents usedCap seenCap fileCap) st := by
    simp only [st_al, kpkReusedEvents, M.stepEvents_append]
  change SepWPp ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) s P Q Qp
  refine sepWPp_conseq hfoc ?_
  apply SepWPp.of_sepWP_ret
  apply sepWP_seq_lscro hcrl (mid := lsρ lsRustNoAllocShimSymCli)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  apply sepWP_seq_lscro hcrl1 (mid := lsρ lsRustAllocSymCli)
  rcases hcrl1 with ⟨hcl1, hro1⟩
  wp_call hshim ()
  refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  rintro ⟨hcl2, hro2⟩
  apply sepWP_seq_lscro ⟨hcl2, hro2⟩ (mid := (blkPl_578).base + 576#64)
  wp_call halloc (15, 1, st)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_al
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by tauto
  have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have hafter_adrp : ∀ (sm : State) (Q_m : SepProp),
      sm.pc = (blkPl_578).base + 588#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 0xf0#64 →
      sm.readReg64 .x29 = s0.sp - 0x60#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      sm.fs = s.fs →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x0 = sf_1.readReg64 .x0 →
      sm.readReg64 .x8 = reusedStrAddrPlaced →
      sm.readReg64 .x19 = x.fut →
      sm.readReg64 .x20 = x.out →
      sm.readReg64 .x27 = seenCap →
      (Q_m ⊢
        memRegion (sf_1.readReg64 .x0) 15 ∗
        A.repAlloc.live (sf_1.readReg64 .x0) 15 1 ∗
        (reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        bytesAt false usedPtr usedBs ∗
        vecU8Tail A.repAlloc usedCap usedPtr usedBs ∗
        bytesAt false seenPtr seenBs ∗
        vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        bytesAt false filePtr fileBs ∗
        vecU8Tail A.repAlloc fileCap filePtr fileBs ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        epiloguePre s0 x ∗ A.pool lim st_al sm ∗ F) →
      SepWP ((blkPC_578).rebase (blkPl_578).base H)
        (s0.readReg64 .lr) sm Q_m Q := by
    intro sm Q_m hpcm hrunm hspm hfpm hcrlm htrm hfsm hvm r0 r8 r19 r20 r27 hQm
    have hsp_alm : sm.spAligned = true := spAligned_sub_f0 hsp_align hspm
    refine SepWP.weaken_pre hQm ?_
    rw [ProofLib.memRegion_split (sf_1.readReg64 .x0) 8 7 (by decide),
        ProofLib.memRegion_eight]
    simp only [sepConj_assoc, sepExists_sepConj_left]
    refine SepWP.exists_elim fun z0 => ?_
    apply sepWP_seq_lscro hcrlm (mid := (blkPl_578).base + 624#64)
    wp_steps_sync_pool ((blkPl_578).base + 624#64)
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_mid
    refine SepWP.fold (write_15_overlap_mid (sf_1.readReg64 .x0) wR0) (by sep_focus) ?_
    rw [ProofLib.memRegion_eight]
    (try simp only [sepExists_sepConj_right])
    (try simp only [sepExists_sepConj_left])
    simp only [sepConj_assoc]
    refine SepWP.exists_elim fun z7 => ?_
    apply sepWP_seq_lscro hcrl_mid (mid := (blkPl_578).base + 744#64)
    wp_steps_sync_pool ((blkPl_578).base + 744#64)
    apply bind_sepWP_state_mark; intro st_2e8; apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_2e8
    refine SepWP.fold (write_15_overlap_done (sf_1.readReg64 .x0) wR0 wR7) (by sep_focus) ?_
    have hlen15 : ((unpack64 wR0).take 7 ++ unpack64 wR7).length = 15 := by
      simp [unpack64_length]
    have hspe24 : (0x8000000000000018#64 : BitVec 64) = speWord 24 := by decide
    refine hclean x st_al s0 st_2e8 24 (sf_1.readReg64 .x0) ((unpack64 wR0).take 7 ++ unpack64 wR7)
      3#64 (st_2e8.readReg64 .x23) usedCap usedPtr usedBs seenCap seenPtr seenBs fileCap filePtr fileBs _
      ((reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗ F)
      (by rw [hlen15]; decide)
      (by rw [hlen15]; decide)
      hoom
      hu_len hu_lt hu_ptr hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      hsp_align
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      hcrl_2e8
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; rw [← hspe24]; kpk_norm)
      (by dsimp only [st_2e8]; rw [hlen15]; kpk_norm)
      rfl
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      (by rw [hlen15]; unfold epiloguePre; kpk_sep_focus)
      fun sf_e P_e htr_e hfs_e hsp_e hcs_e hPe =>
        hk sf_e P_e
          (htr_e.trans ((by dsimp only [st_2e8]; kpk_norm : st_2e8.trace = sm.trace).trans htrm))
          (hfs_e.trans ((by dsimp only [st_2e8]; kpk_norm : st_2e8.fs = sm.fs).trans hfsm))
          hsp_e hcs_e
          (Entails.trans hPe (by rw [hst_reused]; dsimp [kpkMarkOutAt]; sep_focus))
  apply sepWP_seq_lscro hcrl_al (mid := (blkPl_578).base + 588#64)
  wp_steps_sync_pool ((blkPl_578).base + 588#64)
  apply bind_sepWP_state_mark; intro st_adrp; apply SepWP.done (by kpk_norm) (by kpk_norm)
  intro hcrl_adrp
  have hr_addr : (blkPl_578).ρ "libsignal_cli:.rodata..Lanon.32" = reusedStrAddrPlaced := rfl
  exact hafter_adrp st_adrp _
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    hcrl_adrp
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; rw [← hr_addr]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by rw [hsp_sf, hsp]; dsimp only [RustCliAllocBudget.repAlloc_live, Reg.x0]; unfold epiloguePre; kpk_sep_focus)

/-! ## 2. `malformed` Exit (`+676 .. +740`, Cleanup `+744`) -/

/-- `malformed` exit preserving `sf.fs = s.fs` under `AllocContractsFsPlaced`. -/
theorem kpk_malformed_2a4_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFsAlloc : AllocContractsFsPlaced A lim H)
    (x : KpkMarkPollGhost) (st : M.σ) (s0 s : State)
    (wM0 wM6 : BitVec 64)
    (usedCap usedPtr : BitVec 64) (usedBs : List (BitVec 8))
    (seenCap seenPtr : BitVec 64) (seenBs : List (BitVec 8))
    (fileCap filePtr : BitVec 64) (fileBs : List (BitVec 8))
    (P F : SepProp) {Q Qp : State → SepProp → Prop}
    (hfit : FitsEvents M lim st (rustAllocEvents 14 1))
    (hu_len : usedBs.length ≤ usedCap.toNat) (hu_lt : usedCap.toNat < 2 ^ 63)
    (hu_ptr : usedPtr ≠ 0#64)
    (hs_len : seenBs.length ≤ seenCap.toNat) (hs_lt : seenCap.toNat < 2 ^ 63)
    (hs_ptr : seenPtr ≠ 0#64)
    (hf_len : fileBs.length ≤ fileCap.toNat) (hf_lt : fileCap.toNat < 2 ^ 63)
    (hf_ptr : filePtr ≠ 0#64)
    (hpc : s.pc = (blkPl_578).base + 676#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (htr : s.trace = s0.trace)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx25 : s.readReg64 .x25 = seenPtr)
    (hx27 : s.readReg64 .x27 = seenCap)
    (hfoc : P ⊢
      (malformedStrAddrPlaced ↦₆₄ᵣ wM0) ∗
      ((malformedStrAddrPlaced + 6#64) ↦₆₄ᵣ wM6) ∗
      ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
      ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
      bytesAt false usedPtr usedBs ∗
      vecU8Tail A.repAlloc usedCap usedPtr usedBs ∗
      bytesAt false seenPtr seenBs ∗
      vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
      ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
      ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
      bytesAt false filePtr fileBs ∗
      vecU8Tail A.repAlloc fileCap filePtr fileBs ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      epiloguePre s0 x ∗ A.pool lim st s ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s0.trace →
      sf.fs = s.fs →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkOutAt A.repAlloc x.out .malformed ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗
        (malformedStrAddrPlaced ↦₆₄ᵣ wM0) ∗
        ((malformedStrAddrPlaced + 6#64) ↦₆₄ᵣ wM6) ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        A.pool lim (M.stepEvents (kpkMalformedEvents usedCap seenCap fileCap) st) sf ∗ F) →
      Q sf P_f) :
    SepWPp (lsProg_578 H) (s0.readReg64 .lr) s P Q Qp := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hrlay14 : RustLayoutOk 14 1 := ⟨⟨by decide, hpow1, by decide⟩, hal1⟩
  have hfit_dec := hfit
  rcases hfit_dec with ⟨⟨hwma, henf, hphys, hva⟩, -⟩
  have hshim := shim_keepsFs_lscro_of_fs (callerProg := lsProg_578 H) hFsAlloc
    (stk := extHookStack) (by decide) (by decide)
  have halloc := allocNoOomExtern_keepsFs_lscro_of_fs (callerProg := lsProg_578 H) hFsAlloc
  have hclean := @kpk_err_cleanup_2e8_placed_fd _ M A lim H hFsAlloc
  dsimp only [withLsCodeRoLoaded, Spec.keepsFs, withStack, sessionShimBudgetSpec,
    sessionShimSpec, lsProg_578] at hshim
  dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
    rustCliAllocNoOomExternSpecWithStack, rustCliAllocNoOomSpecWithStack, ↓reduceIte,
    lsProg_578] at halloc
  dsimp only [lsProg_578] at hclean
  clear hFsAlloc
  let st_al : M.σ := M.stepEvents (rustAllocEvents 14 1) st
  have hst_malformed :
      M.stepEvents (kpkErrCleanupEvents usedCap seenCap fileCap) st_al =
        M.stepEvents (kpkMalformedEvents usedCap seenCap fileCap) st := by
    simp only [st_al, kpkMalformedEvents, M.stepEvents_append]
  change SepWPp ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) s P Q Qp
  refine sepWPp_conseq hfoc ?_
  apply SepWPp.of_sepWP_ret
  apply sepWP_seq_lscro hcrl (mid := lsρ lsRustNoAllocShimSymCli)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  apply sepWP_seq_lscro hcrl1 (mid := lsρ lsRustAllocSymCli)
  rcases hcrl1 with ⟨hcl1, hro1⟩
  wp_call hshim ()
  refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  rintro ⟨hcl2, hro2⟩
  apply sepWP_seq_lscro ⟨hcl2, hro2⟩ (mid := (blkPl_578).base + 692#64)
  wp_call halloc (14, 1, st)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_al
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by tauto
  have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have hafter_adrp : ∀ (sm : State) (Q_m : SepProp),
      sm.pc = (blkPl_578).base + 712#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 0xf0#64 →
      sm.readReg64 .x29 = s0.sp - 0x60#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      sm.fs = s.fs →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x0 = sf_1.readReg64 .x0 →
      sm.readReg64 .x8 = malformedStrAddrPlaced →
      sm.readReg64 .x19 = x.fut →
      sm.readReg64 .x20 = x.out →
      sm.readReg64 .x25 = seenPtr →
      sm.readReg64 .x27 = seenCap →
      (Q_m ⊢
        memRegion (sf_1.readReg64 .x0) 14 ∗
        A.repAlloc.live (sf_1.readReg64 .x0) 14 1 ∗
        (malformedStrAddrPlaced ↦₆₄ᵣ wM0) ∗
        ((malformedStrAddrPlaced + 6#64) ↦₆₄ᵣ wM6) ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        bytesAt false usedPtr usedBs ∗
        vecU8Tail A.repAlloc usedCap usedPtr usedBs ∗
        bytesAt false seenPtr seenBs ∗
        vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        bytesAt false filePtr fileBs ∗
        vecU8Tail A.repAlloc fileCap filePtr fileBs ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        epiloguePre s0 x ∗ A.pool lim st_al sm ∗ F) →
      SepWP ((blkPC_578).rebase (blkPl_578).base H)
        (s0.readReg64 .lr) sm Q_m Q := by
    intro sm Q_m hpcm hrunm hspm hfpm hcrlm htrm hfsm hvm r0 r8 r19 r20 r25 r27 hQm
    have hsp_alm : sm.spAligned = true := spAligned_sub_f0 hsp_align hspm
    refine SepWP.weaken_pre hQm ?_
    rw [ProofLib.memRegion_split (sf_1.readReg64 .x0) 8 6 (by decide),
        ProofLib.memRegion_eight]
    simp only [sepConj_assoc, sepExists_sepConj_left]
    refine SepWP.exists_elim fun z0 => ?_
    apply sepWP_seq_lscro hcrlm (mid := (blkPl_578).base + 740#64)
    wp_steps_sync_pool ((blkPl_578).base + 740#64)
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_mid
    refine SepWP.fold (write_14_overlap_mid (sf_1.readReg64 .x0) wM0) (by sep_focus) ?_
    rw [ProofLib.memRegion_eight]
    (try simp only [sepExists_sepConj_right])
    (try simp only [sepExists_sepConj_left])
    simp only [sepConj_assoc]
    refine SepWP.exists_elim fun z6 => ?_
    apply sepWP_seq_lscro hcrl_mid (mid := (blkPl_578).base + 744#64)
    wp_steps_sync_pool ((blkPl_578).base + 744#64)
    apply bind_sepWP_state_mark; intro st_2e8; apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_2e8
    refine SepWP.fold (write_14_overlap_done (sf_1.readReg64 .x0) wM0 wM6) (by sep_focus) ?_
    have hlen14 : ((unpack64 wM0).take 6 ++ unpack64 wM6).length = 14 := by
      simp [unpack64_length]
    have hspe1 : (0x8000000000000001#64 : BitVec 64) = speWord 1 := by decide
    refine hclean x st_al s0 st_2e8 1 (sf_1.readReg64 .x0) ((unpack64 wM0).take 6 ++ unpack64 wM6)
      (sm.readReg64 .x28) (st_2e8.readReg64 .x23) usedCap usedPtr usedBs seenCap seenPtr seenBs fileCap filePtr fileBs _
      ((malformedStrAddrPlaced ↦₆₄ᵣ wM0) ∗
        ((malformedStrAddrPlaced + 6#64) ↦₆₄ᵣ wM6) ∗ F)
      (by rw [hlen14]; decide)
      (by rw [hlen14]; decide)
      hoom
      hu_len hu_lt hu_ptr hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      hsp_align
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      hcrl_2e8
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; rw [← hspe1]; kpk_norm)
      (by dsimp only [st_2e8]; rw [hlen14]; kpk_norm)
      rfl
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      (by dsimp only [st_2e8]; kpk_norm)
      (by rw [hlen14]; unfold epiloguePre; kpk_sep_focus)
      fun sf_e P_e htr_e hfs_e hsp_e hcs_e hPe =>
        hk sf_e P_e
          (htr_e.trans ((by dsimp only [st_2e8]; kpk_norm : st_2e8.trace = sm.trace).trans htrm))
          (hfs_e.trans ((by dsimp only [st_2e8]; kpk_norm : st_2e8.fs = sm.fs).trans hfsm))
          hsp_e hcs_e
          (Entails.trans hPe (by rw [hst_malformed]; dsimp [kpkMarkOutAt]; sep_focus))
  apply sepWP_seq_lscro hcrl_al (mid := (blkPl_578).base + 712#64)
  wp_steps_sync_pool ((blkPl_578).base + 712#64)
  apply bind_sepWP_state_mark; intro st_adrp; apply SepWP.done (by kpk_norm) (by kpk_norm)
  intro hcrl_adrp
  have hm_addr : (blkPl_578).ρ "libsignal_cli:.rodata..Lanon.67" = malformedStrAddrPlaced := rfl
  exact hafter_adrp st_adrp _
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    hcrl_adrp
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; rw [← hm_addr]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by dsimp only [st_adrp]; kpk_norm)
    (by rw [hsp_sf, hsp]; dsimp only [RustCliAllocBudget.repAlloc_live, Reg.x0]; unfold epiloguePre; kpk_sep_focus)

/-! ## 3. `seen ++ used` Append & `last_resort.put` Exit (`+892 .. +984` & `+1024 .. +1052`) -/

set_option maxHeartbeats 1200000 in
/-- `seen ++ used` append & `last_resort.put` exit threading `FdsGe3Closed`. -/
theorem kpk_append_37c_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {decStk getStk putStk : Nat}
    (hFsAlloc : AllocContractsFsPlaced A lim H)
    (hP : CliPanicHooksPlaced H)
    (hPut : subroutine_ok (lsProg_578 H) (lsmpl.base 542)
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (x : KpkMarkPollGhost) (st : M.σ) (s0 s : State)
    (usedCap usedPtr : BitVec 64) (usedBs : List (BitVec 8))
    (seenCap seenPtr : BitVec 64) (seenBs : List (BitVec 8))
    (fileCap filePtr : BitVec 64) (fileBs : List (BitVec 8))
    (P F : SepProp) {Q Qp : State → SepProp → Prop}
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64)
    (hlr_chg : x.kg.lastResort.changed.length < 2 ^ 32)
    (hfit_res : FitsEvents M lim st (kpkAppendReserveEvents seenCap seenBs))
    (hfit_put : FitsEnv M lim (M.stepEvents (kpkAppendPrePutEvents seenCap seenBs usedCap) st)
      (PutEnv x.kg.lastResort fileBs (seenBs ++ usedBs)))
    (hu_eq : usedBs.length = 37)
    (hu_len : usedBs.length ≤ usedCap.toNat) (hu_lt : usedCap.toNat < 2 ^ 63)
    (_hu_ptr : usedPtr ≠ 0#64)
    (hseen32 : seenBs.length < 2 ^ 32)
    (hs_len : seenBs.length ≤ seenCap.toNat) (hs_lt : seenCap.toNat < 2 ^ 63)
    (hs_ptr : seenPtr ≠ 0#64)
    (hf_len : fileBs.length ≤ fileCap.toNat) (hf_lt : fileCap.toNat < 2 ^ 63)
    (hf_ptr : filePtr ≠ 0#64)
    (hpc : s.pc = (blkPl_578).base + 892#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (htr : s.trace = s0.trace)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 seenBs.length)
    (hx24 : s.readReg64 .x24 = usedPtr)
    (hx26 : s.readReg64 .x26 = x.self)
    (hx27 : s.readReg64 .x27 = seenCap)
    (hx28 : s.readReg64 .x28 = 37#64)
    (hfoc : P ⊢
      ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 fileBs.length) ∗
      ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
      ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
      ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
      ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗
      ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
      ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
      memRegion (s0.sp - 0xb0#64) 48 ∗
      ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
      ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
      bytesAt false usedPtr usedBs ∗
      vecU8Tail A.repAlloc usedCap usedPtr usedBs ∗
      bytesAt false seenPtr seenBs ∗
      vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
      bytesAt false filePtr fileBs ∗
      vecU8Tail A.repAlloc fileCap filePtr fileBs ∗
      dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
      stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
      epiloguePre s0 x ∗ A.pool lim st s ∗ F)
    (hk : ∀ (sf : State) (evs_put : List AllocEvent) (P_f : SepProp),
      sf.trace = s0.trace →
      FdsGe3Closed sf.fs →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      PutEnv x.kg.lastResort fileBs (seenBs ++ usedBs) evs_put →
      (P_f ⊢ kpkMarkOutAt A.repAlloc x.out .ok ∗
        dirAt A.repAlloc (x.self + 0x28#64) (x.kg.lastResort.put fileBs (seenBs ++ usedBs)) ∗
        ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 fileBs.length) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗
        A.pool lim (M.stepEvents (kpkAppendPrePutEvents seenCap seenBs usedCap ++ evs_put) st) sf ∗
        F) →
      Q sf P_f) :
    SepWPp (lsProg_578 H) (s0.readReg64 .lr) s P Q Qp := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hres_le : doReserveStackX ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hext_le : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  have hres := kpkReserve_at_keepsFs_caller_placed_ok (callerProg := lsProg_578 H)
    hFsAlloc hP (le_refl doReserveStackX)
  have hmc := session_memcpy_region_keepsFs_lscro_of_fs (callerProg := lsProg_578 H) hFsAlloc
    (stk := extHookStack) (by decide) (by decide)
  have hdealloc := dealloc_keepsFs_lscro_of_fs (callerProg := lsProg_578 H) hFsAlloc
  have hput_ep := @kpk_put_and_epilogue_b8_placed_fd _ M A lim H PutEnv decStk getStk putStk hPut
  dsimp only [withLsCodeRoLoaded, Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec,
    sessionMemcpyRegionSpec, lsProg_578] at hmc
  dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustDeallocExternSpecWithStack,
    rustCliDeallocBudgetExternSpecWithStack, lsProg_578] at hdealloc
  dsimp only [lsProg_578] at hres hput_ep
  clear hFsAlloc hP hPut
  let st_res : M.σ := M.stepEvents (kpkAppendReserveEvents seenCap seenBs) st
  let st_pre : M.σ := M.stepEvents (kpkAppendPrePutEvents seenCap seenBs usedCap) st
  have hst_pre_eq : M.stepEvents (optDeallocBufEvents usedCap) st_res = st_pre := by
    simp only [st_res, st_pre, kpkAppendPrePutEvents, M.stepEvents_append]
  change SepWPp ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) s P Q Qp
  refine sepWPp_conseq hfoc ?_
  have hjoin : ∀ (sj : State) (curCap curPtr : BitVec 64) (Q_j : SepProp),
      seenBs.length + 37 ≤ curCap.toNat →
      curCap.toNat < 2 ^ 63 →
      curPtr ≠ 0#64 →
      sj.pc = (blkPl_578).base + 912#64 →
      sj.status = .Running →
      sj.sp = s0.sp - 0xf0#64 →
      sj.readReg64 .x29 = s0.sp - 0x60#64 →
      sj.trace = s0.trace →
      LibsignalCodeRoLoaded lsmpl sj.mem →
      FdsGe3Closed sj.fs →
      calleeSavedVRegs sj = calleeSavedVRegs s0 →
      sj.readReg64 .x8 = curPtr →
      sj.readReg64 .x19 = x.fut →
      sj.readReg64 .x20 = x.out →
      sj.readReg64 .x21 = usedCap →
      sj.readReg64 .x22 = BitVec.ofNat 64 seenBs.length →
      sj.readReg64 .x24 = usedPtr →
      sj.readReg64 .x26 = x.self →
      sj.readReg64 .x28 = 37#64 →
      (Q_j ⊢
        ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 fileBs.length) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ curCap) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ curPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        bytesAt false usedPtr usedBs ∗
        vecU8Tail A.repAlloc usedCap usedPtr usedBs ∗
        A.repAlloc.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ seenBs) ∗
        memRegion (curPtr + BitVec.ofNat 64 seenBs.length) (curCap.toNat - seenBs.length) ∗
        bytesAt false filePtr fileBs ∗
        vecU8Tail A.repAlloc fileCap filePtr fileBs ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        epiloguePre s0 x ∗ A.pool lim st_res sj ∗ F) →
      SepWPp ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) sj Q_j Q Qp := by
    intro sj curCap curPtr Q_j hcur_ge hcur_lt hcur_ptr hpc_j hrun_j hsp_j hfp_j htr_j hcrl_j
      hfds_j hv_j j8 j19 j20 j21 j22 j24 j26 j28 hQj
    have hcur_ne0 : curCap ≠ 0#64 :=
      fun h0 => by have : curCap.toNat = 0 := by subst h0; rfl
                   omega
    have hsp_alj : sj.spAligned = true := spAligned_sub_f0 hsp_align hsp_j
    refine sepWPp_conseq hQj ?_
    rw [subStack_split s0.sp hext_le hhi]
    have hsplit37 :
        memRegion (curPtr + BitVec.ofNat 64 seenBs.length) (curCap.toNat - seenBs.length) =
        memRegion (curPtr + BitVec.ofNat 64 seenBs.length) usedBs.length ∗
          memRegion (curPtr + BitVec.ofNat 64 (seenBs ++ usedBs).length)
            (curCap.toNat - (seenBs ++ usedBs).length) := by
      have hn : curCap.toNat - seenBs.length =
          usedBs.length + (curCap.toNat - (seenBs ++ usedBs).length) := by
        rw [List.length_append, hu_eq]; omega
      rw [ProofLib.memRegion_split' (b := curPtr + BitVec.ofNat 64 seenBs.length)
            (n := usedBs.length) (k := curCap.toNat - (seenBs ++ usedBs).length)
            (b' := curPtr + BitVec.ofNat 64 (seenBs ++ usedBs).length)
            hn (by rw [List.length_append, BitVec.ofNat_add]; bv_omega) (by omega)]
    rw [hsplit37]
    have hused_bytes : bytesAt false usedPtr usedBs = (usedPtr ↦ₛ usedBs) := rfl
    rw [hused_bytes]
    have hpost_drop : ∀ (sd : State) (Q_d : SepProp),
        sd.pc = (blkPl_578).base + 956#64 →
        sd.status = .Running →
        sd.sp = s0.sp - 0xf0#64 →
        sd.trace = s0.trace →
        LibsignalCodeRoLoaded lsmpl sd.mem →
        FdsGe3Closed sd.fs →
        calleeSavedVRegs sd = calleeSavedVRegs s0 →
        sd.readReg64 .x19 = x.fut →
        sd.readReg64 .x20 = x.out →
        sd.readReg64 .x26 = x.self →
        (Q_d ⊢
          ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 fileBs.length) ∗
          ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
          ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
          vecU8 A.repAlloc (s0.sp - 0xc8#64) (seenBs ++ usedBs) ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
          ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
          bytesAt false filePtr fileBs ∗
          vecU8Tail A.repAlloc fileCap filePtr fileBs ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
          stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
          epiloguePre s0 x ∗ A.pool lim st_pre sd ∗ F) →
        SepWPp ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) sd Q_d Q Qp := by
      intro sd Q_d hpc_d hrun_d hsp_d htr_d hcrl_d hfds_d hv_d d19 d20 d26 hQd
      have hsp_ald : sd.spAligned = true := spAligned_sub_f0 hsp_align hsp_d
      refine sepWPp_conseq hQd ?_
      rw [ProofLib.memRegion_split' (b := s0.sp - 0xb0#64) (n := 24) (k := 24)
            (b' := s0.sp - 0x98#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 0xb0#64) (n := 8) (k := 16)
            (b' := s0.sp - 0xa8#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 0xa8#64) (n := 8) (k := 8)
            (b' := s0.sp - 0xa0#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
      kpk_sep_norm
      refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
        SepWPp.exists_elim fun w2 => ?_
      apply sepWPp_of_sepWP_lscro hcrl_d (mid := (blkPl_578).base + 184#64)
      wp_steps_sync_pool ((blkPl_578).base + 184#64)
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl_b8
      apply bind_sepWPp_state_mark; intro _st_b8
      have hfds_b8 : FdsGe3Closed _st_b8.fs := by
        have hfs_eq : _st_b8.fs = sd.fs := by dsimp only [_st_b8]; kpk_norm
        rwa [hfs_eq]
      refine hput_ep x st_pre s0 _ (x.self + 0x28#64) (s0.sp - 0xb0#64) (s0.sp - 0xc8#64)
        x.kg.lastResort fileBs (seenBs ++ usedBs) _
        (((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 fileBs.length) ∗
          ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
          ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
          memRegion (s0.sp - 0x98#64) 24 ∗
          ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
          ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗ F)
        hhi hlr_chg hfit_put
        (by kpk_norm)
        (by kpk_norm)
        hsp_align
        (by kpk_norm)
        (by kpk_norm)
        hcrl_b8
        hfds_b8
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by
          refine Entails.trans ?_
            (sepConj_mono_right
              (sepConj_mono_left
                (vecU8_of_bytes_tail A.repAlloc (s0.sp - 0xb0#64) (s0.sp - 0xa8#64) (s0.sp - 0xa0#64)
                  fileCap filePtr fileBs (by bv_omega) (by bv_omega) hf_len hf_lt hf_ptr)))
          unfold epiloguePre
          kpk_sep_norm
          sep_focus)
        fun sf_p evs_put P_p htr_p hfds_p hsp_p hcs_p hevs_put hPp =>
          hk sf_p evs_put P_p htr_p hfds_p hsp_p hcs_p hevs_put <| by
            have hst_tot :
                M.stepEvents evs_put st_pre =
                  M.stepEvents (kpkAppendPrePutEvents seenCap seenBs usedCap ++ evs_put) st := by
              simp only [st_pre, M.stepEvents_append]
            rw [hst_tot] at hPp
            refine Entails.trans hPp ?_
            have hm48 := slot_b0_24_24_merge s0.sp
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_left hm48))))))))
            sep_focus
    have hlen_app : BitVec.ofNat 64 seenBs.length + 37#64 =
        BitVec.ofNat 64 (seenBs ++ usedBs).length := by
      rw [List.length_append, hu_eq, BitVec.ofNat_add]
    apply sepWPp_of_sepWP_lscro hcrl_j (mid := (blkPl_578).base + 928#64)
    apply sepWP_seq_lscro hcrl_j (mid := lsρ memcpyName)
    wp_steps_sync_pool (lsρ memcpyName)
    apply SepWP.done (by kpk_norm) (by wp_norm_lhs)
    rintro ⟨hcl_mc, hro_mc⟩
    have h37 : (37#64 : BitVec 64).toNat = usedBs.length := hu_eq.symm
    rw [← hsp_j]
    wp_apply using hmc
    refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_928
    apply bind_sepWPp_state_mark; intro st_928
    have hst_928_sp : st_928.sp = s0.sp - 0xf0#64 := by dsimp only [st_928]; kpk_norm
    have hsp_al_928 : st_928.spAligned = true := spAligned_sub_f0 hsp_align hst_928_sp
    have hfds_928 : FdsGe3Closed st_928.fs := by
      have hfs_eq : st_928.fs = sj.fs := by dsimp only [st_928]; kpk_norm
      rwa [hfs_eq]
    dsimp only [st_928] at *
    by_cases hucap : usedCap = 0#64
    · subst hucap
      have hdealloc0 : M.stepEvents (optDeallocBufEvents 0#64) st_res = st_pre := by
        simpa only [optDeallocBufEvents, ↓reduceIte] using hst_pre_eq
      have hres_eq_pre : st_res = st_pre := by
        simpa only [optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil] using hst_pre_eq
      apply sepWPp_of_sepWP_lscro hcrl_928 (mid := (blkPl_578).base + 956#64)
      rw [← hused_bytes, hsp_j]
      refine SepWP.fold
        (Entails.of_eq (pointsToBytes_append curPtr seenBs usedBs).symm)
        (by sep_focus) ?_
      refine SepWP.fold (vecU8_free_zero A.repAlloc usedPtr hu_len) (by sep_focus) ?_
      wp_steps_sync_pool ((blkPl_578).base + 956#64)
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl_956
      apply bind_sepWPp_state_mark; intro _st_956
      have hfds_956 : FdsGe3Closed _st_956.fs := by
        have hfs_eq : _st_956.fs = sj.fs := by dsimp only [_st_956]; kpk_norm
        rwa [hfs_eq]
      refine hpost_drop _ _ (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
        hcrl_956 hfds_956 (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) ?_
      rw [hres_eq_pre, subStack_split s0.sp hext_le hhi]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left
            (vecU8_of_grown_p A.repAlloc (s0.sp - 0xc8#64) (s0.sp - 0xc0#64) (s0.sp - 0xb8#64)
              curCap curPtr (seenBs ++ usedBs) (by bv_omega) (by bv_omega) hcur_ne0
              (by rw [List.length_append, hu_eq]; omega) hcur_lt hcur_ptr))))))
      unfold epiloguePre
      dsimp only [RustCliAllocBudget.repAlloc_live]
      kpk_sep_norm
      sep_focus
    · obtain ⟨hu_pos, hu_pow1, hu_hi⟩ := layoutOk_u8_of_ne_zero hucap hu_lt
      have hrlay_u : RustLayoutOk usedCap.toNat 1 := ⟨⟨hu_pos, hu_pow1, hu_hi⟩, by decide⟩
      have hdealloc_ne :
          M.stepEvents (rustDeallocEvents usedCap.toNat 1) st_res = st_pre := by
        simpa only [optDeallocBufEvents, hucap, ↓reduceIte] using hst_pre_eq
      have hucap_beq : (usedCap == 0#64) = false := beq_eq_false_iff_ne.mpr hucap
      apply sepWPp_of_sepWP_lscro hcrl_928 (mid := (blkPl_578).base + 956#64)
      rw [← hused_bytes, hsp_j]
      refine SepWP.fold
        (Entails.of_eq (pointsToBytes_append curPtr seenBs usedBs).symm)
        (by sep_focus) ?_
      refine SepWP.fold (vecU8_free_ne A.repAlloc (ptr := usedPtr) hucap hu_len hu_lt) (by sep_focus) ?_
      apply sepWP_seq_lscro hcrl_928 (mid := lsρ lsRustDeallocSymCli)
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      rintro ⟨hcl_da, hro_da⟩
      wp_call hdealloc (usedPtr, usedCap.toNat, 1, st_res)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcrl_956
      apply bind_sepWPp_state_mark; intro _st_956
      have hfds_956 : FdsGe3Closed _st_956.fs := by
        have hfs_eq : _st_956.fs = sj.fs := by dsimp only [_st_956]; kpk_norm
        rwa [hfs_eq]
      refine hpost_drop _ _ (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
        hcrl_956 hfds_956 (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) ?_
      rw [hst_928_sp, hdealloc_ne, subStack_split s0.sp hext_le hhi]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left
            (vecU8_of_grown_p A.repAlloc (s0.sp - 0xc8#64) (s0.sp - 0xc0#64) (s0.sp - 0xb8#64)
              curCap curPtr (seenBs ++ usedBs) (by bv_omega) (by bv_omega) hcur_ne0
              (by rw [List.length_append, hu_eq]; omega) hcur_lt hcur_ptr))))))
      unfold epiloguePre
      dsimp only [RustCliAllocBudget.repAlloc_live]
      kpk_sep_norm
      sep_focus
  by_cases hult : (seenCap - BitVec.ofNat 64 seenBs.length).ult 37#64 = true
  · have hbound37 := reserve_seen_bound hseen32 hs_len hs_lt hult
    have hevs_res :
        doReserveEvents ⟨s0.sp - 0xc8#64, seenCap, seenPtr, seenBs, 37⟩ =
          kpkAppendReserveEvents seenCap seenBs := by
      simp only [kpkAppendReserveEvents, hult, ↓reduceIte, doReserveEvents]
    have hfit_doRes :
        FitsEvents M lim st (doReserveEvents ⟨s0.sp - 0xc8#64, seenCap, seenPtr, seenBs, 37⟩) := by
      rwa [hevs_res]
    apply sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 561)
    wp_steps_sync_pool (lsmpl.base 561)
    apply SepWP.done
      (by kpk_norm)
      (by wp_norm_lhs)
    intro hcrl_res
    apply bind_sepWPp_state_mark; intro st_call
    have hsp_res : st_call.sp = s0.sp - 0xf0#64 := by
      dsimp only [st_call]; kpk_norm
    have hfds_call : FdsGe3Closed st_call.fs := by
      have hfs_eq : st_call.fs = s.fs := by dsimp only [st_call]; kpk_norm
      rwa [hfs_eq]
    dsimp only [st_call] at *
    have hlen_seen_nat : (BitVec.ofNat 64 seenBs.length).toNat = seenBs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine kpk_call_reserve_at_placed_fd hres ⟨s0.sp - 0xc8#64, seenCap, seenPtr, seenBs, 37⟩ st
      (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - doReserveStackX) ∗
        ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 fileBs.length) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        bytesAt false usedPtr usedBs ∗
        vecU8Tail A.repAlloc usedCap usedPtr usedBs ∗
        bytesAt false filePtr fileBs ∗
        vecU8Tail A.repAlloc fileCap filePtr fileBs ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        epiloguePre s0 x ∗ F)
      (ret_pc := (blkPl_578).base + 1048#64)
      (by kpk_norm)
      (by kpk_norm)
      (spAligned_sub_f0 hsp_align hsp_res)
      (by kpk_norm)
      hcrl_res
      (by kpk_norm)
      hlen_seen_nat
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      hbound37
      hfit_doRes
      (by
        rw [hsp_res, subStack_split s0.sp hres_le hhi]
        have hv_flat := vecU8At_of_flat_p A.repAlloc (s0.sp - 0xc8#64) seenCap seenPtr seenBs hs_len hs_lt hs_ptr
        have e1 : s0.sp - 0xc8#64 + 8#64 = s0.sp - 0xc0#64 := by bv_omega
        have e2 : s0.sp - 0xc8#64 + 16#64 = s0.sp - 0xb8#64 := by bv_omega
        rw [e1, e2] at hv_flat
        refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_left hv_flat))
        unfold epiloguePre
        kpk_sep_norm
        sep_focus)
      fun sm p' hpcm hrunm hspm hcsm hcrlm hfsm htrm hp'_ne => ?_
    let newCapN := reserveCap seenCap.toNat seenBs.length 37
    have hnew_lt : newCapN < 2 ^ 63 := by dsimp [newCapN] at *; omega
    have hnew_pos : 0 < newCapN := by dsimp [newCapN, reserveCap]; omega
    have hnew_bv_ne : BitVec.ofNat 64 newCapN ≠ 0#64 := by
      intro h0
      have ht := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      change newCapN = 0 at ht; omega
    have hnew_toNat : (BitVec.ofNat 64 newCapN).toNat = newCapN := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hst_res_eq :
        M.stepEvents (doReserveEvents ⟨s0.sp - 0xc8#64, seenCap, seenPtr, seenBs, 37⟩) st = st_res := by
      rw [hevs_res]
    rw [hst_res_eq, vecU8At_unpack_pos_p A.repAlloc (s0.sp - 0xc8#64) (BitVec.ofNat 64 newCapN) p' seenBs hnew_bv_ne]
    kpk_sep_norm
    refine SepWPp.pure_elim fun _ => ?_
    have e1 : s0.sp - 0xc8#64 + 8#64 = s0.sp - 0xc0#64 := by bv_omega
    have e2 : s0.sp - 0xc8#64 + 16#64 = s0.sp - 0xb8#64 := by bv_omega
    rw [e1, e2]
    have hsm_sp : sm.sp = s0.sp - 0xf0#64 := hspm.trans hsp_res
    have hsm_al : sm.spAligned = true := spAligned_sub_f0 hsp_align hsm_sp
    have hfdsm : FdsGe3Closed sm.fs := by rwa [hfsm]
    apply sepWPp_of_sepWP_lscro hcrlm (mid := (blkPl_578).base + 912#64)
    wp_steps_sync_pool ((blkPl_578).base + 912#64)
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_912
    apply bind_sepWPp_state_mark; intro _st_912
    have hfds_912 : FdsGe3Closed _st_912.fs := by
      have hfs_eq : _st_912.fs = sm.fs := by dsimp only [_st_912]; kpk_norm
      rwa [hfs_eq]
    refine hjoin _ (BitVec.ofNat 64 newCapN) p' _
      (by rw [hnew_toNat]; dsimp [newCapN, reserveCap]; omega)
      (by rw [hnew_toNat]; exact hnew_lt)
      hp'_ne
      (by kpk_norm)
      (by kpk_norm)
      (by dsimp only [_st_912]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_sp)))
      (by dsimp only [_st_912]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcsm)]; kpk_norm))
      (by dsimp only [_st_912]; conv_lhs => simp only [wp_norm, arm64_norm, *])
      hcrl_912
      hfds_912
      (by dsimp only [_st_912]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm)]; kpk_norm))
      (by kpk_norm)
      (by dsimp only [_st_912]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm)]; kpk_norm))
      (by dsimp only [_st_912]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm)]; kpk_norm))
      (by dsimp only [_st_912]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x21 hcsm)]; kpk_norm))
      (by kpk_norm)
      (by dsimp only [_st_912]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x24 hcsm)]; kpk_norm))
      (by dsimp only [_st_912]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcsm)]; kpk_norm))
      (by dsimp only [_st_912]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcsm)]; kpk_norm))
      (by
        rw [hsp_res, subStack_split s0.sp hres_le hhi]
        unfold epiloguePre
        kpk_sep_norm
        sep_focus)
  · have hult_f : (seenCap - BitVec.ofNat 64 seenBs.length).ult 37#64 = false :=
      Bool.eq_false_iff.mpr hult
    have hst_res_fast : st = st_res := by
      simp only [st_res, kpkAppendReserveEvents, hult_f, Bool.false_eq_true, ↓reduceIte, M.stepEvents_nil]
    have hfast_ge := fast_seen_cap_ge hseen32 hs_len hult_f
    have hs_ne0 : seenCap ≠ 0#64 :=
      fun h0 => by have : seenCap.toNat = 0 := by subst h0; rfl
                   omega
    have hseen_live : ∀ R : SepProp,
        bytesAt false seenPtr seenBs ∗ (vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗ R) =
        A.repAlloc.live seenPtr seenCap.toNat 1 ∗ ((seenPtr ↦ₛ seenBs) ∗
          (memRegion (seenPtr + BitVec.ofNat 64 seenBs.length) (seenCap.toNat - seenBs.length) ∗ R)) := by
      intro R
      unfold bytesAt vecU8Tail
      simp only [Bool.false_eq_true, hs_ne0, ite_false]
      sep_ac_rfl
    rw [hseen_live]
    apply sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_578).base + 912#64)
    wp_steps_sync_pool ((blkPl_578).base + 912#64)
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_912
    apply bind_sepWPp_state_mark; intro _st_912f
    have hfds_912f : FdsGe3Closed _st_912f.fs := by
      have hfs_eq : _st_912f.fs = s.fs := by dsimp only [_st_912f]; kpk_norm
      rwa [hfs_eq]
    exact hjoin _ seenCap seenPtr _
      hfast_ge hs_lt hs_ptr
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      hcrl_912
      hfds_912f
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by rw [hst_res_fast]; unfold epiloguePre; kpk_sep_focus)

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudgetFd
