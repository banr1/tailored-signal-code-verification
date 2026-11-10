/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegC_CloneSameAcct
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.HelpersPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Stage 2 `pqspkB` Clone and `is_same_account` Check (`0x0650 → 0x068c`)

Verifies `segC_step2_clone_placed` and `segC_step3_sameAcct_placed` on `initProgPlaced` under
`[LibsignalPlacement]`.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm ↓, local wp_norm ↓]
  CliStage2Norm.sp_setPC_pre CliStage2Norm.sp_setMem_setPC_pre CliStage2Norm.sp_writeVReg128_pre
  CliStage2Norm.fs_setPC_pre CliStage2Norm.fs_setMem_pre CliStage2Norm.fs_setPState_pre
  CliStage2Norm.fs_writeReg64_pre CliStage2Norm.fs_writeReg32_pre CliStage2Norm.fs_writeReg_pre
  CliStage2Norm.fs_writeVReg128_pre
  CliStage2Norm.trace_writeVReg128_pre CliStage2Norm.trace_writeReg32_pre
  CliStage2Norm.trace_writeReg_pre
  CliStage2Norm.readReg64_setPC_pre CliStage2Norm.readReg64_setMem_setPC_pre
  CliStage2Norm.readReg64_writeVReg128_pre
  CliStage2Norm.readReg32_setPC_pre CliStage2Norm.readReg32_setMem_setPC_pre
  CliStage2Norm.readReg32_writeVReg128_pre
  CliStage2Norm.readReg_setPC_pre CliStage2Norm.readReg_setMem_setPC_pre
  CliStage2Norm.readReg_writeVReg128_pre
  CliStage2Norm.readVReg128_setPC_pre CliStage2Norm.readVReg128_setMem_setPC_pre
  CliStage2Norm.readVReg128_setMem_pre CliStage2Norm.readVReg128_setPState_pre
  CliStage2Norm.readVReg128_writeReg64_pre CliStage2Norm.readVReg128_writeReg32_pre
  CliStage2Norm.readVReg128_writeReg_pre
  CliStage2Norm.extractLsb_append_lo CliStage2Norm.extractLsb_append_hi
  CliStage2Norm.extractLsb_pack32_0 CliStage2Norm.extractLsb_pack32_8
  CliStage2Norm.extractLsb_pack32_16 CliStage2Norm.extractLsb_pack32_24
  CliStage2Norm.extractLsb_pack32_0_16 CliStage2Norm.extractLsb_pack32_16_16
  symtab_setPC_pre symtab_setMem_pre symtab_setPState_pre
  symtab_writeReg64_pre symtab_writeReg32_pre symtab_writeReg_pre symtab_writeVReg128_pre

set_option maxHeartbeats 1600000 in
/-- Relocatable Stage 2 Step C2 (`+1616 → +1664` and OOM branch `+6436..+6444`): 1568-byte `pqspkB` clone. -/
theorem segC_step2_clone_placed [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiatePlaced s0 s 0x0650)
    (htrace : s.trace = s0.trace)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (hx20 : s.readReg64 (.gpr 20#5) = x.kpkPtr)
    (hx22 : s.readReg64 (.gpr 22#5) = s.sp + 128#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hx25 : s.readReg64 (.gpr 25#5) = 1568#64)
    (hx27 : s.readReg64 (.gpr 27#5) = s.sp + 783#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sf : State) (pqspkPtr : BitVec 64),
      InInitiatePlaced s0 sf 0x0680 →
      sf.trace = s0.trace →
      pqspkPtr ≠ 0#64 →
      sf.readReg64 .x2 = x.bundleA + 120#64 →
      sf.readReg64 (.gpr 22#5) = s.sp + 128#64 →
      sf.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      sf.readReg64 (.gpr 25#5) = 1568#64 →
      sf.readReg64 (.gpr 26#5) = pqspkPtr →
      sf.readReg64 (.gpr 27#5) = s.sp + 783#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf
        (A.pool ∗ A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ x.bundle.kpk) ∗
          ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
          (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (A.pool ∗
        ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
        (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) := by
  apply sepWPp_of_sepWP_fs hh.fs
    (mid := lsρ lsRustNoAllocShimSymCli)
  · have hpc0 : s.pc = (blkPl_521).base + 1616#64 := hctrl.pc
    have hrun0 : s.status = .Running := hctrl.run
    have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
    have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc0 ⊢
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
    refine sepWPp_call_cli_lscro hh.fs
      (transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
        (hh.alloc.shim (stk - cliInitiateFrame) (extHookStack_le_sub hstk) (sub_frame_le_64 hstk64)))
      (x := ())
      (F := A.pool ∗ ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
        (x.kpkPtr ↦ₛ x.bundle.kpk) ∗ F)
      (ret_pc := initPcPlaced 0x0654)
      (by simp only [arm64_norm, hpc0]; try rfl)
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm] using hsp_al)
      (hctrl.inv.of_keepsFrozen hkf1)
      (by simp only [arm64_norm, initPcPlaced, initEntryPlaced, hpc0,
        show (blkPl_521).base = lsmpl.base 521 from rfl]; try bv_omega)
      (by
        dsimp only [withStack, sessionShimSpec]
        try simp only [arm64_norm, emp_sepConj, sepConj_assoc]
        sep_frame)
      (fun sf => hpanic sf _ (initPanicPostPlaced_of_false A S x stk _))
      (fun _ _ => rfl)
      (fun _ => by dsimp only [withStack, sessionShimSpec]; exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 _hsym2 hf2 => ?_
    dsimp only [withStack, sessionShimSpec]
    simp only [arm64_norm, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_pure_left; intro htr2
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
    have hctrl2 : InInitiatePlaced s0 s2 0x0654 :=
      inInitiatePlaced_after_call hctrl
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 (hf2 htr2)
    rcases hcs2 with ⟨_, hx20_2, _, hx22_2, hx23_2, _, hx25_2, _, hx27_2, _, _, _⟩
    simp only [arm64_norm, hx20, hx22, hx23, hx25, hx27] at hx20_2 hx22_2 hx23_2 hx25_2 hx27_2
    rw [stackAt_sub_split_need s.sp (extHookStack_le_sub hstk) (sub_frame_le_64 hstk64)]
    apply sepWPp_of_sepWP_fs hh.fs
      (mid := lsρ lsRustAllocSymCli)
    · have hpc2' : s2.pc = (blkPl_521).base + 1620#64 := hpc2
      dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc2' ⊢
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      refine ⟨by simp only [arm64_norm], fun hkf3 hfiles3 => ?_⟩
      refine sepWPp_call_cli_lscro hh.fs
        (transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hh.alloc.alloc)
        (x := (1568, 1))
        (F := memRegion (s.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
          (x.kpkPtr ↦ₛ x.bundle.kpk) ∗ F)
        (ret_pc := initPcPlaced 0x0660)
        (by simp only [arm64_norm, hpc2']; try rfl)
        (by simp only [arm64_norm, *])
        (by simpa only [arm64_norm, hsp2] using hsp_al)
        (hctrl2.inv.of_keepsFrozen hkf3)
        (by simp only [arm64_norm, initPcPlaced, initEntryPlaced, hpc2',
          show (blkPl_521).base = lsmpl.base 521 from rfl]; try bv_omega)
        (by
          dsimp only [rustAllocSpecWithStack]
          simp only [sepConj_assoc]
          refine Entails.pure_right ⟨by simp only [arm64_norm, hx25_2],
            by simp only [arm64_norm], layoutOk_1568_1⟩ ?_
          try simp only [arm64_norm, hsp2, sepConj_assoc]
          sep_frame)
        (fun sf => hpanic sf _ (initPanicPostPlaced_of_false A S x stk _))
        (fun _ _ => rfl)
        (fun _ => by dsimp only [rustAllocSpecWithStack]; exact Entails.pure_left False.elim)
        fun s4 hpc4 hrun4 hsp4 hcs4 hkf4 _hsym4 hf4 => ?_
      dsimp only [rustAllocSpecWithStack]
      simp only [arm64_norm, hsp2] at hsp4 ⊢
      obtain ⟨_, hx20_4, _, hx22_4, hx23_4, _, hx25_4, _, hx27_4, _, _, _⟩ := id hcs4
      simp only [arm64_norm, hx20_2, hx22_2, hx23_2, hx25_2, hx27_2]
        at hx20_4 hx22_4 hx23_4 hx25_4 hx27_4
      by_cases hnull : s4.readReg64 (.gpr 0#5) = 0#64
      · simp only [hnull, ↓reduceIte]
        apply sepWPp_weaken_pre (P' :=
          ⌜s4.trace = s2.trace ++ [allocFailedEvent]⌝ ∗
            (A.pool ∗ stackAt s.sp extHookStack ∗
              memRegion (s.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
                (stk - cliInitiateFrame - extHookStack) ∗
              ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
              (x.kpkPtr ↦ₛ x.bundle.kpk) ∗ F))
          (Entails.of_eq (by simp only [arm64_norm, sepConj_assoc]; try ac_rfl))
        apply sepWPp_pure_left; intro htr4
        have hfail4 : allocFailedIn s0 s4 := by
          rw [allocFailedIn, htr4, htr2_eq]
          simp
        apply sepWPp_of_sepWP_fs hh.fs
          (mid := lsρ lsRawVecHandleErrorSym)
        · have hpc4' : s4.pc = (blkPl_521).base + 1632#64 := hpc4
          dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc4' ⊢
          wp_steps
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
          refine ⟨by simp only [arm64_norm], fun _ _ => ?_⟩
          apply sepWPp_panic_handleError_placed
            (by simp only [arm64_norm, hpc4']; try rfl)
            (by simp only [arm64_norm, *])
          apply hpanic
          apply initPanicPostPlaced_of_panicked A S x stk
          simpa only [allocFailedIn, arm64_norm] using hfail4
      · set pqspkPtr := s4.readReg64 (.gpr 0#5)
        have hnull0 : pqspkPtr ≠ 0 := hnull
        simp only [hnull0, ↓reduceIte]
        apply sepWPp_weaken_pre (P' :=
          ⌜pqspkPtr.toNat % 1 = 0 ∧ s4.trace = s2.trace⌝ ∗
            (A.pool ∗ A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
              (memRegion (s.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
                (stk - cliInitiateFrame - extHookStack) ∗ stackAt s.sp extHookStack) ∗
              ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
              (x.kpkPtr ↦ₛ x.bundle.kpk) ∗ F))
          (Entails.of_eq (by simp only [arm64_norm, sepConj_assoc]; try ac_rfl))
        apply sepWPp_pure_left; rintro ⟨_, htr4⟩
        rw [← stackAt_sub_split_need s.sp (extHookStack_le_sub hstk) (sub_frame_le_64 hstk64)]
        have htr4_eq : s4.trace = s0.trace := by simpa only [arm64_norm, htr2_eq] using htr4
        have hctrl4 : InInitiatePlaced s0 s4 0x0660 :=
          inInitiatePlaced_after_call hctrl2
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm])
            (by simp only [calleeSavedVRegs, arm64_norm]) hkf3 hfiles3
            hpc4 hrun4 (by simp only [arm64_norm, *]) hcs4 hkf4 (hf4 htr4)
        have hnull_beq : (pqspkPtr == 0#64) = false := beq_false_of_ne hnull
        have hnull_dec : decide (pqspkPtr = 0#64) = false := decide_eq_false hnull
        apply sepWPp_of_sepWP_fs hh.fs
          (mid := lsρ memcpyName)
        · have hpc4' : s4.pc = (blkPl_521).base + 1632#64 := hpc4
          dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc4' ⊢
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
          refine ⟨by simp only [arm64_norm], fun hkf5 hfiles5 => ?_⟩
          refine sepWPp_call_cli_lscro hh.fs
            (transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
              (hh.alloc.session_memcpy_region (stk - cliInitiateFrame)
                (extHookStack_le_sub hstk) (sub_frame_le_64 hstk64)))
            (x := (pqspkPtr, x.kpkPtr, x.bundle.kpk))
            (F := A.pool ∗ A.live pqspkPtr 1568 1 ∗
              ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗ F)
            (ret_pc := initPcPlaced 0x0674)
            (by simp only [arm64_norm, hpc4']; try rfl)
            (by simp only [arm64_norm, *])
            (by simpa only [arm64_norm, hsp4] using hsp_al)
            (hctrl4.inv.of_keepsFrozen hkf5)
            (by simp only [arm64_norm, initPcPlaced, initEntryPlaced, hpc4',
              show (blkPl_521).base = lsmpl.base 521 from rfl]; try bv_omega)
            (by
              dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
              simp only [hkpkLen, sepConj_assoc]
              refine Entails.pure_right ⟨by simp only [arm64_norm]; try rfl,
                by simp only [arm64_norm, hx20_4], by simp only [arm64_norm, hx25_4]⟩ ?_
              try simp only [arm64_norm, hsp4, sepConj_assoc]
              sep_frame)
            (fun sf => hpanic sf _ (initPanicPostPlaced_of_false A S x stk _))
            (fun _ _ => rfl)
            (fun _ => by
              dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
              exact Entails.pure_left False.elim)
            fun s6 hpc6 hrun6 hsp6 hcs6 hkf6 _hsym6 hf6 => ?_
          dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
          simp only [arm64_norm, hsp4, sepConj_assoc] at hsp6 ⊢
          apply sepWPp_pure_left; rintro ⟨_, htr6⟩
          have htr6_eq : s6.trace = s0.trace := by simpa only [arm64_norm, htr4_eq] using htr6
          have hctrl6 : InInitiatePlaced s0 s6 0x0674 :=
            inInitiatePlaced_after_call hctrl4
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
              (by simp only [arm64_norm])
              (by simp only [calleeSavedVRegs, arm64_norm]) hkf5 hfiles5
              hpc6 hrun6 (by simp only [arm64_norm, *]) hcs6 hkf6 (hf6 htr6)
          rcases hcs6 with ⟨_, _, _, hx22_6, hx23_6, _, hx25_6, hx26_6, hx27_6, _, _, _⟩
          simp only [arm64_norm, hx22_4, hx23_4, hx25_4, hx27_4]
            at hx22_6 hx23_6 hx25_6 hx26_6 hx27_6
          apply sepWPp_of_sepWP_fs hh.fs
            (mid := (blkPl_521).base + 1664#64)
          · have hpc6' : s6.pc = (blkPl_521).base + 1652#64 := hpc6
            dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc6' ⊢
            wp_steps
            apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
            refine ⟨by simp only [arm64_norm], fun hkf7 hfiles7 => ?_⟩
            have hctrl7 : InInitiatePlaced s0 _ 0x0680 :=
              inInitiatePlaced_of_step hctrl6 (by simp only [initPcPlaced, initEntryPlaced, hpc6',
                show (blkPl_521).base = lsmpl.base 521 from rfl, arm64_norm]; try bv_omega)
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hsp6])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [calleeSavedVRegs, arm64_norm]) hkf7 hfiles7
            refine sepWPp_weaken_pre ?_
              (hnext _ pqspkPtr hctrl7
                (by simpa only [arm64_norm] using htr6_eq)
                hnull
                (by simp only [arm64_norm])
                (by simp only [arm64_norm, hx22_6])
                (by simp only [arm64_norm, hx23_6])
                (by simp only [arm64_norm, hx25_6])
                (by simp only [arm64_norm, hx26_6]; try rfl)
                (by simp only [arm64_norm, hx27_6]))
            try simp only [arm64_norm, hsp6, sepConj_assoc]
            sep_frame

set_option maxHeartbeats 1200000 in
/-- Relocatable Stage 2 Step C3 (`+1664 → +1676`): `is_same_account` returning `0` via `InitOk₀.distinctAcct`. -/
theorem segC_step3_sameAcct_placed [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W] {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {kp : IdentityKeyPair} {pqspkPtr : BitVec 64}
    {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hLocal : InitLocalCalleesPlaced A mmpl gh W stk)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiatePlaced s0 s 0x0680)
    (htrace : s.trace = s0.trace)
    (hx2 : s.readReg64 .x2 = x.bundleA + 120#64)
    (hx22 : s.readReg64 (.gpr 22#5) = s.sp + 128#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hx25 : s.readReg64 (.gpr 25#5) = 1568#64)
    (hx26 : s.readReg64 (.gpr 26#5) = pqspkPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = s.sp + 783#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sf : State,
      InInitiatePlaced s0 sf 0x068c →
      sf.trace = s0.trace →
      (sf.readReg64 .x0).setWidth 32 = 0#32 →
      sf.readReg64 (.gpr 22#5) = s.sp + 128#64 →
      sf.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      sf.readReg64 (.gpr 25#5) = 1568#64 →
      sf.readReg64 (.gpr 26#5) = pqspkPtr →
      sf.readReg64 (.gpr 27#5) = s.sp + 783#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf
        (initArgsAtPlaced s.sp x s0 ∗
          ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          protocolAddressAt A x.me x.meA ∗
          ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          protocolAddressAt A x.peer x.peerA ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (initArgsAtPlaced s.sp x s0 ∗
        ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        protocolAddressAt A x.me x.meA ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        protocolAddressAt A x.peer x.peerA ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) := by
  unfold initArgsAtPlaced
  rw [stackAt_sub_split_need s.sp (isSameAccountStack_le_sub hstk) (sub_frame_le_64 hstk64)]
  apply sepWPp_of_sepWP_fs (traceFsSound_initPlaced mmpl gh W)
    (mid := lsmpl.base 17)
  · have hpc0 : s.pc = (blkPl_521).base + 1664#64 := hctrl.pc
    have hrun0 : s.status = .Running := hctrl.run
    have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
    have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc0 ⊢
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
    let isaG : Pqxdh.WireEntries.IsSameAccountDistinctGhost :=
      { localIkA := s.sp + 776#64
        localIk := kp.identityKey
        locA := x.meA
        loc := x.me
        remoteIkA := x.bundleA + 120#64
        remoteIk := x.bundle.idKey
        remA := x.peerA
        rem := x.peer }
    refine sepWPp_call_cli_lscro (traceFsSound_initPlaced mmpl gh W)
      hLocal.isSameAccount
      (x := isaG)
      (F := ((s.sp + 0xd0#64) ↦₆₄ x.peerA) ∗ ((s.sp + 0xd8#64) ↦₆₄ x.meA) ∗
        ((s.sp + 0xe0#64) ↦₆₄ (x.stores + 0xf0#64)) ∗ ((s.sp + 0xe8#64) ↦₆₄ lsρ cliSessionVtSym) ∗
        ((s.sp + 0xf0#64) ↦₆₄ x.stores) ∗ ((s.sp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
        ((s.sp + 0x100#64) ↦₆₄ x.bundleA) ∗ ((s.sp + 0x108#64) ↦₆₄ 0#64) ∗
        ((s.sp + 0x110#64) ↦₃₂ 0#32) ∗ memRegion (s.sp + 0x114#64) 4 ∗
        ((s.sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
        ((s.sp + 0x120#64) ↦₆₄ (x.bundleA + 0x78#64)) ∗
        memRegion (s.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame -
            Pqxdh.WireEntries.isSameAccountDistinctStack) ∗ F)
      (ret_pc := initPcPlaced 0x068c)
      (by simp only [arm64_norm, hpc0]; try rfl)
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm] using hsp_al)
      (hctrl.inv.of_keepsFrozen hkf1)
      (by simp only [arm64_norm, initPcPlaced, initEntryPlaced, hpc0,
        show (blkPl_521).base = lsmpl.base 521 from rfl]; try bv_omega)
      (by
        dsimp only [Pqxdh.WireEntries.isSameAccountDistinctSpec, isaG]
        have hdist := distinctSid_of_not_sameServiceId hinitOk.distinctAcct
        simp only [sepConj_assoc]
        refine Entails.pure_right
          ⟨by simp only [arm64_norm, hx22]; try bv_omega,
           by simp only [arm64_norm],
           by simp only [arm64_norm, hx2],
           by simp only [arm64_norm],
           Or.inr (fun v h1 h2 => hdist v v h1 h2 rfl)⟩ ?_
        try simp only [arm64_norm, sepConj_assoc]
        sep_frame)
      (fun sf => hpanic sf _ (initPanicPostPlaced_of_false A S x stk _))
      (fun _ _ => rfl)
      (fun _ => by
        dsimp only [Pqxdh.WireEntries.isSameAccountDistinctSpec]
        exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 _hsym2 hf2 => ?_
    dsimp only [Pqxdh.WireEntries.isSameAccountDistinctSpec, isaG]
    simp only [arm64_norm, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_pure_left; rintro ⟨hw0, htr2⟩
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
    have hctrl2 : InInitiatePlaced s0 s2 0x068c :=
      inInitiatePlaced_after_call hctrl
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 (hf2 htr2)
    rcases hcs2 with ⟨_, _, _, hx22_2, hx23_2, _, hx25_2, hx26_2, hx27_2, _, _, _⟩
    simp only [arm64_norm, hx22, hx23, hx25, hx26, hx27]
      at hx22_2 hx23_2 hx25_2 hx26_2 hx27_2
    refine sepWPp_weaken_pre ?_
      (hnext s2 hctrl2 htr2_eq hw0 hx22_2 hx23_2 hx25_2 hx26_2 hx27_2)
    unfold initArgsAtPlaced
    rw [stackAt_sub_split_need s.sp (isSameAccountStack_le_sub hstk) (sub_frame_le_64 hstk64)]
    try simp only [arm64_norm, hsp2, sepConj_assoc]
    sep_frame

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
end
