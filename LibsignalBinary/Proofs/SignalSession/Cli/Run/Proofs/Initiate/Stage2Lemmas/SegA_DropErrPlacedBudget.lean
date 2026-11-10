/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA_DropErrPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SpeSplit
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Stage 2 `get_identity_key_pair` Future Teardown and Error Branch

Verifies `segA_drop_and_dealloc_placed` and `segA_step4_err_placed` on `initProgPlaced` over
`RustCliAllocBudget M` and `VmPreserved`, advancing the cost-model state by `rustDeallocEvents 16 8`.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA_DropErrPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
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
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate hiding InitPanicPostPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas hiding initPanicPostPlaced_of_false
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget RustLayoutOk
   VmPreserved rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitPanicPostPlaced initPanicPostPlaced_of_false)

private theorem sepWPp_of_sepWP_fs_vm {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hFs : TraceFsSound prog)
    (h : SepWP prog mid s P
      (fun sm Pm =>
        VmPreserved s sm ∧
          (sm.trace = s.trace ∧
            (VmPreserved s sm → s.mem.KeepsFrozen sm.mem → sm.fs.files = s.fs.files →
              SepWPp prog ret sm Pm Q Qp oom)))) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvmp, htr, hcont⟩ | ⟨_, hfalse⟩⟩
  · have hfiles : sm.fs.files = s.fs.files :=
      hFs.files_eq hsteps (evs := []) (by simpa using htr) NoFsEv.nil
    obtain ⟨sf, hsteps', hout⟩ := hcont hvmp hsteps.keepsFrozen hfiles R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

private theorem sepWP_done_tpidr {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0) (hpost : Q s P) :
    SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  SepWP.done hpc hrun ⟨htp, hpost⟩

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

set_option maxHeartbeats 1200000 in
/-- Budget-threaded optional future drop and `__rust_dealloc(box, 16, 8)` (`+1380 → +1412`, `0x0584`). -/
theorem segA_drop_and_dealloc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W] {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {box : BitVec 64}
    {v22 v26 v27 v25 v28 v24 v21 : BitVec 64}
    {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} {F : SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFutDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
      (withLsCodeRoLoaded lsmpl futDropBudgetSpec))
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiatePlaced s0 s 0x0564)
    (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = lsmpl.base 547)
    (hx20 : s.readReg64 (.gpr 20#5) = box)
    (hx23 : s.readReg64 (.gpr 23#5) = lsρ idKeyPairFutVtSym)
    (hx22 : s.readReg64 (.gpr 22#5) = v22)
    (hx26 : s.readReg64 (.gpr 26#5) = v26)
    (hx27 : s.readReg64 (.gpr 27#5) = v27)
    (hx25 : s.readReg64 (.gpr 25#5) = v25)
    (hx28 : s.readReg64 (.gpr 28#5) = v28)
    (hx24 : s.readReg64 (.gpr 24#5) = v24)
    (hx21 : s.readReg64 (.gpr 21#5) = v21)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sf : State,
      InInitiatePlaced s0 sf 0x0584 →
      sf.trace = s0.trace →
      sf.readReg64 (.gpr 22#5) = v22 →
      sf.readReg64 (.gpr 26#5) = v26 →
      sf.readReg64 (.gpr 27#5) = v27 →
      sf.readReg64 (.gpr 25#5) = v25 →
      sf.readReg64 (.gpr 28#5) = v28 →
      sf.readReg64 (.gpr 24#5) = v24 →
      sf.readReg64 (.gpr 21#5) = v21 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf
        (A.pool lim (M.stepEvents (rustDeallocEvents 16 8) st) sf ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (A.pool lim st s ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp oom := by
  suffices h0570 : ∀ sd : State,
      InInitiatePlaced s0 sd 0x0570 →
      sd.trace = s0.trace →
      sd.sp = s.sp →
      sd.readReg64 (.gpr 20#5) = box →
      sd.readReg64 (.gpr 23#5) = lsρ idKeyPairFutVtSym →
      sd.readReg64 (.gpr 22#5) = v22 →
      sd.readReg64 (.gpr 26#5) = v26 →
      sd.readReg64 (.gpr 27#5) = v27 →
      sd.readReg64 (.gpr 25#5) = v25 →
      sd.readReg64 (.gpr 28#5) = v28 →
      sd.readReg64 (.gpr 24#5) = v24 →
      sd.readReg64 (.gpr 21#5) = v21 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sd
        (A.pool lim st sd ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp oom by
    by_cases hz : lsmpl.base 547 = 0#64
    · apply sepWPp_of_sepWP_fs (traceFsSound_initPlaced mmpl gh W) (mid := (blkPl_521).base + 1392#64)
      · have hpc0 : s.pc = (blkPl_521).base + 1380#64 := hctrl.pc
        have hrun0 : s.status = .Running := hctrl.run
        have hx8z : s.readReg64 .x8 = 0#64 := hx8.trans hz
        clear hx8 hz
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc0 ⊢
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
        refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
        have hbase : (blkPl_521).base = lsmpl.base 521 := rfl
        have hpool1 : A.pool lim st (s.setPC ((blkPl_521).base + 1392#64)) = A.pool lim st s := by
          simp only [arm64_norm]
        rw [← hpool1]
        exact h0570 _
          (inInitiatePlaced_of_step hctrl (by simp only [initPcPlaced, initEntryPlaced, hpc0, hbase, arm64_norm]; try bv_omega)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1)
          (by simpa only [arm64_norm] using htrace)
          (by simp only [arm64_norm])
          (by simp only [arm64_norm, hx20])
          (by simp only [arm64_norm, hx23])
          (by simp only [arm64_norm, hx22])
          (by simp only [arm64_norm, hx26])
          (by simp only [arm64_norm, hx27])
          (by simp only [arm64_norm, hx25])
          (by simp only [arm64_norm, hx28])
          (by simp only [arm64_norm, hx24])
          (by simp only [arm64_norm, hx21])
    · apply sepWPp_of_sepWP_fs (traceFsSound_initPlaced mmpl gh W)
        (mid := lsmpl.base 547)
      · generalize hdrop : lsmpl.base 547 = dropAddr at hx8 hz ⊢
        have hz_beq : (dropAddr == 0#64) = false := beq_false_of_ne hz
        have hz_dec : decide (dropAddr = 0#64) = false := decide_eq_false hz
        have hpc0 : s.pc = (blkPl_521).base + 1380#64 := hctrl.pc
        have hrun0 : s.status = .Running := hctrl.run
        have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
        have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc0 ⊢
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
        refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
        have hbase : (blkPl_521).base = lsmpl.base 521 := rfl
        refine sepWPp_call_cli_lscro (traceFsSound_initPlaced mmpl gh W)
          hFutDrop
          (x := ())
          (F := A.pool lim st s ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
            stackAt s.sp (stk - cliInitiateFrame) ∗ F)
          (ret_pc := initPcPlaced 0x0570)
          (by simp only [arm64_norm, hx8, hdrop])
          (by simp only [arm64_norm, *])
          (by simpa only [arm64_norm] using hsp_al)
          (hctrl.inv.of_keepsFrozen hkf1)
          (by simp only [arm64_norm, initPcPlaced, initEntryPlaced, hpc0, hbase]; try bv_omega)
          (by dsimp only [futDropBudgetSpec]; rw [emp_sepConj]; exact Entails.refl _)
          (fun sf => hpanic sf _ (initPanicPostPlaced_of_false A lim InitEnv S x st0 stk _))
          (fun _ _ => rfl)
          (fun _ => by dsimp only [futDropBudgetSpec]; exact Entails.pure_left False.elim)
          fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 _hsym2 hf2 => ?_
        dsimp only [futDropBudgetSpec]
        simp only [arm64_norm, sepConj_assoc] at hsp2 ⊢
        apply sepWPp_pure_left; rintro ⟨htr2, hvm2⟩
        have hpool2 : A.pool lim st s2 = A.pool lim st s :=
          (A.pool_transport lim st _ s2 hvm2).trans (by simp only [arm64_norm])
        rw [← hpool2]
        have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
        have hctrl2 : InInitiatePlaced s0 s2 0x0570 :=
          inInitiatePlaced_after_call hctrl
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm])
            (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
            hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 (hf2 htr2)
        rcases hcs2 with
          ⟨_, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, _⟩
        simp only [arm64_norm, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28]
          at hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
        exact h0570 s2 hctrl2 htr2_eq hsp2 hx20_2 hx23_2 hx22_2 hx26_2 hx27_2 hx25_2 hx28_2
          hx24_2 hx21_2

  intro sd hctrld htrd hspd hx20d hx23d hx22d hx26d hx27d hx25d hx28d hx24d hx21d
  have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
  apply sepWPp_with_rodata (fun _ => rodata_idKeyPairFutSize_placed hctrld.inv)
  apply sepWPp_with_rodata (fun _ => rodata_idKeyPairFutAlign_placed hctrld.inv)
  rw [stackAt_sub_split_need s.sp (extHookStack_le_sub hstk) (sub_frame_le_64 hstk64)]
  apply sepWPp_weaken_pre (P' :=
    ((lsρ idKeyPairFutVtSym + 0x10#64) ↦₆₄ᵣ 8#64) ∗
      ((lsρ idKeyPairFutVtSym + 8#64) ↦₆₄ᵣ 16#64) ∗
      A.pool lim st sd ∗ A.live box 16 8 ∗ memRegion box 16 ∗
      stackAt s.sp extHookStack ∗
      memRegion (s.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
        (stk - cliInitiateFrame - extHookStack) ∗ F) (by
    have hboxMr := idOwnFutBox_entails_mr16 box x.stores 1#8
    simp only [sepConj_assoc]
    refine entails_by_focus (by sep_frame) hboxMr ?_
    sep_frame)
  apply sepWPp_of_sepWP_fs (traceFsSound_initPlaced mmpl gh W)
    (mid := lsρ lsRustDeallocSymCli)
  · have hpcd : sd.pc = (blkPl_521).base + 1392#64 := hctrld.pc
    have hrund : sd.status = .Running := hctrld.run
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpcd ⊢
    wp_steps
    try simp only [sepConj_assoc]
    apply sepWP_drop_left
    apply sepWP_drop_left
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
    have hbase : (blkPl_521).base = lsmpl.base 521 := rfl
    refine sepWPp_call_cli_lscro (traceFsSound_initPlaced mmpl gh W)
      (transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hAlloc.dealloc)
      (x := (box, 16, 8, st))
      (F := memRegion (s.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
        (stk - cliInitiateFrame - extHookStack) ∗ F)
      (ret_pc := initPcPlaced 0x0584)
      (by simp only [arm64_norm, hpcd])
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm, hspd] using hsp_al)
      (hctrld.inv.of_keepsFrozen hkf1)
      (by simp only [arm64_norm, initPcPlaced, initEntryPlaced, hpcd, hbase]; try bv_omega)
      (by
        dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          rustCliDeallocBudgetExternSpecWithStack]
        try simp only [sepConj_assoc]
        refine Entails.pure_right
          ⟨by simp only [arm64_norm, hx20d],
           by simp only [arm64_norm],
           by simp only [arm64_norm],
           ⟨layoutOk_16_8, by decide⟩,
           by
             refine Eq.mp ?_
               (_root_.LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 521
                 0x0584#64 (by decide) (by decide))
             congr 1⟩ ?_
        simp only [arm64_norm, hspd, sepConj_assoc]
        sep_frame)
      (fun sf => hpanic sf _ (initPanicPostPlaced_of_false A lim InitEnv S x st0 stk _))
      (fun _ _ => rfl)
      (fun _ => by
        dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          rustCliDeallocBudgetExternSpecWithStack]
        exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 _hsym2 hf2 => ?_
    dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    simp only [arm64_norm, hspd, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_pure_left; intro htr2
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrd] using htr2
    have hctrl2 : InInitiatePlaced s0 s2 0x0584 :=
      inInitiatePlaced_after_call hctrld
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, hspd, hsp2]) hcs2 hkf2 (hf2 htr2)
    rcases hcs2 with
      ⟨_, _, hx21_2, hx22_2, _, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, _⟩
    simp only [arm64_norm, hx21d, hx22d, hx24d, hx25d, hx26d, hx27d, hx28d]
      at hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
    apply sepWPp_weaken_pre (P' :=
      A.pool lim (M.stepEvents (rustDeallocEvents 16 8) st) s2 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      (Entails.of_eq (by
        rw [stackAt_sub_split_need s.sp (extHookStack_le_sub hstk) (sub_frame_le_64 hstk64)]
        ac_rfl))
    exact hnext s2 hctrl2 htr2_eq hx22_2 hx26_2 hx27_2 hx25_2 hx28_2 hx24_2 hx21_2

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 400000 in
/-- Budget-threaded Stage 2 `get_identity_key_pair` error branch (`+1124 → +1412` on `ans = .error ()`). -/
theorem segA_step4_err_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W] {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {box : BitVec 64} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} {F : SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFutDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
      (withLsCodeRoLoaded lsmpl futDropBudgetSpec))
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiatePlaced s0 s 0x0464)
    (htrace : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 4064#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 664#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sf : State) (k : RunDrop.SpeOwned) (w0 w1 w2 w3 w4 w5 : BitVec 64)
        (R_spe : SepProp),
      InInitiatePlaced s0 sf 0x0584 →
      sf.trace = s0.trace →
      w0 ≠ 0#64 - 3#64 →
      (((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
        ((x.ret + 24#64) ↦₆₄ w3) ∗ ((x.ret + 32#64) ↦₆₄ w4) ∗ ((x.ret + 40#64) ↦₆₄ w5) ∗ R_spe) ⊢
        RunDrop.speOwnedAt A.repAlloc x.ret k) →
      sf.readReg64 (.gpr 22#5) = 1#64 →
      sf.readReg64 (.gpr 26#5) = w0 →
      sf.readReg64 (.gpr 27#5) = w1 →
      sf.readReg64 (.gpr 25#5) = w2 →
      sf.readReg64 (.gpr 28#5) = w3 →
      sf.readReg64 (.gpr 24#5) = w4 →
      sf.readReg64 (.gpr 21#5) = w5 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf
        (A.pool lim (M.stepEvents (rustDeallocEvents 16 8) st) sf ∗ R_spe ∗
          memRegion (s.sp + 120#64) 8 ∗
          memRegion (s.sp + 1472#64) 16 ∗
          memRegion (s.sp + 1864#64) 24 ∗
          memRegion (s.sp + 5632#64) 72 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (A.pool lim st s ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
        memRegion (s.sp + 120#64) 8 ∗
        ((s.sp + 1472#64) ↦₆₄ box) ∗
        ((s.sp + 1480#64) ↦₆₄ lsρ idKeyPairFutVtSym) ∗
        memRegion (s.sp + 1864#64) 24 ∗
        idKeyPairOutAt A.repAlloc (s.sp + 5632#64) (.error ()) ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp oom := by
  apply sepWPp_with_rodata (fun _ => rodata_idKeyPairFutDrop_placed hctrl.inv)
  unfold idKeyPairOutAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  apply sepWPp_exists_left; intro k
  rw [mr_split (s.sp + 1864#64) (s.sp + 1872#64) 8 16 24 rfl (by bv_omega),
      mr_split (s.sp + 1872#64) (s.sp + 1880#64) 8 8 16 rfl (by bv_omega),
      mr_split (s.sp + 1872#64) (s.sp + 1873#64) 1 7 8 rfl (by bv_omega),
      mr_split (s.sp + 1880#64) (s.sp + 1887#64) 7 1 8 rfl (by bv_omega),
      mr_split (s.sp + 5688#64) (s.sp + 5696#64) 8 8 16 rfl (by bv_omega),
      mr_split (s.sp + 5696#64) (s.sp + 5697#64) 1 7 8 rfl (by bv_omega),
      memRegion_8_eq_exists (s.sp + 120#64),
      memRegion_8_eq_exists (s.sp + 1864#64),
      memRegion_1_eq_exists (s.sp + 1872#64),
      memRegion_8_eq_exists (s.sp + 5688#64),
      memRegion_1_eq_exists (s.sp + 5696#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  apply sepWPp_exists_left; intro c96
  apply sepWPp_exists_left; intro c88
  apply sepWPp_exists_left; intro c72
  apply sepWPp_exists_left; intro c64
  apply sepWPp_exists_left; intro c120
  refine sepWPp_focus (by sep_frame) (sevenHi_of_memRegion7 (s.sp + 1880#64)) ?_
  simp only [sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply sepWPp_exists_left; intro c6
  apply sepWPp_exists_left; intro c5
  apply sepWPp_exists_left; intro c4
  apply sepWPp_exists_left; intro c3
  apply sepWPp_exists_left; intro c2
  apply sepWPp_exists_left; intro c1
  apply sepWPp_exists_left; intro c0
  refine sepWPp_focus (by sep_frame) (sevenHi_of_memRegion7 (s.sp + 5633#64)) ?_
  simp only [sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply sepWPp_exists_left; intro d6
  apply sepWPp_exists_left; intro d5
  apply sepWPp_exists_left; intro d4
  apply sepWPp_exists_left; intro d3
  apply sepWPp_exists_left; intro d2
  apply sepWPp_exists_left; intro d1
  apply sepWPp_exists_left; intro d0
  refine sepWPp_focus (by sep_frame) (speOwnedAt_split_move A.repAlloc (s.sp + 5640#64) x.ret k) ?_
  simp only [sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply sepWPp_exists_left; intro w0
  apply sepWPp_exists_left; intro w1
  apply sepWPp_exists_left; intro w2
  apply sepWPp_exists_left; intro w3
  apply sepWPp_exists_left; intro w4
  apply sepWPp_exists_left; intro w5
  apply sepWPp_exists_left; intro R_spe
  apply sepWPp_pure_left; rintro ⟨hw0_ne3, hspe_move⟩
  have hpc0 : s.pc = (blkPl_521).base + 1124#64 := hctrl.pc
  have hrun0 : s.status = .Running := hctrl.run
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true :=
    spAligned_mask_of_frame hctrl.sp hctrl.spAligned
  generalize hdrop : lsmpl.base 547 = dropAddr
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc0 ⊢
  apply sepWPp_of_sepWP_fs_vm (traceFsSound_initPlaced mmpl gh W) (mid := (blkPl_521).base + 1380#64)
  by_vm_steps (
    wp_steps
    wp_steps
    conv => arg 4; simp only [sevenHi_to_Lo_rest s.sp 5633#64 5634#64 5635#64 5636#64 5637#64 5638#64 5639#64 d0 d1 d2 d3 d4 d5 d6,
      sepConj_assoc]
    wp_steps
    conv => arg 4; simp only [sevenHi_to_Lo_rest s.sp 1880#64 1881#64 1882#64 1883#64 1884#64 1885#64 1886#64 c0 c1 c2 c3 c4 c5 c6,
      sepConj_assoc]
    wp_steps
    conv => arg 4; simp only [← sevenHi_to_Lo_rest s.sp 1880#64 1881#64 1882#64 1883#64 1884#64 1885#64 1886#64 d0 d1 d2 d3 c4 c5 c6,
      sepConj_assoc]
    wp_steps
    refine SepWP.weaken_pre (P' :=
      ((lsρ idKeyPairFutVtSym) ↦₆₄ᵣ dropAddr) ∗
        (A.pool lim st s ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗
          R_spe ∗
          memRegion (s.sp + 120#64) 8 ∗
          memRegion (s.sp + 1472#64) 16 ∗
          memRegion (s.sp + 1864#64) 24 ∗
          memRegion (s.sp + 5632#64) 72 ∗ F)) (by
      have hm120 := mr_of_u64 (s.sp + 120#64) (s.sp + 664#64)
      have hm1472 := mr_fold (s.sp + 1472#64) (s.sp + 1480#64) 8 8 16
        (mr_of_u64 _ box) (mr_of_u64 _ (lsρ idKeyPairFutVtSym)) rfl (by bv_omega)
      have hm1864 :
          ((s.sp + 1864#64) ↦₆₄ c88) ∗ (((s.sp + 1872#64) ↦₈ c96) ∗
            (memRegion (s.sp + 1873#64) 7 ∗
              ((((s.sp + 1880#64) ↦₈ d0) ∗ ((s.sp + 1881#64) ↦₈ d1) ∗
                ((s.sp + 1882#64) ↦₈ d2) ∗ ((s.sp + 1883#64) ↦₃₂ (d6 ++ d5 ++ d4 ++ d3))) ∗
                memRegion (s.sp + 1887#64) 1))) ⊢
          memRegion (s.sp + 1864#64) 24 := by
        refine mr_fold (s.sp + 1864#64) (s.sp + 1872#64) 8 16 24 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
        refine mr_fold (s.sp + 1872#64) (s.sp + 1873#64) 1 15 16 (mr_of_u8 _ _) ?_ rfl (by bv_omega)
        refine mr_fold (s.sp + 1873#64) (s.sp + 1880#64) 7 8 15 (Entails.refl _) ?_ rfl (by bv_omega)
        exact mr_fold (s.sp + 1880#64) (s.sp + 1887#64) 7 1 8
          (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
            sevenHi_entails_mr7 (s.sp + 1880#64) d0 d1 d2 (d6 ++ d5 ++ d4 ++ d3))
          (Entails.refl _) rfl (by bv_omega)
      have hm5632 :
          ((s.sp + 5632#64) ↦₈ 1#8) ∗
            ((((s.sp + 5633#64) ↦₃₂ (d3 ++ d2 ++ d1 ++ d0)) ∗ ((s.sp + 5637#64) ↦₈ d4) ∗
              ((s.sp + 5638#64) ↦₈ d5) ∗ ((s.sp + 5639#64) ↦₈ d6)) ∗
              ((((s.sp + 5640#64) ↦₆₄ w0) ∗ ((s.sp + 5648#64) ↦₆₄ w1) ∗
                ((s.sp + 5656#64) ↦₆₄ w2) ∗ ((s.sp + 5664#64) ↦₆₄ w3)) ∗
                (((s.sp + 5672#64) ↦₆₄ w4) ∗ (((s.sp + 5680#64) ↦₆₄ w5) ∗
                  (((s.sp + 5688#64) ↦₆₄ c88) ∗
                    (((s.sp + 5696#64) ↦₈ c96) ∗ memRegion (s.sp + 5697#64) 7)))))) ⊢
          memRegion (s.sp + 5632#64) 72 := by
        refine mr_fold (s.sp + 5632#64) (s.sp + 5633#64) 1 71 72 (mr_of_u8 _ _) ?_ rfl (by bv_omega)
        refine mr_fold (s.sp + 5633#64) (s.sp + 5640#64) 7 64 71
          (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
            sevenLo_entails_mr7 (s.sp + 5633#64) (d3 ++ d2 ++ d1 ++ d0) d4 d5 d6) ?_
          rfl (by bv_omega)
        refine mr_fold (s.sp + 5640#64) (s.sp + 5672#64) 32 32 64
          (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
            words4_entails_mr32 (s.sp + 5640#64) w0 w1 w2 w3) ?_
          rfl (by bv_omega)
        refine mr_fold (s.sp + 5672#64) (s.sp + 5680#64) 8 24 32 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
        refine mr_fold (s.sp + 5680#64) (s.sp + 5688#64) 8 16 24 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
        refine mr_fold (s.sp + 5688#64) (s.sp + 5696#64) 8 8 16 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
        exact mr_fold (s.sp + 5696#64) (s.sp + 5697#64) 1 7 8
          (mr_of_u8 _ _) (Entails.refl _) rfl (by bv_omega)
      simp only [hx21, sepConj_assoc] at hm120 hm1472 hm1864 hm5632 ⊢
      refine entails_by_focus (by sep_frame) hm120 ?_
      refine entails_by_focus (by sep_frame) hm1472 ?_
      refine entails_by_focus (by sep_frame) hm1864 ?_
      refine entails_by_focus (by sep_frame) hm5632 ?_
      sep_frame) ?_
    apply sepWP_drop_left
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    refine ⟨by simp only [arm64_norm], fun hvm hkf1 hfiles1 => ?_⟩
    have hbase : (blkPl_521).base = lsmpl.base 521 := rfl
    have hctrl1 : InInitiatePlaced s0 _ 0x0564 :=
      inInitiatePlaced_of_step hctrl (by simp only [initPcPlaced, initEntryPlaced, hpc0, hbase, arm64_norm]; try bv_omega)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
    refine sepWPp_weaken_pre ?_ (segA_drop_and_dealloc_placed
      (st := st) (box := box)
      (F := R_spe ∗ memRegion (s.sp + 120#64) 8 ∗ memRegion (s.sp + 1472#64) 16 ∗
        memRegion (s.sp + 1864#64) 24 ∗ memRegion (s.sp + 5632#64) 72 ∗ F)
      (v22 := 1#64) (v26 := w0) (v27 := w1) (v25 := w2)
      (v28 := w3) (v24 := w4) (v21 := w5) hAlloc hFutDrop hstk hstk64 hctrl1
      (by simpa only [arm64_norm] using htrace)
      (by simp only [arm64_norm, hdrop])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      hpanic
      fun sf hctrlf htrf hx22f hx26f hx27f hx25f hx28f hx24f hx21f => ?_)
    · rw [A.pool_of_vmPreserved hvm]
      simp only [arm64_norm, sepConj_assoc]
      sep_frame
    · refine sepWPp_weaken_pre ?_
        (hnext sf k w0 w1 w2 w3 w4 w5 R_spe hctrlf htrf hw0_ne3 hspe_move hx22f hx26f hx27f hx25f
          hx28f hx24f hx21f)
      try simp only [arm64_norm, sepConj_assoc]
      sep_frame)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA_DropErrPlacedBudget
end
