/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegAPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Stage 2 (`0x0390 → 0x0760`)

Proves `initiate_stage2_placed_ok` and `stage2Placed_ok` on block `521` (`initProgPlaced`) over
`RustCliAllocBudget M`, discharging `signal_session_coins_fill` internally at residual stack
`stk - cliInitiateFrame` from `hh.allocFs`.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 200000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2PlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
  derivePublicKeyBytesSpec derivePublicKeyBytesStackSpec
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate hiding
  InitExitPostPlaced InitPanicPostPlaced stage2MemPlaced stage3MemPlaced
  RunHooksPlaced InitStoreCalleesPlaced InitLocalCalleesPlaced initiate_stage2_placed_ok
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas hiding
  initPanicPostPlaced_of_false segA_placed_ok
  segA_step1_coins_placed segA_step2_ek_placed segA_step3_poll_placed
  segA_step4_err_placed segA_step4_ok_placed segB_err_placed_ok segC_placed_ok
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents OomPreserved RustCliAllocBudget
   VmPreserved rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
  (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (derivePublicKeyBytesBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced initPanicPostPlaced_of_false
   stage2MemPlaced stage3MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (CliIdKeyPairPollEnv ExistingStoreCalleesEnvs InitStoreCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA_PrepPlacedBudget
  (segA_step2_ek_placed segA_step3_poll_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA_DropErrPlacedBudget
  (segA_step4_err_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA_Step4OkPlacedBudget
  (segA_step4_ok_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegB_ErrPlacedBudget
  (segB_err_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegC_FinishPlacedBudget
  (segC_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegAPlacedBudget
  (segA_placed_ok)

/-! ## `signal_session_coins_fill` bridge at `stk - cliInitiateFrame` -/

/-- Weakens `withLsRoCl lsmpl (CoinsFillPlacedBudget.coinsFillSpecPlacedW3 stk)` to `withLsCodeRoLoaded lsmpl (withVmPreserved ...)`. -/
theorem coinsFill_vmPreserved_of_rocl [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {stk : Nat}
    (h : subroutine_ok prog entry
      (withLsRoCl lsmpl (CoinsFillPlacedBudget.coinsFillSpecPlacedW3 stk))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (withVmPreserved (coinsFillSpecPlacedW3 stk))) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsRoCl, withLsCodeRoLoaded, withVmPreserved,
    CoinsFillPlacedBudget.coinsFillSpecPlacedW3, coinsFillSpecPlacedW3] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  rcases hq with ⟨_, ⟨htr, hfs, hvm⟩, hrest⟩
  exact ⟨hvm, ⟨htr, hfs⟩, hrest⟩

/-- Transfers `signal_session_coins_fill` (block `618`) to `initProgPlaced` at any `cliCoinsFillStackPlaced ≤ cStk ≤ 2 ^ 63`. -/
theorem coinsFill_placed_ok_at_init_vmPreserved [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (hFs : AllocContractsFsPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {cStk : Nat} (hstk : cliCoinsFillStackPlaced ≤ cStk) (hstk64 : cStk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (coinsFillSpecPlacedW3 cStk))) :=
  coinsFill_vmPreserved_of_rocl
    (CoinsFillPlacedBudget.signal_session_coins_fill_placed_ok_at_init mmpl gh W hFs hstk hstk64)

theorem coinsFillStackPlaced_le_sub {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) :
    cliCoinsFillStackPlaced ≤ stk - cliInitiateFrame :=
  Nat.le_trans (by decide : cliCoinsFillStackPlaced ≤ 516880) (stk_sub_ge_base hstk)

/-- Specializes `coinsFill_placed_ok_at_init_vmPreserved` at `stk - cliInitiateFrame`. -/
theorem coinsFill_at_init_frame_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {B : RunBudgets}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (hFs : AllocContractsFsPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved (coinsFillSpecPlacedW3 (stk - cliInitiateFrame)))) :=
  coinsFill_placed_ok_at_init_vmPreserved mmpl gh W hFs
    (coinsFillStackPlaced_le_sub hstk) (sub_frame_le_63 hstk64)

/-! ## Stage 2 composition at `stk - cliInitiateFrame` -/

private theorem sepWPp_of_sepWP_fs_vm {prog : Program} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
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
/-- Stage 2 Step A1 (`+912 → +952`) taking a `coinsFillSpecPlacedW3 (stk - cliInitiateFrame)` witness. -/
theorem segA_step1_coins_placed_at_frame [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W] {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} {F : SepProp}
    (hCoinsFrame : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved (coinsFillSpecPlacedW3 (stk - cliInitiateFrame)))))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hctrl : InInitiatePlaced s0 s 0x0390)
    (htrace : s.trace = s0.trace)
    (hx22 : s.readReg64 (.gpr 22#5) = 0#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hx25 : s.readReg64 (.gpr 25#5) = 0#64 - 1#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 8#64)
    (hx27 : s.readReg64 (.gpr 27#5) = 0#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sf : State,
      InInitiatePlaced s0 sf 0x03b8 →
      sf.trace = s0.trace →
      sf.readReg64 (.gpr 21#5) = s.sp + 664#64 →
      sf.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf
        (A.pool lim st sf ∗
          initFreshRecAt s.sp ∗
          coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          ((s.sp + 5632#64) ↦ₛ (padCoins x.coins).toList.take 32) ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (A.pool lim st s ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        memRegion (s.sp + 296#64) 32 ∗
        memRegion (s.sp + 5632#64) 32 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp oom := by
  rw [mr_32_eq_words4 (s.sp + 296#64), mr_32_eq_words4 (s.sp + 5632#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  iterate 8 (apply sepWPp_exists_left; intro _)
  have hpc0 : s.pc = (blkPl_521).base + 912#64 := hctrl.pc
  have hrun0 : s.status = .Running := hctrl.run
  have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc0 ⊢
  apply sepWPp_of_sepWP_fs_vm (traceFsSound_initPlaced mmpl gh W)
    (mid := lsmpl.base 618)
  by_vm_steps (
    wp_steps
    refine SepWP.weaken_pre (P' :=
      coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        A.pool lim st s ∗
        initFreshRecAt s.sp ∗
        memRegion (s.sp + 5632#64) 32 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F) (by
      have hm5632 := words4_entails_mr32 (s.sp + 5632#64) 0#64 0#64 0#64 0#64
      rw [initFreshRecAt_eq_fsp s.sp]
      simp only [hx22, hx26, hx27, hx25, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        at hm5632 ⊢
      refine entails_by_focus (by sep_frame) hm5632 ?_
      sep_frame) ?_
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    refine ⟨by simp only [arm64_norm], fun hvm1 hkf1 hfiles1 => ?_⟩
    let cfG : CoinsFillGhost :=
      { dst := s.sp + 5632#64, len := 32, p₀ := x.coinsP, coins := x.coins, pos := 0 }
    refine sepWPp_call_cli_lscro (traceFsSound_initPlaced mmpl gh W)
      hCoinsFrame
      (x := cfG)
      (F := A.pool lim st s ∗ initFreshRecAt s.sp ∗ F)
      (ret_pc := initPcPlaced 0x03b8)
      (by simp only [arm64_norm, hpc0]; try rfl)
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm] using hsp_al)
      (hctrl.inv.of_keepsFrozen hkf1)
      (by simp only [arm64_norm, initPcPlaced, initEntryPlaced, hpc0,
        show (blkPl_521).base = lsmpl.base 521 from rfl]; try bv_omega)
      (by
        dsimp only [withVmPreserved, coinsFillSpecPlacedW3,
          LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, cfG]
        simp only [sepConj_assoc]
        refine Entails.pure_right
          ⟨by simp only [arm64_norm]; try bv_omega,
           by simp only [arm64_norm],
           hcoinsLt, by decide⟩ ?_
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (Entails.pure_right (hctrl.inv.of_keepsFrozen hkf1) (Entails.refl _)))))
        try simp only [arm64_norm, sepConj_assoc]
        sep_frame)
      (fun sf => hpanic sf _ (initPanicPostPlaced_of_false A lim InitEnv S x st0 stk _))
      (fun _ _ => rfl)
      (fun _ => by
        dsimp only [withVmPreserved, coinsFillSpecPlacedW3]
        exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 _hsym2 hf2 => ?_
    dsimp only [withVmPreserved, coinsFillSpecPlacedW3, cfG]
    simp only [arm64_norm, Nat.zero_add, List.drop_zero, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_pure_left; rintro ⟨hvm2, htr2, _⟩
    have hpool2 : A.pool lim st s2 = A.pool lim st s :=
      A.pool_of_vmPreserved (hvm1.trans hvm2)
    rw [← hpool2]
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
    have hctrl2 : InInitiatePlaced s0 s2 0x03b8 :=
      inInitiatePlaced_after_call hctrl
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 (hf2 htr2)
    rcases hcs2 with ⟨_, _, hx21_2, _, hx23_2, _, _, _, _, _, _, _⟩
    simp only [arm64_norm, hx23] at hx21_2 hx23_2
    refine sepWPp_weaken_pre ?_
      (hnext s2 hctrl2 htr2_eq (by bv_omega) hx23_2)
    try simp only [hsp2, sepConj_assoc]
    sep_frame)

private theorem sepWPp_pure_4th {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 Rest : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3 ∗ Rest) Q Qp oom) :
    SepWPp prog ret s (P1 ∗ P2 ∗ P3 ∗ ⌜φ⌝ ∗ Rest) Q Qp oom :=
  sepWPp_weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_pure_left h)

private theorem initArgsAtPlaced_entails_mr88 [LibsignalPlacement] (fsp : BitVec 64)
    (x : InitGhost) (s0 : State) :
    initArgsAtPlaced fsp x s0 ⊢ memRegion (fsp + 0xd0#64) 88 := by
  unfold initArgsAtPlaced
  refine mr_fold (fsp + 0xd0#64) (fsp + 0xd8#64) 8 80 88 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0xd8#64) (fsp + 0xe0#64) 8 72 80 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0xe0#64) (fsp + 0xe8#64) 8 64 72 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0xe8#64) (fsp + 0xf0#64) 8 56 64 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0xf0#64) (fsp + 0xf8#64) 8 48 56 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0xf8#64) (fsp + 0x100#64) 8 40 48 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x100#64) (fsp + 0x108#64) 8 32 40 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x108#64) (fsp + 0x110#64) 8 24 32 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x110#64) (fsp + 0x114#64) 4 20 24 (mr_of_u32 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x114#64) (fsp + 0x118#64) 4 16 20 (Entails.refl _) ?_ rfl (by bv_omega)
  exact mr_fold (fsp + 0x118#64) (fsp + 0x120#64) 8 8 16
    (mr_of_u64 _ _) (mr_of_u64 _ _) rfl (by bv_omega)

private theorem stage2_err_locals_placed_fold [LibsignalPlacement] (fsp : BitVec 64)
    (x : InitGhost) (s0 : State) (ekAPk ekASk : List (BitVec 8)) (opkId : BitVec 32)
    (hekPk : ekAPk.length = 32) (hekSk : ekASk.length = 32) :
    initFreshRecAt fsp ∗
      (memRegion fsp 0x78 ∗
        memRegion (fsp + 120#64) 8 ∗
        memRegion (fsp + 0x80#64) 0x50 ∗
        initArgsAtPlaced fsp x s0 ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        ((fsp + 664#64) ↦ₛ ekAPk) ∗
        ((fsp + 696#64) ↦ₛ ekASk) ∗
        ((fsp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((fsp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
        ((fsp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((fsp + 772#64) ↦₃₂ opkId) ∗
        memRegion (fsp + 776#64) 344 ∗
        memRegion (fsp + 0x460#64) 0x158 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 1472#64) 16 ∗
        memRegion (fsp + 1864#64) 24 ∗
        memRegion (fsp + 1904#64) 32 ∗
        memRegion (fsp + 2336#64) 32 ∗
        memRegion (fsp + 2496#64) 32 ∗
        memRegion (fsp + 4064#64) 32 ∗
        memRegion (fsp + 4096#64) 32 ∗
        memRegion (fsp + 5632#64) 72 ∗
        scratch5baGaps fsp) ⊢
      memRegion fsp initLocalsSize := by
  have hmFresh : initFreshRecAt fsp ⊢ memRegion (fsp + 296#64) 32 := by
    rw [initFreshRecAt_eq_fsp fsp]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      words4_entails_mr32 (fsp + 296#64) 0#64 8#64 0#64 (0#64 - 1#64)
  have hmArgs := initArgsAtPlaced_entails_mr88 fsp x s0
  have hm4064 := mr_fold (fsp + 4064#64) (fsp + 4096#64) 32 32 64
    (Entails.refl _) (Entails.refl _) rfl (by bv_omega)
  have hm5ba :
      memRegion (fsp + 1472#64) 16 ∗
        (memRegion (fsp + 1864#64) 24 ∗
          (memRegion (fsp + 1904#64) 32 ∗
            (memRegion (fsp + 2336#64) 32 ∗
              (memRegion (fsp + 2496#64) 32 ∗
                ((memRegion (fsp + 4064#64) 32 ∗ memRegion (fsp + 4096#64) 32) ∗
                  (memRegion (fsp + 5632#64) 72 ∗ scratch5baGaps fsp)))))) ⊢
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
    rw [scratch5ba_split fsp]
    simp only [sepConj_assoc] at hm4064 ⊢
    refine entails_by_focus (by sep_frame) hm4064 ?_
    sep_frame
  refine Entails.trans (by
    have h664 := mr_of_bytes (fsp + 664#64) ekAPk 32 hekPk
    have h696 := mr_of_bytes (fsp + 696#64) ekASk 32 hekSk
    have h728 := mr_of_bytes (fsp + 728#64) x.bundle.spk.bytes.toList 32
      x.bundle.spk.bytes.property
    have h760 := mr_of_u64 (fsp + 760#64) (x.bundleA + 88#64)
    have h768 := mr_of_u32 (fsp + 768#64) (if x.bundle.opk.isSome then 1#32 else 0#32)
    have h772 := mr_of_u32 (fsp + 772#64) opkId
    have h5b8 := mr_of_u8 (fsp + 0x5b8#64) 0#8
    have h5b9 := mr_of_u8 (fsp + 0x5b9#64) 0#8
    refine (?_ : _ ⊢
      memRegion fsp 0x78 ∗ memRegion (fsp + 120#64) 8 ∗ memRegion (fsp + 0x80#64) 0x50 ∗
        memRegion (fsp + 0xd0#64) 88 ∗ memRegion (fsp + 296#64) 32 ∗
        memRegion (fsp + 0x148#64) 0x150 ∗ memRegion (fsp + 664#64) 32 ∗
        memRegion (fsp + 696#64) 32 ∗ memRegion (fsp + 728#64) 32 ∗
        memRegion (fsp + 760#64) 8 ∗ memRegion (fsp + 768#64) 4 ∗ memRegion (fsp + 772#64) 4 ∗
        memRegion (fsp + 776#64) 344 ∗ memRegion (fsp + 0x460#64) 0x158 ∗
        memRegion (fsp + 0x5b8#64) 1 ∗ memRegion (fsp + 0x5b9#64) 1 ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba))
    simp only [sepConj_assoc] at hmFresh hmArgs hm5ba h664 h696 h728 h760 h768 h772 h5b8 h5b9 ⊢
    refine entails_by_focus (by sep_frame) hmFresh ?_
    refine entails_by_focus (by sep_frame) hmArgs ?_
    refine entails_by_focus (by sep_frame) hm5ba ?_
    refine entails_by_focus (by sep_frame) h664 ?_
    refine entails_by_focus (by sep_frame) h696 ?_
    refine entails_by_focus (by sep_frame) h728 ?_
    refine entails_by_focus (by sep_frame) h760 ?_
    refine entails_by_focus (by sep_frame) h768 ?_
    refine entails_by_focus (by sep_frame) h772 ?_
    refine entails_by_focus (by sep_frame) h5b8 ?_
    refine entails_by_focus (by sep_frame) h5b9 ?_
    sep_frame) ?_
  refine mr_fold fsp (fsp + 120#64) 0x78 (initLocalsSize - 120) initLocalsSize
    (Entails.refl _) ?_ rfl rfl
  refine mr_fold (fsp + 120#64) (fsp + 0x80#64) 8 (initLocalsSize - 128) (initLocalsSize - 120)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x80#64) (fsp + 0xd0#64) 0x50 (initLocalsSize - 208) (initLocalsSize - 128)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0xd0#64) (fsp + 296#64) 88 (initLocalsSize - 296) (initLocalsSize - 208)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 296#64) (fsp + 0x148#64) 32 (initLocalsSize - 328) (initLocalsSize - 296)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x148#64) (fsp + 664#64) 0x150 (initLocalsSize - 664) (initLocalsSize - 328)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 664#64) (fsp + 696#64) 32 (initLocalsSize - 696) (initLocalsSize - 664)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 696#64) (fsp + 728#64) 32 (initLocalsSize - 728) (initLocalsSize - 696)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 728#64) (fsp + 760#64) 32 (initLocalsSize - 760) (initLocalsSize - 728)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 760#64) (fsp + 768#64) 8 (initLocalsSize - 768) (initLocalsSize - 760)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 768#64) (fsp + 772#64) 4 (initLocalsSize - 772) (initLocalsSize - 768)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 772#64) (fsp + 776#64) 4 (initLocalsSize - 776) (initLocalsSize - 772)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 776#64) (fsp + 0x460#64) 344 (initLocalsSize - 1120) (initLocalsSize - 776)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x460#64) (fsp + 0x5b8#64) 0x158 (initLocalsSize - 1464) (initLocalsSize - 1120)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x5b8#64) (fsp + 0x5b9#64) 1 (initLocalsSize - 1465) (initLocalsSize - 1464)
    (Entails.refl _) ?_ rfl (by bv_omega)
  exact mr_fold (fsp + 0x5b9#64) (fsp + 0x5ba#64) 1 (initLocalsSize - 0x5ba) (initLocalsSize - 1465)
    (Entails.refl _) (Entails.refl _) rfl (by bv_omega)

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 400000 in
/-- Parametric-`PollEnv` Stage 2 composition (`0x0390 → 0x0760` and early `Err` / OOM exits) at `stk - cliInitiateFrame`. -/
theorem segA_placed_ok_at_frame [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {PollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W] {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {stk : Nat} {s0 s2 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoinsFrame : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved (coinsFillSpecPlacedW3 (stk - cliInitiateFrame)))))
    (hDerivePub : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 200)
      (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec W.C.pubKey)))
    (hZeroize : subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsStaticSecretDropSym)
      (withVmPreserved zeroizeSecretSpec))
    (hRoKeyPairSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliIdentityVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 602) ∗ P))
    (hIdKeyPairShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 602)
      (SpecsPlacedBudget.idOwnShimSpecPlaced idKeyPairFutVtSym A lim (stk - cliInitiateFrame)))
    (hIdKeyPairPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 567)
      (SpecsPlacedBudget.idKeyPairPollSpecPlaced
        cliIo.rd cliWrOk A lim PollEnv (stk - cliInitiateFrame)))
    (hFutDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
      (withLsCodeRoLoaded lsmpl futDropBudgetSpec))
    (hSameAcct : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 17)
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved
          (Pqxdh.WireEntries.isSameAccountDistinctSpec A.repAlloc uuidTryParse))))
    (hFitsShim : FitsEnv M lim st (BoxAllocEnv 16))
    (hFitsPoll : ∀ (evs1 : List AllocEvent) (box : BitVec 64),
      BoxAllocEnv 16 evs1 → box ≠ 0#64 →
      FitsEnv M lim (M.stepEvents evs1 st)
        (PollEnv x.F
          { fut := box
            out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
            self := x.stores
            own := StoresGhost.opened.identity.own }))
    (hEnvErr : ∀ (evs1 evs2 : List AllocEvent) (box : BitVec 64),
      StoresGhost.opened.identity.keyPair cliIo.rd x.F = .error () →
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      PollEnv x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8) st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs2 : AtStage2Placed W X x be s0 s2)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hoom : ∀ (evs1 evs2 : List AllocEvent) (box : BitVec 64) (kp : IdentityKeyPair)
        (s_call sf : State) (F' : SepProp),
      StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp →
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      PollEnv x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      s_call.fs.files = s0.fs.files → s_call.trace = s0.trace →
      (⌜¬ FitsEvents M lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8) st)
            (rustAllocEvents 1568 1) ∧ OomPreserved s_call sf⌝ ∗ F' ⊢ oom sf))
    (hnext : ∀ (s3 : State) (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
        (pqspkPtr : BitVec 64) (opkId : BitVec 32)
        (evs1 evs2 : List AllocEvent) (box : BitVec 64),
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      PollEnv x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
        (stage3MemPlaced A lim
          (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8 ++ rustAllocEvents 1568 1) st)
          x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s2
      (stage2MemPlaced A lim st x stk s0 s2) Q Qp oom := by
  have hfsp : s2.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := hs2.ctrl.sp
  have hfiles0 : s0.fs.files = x.F := hs2.ctrl.files0.symm.trans hs2.files
  have hx23_s2 : s2.readReg64 (.gpr 23#5) = s2.sp + 128#64 := by
    rw [hfsp]; exact hs2.x23
  have hx25_s2 : s2.readReg64 (.gpr 25#5) = 0#64 - 1#64 := hs2.x25
  unfold stage2MemPlaced
  dsimp only
  rw [← hfsp,
      cliBundleAt_eq_body x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr,
      mr_split s2.sp (s2.sp + 120#64) 0x78 0x58 0xd0 rfl rfl,
      mr_split (s2.sp + 120#64) (s2.sp + 0x80#64) 8 0x50 0x58 rfl (by bv_omega),
      mr_split (s2.sp + 0x128#64) (s2.sp + 0x148#64) 32 0x470 0x490 rfl (by bv_omega),
      mr_split (s2.sp + 0x148#64) (s2.sp + 664#64) 0x150 0x320 0x470 rfl (by bv_omega),
      mr_split (s2.sp + 664#64) (s2.sp + 696#64) 32 0x300 0x320 rfl (by bv_omega),
      mr_split (s2.sp + 696#64) (s2.sp + 728#64) 32 0x2e0 0x300 rfl (by bv_omega),
      mr_split (s2.sp + 728#64) (s2.sp + 776#64) 48 0x2b0 0x2e0 rfl (by bv_omega),
      mr_split (s2.sp + 776#64) (s2.sp + 0x460#64) 344 0x158 0x2b0 rfl (by bv_omega),
      scratch5ba_split s2.sp,
      mr_split (s2.sp + 4064#64) (s2.sp + 4096#64) 32 32 64 rfl (by bv_omega),
      mr_split (s2.sp + 5632#64) (s2.sp + 5664#64) 32 40 72 rfl (by bv_omega)]
  have h296 : s2.sp + 0x128#64 = s2.sp + 296#64 := rfl
  rw [h296]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepWPp_exists_left; intro opkId
  apply sepWPp_pure_4th; intro hbPure
  refine' sepWPp_weaken_pre ?_
    (segA_step1_coins_placed_at_frame (st := st) hCoinsFrame hcoinsLt hs2.ctrl hs2.trace
      hs2.x22 hx23_s2 hx25_s2 hs2.x26 hs2.x27 hpanic
      fun s_a1 hctrl_a1 htr_a1 hx21_a1 hx23_a1 => ?_)
  · try simp only [sepConj_assoc]
    sep_frame
  have hsp_a1 : s_a1.sp = s2.sp := hctrl_a1.sp.trans hfsp.symm
  rw [← hsp_a1] at hx21_a1 hx23_a1 ⊢
  refine' sepWPp_weaken_pre ?_
    (segA_step2_ek_placed (st := st) hDerivePub hZeroize hctrl_a1 htr_a1 hx21_a1 hx23_a1 hpanic
      fun s_a2 ekASk ekAPk hctrl_a2 htr_a2 hekPair hx20_a2 hx21_a2 hx23_a2 => ?_)
  · try simp only [sepConj_assoc]
    sep_frame
  have hsp_a2 : s_a2.sp = s_a1.sp := hctrl_a2.sp.trans hctrl_a1.sp.symm
  rw [← hsp_a2] at hx20_a2 hx21_a2 hx23_a2 ⊢
  refine' sepWPp_weaken_pre ?_
    (segA_step3_poll_placed (st := st) (opkId := opkId)
      @hRoKeyPairSlot hIdKeyPairShim hIdKeyPairPoll hFitsShim
      (fun evs1 box hevs1 hbox_ne => by
        rw [hctrl_a2.sp]
        exact hFitsPoll evs1 box hevs1 hbox_ne)
      hinitOk hctrl_a2 htr_a2 hfiles0 hx20_a2 hx21_a2 hx23_a2 hpanic
      fun s_a3 box ans evs1 evs2 hctrl_a3 htr_a3 hbox_ne hans hevs1 hevs2 hx20_a3 hx21_a3 => ?_)
  · have hm5632 := mr_fold (s_a2.sp + 5632#64) (s_a2.sp + 5664#64) 32 40 72
      (Entails.refl _) (Entails.refl _) rfl (by bv_omega)
    try simp only [sepConj_assoc] at hm5632 ⊢
    refine entails_by_focus (by sep_frame) hm5632 ?_
    sep_frame
  have hevs2_fsp : PollEnv x.F
      { fut := box
        out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
        self := x.stores
        own := StoresGhost.opened.identity.own } evs2 := by
    simpa only [hctrl_a2.sp] using hevs2
  have hsp_a3 : s_a3.sp = s_a2.sp := hctrl_a3.sp.trans hctrl_a2.sp.symm
  rw [← hsp_a3] at hx20_a3 hx21_a3 ⊢
  cases ans with
  | error u =>
    cases u
    obtain ⟨evs_err, hEnv_err, hst_err⟩ := hEnvErr evs1 evs2 box hans.symm hbox_ne hevs1 hevs2_fsp
    refine' sepWPp_weaken_pre ?_
      (segA_step4_err_placed (st := M.stepEvents (evs1 ++ evs2) st) (box := box)
        hAlloc hFutDrop hstk hstk64 hctrl_a3 htr_a3
        hx20_a3 hx21_a3 hpanic
        fun sf k w0 w1 w2 w3 w4 w5 R_spe hctrlf htrf hw0_ne3 hspe_move
          hx22f hx26f hx27f hx25f hx28f hx24f hx21f => ?_)
    · rw [show StoreDefs.idOwnFutBoxAt = idOwnFutBoxAt from rfl,
          show StoreDefs.idKeyPairOutAt = idKeyPairOutAt from rfl]
      try simp only [sepConj_assoc]
      sep_frame
    have hfsp_a3 : s_a3.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := hctrl_a3.sp
    have hekPkLen : ekAPk.length = 32 := by rw [hekPair.2]; exact List.Vector.toList_length _
    have hekSkLen : ekASk.length = 32 := by rw [hekPair.1]; exact List.Vector.toList_length _
    have hLocals := stage2_err_locals_placed_fold (s0.sp - BitVec.ofNat 64 cliInitiateFrame)
      x s0 ekAPk ekASk opkId hekPkLen hekSkLen
    have hBundle :=
      cliBundleBody_entails x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId hbPure
    rw [← M.stepEvents_append (evs1 ++ evs2) (rustDeallocEvents 16 8) st, hst_err, hfsp_a3]
    refine' sepWPp_weaken_pre ?_
      (segB_err_placed_ok hEnv_err hS hstk hstk64 hctrlf htrf hs2.x8 hans.symm
        hx22f hx26f hx27f hx25f hx28f hx24f hx21f hw0_ne3 hspe_move hLocals hpost)
    try simp only [sepConj_assoc] at hBundle ⊢
    refine entails_by_focus (by sep_frame) hBundle ?_
    sep_frame
  | ok kp =>
    refine' sepWPp_weaken_pre ?_
      (segA_step4_ok_placed (st := M.stepEvents (evs1 ++ evs2) st) (kp := kp) (box := box)
        hAlloc hFutDrop hstk hstk64 hctrl_a3 htr_a3
        hx20_a3 hx21_a3 hpanic
        fun sf b0 b1 b2 b3 b4 b5 b6 b63 u1 u2 u3 u4 u5 u6 u7 hctrlf htrf
          hx22f hx26f hx27f hx25f hx28f hx24f hx21f hkpLo hkpHi => ?_)
    · rw [show StoreDefs.idOwnFutBoxAt = idOwnFutBoxAt from rfl,
          show StoreDefs.idKeyPairOutAt = idKeyPairOutAt from rfl]
      try simp only [sepConj_assoc]
      sep_frame
    have hsp_sf : sf.sp = s_a3.sp := hctrlf.sp.trans hctrl_a3.sp.symm
    rw [← M.stepEvents_append (evs1 ++ evs2) (rustDeallocEvents 16 8) st, ← hsp_sf]
    refine' sepWPp_weaken_pre ?_
      (segC_placed_ok (st := M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8) st)
        hAlloc hSameAcct hinitOk hstk hstk64 hs2 hctrlf htrf hans.symm hekPair hbPure
        hx22f hx26f hx27f hx25f hx28f hx24f hx21f hkpLo hkpHi hpanic
        (fun s_call sf' F' hfc htc =>
          hoom evs1 evs2 box kp s_call sf' F' hans.symm hbox_ne hevs1 hevs2_fsp hfc htc)
        (fun s3 kp' ekASk' ekAPk' pqspkPtr opkId' hs3 => by
          rw [← M.stepEvents_append (evs1 ++ evs2 ++ rustDeallocEvents 16 8)
            (rustAllocEvents 1568 1) st]
          exact hnext s3 kp' ekASk' ekAPk' pqspkPtr opkId' evs1 evs2 box hbox_ne
            hevs1 hevs2_fsp hs3))
    have hm4064 := mr_fold (sf.sp + 4064#64) (sf.sp + 4096#64) 32 32 64
      (Entails.refl _) (Entails.refl _) rfl (by bv_omega)
    try simp only [sepConj_assoc] at hm4064 ⊢
    refine entails_by_focus (by sep_frame) hm4064 ?_
    sep_frame

/-! ## Bundled Stage 2 theorems -/

/-- Budget-threaded Stage 2 (`0x0390 → 0x0760`) parameterized by `hCoins` at `cliCoinsFillStackPlaced = 4176`. -/
theorem initiate_stage2_placed_ok_of_coinsPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : CryptoVerification.LibsignalSpqrV1.Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {stk : Nat} {s0 s2 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (withVmPreserved (coinsFillSpecPlacedW3 cStk))))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFitsShim : FitsEnv M lim st (BoxAllocEnv 16))
    (hFitsPoll : ∀ (evs1 : List AllocEvent) (box : BitVec 64),
      BoxAllocEnv 16 evs1 → box ≠ 0#64 →
      FitsEnv M lim (M.stepEvents evs1 st)
        (CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
          { fut := box
            out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
            self := x.stores
            own := StoresGhost.opened.identity.own }))
    (hEnvErr : ∀ (evs1 evs2 : List AllocEvent) (box : BitVec 64),
      StoresGhost.opened.identity.keyPair cliIo.rd x.F = .error () →
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8) st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs2 : AtStage2Placed W X x be s0 s2)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hoom : ∀ (evs1 evs2 : List AllocEvent) (box : BitVec 64) (kp : IdentityKeyPair)
        (s_call sf : State) (F' : SepProp),
      StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp →
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      s_call.fs.files = s0.fs.files → s_call.trace = s0.trace →
      (⌜¬ FitsEvents M lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8) st)
            (rustAllocEvents 1568 1) ∧ OomPreserved s_call sf⌝ ∗ F' ⊢ oom sf))
    (hnext : ∀ (s3 : State) (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
        (pqspkPtr : BitVec 64) (opkId : BitVec 32)
        (evs1 evs2 : List AllocEvent) (box : BitVec 64),
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
        (stage3MemPlaced A lim
          (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8 ++ rustAllocEvents 1568 1) st)
          x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s2
      (stage2MemPlaced A lim st x stk s0 s2) Q Qp oom := by
  have : InitTraceFsSound mmpl gh W := ⟨hh.fs⟩
  exact segA_placed_ok_at_frame
    hh.alloc
    (hCoins (coinsFillStackPlaced_le_sub hstk) (sub_frame_le_63 hstk64))
    hLocal.derivePubKeyBytes
    (ls_hook_ok_of_mem (prog := initProgPlaced mmpl gh W) hh.staticDrop)
    @hStore.rodata_idVt_keyPairSlot
    hStore.idKeyPairShim
    hStore.idKeyPairPoll
    hStore.futDrop
    hLocal.isSameAccount
    hFitsShim hFitsPoll hEnvErr hS hinitOk hcoinsLt hstk hstk64 hs2 hpost hpanic hoom hnext

/-- Budget-threaded Stage 2 (`0x0390 → 0x0760` and early `Err` / OOM exits), discharging `coins_fill` internally from `hh.allocFs`. -/
theorem initiate_stage2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : CryptoVerification.LibsignalSpqrV1.Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {stk : Nat} {s0 s2 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFitsShim : FitsEnv M lim st (BoxAllocEnv 16))
    (hFitsPoll : ∀ (evs1 : List AllocEvent) (box : BitVec 64),
      BoxAllocEnv 16 evs1 → box ≠ 0#64 →
      FitsEnv M lim (M.stepEvents evs1 st)
        (CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
          { fut := box
            out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
            self := x.stores
            own := StoresGhost.opened.identity.own }))
    (hEnvErr : ∀ (evs1 evs2 : List AllocEvent) (box : BitVec 64),
      StoresGhost.opened.identity.keyPair cliIo.rd x.F = .error () →
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8) st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs2 : AtStage2Placed W X x be s0 s2)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hoom : ∀ (evs1 evs2 : List AllocEvent) (box : BitVec 64) (kp : IdentityKeyPair)
        (s_call sf : State) (F' : SepProp),
      StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp →
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      s_call.fs.files = s0.fs.files → s_call.trace = s0.trace →
      (⌜¬ FitsEvents M lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8) st)
            (rustAllocEvents 1568 1) ∧ OomPreserved s_call sf⌝ ∗ F' ⊢ oom sf))
    (hnext : ∀ (s3 : State) (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
        (pqspkPtr : BitVec 64) (opkId : BitVec 32)
        (evs1 evs2 : List AllocEvent) (box : BitVec 64),
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
        (stage3MemPlaced A lim
          (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8 ++ rustAllocEvents 1568 1) st)
          x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s2
      (stage2MemPlaced A lim st x stk s0 s2) Q Qp oom :=
  initiate_stage2_placed_ok_of_coinsPlaced
    hh
    (fun hcs hcs64 => coinsFill_placed_ok_at_init_vmPreserved mmpl gh W hh.allocFs hcs hcs64)
    hStore hLocal hFitsShim hFitsPoll hEnvErr hS hinitOk hcoinsLt hstk hstk64 hspk
    hs2 hpost hpanic hoom hnext

/-- Proposition bundling the budget-threaded Stage 2 (`0x0390 → 0x0760`) continuation contract. -/
def Stage2PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (eEnvs : ExistingStoreCalleesEnvs)
    (InitStateEnv : CryptoVerification.LibsignalSpqrV1.Params → List AllocEvent → Prop)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem) : Prop :=
  ∀ {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {stk : Nat} {s0 s2 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
    RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    (∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (withVmPreserved (coinsFillSpecPlacedW3 cStk)))) →
    InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk →
    InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk →
    FitsEnv M lim st (BoxAllocEnv 16) →
    (∀ (evs1 : List AllocEvent) (box : BitVec 64),
      BoxAllocEnv 16 evs1 → box ≠ 0#64 →
      FitsEnv M lim (M.stepEvents evs1 st)
        (CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
          { fut := box
            out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
            self := x.stores
            own := StoresGhost.opened.identity.own })) →
    (∀ (evs1 evs2 : List AllocEvent) (box : BitVec 64),
      StoresGhost.opened.identity.keyPair cliIo.rd x.F = .error () →
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8) st = M.stepEvents evs st0) →
    S.initiate = initDef X ⟨W.C, W.Q⟩ →
    InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
    x.coins.length < 2 ^ 63 →
    cliInitiateNeed B ≤ stk →
    stk ≤ 2 ^ 63 →
    stk ≤ s0.sp.toNat →
    AtStage2Placed W X x be s0 s2 →
    (∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) →
    (∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf) →
    (∀ (evs1 evs2 : List AllocEvent) (box : BitVec 64) (kp : IdentityKeyPair)
        (s_call sf : State) (F' : SepProp),
      StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp →
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      s_call.fs.files = s0.fs.files → s_call.trace = s0.trace →
      (⌜¬ FitsEvents M lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8) st)
            (rustAllocEvents 1568 1) ∧ OomPreserved s_call sf⌝ ∗ F' ⊢ oom sf)) →
    (∀ (s3 : State) (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
        (pqspkPtr : BitVec 64) (opkId : BitVec 32)
        (evs1 evs2 : List AllocEvent) (box : BitVec 64),
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
        (stage3MemPlaced A lim
          (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8 ++ rustAllocEvents 1568 1) st)
          x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom) →
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s2
      (stage2MemPlaced A lim st x stk s0 s2) Q Qp oom

/-- Unconditional proof of `Stage2PlacedOk`. -/
theorem stage2Placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (eEnvs : ExistingStoreCalleesEnvs)
    (InitStateEnv : CryptoVerification.LibsignalSpqrV1.Params → List AllocEvent → Prop)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem) :
    Stage2PlacedOk A lim eEnvs InitStateEnv InitEnv mmpl gh W X B S :=
  fun hh hCoins hStore hLocal hFitsShim hFitsPoll hEnvErr hS hinitOk hcoinsLt hstk hstk64 hspk
      hs2 hpost hpanic hoom hnext =>
    initiate_stage2_placed_ok_of_coinsPlaced hh @hCoins hStore hLocal
      hFitsShim hFitsPoll hEnvErr hS hinitOk hcoinsLt hstk hstk64 hspk
      hs2 hpost hpanic hoom hnext

/-- Compatibility wrapper accepting `hCoins` at `cliCoinsFillStack = 4128`. -/
theorem initiate_stage2_placed_ok_of_coins [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : CryptoVerification.LibsignalSpqrV1.Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {stk : Nat} {s0 s2 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (withVmPreserved (coinsFillSpecPlacedW3 cStk))))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFitsShim : FitsEnv M lim st (BoxAllocEnv 16))
    (hFitsPoll : ∀ (evs1 : List AllocEvent) (box : BitVec 64),
      BoxAllocEnv 16 evs1 → box ≠ 0#64 →
      FitsEnv M lim (M.stepEvents evs1 st)
        (CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
          { fut := box
            out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
            self := x.stores
            own := StoresGhost.opened.identity.own }))
    (hEnvErr : ∀ (evs1 evs2 : List AllocEvent) (box : BitVec 64),
      StoresGhost.opened.identity.keyPair cliIo.rd x.F = .error () →
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8) st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs2 : AtStage2Placed W X x be s0 s2)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hoom : ∀ (evs1 evs2 : List AllocEvent) (box : BitVec 64) (kp : IdentityKeyPair)
        (s_call sf : State) (F' : SepProp),
      StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp →
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      s_call.fs.files = s0.fs.files → s_call.trace = s0.trace →
      (⌜¬ FitsEvents M lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8) st)
            (rustAllocEvents 1568 1) ∧ OomPreserved s_call sf⌝ ∗ F' ⊢ oom sf))
    (hnext : ∀ (s3 : State) (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
        (pqspkPtr : BitVec 64) (opkId : BitVec 32)
        (evs1 evs2 : List AllocEvent) (box : BitVec 64),
      box ≠ 0#64 →
      BoxAllocEnv 16 evs1 →
      CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
        (stage3MemPlaced A lim
          (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8 ++ rustAllocEvents 1568 1) st)
          x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s2
      (stage2MemPlaced A lim st x stk s0 s2) Q Qp oom := by
  have : InitTraceFsSound mmpl gh W := ⟨hh.fs⟩
  exact segA_placed_ok
    hh.alloc @hCoins
    hLocal.derivePubKeyBytes
    (ls_hook_ok_of_mem (prog := initProgPlaced mmpl gh W) hh.staticDrop)
    @hStore.rodata_idVt_keyPairSlot
    hStore.idKeyPairShim
    hStore.idKeyPairPoll
    hStore.futDrop
    hLocal.isSameAccount
    hFitsShim hFitsPoll hEnvErr hS hinitOk hcoinsLt hstk hstk64 hs2 hpost hpanic hoom hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2PlacedBudget

end
