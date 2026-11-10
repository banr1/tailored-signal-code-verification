/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.MallocngBridge
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.IfaceBudgetBaseBridges
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Heap.MallocngRustBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetHelpers
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.HooksE.Common

/-!
# `(γ, tp)`-Independent `mallocng` Ghost Hooks and `f3CliGhostHooksFixed`

Constructs `(γ, tp)`-independent ghost hooks for the five Rust allocator symbols (`__rust_alloc`,
`__rust_dealloc`, `__rust_realloc`, `__rust_alloc_zeroed`, `__rust_no_alloc_shim_is_unstable_v2`),
`<String as Clone>::clone`, and `readStdin`, and packages them with `f3ReadFileFixedGhostHookFineSub`
into the 8-field `f3CliGhostHooksFixed : CliGhostHooks` bundle satisfying `∀ γ tp, HookOk`,
`CliGhostHooksFs`, `FsTHooks`, and `GhostExternReplaysS`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks

attribute [local instance] Classical.propDecidable

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.CType Arm64.Process ProofLib.SepLogic SepProp
open Arm64.Obj hiding bytesAt
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns
  ls_hook_ok_ultra_of_mem lsmpl lsρ
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles subroutine_ok_rocl_of_plain withLsRoCl
)
open CryptoVerification.RustHeap (
  RustAlloc allocHookStack vecHeader vecU8 vecU8At
)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack framelessMemcpySpec sessionMemcpyRegionSpec sessionMemcpySpec
  sessionMemsetRegionSpec sessionMemsetSpec
)
open CryptoVerification.E2E (
  cloneSrc restoreCallerRegs stepRustAlloc1 stepRustDealloc1 writeVecHeader
)
open CryptoVerification.E2E.HooksE.HooksOkAux (
  keepsFrozen_write64_of_pointsTo64 satisfies_write64_of_pointsTo64
)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli
  lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym lsWriteFileSym
  lsWriteStdoutSym readStdinResult writeFileHook writeStdoutHook
)
open CryptoVerification.SignalSession.Cli (getResultAt ioVecAt)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617 instIsLsBlockProg_617)
open CryptoVerification.SignalSession.Cli.MainHops (
  ReadStdinGhost cliExternsPlaced_writeFile cliExternsPlaced_writeStdout cliIo cliWrOk hookNoop_fs
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks CliGhostHooksFs FsTHooks IsFsC cliGhostExterns cliGhostExterns_other
  cliGhostExterns_readFile_some cliGhostExterns_readStdin_some cliGhostExterns_stringClone_some
  fsTHooks_cliExternsPlaced fsTHooks_cliGhostExterns_of_fs hookNoop_fsT
)
open VerifiedLibraries.Mallocng (
  IsPow2Align MallocngMaxAllocSize MaxAlignedAllocAlign
  alignedAllocAlignOk mallocngAddrsOfPlacement mallocngAlignedAllocOk mallocngAlignedEffSize
  mallocngStackBytes
)
open VerifiedLibraries.Mallocng.Proofs (
  copyFinish_entails copyPrep_entails isPow2Align_alignedAllocOk
  isPow2Align_dvd_16 isPow2Align_dvd_max16 isPow2Align_of_toNat_pow2
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents
  MallocngCostModelIface MallocngCostModelSound MallocngModelBlock MallocngModelEnv
  MallocngModelInitBlock MallocngModelPostEnv
  NullAllowed OomPreserved RustAllocAddrs RustCliAllocBudget RustCliAllocBudgetEntries
  RustLayoutOk VmPreserved allocMallocng_svcValid
  mallocngBudgetPoolAt mallocngLiveM mallocngModelAlignedAllocSpec mallocngModelReallocSpec
  hookOk_rustCliAllocBudget_of_base hookOk_rustCliDeallocBudget_of_base
  hookOk_rustCliReallocBudget_of_base
  mallocngRustCliAllocBudget rustAllocEvents rustCliAllocBudgetSpec rustCliAllocBudgetSpecBase
  rustCliDeallocBudgetSpec rustCliDeallocBudgetSpecBase
  rustCliReallocBudgetSpec rustCliReallocBudgetSpecBase rustDeallocEvents rustReallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  StringCloneEnv fitsEvents_stringClone_of_fitsEnv stringCloneBudgetCondSpec stringCloneBudgetSpec
  stringCloneEnv_events stringCloneEvents stringCloneNoOomSpec subroutine_ok_stringCloneNoOom_of_cond
)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events rustAllocZeroedBudgetSpec)
open LibsignalBinary.Heap.Fine (fineCostModel fineCostModelIface fineCostModelSound)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  CodeBlocksPermRX CodeBlocksPermRXMem
  allocCallPreserved_of_mallocngProcPreserved allocCallPreserved_refl allocCallPreserved_trans
  cc_retHook_setMem_sameRegs callocHookBridgeSpec fineHookRustCliAllocBudget freeHookBridgeSpec
  hook_oom_false mallocHookBridgeSpec mallocngHook mallocngHookBudgetPool
  mallocngHookBudgetPool_transport mallocngHookRustCliAllocBudget
  oomCond_to_oomPreserved_hookExit packHookPostEnv procPreserved_hookExit runPlacedAllocHook
  spAligned_sub_16 stackAt_split_frame unpackHookBudgetPool vmPreserved_restoreCallerRegs
  vmPreserved_retHook_setMem vmPreserved_writeReg64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetHelpers (
  calloc_budget_hookOk fitsEvent_of_fitsAlloc1 free_budget_hookOk malloc_budget_hookOk
  pointsTo_replicate_to_memRegion rustAllocEvents_one stepRustAlloc1_budget_cps
  stepRustDealloc1_budget_cps write_empty_vecU8 write_vecU8_from_alloc
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (
  stringCloneHookMallocng
)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (PublicApiDecHooksPlaced)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget (Stage2ContractsMinPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks CliGhostSpqrAllocHooks allocContractsFsPlaced_of_hooks
  allocContractsXCliPlaced_of_hooks codecHooksPlaced_of_hooks publicApiDecHooksPlaced_of_hooks
  stage2ContractsMinPlaced_of_hooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant StubReachesTarget
  hookOk_frame_extra keepFsTrace keepFsTrace_fs keepFsTrace_fsT keepFsTrace_ok
  linkedGhostBudget linkedGhostBudget_pool_stripS real_subroutine_run_of_stripS
  specPreservesFsTrace_alloc specPreservesFsTrace_dealloc specPreservesFsTrace_realloc
  specPreservesFsTraceExact_allocBase specPreservesFsTraceExact_deallocBase
  specPreservesFsTraceExact_reallocBase specStripSInvariant_alloc specStripSInvariant_dealloc
  specStripSInvariant_realloc stringCloneHookMallocng_fsT
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed ReadFileRuleEnvFixed
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced (
  ActiveReadStdinLinkedRun CompiledReadStdinEnv compiledReadStdinEnv_sub_bounded
  fitsEnv_compiled_of_sub keepFilesTrace keepFilesTrace_fsT keepFilesTrace_ok_readStdin
  readStdinBudgetCondSpec real_readStdin_run_of_stripS
  subroutine_ok_readStdinBudgetCondSpec_of_extHookStack writeFileHook_ok_placed
  writeStdoutHook_ok_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook (
  F3ReadFileFixedCallGuard f3ReadFileFixedGhostHookFine f3ReadFileFixedGhostHookFineSub
  f3ReadFileFixedGhostHookFine_ok_lit f3ReadFileFixedGhostHook_steps_of_call
  fineHookRustCliAllocBudget_pool_stripS
  hRead_of_f3ReadFileFixedGhostHookFine hRead_withPanics_of_f3ReadFileFixedGhostHookFine
  readFileAnyBudgetCondSpec subroutine_ok_readFileAnyBudgetCondSpec_of_extHookStack
)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced (
  MainIoOfPlaced ReadStdinBoundedEnv readStdinBoundedEnv_of_hook_gt readStdinBoundedEnv_of_hook_le
  readStdinSpecOfPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsFsPlaced AllocContractsXCliPlaced readFileSpecPlaced
)

/-! ## Placed `realloc` and `aligned_alloc` `MultiCodeROHook` Budget Bridges -/

private theorem pure_sepConj_of_true {P : Prop} {Q : SepProp} (h : P) : (⌜P⌝ ∗ Q) = Q := by
  simp [h]

private theorem ite_pos {α : Type _} {c : Prop} [Decidable c] (hc : c) {t e : α} :
    (if c then t else e) = t := by
  split
  · rfl
  · rename_i hnc
    exact False.elim (hnc hc)

private theorem ite_neg {α : Type _} {c : Prop} [Decidable c] (hnc : ¬ c) {t e : α} :
    (if c then t else e) = e := by
  split
  · rename_i hc
    exact False.elim (hnc hc)
  · rfl

def reallocHookBridgeSpec (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × Nat × Nat × List (BitVec 8) × BitVec 64 × M.σ) where
  pre := fun (p, newSize, oldSize, align, bs, sp, st) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧ s0.sp = sp ∧
      p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + oldSize < 2 ^ 64 ∧ bs.length ≤ oldSize⌝ ∗
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
      I.BlockM γ p oldSize (max align 16) ∗
      (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
      stackFrameAt sp mallocngStackBytes
  post := fun (p, newSize, oldSize, align, bs, sp, st) s0 sf =>
    let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
    let keptBs := bs.take newSize.toNat
    let st' := if ok then M.step (.realloc align oldSize newSize.toNat) st else st
    ⌜AllocCallPreserved s0 sf⌝ ∗
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st' sf ∗
      stackFrameAt sp mallocngStackBytes ∗
      (if ok then
        ⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
          (sf.readReg64 .x0).toNat + newSize.toNat < 2 ^ 64 ∧
          keptBs.length ≤ newSize.toNat⌝ ∗
          I.BlockM γ (sf.readReg64 .x0) newSize.toNat (max align 16) ∗
          (sf.readReg64 .x0 ↦ₛ keptBs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 keptBs.length)
            (newSize.toNat - keptBs.length)
       else
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          I.BlockM γ p oldSize (max align 16) ∗
          (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length))
  onOom := fun (_, newSize, oldSize, align, _, _, st) s0 sf =>
    ⌜¬ FitsEvent M lim st (.realloc align oldSize newSize.toNat) ∧ OomPreserved s0 sf⌝

theorem realloc_budget_hookOk {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) :
    HookOk (mallocngHook mpl "realloc")
      (reallocHookBridgeSpec M I γ mpl tp brkStart lim) := by
  have hEntries := hS.entries_ok mpl allocMallocng hPl allocMallocng_svcValid
  refine runPlacedAllocHook hPl (hEntries.realloc_ok γ) ?_
  rintro ⟨p, newSize, oldSize, align, bs, sp, st⟩ R s0 i hpre
  set entry := VerifiedLibraries.mallocngLib.fnAddr mpl "realloc"
  set s0' := multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0
  dsimp only [reallocHookBridgeSpec] at hpre
  have hpreEq :
      (⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧ s0.sp = sp ∧
          p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + oldSize < 2 ^ 64 ∧ bs.length ≤ oldSize⌝ ∗
        mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
        I.BlockM γ p oldSize (max align 16) ∗
        (p ↦ₛ bs) ∗
        memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
        stackFrameAt sp mallocngStackBytes) ∗ R =
      ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧ s0.sp = sp ∧
          p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + oldSize < 2 ^ 64 ∧ bs.length ≤ oldSize⌝ ∗
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
          (I.BlockM γ p oldSize (max align 16) ∗
            (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
            stackFrameAt sp mallocngStackBytes ∗ R)) := by sep_ac_rfl
  rw [hpreEq, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hsp, hpNe, hp16, hpFit, hbsLe⟩, hpre⟩ := hpre
  obtain ⟨staticIvs, ivs0, hrx0, hInv0, hIvsLen, hIvsSum, hpreEnv⟩ := unpackHookBudgetPool hS hpre
  refine ⟨(p, newSize, sp, some (oldSize, align, bs), tp, brkStart, st, ivs0), R, ?_, ?_, ?_⟩
  · dsimp only [mallocngModelReallocSpec, ToBaseSpec.toSpec, MallocngModelInitBlock]
    have hx0' : s0'.readReg64 .x0 = p := by
      simpa [s0', multiCodeROHookEntry_readReg64 _ _ _ _ _ .x0] using hx0
    have hx1' : s0'.readReg64 .x1 = newSize := by
      simpa [s0', multiCodeROHookEntry_readReg64 _ _ _ _ _ .x1] using hx1
    have hsp' : s0'.sp = sp := by simpa [s0', multiCodeROHookEntry_sp] using hsp
    have henv' :
        MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0' =
          MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0 := by
      simp [MallocngModelEnv, s0',
        multiCodeROHookEntry_tpidrEl0, multiCodeROHookEntry_brkStart, multiCodeROHookEntry_brk]
    simp only [ctype_simp, henv', sepConj_assoc]
    have h0 : s0'.readReg64 (.gpr 0#5) = p := hx0'
    have h1 : s0'.readReg64 (.gpr 1#5) = newSize := hx1'
    rw [sepConj_left_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
      pure_sepConj_of_true (by simp [h0, h1, hsp', hpNe, hp16, hbsLe]; omega)]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpreEnv
  · intro sf' _hLf hpprw' hkf' _hoom hoomSat
    dsimp only [mallocngModelReallocSpec, ToBaseSpec.toSpec] at hoomSat
    rw [satisfies_pure_sepConj] at hoomSat
    obtain ⟨hOomCond, hCodeRest⟩ := hoomSat
    have hR_exit :
        (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').mem ⊨ R := by
      have hs0_codeR : s0.mem ⊨ VerifiedLibraries.mallocngLib.codeRO mpl ∗ R := by
        have h1 : s0.mem ⊨
            MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0 ∗
              (I.BlockM γ p oldSize (max align 16) ∗
                (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
                stackFrameAt sp mallocngStackBytes) ∗
              (VerifiedLibraries.mallocngLib.codeRO mpl ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpreEnv
        exact Satisfies.of_sep_right (Satisfies.of_sep_right h1)
      have hsf_codeR :
          (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').mem ⊨
            VerifiedLibraries.mallocngLib.codeRO mpl ∗ R := by
        simpa only [multiCodeROHookExit_mem] using
          satisfies_restoreMultiCodeMem hPl hkf' hs0_codeR hCodeRest
      exact Satisfies.of_sep_right hsf_codeR
    have hOomPres := oomCond_to_oomPreserved_hookExit hOomCond
    have hNotFit : ¬ FitsEvent M lim st (.realloc align oldSize newSize.toNat) := by
      rintro ⟨hMax, hFitStep⟩
      have hok : decide (newSize.toNat ≤ MallocngMaxAllocSize) = true := decide_eq_true hMax
      simp only [hok, ↓reduceIte] at hOomCond
      exact hook_oom_false hFitStep hrx0 hInv0 hIvsLen hIvsSum hpprw' hOomCond
    dsimp only [reallocHookBridgeSpec]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hNotFit, hOomPres⟩, hR_exit⟩
  · intro sf' hLf hpprw' _hkf' _hret _hcc hpost
    dsimp only [mallocngModelReallocSpec, ToBaseSpec.toSpec] at hpost
    let sf := multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf'
    let keptBs := bs.take newSize.toNat
    have hx0_exit : sf'.readReg64 (.gpr 0#5) = sf.readReg64 .x0 :=
      (multiCodeROHookExit_readReg64 VerifiedLibraries.mallocngLib mpl i s0 sf' .x0).symm
    cases hok : decide (newSize.toNat ≤ MallocngMaxAllocSize) with
    | true =>
      have hPack := packHookPostEnv I γ mpl tp brkStart
        (st' := M.step (.realloc align oldSize newSize.toNat) st) hrx0 hInv0 hLf hpprw'
      simp only [hok, ↓reduceIte, ctype_simp, MallocngModelInitBlock,
        Option.map_some, Option.getD_some, emp_sepConj, sepConj_assoc] at hpost
      rw [← sepConj_assoc, sepConj_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
        sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨⟨_, ⟨_, hne, hal16, hfit64, hkeptLe⟩, hacc⟩, hpost⟩ := hpost
      rw [hx0_exit] at hne hal16 hfit64 hpost
      change keptBs.length ≤ newSize.toNat at hkeptLe
      have hacp : AllocCallPreserved s0 sf :=
        allocCallPreserved_of_mallocngProcPreserved (procPreserved_hookExit hacc.1)
      have hmax16 : max (max align 16) 16 = max align 16 := by omega
      rw [hmax16] at hpost
      have hpostReord : sf.mem ⊨
          (VerifiedLibraries.mallocngLib.codeRO mpl ∗
            MallocngModelPostEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart
              (M.step (.realloc align oldSize newSize.toNat) st) ivs0 s0' sf') ∗
            (I.BlockM γ (sf.readReg64 .x0) newSize.toNat (max align 16) ∗
              (sf.readReg64 .x0 ↦ₛ keptBs) ∗
              memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 keptBs.length)
                (newSize.toNat - keptBs.length) ∗
              stackFrameAt sp mallocngStackBytes ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      have hpost1 := Satisfies.mono (sepConj_mono_left hPack) hpostReord
      dsimp only [reallocHookBridgeSpec]
      simp only [hok, ↓reduceIte]
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngHookBudgetPool M I γ mpl tp brkStart lim
              (M.step (.realloc align oldSize newSize.toNat) st) sf ∗
            stackFrameAt sp mallocngStackBytes ∗
            (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + newSize.toNat < 2 ^ 64 ∧
                keptBs.length ≤ newSize.toNat⌝ ∗
              I.BlockM γ (sf.readReg64 .x0) newSize.toNat (max align 16) ∗
              (sf.readReg64 .x0 ↦ₛ keptBs) ∗
              memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 keptBs.length)
                (newSize.toNat - keptBs.length))) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + newSize.toNat < 2 ^ 64 ∧
                keptBs.length ≤ newSize.toNat⌝ ∗
              (mallocngHookBudgetPool M I γ mpl tp brkStart lim
                  (M.step (.realloc align oldSize newSize.toNat) st) sf ∗
                (I.BlockM γ (sf.readReg64 .x0) newSize.toNat (max align 16) ∗
                  (sf.readReg64 .x0 ↦ₛ keptBs) ∗
                  memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 keptBs.length)
                    (newSize.toNat - keptBs.length) ∗
                  stackFrameAt sp mallocngStackBytes ∗ R))) := by sep_ac_rfl
      rw [hGoalEq, satisfies_pure_sepConj]
      refine ⟨hacp, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hne, hal16, hfit64, hkeptLe⟩, hpost1⟩
    | false =>
      have hPack := packHookPostEnv I γ mpl tp brkStart (st' := st) hrx0 hInv0 hLf hpprw'
      simp only [hok, Bool.false_eq_true, ↓reduceIte, ctype_simp, MallocngModelInitBlock,
        sepConj_assoc] at hpost
      rw [← sepConj_assoc, sepConj_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
        sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨⟨_, _, hacc⟩, hpost⟩ := hpost
      have hacp : AllocCallPreserved s0 sf :=
        allocCallPreserved_of_mallocngProcPreserved (procPreserved_hookExit hacc.1)
      have hPullNull :
          VerifiedLibraries.mallocngLib.codeRO mpl ∗
            (I.BlockM γ p oldSize (max align 16) ∗
              ((p ↦ₛ bs) ∗
                (memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
                  (⌜sf'.readReg64 (.gpr 0#5) = 0#64⌝ ∗
                    (MallocngModelPostEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0
                        s0' sf' ∗
                      (stackFrameAt sp mallocngStackBytes ∗ R)))))) =
          ⌜sf'.readReg64 (.gpr 0#5) = 0#64⌝ ∗
            ((VerifiedLibraries.mallocngLib.codeRO mpl ∗
              MallocngModelPostEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0' sf') ∗
              (I.BlockM γ p oldSize (max align 16) ∗
                (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
                stackFrameAt sp mallocngStackBytes ∗ R)) := by sep_ac_rfl
      rw [hPullNull, satisfies_pure_sepConj] at hpost
      obtain ⟨hnull, hpost⟩ := hpost
      rw [hx0_exit] at hnull
      have hpost1 := Satisfies.mono (sepConj_mono_left hPack) hpost
      dsimp only [reallocHookBridgeSpec]
      simp only [hok, Bool.false_eq_true, ↓reduceIte]
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngHookBudgetPool M I γ mpl tp brkStart lim st sf ∗
            stackFrameAt sp mallocngStackBytes ∗
            (⌜sf.readReg64 .x0 = 0#64⌝ ∗
              I.BlockM γ p oldSize (max align 16) ∗
              (p ↦ₛ bs) ∗
              memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length))) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜sf.readReg64 .x0 = 0#64⌝ ∗
              (mallocngHookBudgetPool M I γ mpl tp brkStart lim st sf ∗
                (I.BlockM γ p oldSize (max align 16) ∗
                  (p ↦ₛ bs) ∗
                  memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
                  stackFrameAt sp mallocngStackBytes ∗ R))) := by sep_ac_rfl
      rw [hGoalEq, satisfies_pure_sepConj]
      refine ⟨hacp, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hnull, hpost1⟩

def alignedAllocHookBridgeSpec (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × M.σ) where
  pre := fun (align, len, sp, st) s0 =>
    ⌜s0.readReg64 .x0 = align ∧ s0.readReg64 .x1 = len ∧ s0.sp = sp ∧
      align.toNat ≤ MaxAlignedAllocAlign⌝ ∗
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
      stackFrameAt sp mallocngStackBytes
  post := fun (align, len, sp, st) s0 sf =>
    let ok := mallocngAlignedAllocOk align len
    let st' := if ok then M.step (.aligned align.toNat len.toNat) st else st
    ⌜AllocCallPreserved s0 sf⌝ ∗
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st' sf ∗
      stackFrameAt sp mallocngStackBytes ∗
      (if ok then
        ⌜sf.readReg64 .x0 ≠ 0#64 ∧ max align.toNat 16 ∣ (sf.readReg64 .x0).toNat ∧
          (sf.readReg64 .x0).toNat + len.toNat < 2 ^ 64⌝ ∗
          I.BlockM γ (sf.readReg64 .x0) len.toNat (max align.toNat 16) ∗
          memRegion (sf.readReg64 .x0) len.toNat
       else
        ⌜sf.readReg64 .x0 = 0#64⌝)
  onOom := fun (align, len, _, st) s0 sf =>
    ⌜¬ (alignedAllocAlignOk align = true ∧
        FitsEvent M lim st (.aligned align.toNat len.toNat)) ∧
      OomPreserved s0 sf⌝

theorem alignedAlloc_budget_hookOk {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) :
    HookOk (mallocngHook mpl "aligned_alloc")
      (alignedAllocHookBridgeSpec M I γ mpl tp brkStart lim) := by
  have hEntries := hS.entries_ok mpl allocMallocng hPl allocMallocng_svcValid
  refine runPlacedAllocHook hPl (hEntries.alignedAlloc_ok γ) ?_
  rintro ⟨align, len, sp, st⟩ R s0 i hpre
  set entry := VerifiedLibraries.mallocngLib.fnAddr mpl "aligned_alloc"
  set s0' := multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0
  dsimp only [alignedAllocHookBridgeSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hsp, halMax⟩, hpre⟩ := hpre
  obtain ⟨staticIvs, ivs0, hrx0, hInv0, hIvsLen, hIvsSum, hpreEnv⟩ := unpackHookBudgetPool hS hpre
  refine ⟨(align, len, sp, tp, brkStart, st, ivs0), R, ?_, ?_, ?_⟩
  · dsimp only [mallocngModelAlignedAllocSpec, ToBaseSpec.toSpec]
    have hx0' : s0'.readReg64 .x0 = align := by
      simpa [s0', multiCodeROHookEntry_readReg64 _ _ _ _ _ .x0] using hx0
    have hx1' : s0'.readReg64 .x1 = len := by
      simpa [s0', multiCodeROHookEntry_readReg64 _ _ _ _ _ .x1] using hx1
    have hsp' : s0'.sp = sp := by simpa [s0', multiCodeROHookEntry_sp] using hsp
    have henv' :
        MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0' =
          MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0 := by
      simp [MallocngModelEnv, s0',
        multiCodeROHookEntry_tpidrEl0, multiCodeROHookEntry_brkStart, multiCodeROHookEntry_brk]
    simp only [ctype_simp, henv', sepConj_assoc]
    have h0 : s0'.readReg64 (.gpr 0#5) = align := hx0'
    have h1 : s0'.readReg64 (.gpr 1#5) = len := hx1'
    rw [sepConj_left_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
      pure_sepConj_of_true (by simp [h0, h1, hsp', halMax])]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpreEnv
  · intro sf' _hLf hpprw' hkf' _hoom hoomSat
    dsimp only [mallocngModelAlignedAllocSpec, ToBaseSpec.toSpec] at hoomSat
    rw [satisfies_pure_sepConj] at hoomSat
    obtain ⟨hOomCond, hCodeRest⟩ := hoomSat
    have hR_exit :
        (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').mem ⊨ R := by
      have hs0_codeR : s0.mem ⊨ VerifiedLibraries.mallocngLib.codeRO mpl ∗ R := by
        have h1 : s0.mem ⊨
            MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0 ∗
              stackFrameAt sp mallocngStackBytes ∗
              (VerifiedLibraries.mallocngLib.codeRO mpl ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpreEnv
        exact Satisfies.of_sep_right (Satisfies.of_sep_right h1)
      have hsf_codeR :
          (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').mem ⊨
            VerifiedLibraries.mallocngLib.codeRO mpl ∗ R := by
        simpa only [multiCodeROHookExit_mem] using
          satisfies_restoreMultiCodeMem hPl hkf' hs0_codeR hCodeRest
      exact Satisfies.of_sep_right hsf_codeR
    have hOomPres := oomCond_to_oomPreserved_hookExit hOomCond
    have hNotFit :
        ¬ (alignedAllocAlignOk align = true ∧
            FitsEvent M lim st (.aligned align.toNat len.toNat)) := by
      rintro ⟨halOk, hMax, hFitStep⟩
      change mallocngAlignedEffSize align.toNat len.toNat ≤ MallocngMaxAllocSize at hMax
      have hok : mallocngAlignedAllocOk align len = true := by
        unfold mallocngAlignedAllocOk
        simp [halOk, decide_eq_true hMax]
      simp only [hok, ↓reduceIte] at hOomCond
      exact hook_oom_false hFitStep hrx0 hInv0 hIvsLen hIvsSum hpprw' hOomCond
    dsimp only [alignedAllocHookBridgeSpec]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hNotFit, hOomPres⟩, hR_exit⟩
  · intro sf' hLf hpprw' _hkf' _hret _hcc hpost
    dsimp only [mallocngModelAlignedAllocSpec, ToBaseSpec.toSpec] at hpost
    let sf := multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf'
    have hx0_exit : sf'.readReg64 (.gpr 0#5) = sf.readReg64 .x0 :=
      (multiCodeROHookExit_readReg64 VerifiedLibraries.mallocngLib mpl i s0 sf' .x0).symm
    cases hok : mallocngAlignedAllocOk align len with
    | true =>
      have hPack := packHookPostEnv I γ mpl tp brkStart
        (st' := M.step (.aligned align.toNat len.toNat) st) hrx0 hInv0 hLf hpprw'
      simp only [hok, ↓reduceIte, ctype_simp, MallocngModelBlock, sepConj_assoc] at hpost
      rw [← sepConj_assoc, sepConj_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
        sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨⟨⟨_, hne, hal, hfit64⟩, hacc⟩, hpost⟩ := hpost
      rw [hx0_exit] at hne hal hfit64 hpost
      have hacp : AllocCallPreserved s0 sf :=
        allocCallPreserved_of_mallocngProcPreserved (procPreserved_hookExit hacc.1)
      have hpostReord : sf.mem ⊨
          (VerifiedLibraries.mallocngLib.codeRO mpl ∗
            MallocngModelPostEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart
              (M.step (.aligned align.toNat len.toNat) st) ivs0 s0' sf') ∗
            (I.BlockM γ (sf.readReg64 .x0) len.toNat (max align.toNat 16) ∗
              memRegion (sf.readReg64 .x0) len.toNat ∗
              stackFrameAt sp mallocngStackBytes ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      have hpost1 := Satisfies.mono (sepConj_mono_left hPack) hpostReord
      dsimp only [alignedAllocHookBridgeSpec]
      simp only [hok, ↓reduceIte]
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngHookBudgetPool M I γ mpl tp brkStart lim
              (M.step (.aligned align.toNat len.toNat) st) sf ∗
            stackFrameAt sp mallocngStackBytes ∗
            (⌜sf.readReg64 .x0 ≠ 0#64 ∧ max align.toNat 16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + len.toNat < 2 ^ 64⌝ ∗
              I.BlockM γ (sf.readReg64 .x0) len.toNat (max align.toNat 16) ∗
              memRegion (sf.readReg64 .x0) len.toNat)) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜sf.readReg64 .x0 ≠ 0#64 ∧ max align.toNat 16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + len.toNat < 2 ^ 64⌝ ∗
              (mallocngHookBudgetPool M I γ mpl tp brkStart lim
                  (M.step (.aligned align.toNat len.toNat) st) sf ∗
                (I.BlockM γ (sf.readReg64 .x0) len.toNat (max align.toNat 16) ∗
                  memRegion (sf.readReg64 .x0) len.toNat ∗
                  stackFrameAt sp mallocngStackBytes ∗ R))) := by sep_ac_rfl
      rw [hGoalEq, satisfies_pure_sepConj]
      refine ⟨hacp, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hne, hal, hfit64⟩, hpost1⟩
    | false =>
      have hPack := packHookPostEnv I γ mpl tp brkStart (st' := st) hrx0 hInv0 hLf hpprw'
      simp only [hok, Bool.false_eq_true, ↓reduceIte, ctype_simp, sepConj_assoc] at hpost
      rw [← sepConj_assoc, sepConj_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
        sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨⟨_, hacc⟩, hpost⟩ := hpost
      rw [← sepConj_assoc, sepConj_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
        sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨hnull, hpost⟩ := hpost
      rw [hx0_exit] at hnull
      have hacp : AllocCallPreserved s0 sf :=
        allocCallPreserved_of_mallocngProcPreserved (procPreserved_hookExit hacc.1)
      have hpostReord : sf.mem ⊨
          (VerifiedLibraries.mallocngLib.codeRO mpl ∗
            MallocngModelPostEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0' sf') ∗
            (stackFrameAt sp mallocngStackBytes ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      have hpost1 := Satisfies.mono (sepConj_mono_left hPack) hpostReord
      dsimp only [alignedAllocHookBridgeSpec]
      simp only [hok, Bool.false_eq_true, ↓reduceIte]
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngHookBudgetPool M I γ mpl tp brkStart lim st sf ∗
            stackFrameAt sp mallocngStackBytes ∗
            ⌜sf.readReg64 .x0 = 0#64⌝) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜sf.readReg64 .x0 = 0#64⌝ ∗
              (mallocngHookBudgetPool M I γ mpl tp brkStart lim st sf ∗
                (stackFrameAt sp mallocngStackBytes ∗ R))) := by sep_ac_rfl
      rw [hGoalEq, satisfies_pure_sepConj]
      refine ⟨hacp, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hnull, hpost1⟩

/-! ## `(γ, tp)`-Independent `mallocng` Fallbacks -/

private theorem stackAt_allocHookStack_split (sp : BitVec 64) :
    stackAt sp allocHookStack =
      stackFrameAt sp mallocngStackBytes ∗ memRegion (sp - 4096#64) 3072 := by
  have hm0 : mallocngStackBytes = 1024 := rfl
  have ha0 : allocHookStack = 4096 := rfl
  rw [stackAt, ha0, stackFrameAt_eq_memRegion sp mallocngStackBytes (by omega)]
  have h1 := (SepFrameInfer.memRegion_merge (sp - 4096#64)
    (sp - BitVec.ofNat 64 mallocngStackBytes) 3072 mallocngStackBytes 4096
    (by rw [hm0]; bv_omega) (by omega) (by omega)).symm
  rw [show BitVec.ofNat 64 (4096 : Nat) = 4096#64 from rfl, h1]
  sep_ac_rfl

private theorem cc_retHook_setMem_writeX0 {s0 s : State} (m : Memory) (v : BitVec 64)
    (hregs : s.regs = s0.regs) (hvregs : s.vregs = s0.vregs) (hsp : s.sp = s0.sp)
    (hrun : s.status = .Running) :
    Returned s0 (retHook (fun st => (st.setMem m).writeReg64 .x0 v) s) ∧
      CallingConventionPreserved s0 (retHook (fun st => (st.setMem m).writeReg64 .x0 v) s) := by
  have hlr : s.readReg64 .lr = s0.readReg64 .lr := by simp [State.readReg64, hregs]
  refine ⟨⟨by simp [retHook, State.setPC, State.setMem, State.writeReg64, hlr],
    by simp [retHook, State.setPC, State.setMem, State.writeReg64, hsp],
    by simp [retHook, State.setPC, State.setMem, State.writeReg64, hrun]⟩, ?_⟩
  simp [CallingConventionPreserved, CalleeSavedPreserved,
    retHook, State.setPC, State.setMem, State.writeReg64, State.readReg64,
    RegFile.read, RegFile.write, hregs, hvregs, hsp]

private theorem vmPreserved_retHook_setMem_writeX0 {s : State} {m : Memory} (v : BitVec 64)
    (hperm : m.perm = s.mem.perm) :
    VmPreserved s (retHook (fun st => (st.setMem m).writeReg64 .x0 v) s) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, fun a => ?_, fun _ _ _ => ?_⟩
  · simp [retHook, State.setPC, State.setMem, State.writeReg64]
  · simp [retHook, State.setPC, State.setMem, State.writeReg64]
  · simp [retHook, State.setPC, State.setMem, State.writeReg64]
  · simp [retHook, State.setPC, State.setMem, State.writeReg64]
  · simp [retHook, State.setPC, State.setMem, State.writeReg64, congrFun hperm a]
  · simp [retHook, State.setPC, State.setMem, State.writeReg64]

private theorem allocCallPreserved_retHook_restore {s0 s1 : State} (m : Memory)
    (h : AllocCallPreserved s0 s1) :
    AllocCallPreserved s0 (retHook (fun st => st.setMem m) (restoreCallerRegs s0 s1)) := by
  rcases h with ⟨hfs, htr, hsig, htp, hbrkS, horc, hsym⟩
  exact ⟨hfs, htr, hsig, htp, hbrkS, horc, hsym⟩

private theorem allocCallPreserved_retHook_restore_x0 {s0 s1 : State} (m : Memory) (v : BitVec 64)
    (h : AllocCallPreserved s0 s1) :
    AllocCallPreserved s0
      (retHook (fun st => (st.setMem m).writeReg64 .x0 v) (restoreCallerRegs s0 s1)) := by
  rcases h with ⟨hfs, htr, hsig, htp, hbrkS, horc, hsym⟩
  exact ⟨by simpa [retHook, restoreCallerRegs, State.setPC, State.setMem, State.writeReg64] using hfs,
    by simpa [retHook, restoreCallerRegs, State.setPC, State.setMem, State.writeReg64] using htr,
    by simpa [retHook, restoreCallerRegs, State.setPC, State.setMem, State.writeReg64] using hsig,
    by simpa [retHook, restoreCallerRegs, State.setPC, State.setMem, State.writeReg64] using htp,
    by simpa [retHook, restoreCallerRegs, State.setPC, State.setMem, State.writeReg64] using hbrkS,
    by simpa [retHook, restoreCallerRegs, State.setPC, State.setMem, State.writeReg64] using horc,
    by simpa [retHook, restoreCallerRegs, State.setPC, State.setMem, State.writeReg64] using hsym⟩

private theorem max_pow2_eight (k : Nat) : max (2 ^ k) 8 = 2 ^ (max k 3) := by
  by_cases hk : k ≤ 3
  · have hle : 2 ^ k ≤ 8 := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> decide
    rw [Nat.max_eq_right hle, Nat.max_eq_right hk]; rfl
  · have hge : 8 ≤ 2 ^ k := by
      have h3 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [Nat.max_eq_left hge, Nat.max_eq_left (by omega)]

private theorem pow2_align_dvd_props {align : Nat} (hPow : ∃ k, align = 2 ^ k) :
    align ∣ max align 16 ∧ 16 ∣ max align 16 := by
  rcases hPow with ⟨k, rfl⟩
  by_cases hk : k ≤ 4
  · have hle : 2 ^ k ≤ 16 := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with
        rfl | rfl | rfl | rfl | rfl <;> decide
    rw [Nat.max_eq_right hle]
    refine ⟨?_, Nat.dvd_refl 16⟩
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with
      rfl | rfl | rfl | rfl | rfl <;> decide
  · have hge : 16 ≤ 2 ^ k := by
      have h4 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [Nat.max_eq_left hge]
    exact ⟨Nat.dvd_refl _, by simpa using Nat.pow_dvd_pow 2 (by omega : 4 ≤ k)⟩

private theorem effAlign_ok_props {align : Nat}
    (hPow : ∃ k, align = 2 ^ k) (hAlMax : align ≤ 2 ^ 31) :
    let eff := BitVec.ofNat 64 (max align 8)
    eff.toNat = max align 8 ∧
      eff.toNat ≤ MaxAlignedAllocAlign ∧
      alignedAllocAlignOk eff = true ∧
      max eff.toNat 16 = max align 16 := by
  intro eff
  have hMaxEq : MaxAlignedAllocAlign = 2 ^ 31 := rfl
  have heffNat : eff.toNat = max align 8 := by
    dsimp [eff]
    exact Nat.mod_eq_of_lt (by omega)
  have heffPow : IsPow2Align eff := by
    rcases hPow with ⟨k, rfl⟩
    exact isPow2Align_of_toNat_pow2 (k := max k 3) (by rw [heffNat, max_pow2_eight])
  exact ⟨heffNat, by rw [heffNat, hMaxEq]; omega,
    isPow2Align_alignedAllocOk heffPow, by rw [heffNat]; omega⟩

private theorem nullAllowed_of_not_le_max {size align : Nat}
    (h : ¬ size ≤ MallocngMaxAllocSize) : NullAllowed size align := by
  unfold NullAllowed MallocngMaxAllocSize at *
  omega

private theorem nullAllowed_of_alignedAllocOk_false {size align : Nat} {sizeBv : BitVec 64}
    (hSzBv : sizeBv.toNat = size)
    (hPow : ∃ k, align = 2 ^ k) (hAlMax : align ≤ 2 ^ 31)
    (hok : mallocngAlignedAllocOk (BitVec.ofNat 64 (max align 8)) sizeBv = false) :
    NullAllowed size align := by
  obtain ⟨heffNat, _, halOk, _⟩ := effAlign_ok_props hPow hAlMax
  have hNotEff : ¬ (mallocngAlignedEffSize (max align 8) size ≤ MallocngMaxAllocSize) := by
    intro hle
    have htrue : mallocngAlignedAllocOk (BitVec.ofNat 64 (max align 8)) sizeBv = true := by
      unfold mallocngAlignedAllocOk
      rw [halOk, heffNat, hSzBv, decide_eq_true hle]
      rfl
    rw [htrue] at hok
    cases hok
  unfold NullAllowed mallocngAlignedEffSize MallocngMaxAllocSize at *
  split at hNotEff <;> omega

/-- `(γ, tp)`-independent `mallocng` fallback for `__rust_dealloc`. -/
noncomputable def f3DeallocFallbackRaw (mpl : Obj.MultiPlacement) (s0 : State) : State :=
  let s1 := mallocngHook mpl "free" s0
  if s1.status != .Running then s1
  else retHook (fun st => st.setMem s1.mem) (restoreCallerRegs s0 s1)

noncomputable def f3DeallocFallback (mpl : Obj.MultiPlacement) : State → State :=
  keepFsTrace (f3DeallocFallbackRaw mpl)

theorem f3DeallocFallback_fs (mpl : Obj.MultiPlacement) (s : State) :
    (f3DeallocFallback mpl s).fs = s.fs :=
  keepFsTrace_fs _ s

theorem f3DeallocFallback_fsT (mpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (f3DeallocFallback mpl) :=
  keepFsTrace_fsT _

theorem f3DeallocFallback_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {mpl : Obj.MultiPlacement} (brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk (f3DeallocFallback mpl)
      (rustCliDeallocBudgetSpecBase M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim) := by
  refine keepFsTrace_ok ?_ (fun x R s0 hout => specPreservesFsTraceExact_deallocBase _ lim x R s0 _ hout)
  rintro ⟨p, size, align, st⟩ R s0 hrun hpre hsp
  dsimp only [rustCliDeallocBudgetSpecBase, mallocngHookRustCliAllocBudget, mallocngLiveM] at hpre
  have hpreEq :
      (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = size ∧ (s0.readReg64 .x2).toNat = align⌝ ∗
        mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
        (I.BlockM γ p size (max align 16) ∗
          ⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64 ∧
            RustLayoutOk size align⌝) ∗
        memRegion p size ∗
        stackAt s0.sp allocHookStack) ∗ R =
      ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = size ∧ (s0.readReg64 .x2).toNat = align⌝ ∗
        (⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64 ∧
            RustLayoutOk size align⌝ ∗
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
            (I.BlockM γ p size (max align 16) ∗
              memRegion p size ∗
              stackAt s0.sp allocHookStack ∗ R))) := by sep_ac_rfl
  rw [hpreEq, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, _, _⟩, hpre⟩ := hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hpNe, _, hp16, hpFit, _⟩, hpre⟩ := hpre
  let Slack := memRegion (s0.sp - 4096#64) 3072
  rw [stackAt_allocHookStack_split s0.sp] at hpre
  have hpreF : s0.mem ⊨
      (freeHookBridgeSpec M I γ mpl tp brkStart lim).pre
        (p, size, align, s0.sp, st) s0 ∗ (Slack ∗ R) := by
    dsimp only [freeHookBridgeSpec]
    simp only [hpNe, ↓reduceIte, sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0, trivial, hp16, hpFit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [Slack]; sep_ac_rfl)) hpre
  obtain ⟨hkf1, hsym1, hout1⟩ := free_budget_hookOk hS γ tp brkStart lim hPl
    (p, size, align, s0.sp, st) (Slack ∗ R) s0 hrun hpreF hsp
  unfold f3DeallocFallbackRaw
  dsimp only
  set s1 := mallocngHook mpl "free" s0
  rcases hout1 with ⟨hret1, _, hpost1⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · have hs1Run : s1.status = .Running := hret1.2.2
    have hs1Bne : (s1.status != .Running) = false := by rw [hs1Run]; rfl
    simp only [hs1Bne, Bool.false_eq_true, ↓reduceIte]
    dsimp only [freeHookBridgeSpec] at hpost1
    rw [beq_eq_false_iff_ne.mpr hpNe] at hpost1
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hpost1
    rw [satisfies_pure_sepConj] at hpost1
    obtain ⟨hacp1, hpost1⟩ := hpost1
    set sKeep := restoreCallerRegs s0 s1
    set sf := retHook (fun st => st.setMem s1.mem) sKeep
    have hvm : VmPreserved s1 sf :=
      (vmPreserved_restoreCallerRegs s0 s1).trans (vmPreserved_retHook_setMem (s := sKeep) rfl)
    have hpoolSf := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim
      (M.step (.free align size) st) hvm
    have hcc := cc_retHook_setMem_sameRegs (s0 := s0) (s := sKeep) s1.mem rfl rfl rfl hs1Run
    refine ⟨hkf1, hsym1, Or.inl ⟨hcc.1, hcc.2, ?_⟩⟩
    dsimp only [rustCliDeallocBudgetSpecBase, mallocngHookRustCliAllocBudget, rustDeallocEvents]
    have hStep : M.stepEvents [.free align size] st = M.step (.free align size) st := rfl
    change s1.mem ⊨ _
    rw [hStep, hpoolSf, stackAt_allocHookStack_split s0.sp]
    have hGoalEq :
        (⌜AllocCallPreserved s0 sf ∧
            M.liveBytes (M.step (.free align size) st) ≤ M.liveBytes st⌝ ∗
          mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.free align size) st) s1 ∗
          (stackFrameAt s0.sp mallocngStackBytes ∗ Slack)) ∗ R =
        ⌜AllocCallPreserved s0 sf ∧
            M.liveBytes (M.step (.free align size) st) ≤ M.liveBytes st⌝ ∗
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.free align size) st) s1 ∗
            (stackFrameAt s0.sp mallocngStackBytes ∗ (Slack ∗ R))) := by
      dsimp [Slack]; sep_ac_rfl
    rw [hGoalEq, satisfies_pure_sepConj]
    exact ⟨⟨allocCallPreserved_retHook_restore s1.mem hacp1, M.liveBytes_free_le align size st⟩,
      hpost1⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- `(γ, tp)`-independent `mallocng` fallback for `__rust_alloc` (`zeroed = false`) and
    `__rust_alloc_zeroed` (`zeroed = true`). -/
noncomputable def f3AllocFallbackRaw (mpl : Obj.MultiPlacement) (zeroed : Bool)
    (s0 : State) : State :=
  let sizeBv := s0.readReg64 .x0
  let alignBv := s0.readReg64 .x1
  let size := sizeBv.toNat
  let align := alignBv.toNat
  if align ≤ 16 ∧ align ≤ size then
    let sCall := if zeroed then s0.writeReg64 .x1 1#64 else s0
    let s1 := mallocngHook mpl (if zeroed then "calloc" else "malloc") sCall
    if s1.status != .Running then s1
    else
      let p := s1.readReg64 .x0
      retHook (fun st => (st.setMem s1.mem).writeReg64 .x0 p) (restoreCallerRegs s0 s1)
  else
    let effAlign := BitVec.ofNat 64 (max align 8)
    let sCall := (s0.writeReg64 .x0 effAlign).writeReg64 .x1 sizeBv
    let s1 := mallocngHook mpl "aligned_alloc" sCall
    if s1.status != .Running then s1
    else
      let p := s1.readReg64 .x0
      let mOut :=
        if zeroed && (p != 0#64) then s1.mem.writeBytes p (List.replicate size 0#8)
        else s1.mem
      retHook (fun st => (st.setMem mOut).writeReg64 .x0 p) (restoreCallerRegs s0 s1)

noncomputable def f3AllocFallback (mpl : Obj.MultiPlacement) (zeroed : Bool) : State → State :=
  keepFsTrace (f3AllocFallbackRaw mpl zeroed)

theorem f3AllocFallback_fs (mpl : Obj.MultiPlacement) (zeroed : Bool) (s : State) :
    (f3AllocFallback mpl zeroed s).fs = s.fs :=
  keepFsTrace_fs _ s

theorem f3AllocFallback_fsT (mpl : Obj.MultiPlacement) (zeroed : Bool) :
    HookFsTraced IsFsC (f3AllocFallback mpl zeroed) :=
  keepFsTrace_fsT _

theorem f3AllocFallback_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {mpl : Obj.MultiPlacement} (brkStart : BitVec 64) (lim : BudgetLimits) (zeroed : Bool)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk (f3AllocFallback mpl zeroed)
      (rustCliAllocBudgetSpecBase M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart)
        lim zeroed) := by
  refine keepFsTrace_ok ?_ (fun x R s0 hout => specPreservesFsTraceExact_allocBase _ lim zeroed x R s0 _ hout)
  rintro ⟨size, align, st⟩ R s0 hrun hpre hsp
  dsimp only [rustCliAllocBudgetSpecBase, mallocngHookRustCliAllocBudget, mallocngLiveM] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, ⟨⟨hSzPos, hPow, hSum63⟩, hAlMax⟩⟩, hpre⟩ := hpre
  obtain ⟨hAlDvdMax, h16DvdMax⟩ := pow2_align_dvd_props hPow
  let Slack := memRegion (s0.sp - 4096#64) 3072
  rw [stackAt_allocHookStack_split s0.sp] at hpre
  unfold f3AllocFallbackRaw
  dsimp only
  rw [hx0, hx1]
  set sizeBv := s0.readReg64 .x0
  by_cases hFast : align ≤ 16 ∧ align ≤ size
  · rw [ite_pos hFast]
    have hevFast : rustAllocEvents size align = [.alloc size] := by
      unfold rustAllocEvents; simp [hFast]
    have hMax16 : max align 16 = 16 := Nat.max_eq_right hFast.1
    cases zeroed with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hpreM : s0.mem ⊨
          (mallocHookBridgeSpec M I γ mpl tp brkStart lim).pre
            (sizeBv, s0.sp, st) s0 ∗ (Slack ∗ R) := by
        dsimp only [mallocHookBridgeSpec]
        rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨rfl, rfl⟩, Satisfies.mono (Entails.of_eq (by dsimp [Slack]; sep_ac_rfl)) hpre⟩
      obtain ⟨hkf1, hsym1, hout1⟩ := malloc_budget_hookOk hS γ tp brkStart lim hPl
        (sizeBv, s0.sp, st) (Slack ∗ R) s0 hrun hpreM hsp
      set s1 := mallocngHook mpl "malloc" s0
      rcases hout1 with ⟨hret1, _, hpost1⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨hoom1, hoomSat⟩
      · have hs1Run : s1.status = .Running := hret1.2.2
        have hs1Bne : (s1.status != .Running) = false := by rw [hs1Run]; rfl
        simp only [hs1Bne, Bool.false_eq_true, ↓reduceIte]
        dsimp only [mallocHookBridgeSpec] at hpost1
        rw [hx0] at hpost1
        set p := s1.readReg64 .x0
        set sKeep := restoreCallerRegs s0 s1
        set sf := retHook (fun st => (st.setMem s1.mem).writeReg64 .x0 p) sKeep
        have hsfX0 : sf.readReg64 .x0 = p := by
          simp [sf, retHook, State.setPC, State.setMem, State.writeReg64, State.readReg64,
            RegFile.read, RegFile.write]
        have hcc := cc_retHook_setMem_writeX0 (s0 := s0) (s := sKeep) s1.mem p rfl rfl rfl hs1Run
        have hvm : VmPreserved s1 sf :=
          (vmPreserved_restoreCallerRegs s0 s1).trans
            (vmPreserved_retHook_setMem_writeX0 (s := sKeep) p rfl)
        refine ⟨hkf1, hsym1, Or.inl ⟨hcc.1, hcc.2, ?_⟩⟩
        dsimp only [rustCliAllocBudgetSpecBase, mallocngHookRustCliAllocBudget, mallocngLiveM]
        rw [hevFast, hsfX0]
        change s1.mem ⊨ _
        cases hok : decide (size ≤ MallocngMaxAllocSize) with
        | true =>
          simp only [hok, ↓reduceIte, sepConj_assoc] at hpost1
          rw [satisfies_pure_sepConj] at hpost1
          obtain ⟨hacp1, hpost1⟩ := hpost1
          have hPull :
              mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗
                  (⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64⌝ ∗
                    (I.BlockM γ p size 16 ∗ (memRegion p size ∗ (Slack ∗ R))))) =
              ⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64⌝ ∗
                (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
                  ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                    I.BlockM γ p size 16 ∗ memRegion p size ∗ R)) := by
            dsimp [p, Slack]; sep_ac_rfl
          rw [hPull, satisfies_pure_sepConj] at hpost1
          obtain ⟨⟨hpNe, hp16, hpFit⟩, hpost1⟩ := hpost1
          have hpNe0 : p ≠ 0 := hpNe
          have hpAl : align ∣ p.toNat := Nat.dvd_trans (hMax16 ▸ hAlDvdMax) hp16
          have hpoolSf := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim
            (M.step (.alloc size) st) hvm
          simp only [hpNe0, ↓reduceIte, Bool.false_eq_true,
            AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil,
            hpoolSf, stackAt_allocHookStack_split s0.sp, hMax16]
          have hGoalEq :
              (⌜AllocCallPreserved s0 sf⌝ ∗
                mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                (⌜p.toNat % align = 0⌝ ∗
                  (I.BlockM γ p size 16 ∗
                    ⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64 ∧
                      RustLayoutOk size align⌝) ∗
                  memRegion p size)) ∗ R =
              ⌜AllocCallPreserved s0 sf⌝ ∗
                (⌜p.toNat % align = 0⌝ ∗
                  (⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64 ∧
                      RustLayoutOk size align⌝ ∗
                    (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
                      ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                        I.BlockM γ p size 16 ∗ memRegion p size ∗ R)))) := by
            dsimp [Slack]; sep_ac_rfl
          rw [hGoalEq, satisfies_pure_sepConj]
          refine ⟨allocCallPreserved_retHook_restore_x0 s1.mem p hacp1, ?_⟩
          rw [satisfies_pure_sepConj]
          refine ⟨Nat.mod_eq_zero_of_dvd hpAl, ?_⟩
          rw [satisfies_pure_sepConj]
          exact ⟨⟨hpNe, hpAl, hp16, hpFit, ⟨hSzPos, hPow, hSum63⟩, hAlMax⟩, hpost1⟩
        | false =>
          simp only [hok, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hpost1
          rw [satisfies_pure_sepConj] at hpost1
          obtain ⟨hacp1, hpost1⟩ := hpost1
          have hPull :
              mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ (⌜p = 0#64⌝ ∗ (Slack ∗ R))) =
              ⌜p = 0#64⌝ ∗
                (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                  ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗ R)) := by
            dsimp [p, Slack]; sep_ac_rfl
          rw [hPull, satisfies_pure_sepConj] at hpost1
          obtain ⟨hp0, hpost1⟩ := hpost1
          have hpEq0 : p = 0 := hp0
          have hpoolSf := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hvm
          simp only [hpEq0, ↓reduceIte, hpoolSf, stackAt_allocHookStack_split s0.sp]
          have hGoalEq :
              (⌜AllocCallPreserved s0 sf⌝ ∗
                mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                ⌜NullAllowed size align⌝) ∗ R =
              ⌜AllocCallPreserved s0 sf⌝ ∗
                (⌜NullAllowed size align⌝ ∗
                  (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                    ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗ R))) := by
            dsimp [Slack]; sep_ac_rfl
          rw [hGoalEq, satisfies_pure_sepConj]
          refine ⟨allocCallPreserved_retHook_restore_x0 s1.mem p hacp1, ?_⟩
          rw [satisfies_pure_sepConj]
          exact ⟨nullAllowed_of_not_le_max (of_decide_eq_false hok), hpost1⟩
      · exact False.elim (not_satisfies_false_sepConj hp)
      · exact False.elim (not_satisfies_false_sepConj he)
      · have hs1Bne : (s1.status != .Running) = true := by rw [hoom1]; rfl
        simp only [hs1Bne, ↓reduceIte]
        dsimp only [mallocHookBridgeSpec] at hoomSat
        rw [hx0, satisfies_pure_sepConj] at hoomSat
        obtain ⟨⟨hNotFit, hOomPres⟩, hRSat⟩ := hoomSat
        refine ⟨hkf1, hsym1, Or.inr (Or.inr (Or.inr ⟨hoom1, ?_⟩))⟩
        dsimp only [rustCliAllocBudgetSpecBase]
        rw [hevFast, satisfies_pure_sepConj]
        exact ⟨⟨fun h => hNotFit h.1, hOomPres⟩, Satisfies.of_sep_right hRSat⟩
    | true =>
      simp only [↓reduceIte]
      set sCall := s0.writeReg64 .x1 1#64
      have hvmCall : VmPreserved s0 sCall := vmPreserved_writeReg64 s0 .x1 1#64
      have hpoolCall := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hvmCall
      have hsCallSp : sCall.spAligned = true := hsp
      have hpreC : sCall.mem ⊨
          (callocHookBridgeSpec M I γ mpl tp brkStart lim).pre
            (sizeBv, 1#64, s0.sp, st) sCall ∗ (Slack ∗ R) := by
        dsimp only [callocHookBridgeSpec]
        change s0.mem ⊨ _
        rw [hpoolCall, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨by simp [sCall, sizeBv, State.writeReg64, State.readReg64, RegFile.read, RegFile.write],
          by simp [sCall, State.writeReg64, State.readReg64, RegFile.read, RegFile.write], rfl⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by dsimp [Slack]; sep_ac_rfl)) hpre
      obtain ⟨hkf1, hsym1, hout1⟩ := calloc_budget_hookOk hS γ tp brkStart lim hPl
        (sizeBv, 1#64, s0.sp, st) (Slack ∗ R) sCall hrun hpreC hsCallSp
      set s1 := mallocngHook mpl "calloc" sCall
      rcases hout1 with ⟨hret1, _, hpost1⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨hoom1, hoomSat⟩
      · have hs1Run : s1.status = .Running := hret1.2.2
        have hs1Bne : (s1.status != .Running) = false := by rw [hs1Run]; rfl
        simp only [hs1Bne, Bool.false_eq_true, ↓reduceIte]
        dsimp only [callocHookBridgeSpec] at hpost1
        have hmul1 : sizeBv.toNat * (1#64 : BitVec 64).toNat = size := by
          change sizeBv.toNat * 1 = size; rw [Nat.mul_one, hx0]
        rw [hmul1] at hpost1
        set p := s1.readReg64 .x0
        set sKeep := restoreCallerRegs s0 s1
        set sf := retHook (fun st => (st.setMem s1.mem).writeReg64 .x0 p) sKeep
        have hsfX0 : sf.readReg64 .x0 = p := by
          simp [sf, retHook, State.setPC, State.setMem, State.writeReg64, State.readReg64,
            RegFile.read, RegFile.write]
        have hcc := cc_retHook_setMem_writeX0 (s0 := s0) (s := sKeep) s1.mem p rfl rfl rfl hs1Run
        have hvm : VmPreserved s1 sf :=
          (vmPreserved_restoreCallerRegs s0 s1).trans
            (vmPreserved_retHook_setMem_writeX0 (s := sKeep) p rfl)
        refine ⟨hkf1, hsym1, Or.inl ⟨hcc.1, hcc.2, ?_⟩⟩
        dsimp only [rustCliAllocBudgetSpecBase, mallocngHookRustCliAllocBudget, mallocngLiveM]
        rw [hevFast, hsfX0]
        change s1.mem ⊨ _
        cases hok : decide (size ≤ MallocngMaxAllocSize) with
        | true =>
          simp only [hok, ↓reduceIte, sepConj_assoc] at hpost1
          rw [satisfies_pure_sepConj] at hpost1
          obtain ⟨hacp1', hpost1⟩ := hpost1
          have hacp1 : AllocCallPreserved s0 s1 := hacp1'
          have hPull :
              mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗
                  (⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64⌝ ∗
                    (I.BlockM γ p size 16 ∗ ((p ↦ₛ List.replicate size 0#8) ∗ (Slack ∗ R))))) =
              ⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64⌝ ∗
                (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
                  ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                    I.BlockM γ p size 16 ∗ (p ↦ₛ List.replicate size 0#8) ∗ R)) := by
            dsimp [p, Slack]; sep_ac_rfl
          rw [hPull, satisfies_pure_sepConj] at hpost1
          obtain ⟨⟨hpNe, hp16, hpFit⟩, hpost1⟩ := hpost1
          have hpNe0 : p ≠ 0 := hpNe
          have hpAl : align ∣ p.toNat := Nat.dvd_trans (hMax16 ▸ hAlDvdMax) hp16
          have hpoolSf := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim
            (M.step (.alloc size) st) hvm
          simp only [hpNe0, ↓reduceIte,
            AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil,
            hpoolSf, stackAt_allocHookStack_split s0.sp, hMax16]
          have hGoalEq :
              (⌜AllocCallPreserved s0 sf⌝ ∗
                mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                (⌜p.toNat % align = 0⌝ ∗
                  (I.BlockM γ p size 16 ∗
                    ⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64 ∧
                      RustLayoutOk size align⌝) ∗
                  (p ↦ₛ List.replicate size 0#8))) ∗ R =
              ⌜AllocCallPreserved s0 sf⌝ ∗
                (⌜p.toNat % align = 0⌝ ∗
                  (⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64 ∧
                      RustLayoutOk size align⌝ ∗
                    (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
                      ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                        I.BlockM γ p size 16 ∗ (p ↦ₛ List.replicate size 0#8) ∗ R)))) := by
            dsimp [Slack]; sep_ac_rfl
          rw [hGoalEq, satisfies_pure_sepConj]
          refine ⟨allocCallPreserved_retHook_restore_x0 s1.mem p hacp1, ?_⟩
          rw [satisfies_pure_sepConj]
          refine ⟨Nat.mod_eq_zero_of_dvd hpAl, ?_⟩
          rw [satisfies_pure_sepConj]
          exact ⟨⟨hpNe, hpAl, hp16, hpFit, ⟨hSzPos, hPow, hSum63⟩, hAlMax⟩, hpost1⟩
        | false =>
          simp only [hok, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hpost1
          rw [satisfies_pure_sepConj] at hpost1
          obtain ⟨hacp1', hpost1⟩ := hpost1
          have hacp1 : AllocCallPreserved s0 s1 := hacp1'
          have hPull :
              mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ (⌜p = 0#64⌝ ∗ (Slack ∗ R))) =
              ⌜p = 0#64⌝ ∗
                (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                  ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗ R)) := by
            dsimp [p, Slack]; sep_ac_rfl
          rw [hPull, satisfies_pure_sepConj] at hpost1
          obtain ⟨hp0, hpost1⟩ := hpost1
          have hpEq0 : p = 0 := hp0
          have hpoolSf := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hvm
          simp only [hpEq0, ↓reduceIte, hpoolSf, stackAt_allocHookStack_split s0.sp]
          have hGoalEq :
              (⌜AllocCallPreserved s0 sf⌝ ∗
                mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                ⌜NullAllowed size align⌝) ∗ R =
              ⌜AllocCallPreserved s0 sf⌝ ∗
                (⌜NullAllowed size align⌝ ∗
                  (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                    ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗ R))) := by
            dsimp [Slack]; sep_ac_rfl
          rw [hGoalEq, satisfies_pure_sepConj]
          refine ⟨allocCallPreserved_retHook_restore_x0 s1.mem p hacp1, ?_⟩
          rw [satisfies_pure_sepConj]
          exact ⟨nullAllowed_of_not_le_max (of_decide_eq_false hok), hpost1⟩
      · exact False.elim (not_satisfies_false_sepConj hp)
      · exact False.elim (not_satisfies_false_sepConj he)
      · have hs1Bne : (s1.status != .Running) = true := by rw [hoom1]; rfl
        simp only [hs1Bne, ↓reduceIte]
        dsimp only [callocHookBridgeSpec] at hoomSat
        have hmul1 : sizeBv.toNat * (1#64 : BitVec 64).toNat = size := by
          change sizeBv.toNat * 1 = size; rw [Nat.mul_one, hx0]
        rw [hmul1, satisfies_pure_sepConj] at hoomSat
        obtain ⟨⟨hNotFit, hOomPres⟩, hRSat⟩ := hoomSat
        refine ⟨hkf1, hsym1, Or.inr (Or.inr (Or.inr ⟨hoom1, ?_⟩))⟩
        dsimp only [rustCliAllocBudgetSpecBase]
        rw [hevFast, satisfies_pure_sepConj]
        exact ⟨⟨fun h => hNotFit h.1, hOomPres⟩, Satisfies.of_sep_right hRSat⟩
  · rw [ite_neg hFast]
    have hevSlow : rustAllocEvents size align = [.aligned (max align 8) size] := by
      unfold rustAllocEvents; simp [hFast]
    obtain ⟨heffNat, heffMax, heffOk, _⟩ := effAlign_ok_props hPow hAlMax
    have hMax8_16 : max (max align 8) 16 = max align 16 := by omega
    set effAlign := BitVec.ofNat 64 (max align 8)
    set sCall := (s0.writeReg64 .x0 effAlign).writeReg64 .x1 sizeBv
    have hvmCall : VmPreserved s0 sCall :=
      (vmPreserved_writeReg64 s0 .x0 effAlign).trans
        (vmPreserved_writeReg64 (s0.writeReg64 .x0 effAlign) .x1 sizeBv)
    have hpoolCall := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hvmCall
    have hpreA : sCall.mem ⊨
        (alignedAllocHookBridgeSpec M I γ mpl tp brkStart lim).pre
          (effAlign, sizeBv, s0.sp, st) sCall ∗ (Slack ∗ R) := by
      dsimp only [alignedAllocHookBridgeSpec]
      change s0.mem ⊨ _
      rw [hpoolCall, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp [sCall, State.writeReg64, State.readReg64, RegFile.read, RegFile.write],
        by simp [sCall, State.writeReg64, State.readReg64, RegFile.read, RegFile.write],
        rfl, heffMax⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by dsimp [Slack]; sep_ac_rfl)) hpre
    obtain ⟨hkf1, hsym1, hout1⟩ := alignedAlloc_budget_hookOk hS γ tp brkStart lim hPl
      (effAlign, sizeBv, s0.sp, st) (Slack ∗ R) sCall hrun hpreA hsp
    set s1 := mallocngHook mpl "aligned_alloc" sCall
    rcases hout1 with ⟨hret1, _, hpost1⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨hoom1, hoomSat⟩
    · have hs1Run : s1.status = .Running := hret1.2.2
      have hs1Bne : (s1.status != .Running) = false := by rw [hs1Run]; rfl
      simp only [hs1Bne, Bool.false_eq_true, ↓reduceIte]
      dsimp only [alignedAllocHookBridgeSpec] at hpost1
      rw [heffNat, hx0] at hpost1
      set p := s1.readReg64 .x0
      set mOut :=
        if zeroed && (p != 0#64) then s1.mem.writeBytes p (List.replicate size 0#8)
        else s1.mem
      set sKeep := restoreCallerRegs s0 s1
      set sf := retHook (fun st => (st.setMem mOut).writeReg64 .x0 p) sKeep
      have hsfX0 : sf.readReg64 .x0 = p := by
        simp [sf, retHook, State.setPC, State.setMem, State.writeReg64, State.readReg64,
          RegFile.read, RegFile.write]
      have hcc := cc_retHook_setMem_writeX0 (s0 := s0) (s := sKeep) mOut p rfl rfl rfl hs1Run
      have hmOutPerm : mOut.perm = s1.mem.perm := by
        dsimp [mOut]
        split
        · exact Memory.perm_writeBytes s1.mem p (List.replicate size 0#8)
        · rfl
      have hvm : VmPreserved s1 sf :=
        (vmPreserved_restoreCallerRegs s0 s1).trans
          (vmPreserved_retHook_setMem_writeX0 (s := sKeep) p hmOutPerm)
      cases hok : mallocngAlignedAllocOk effAlign sizeBv with
      | true =>
        simp only [hok, ↓reduceIte, hMax8_16, sepConj_assoc] at hpost1
        rw [satisfies_pure_sepConj] at hpost1
        obtain ⟨hacp1', hpost1⟩ := hpost1
        have hacp1 : AllocCallPreserved s0 s1 := hacp1'
        have hPull :
            mallocngHookBudgetPool M I γ mpl tp brkStart lim
                (M.step (.aligned (max align 8) size) st) s1 ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗
                (⌜p ≠ 0#64 ∧ max align 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64⌝ ∗
                  (I.BlockM γ p size (max align 16) ∗ (memRegion p size ∗ (Slack ∗ R))))) =
            ⌜p ≠ 0#64 ∧ max align 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64⌝ ∗
              (memRegion p size ∗
                (mallocngHookBudgetPool M I γ mpl tp brkStart lim
                    (M.step (.aligned (max align 8) size) st) s1 ∗
                  ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                    I.BlockM γ p size (max align 16) ∗ R))) := by
          dsimp [p, Slack]; sep_ac_rfl
        rw [hPull, satisfies_pure_sepConj] at hpost1
        obtain ⟨⟨hpNe, hpMaxAl, hpFit⟩, hpost1⟩ := hpost1
        have hpNe0 : p ≠ 0 := hpNe
        have hpAl : align ∣ p.toNat := Nat.dvd_trans hAlDvdMax hpMaxAl
        have hp16 : 16 ∣ p.toNat := Nat.dvd_trans h16DvdMax hpMaxAl
        have hpoolSf := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim
          (M.step (.aligned (max align 8) size) st) hvm
        cases zeroed with
        | false =>
          have hmOutEq : mOut = s1.mem := by simp [mOut]
          have hsfKf : s0.mem.KeepsFrozen sf.mem := by
            change s0.mem.KeepsFrozen mOut; rw [hmOutEq]; exact hkf1
          refine ⟨hsfKf, hsym1, Or.inl ⟨hcc.1, hcc.2, ?_⟩⟩
          dsimp only [rustCliAllocBudgetSpecBase, mallocngHookRustCliAllocBudget, mallocngLiveM]
          rw [hevSlow, hsfX0]
          change mOut ⊨ _
          rw [hmOutEq]
          simp only [hpNe0, ↓reduceIte, Bool.false_eq_true,
            AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil,
            hpoolSf, stackAt_allocHookStack_split s0.sp]
          have hGoalEq :
              (⌜AllocCallPreserved s0 sf⌝ ∗
                mallocngHookBudgetPool M I γ mpl tp brkStart lim
                  (M.step (.aligned (max align 8) size) st) s1 ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                (⌜p.toNat % align = 0⌝ ∗
                  (I.BlockM γ p size (max align 16) ∗
                    ⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64 ∧
                      RustLayoutOk size align⌝) ∗
                  memRegion p size)) ∗ R =
              ⌜AllocCallPreserved s0 sf⌝ ∗
                (⌜p.toNat % align = 0⌝ ∗
                  (⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64 ∧
                      RustLayoutOk size align⌝ ∗
                    (memRegion p size ∗
                      (mallocngHookBudgetPool M I γ mpl tp brkStart lim
                          (M.step (.aligned (max align 8) size) st) s1 ∗
                        ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                          I.BlockM γ p size (max align 16) ∗ R))))) := by
            dsimp [Slack]; sep_ac_rfl
          rw [hGoalEq, satisfies_pure_sepConj]
          refine ⟨allocCallPreserved_retHook_restore_x0 mOut p hacp1, ?_⟩
          rw [satisfies_pure_sepConj]
          refine ⟨Nat.mod_eq_zero_of_dvd hpAl, ?_⟩
          rw [satisfies_pure_sepConj]
          exact ⟨⟨hpNe, hpAl, hp16, hpFit, ⟨hSzPos, hPow, hSum63⟩, hAlMax⟩, hpost1⟩
        | true =>
          have hpBne : (p != 0#64) = true := bne_iff_ne.mpr hpNe
          have hmOutEq : mOut = s1.mem.writeBytes p (List.replicate size 0#8) := by
            simp [mOut, hpBne]
          have hpost1' : s1.mem ⊨
              memRegion p (List.replicate size 0#8).length ∗
                (mallocngHookBudgetPool M I γ mpl tp brkStart lim
                    (M.step (.aligned (max align 8) size) st) s1 ∗
                  ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                    I.BlockM γ p size (max align 16) ∗ R)) := by
            simpa only [List.length_replicate] using hpost1
          have hrepFit : (List.replicate size 0#8).length ≤ 2 ^ 64 := by
            rw [List.length_replicate]; omega
          have hkfW := keepsFrozen_writeBytes_of_memRegion (List.replicate size 0#8)
            hrepFit hpost1'
          have hsatW := satisfies_writeBytes (List.replicate size 0#8) hrepFit hpost1'
          have hsfKf : s0.mem.KeepsFrozen sf.mem := by
            change s0.mem.KeepsFrozen mOut; rw [hmOutEq]; exact hkf1.trans hkfW
          refine ⟨hsfKf, hsym1, Or.inl ⟨hcc.1, hcc.2, ?_⟩⟩
          dsimp only [rustCliAllocBudgetSpecBase, mallocngHookRustCliAllocBudget, mallocngLiveM]
          rw [hevSlow, hsfX0]
          change mOut ⊨ _
          rw [hmOutEq]
          simp only [hpNe0, ↓reduceIte,
            AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil,
            hpoolSf, stackAt_allocHookStack_split s0.sp]
          have hGoalEq :
              (⌜AllocCallPreserved s0 sf⌝ ∗
                mallocngHookBudgetPool M I γ mpl tp brkStart lim
                  (M.step (.aligned (max align 8) size) st) s1 ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                (⌜p.toNat % align = 0⌝ ∗
                  (I.BlockM γ p size (max align 16) ∗
                    ⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64 ∧
                      RustLayoutOk size align⌝) ∗
                  (p ↦ₛ List.replicate size 0#8))) ∗ R =
              ⌜AllocCallPreserved s0 sf⌝ ∗
                (⌜p.toNat % align = 0⌝ ∗
                  (⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64 ∧
                      RustLayoutOk size align⌝ ∗
                    ((p ↦ₛ List.replicate size 0#8) ∗
                      (mallocngHookBudgetPool M I γ mpl tp brkStart lim
                          (M.step (.aligned (max align 8) size) st) s1 ∗
                        ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                          I.BlockM γ p size (max align 16) ∗ R))))) := by
            dsimp [Slack]; sep_ac_rfl
          rw [hGoalEq, satisfies_pure_sepConj]
          refine ⟨allocCallPreserved_retHook_restore_x0 mOut p hacp1, ?_⟩
          rw [satisfies_pure_sepConj]
          refine ⟨Nat.mod_eq_zero_of_dvd hpAl, ?_⟩
          rw [satisfies_pure_sepConj]
          exact ⟨⟨hpNe, hpAl, hp16, hpFit, ⟨hSzPos, hPow, hSum63⟩, hAlMax⟩, hsatW⟩
      | false =>
        simp only [hok, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hpost1
        rw [satisfies_pure_sepConj] at hpost1
        obtain ⟨hacp1', hpost1⟩ := hpost1
        have hacp1 : AllocCallPreserved s0 s1 := hacp1'
        have hPull :
            mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗ (⌜p = 0#64⌝ ∗ (Slack ∗ R))) =
            ⌜p = 0#64⌝ ∗
              (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗ R)) := by
          dsimp [p, Slack]; sep_ac_rfl
        rw [hPull, satisfies_pure_sepConj] at hpost1
        obtain ⟨hp0, hpost1⟩ := hpost1
        have hpEq0 : p = 0 := hp0
        have hmOutEq : mOut = s1.mem := by simp [mOut, hp0]
        have hpoolSf := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hvm
        have hsfKf : s0.mem.KeepsFrozen sf.mem := by
          change s0.mem.KeepsFrozen mOut; rw [hmOutEq]; exact hkf1
        refine ⟨hsfKf, hsym1, Or.inl ⟨hcc.1, hcc.2, ?_⟩⟩
        dsimp only [rustCliAllocBudgetSpecBase, mallocngHookRustCliAllocBudget]
        rw [hevSlow, hsfX0]
        change mOut ⊨ _
        rw [hmOutEq]
        simp only [hpEq0, ↓reduceIte, hpoolSf, stackAt_allocHookStack_split s0.sp]
        have hGoalEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗
              mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
              ⌜NullAllowed size align⌝) ∗ R =
            ⌜AllocCallPreserved s0 sf⌝ ∗
              (⌜NullAllowed size align⌝ ∗
                (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                  ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗ R))) := by
          dsimp [Slack]; sep_ac_rfl
        rw [hGoalEq, satisfies_pure_sepConj]
        refine ⟨allocCallPreserved_retHook_restore_x0 mOut p hacp1, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨nullAllowed_of_alignedAllocOk_false hx0 hPow hAlMax hok, hpost1⟩
    · exact False.elim (not_satisfies_false_sepConj hp)
    · exact False.elim (not_satisfies_false_sepConj he)
    · have hs1Bne : (s1.status != .Running) = true := by rw [hoom1]; rfl
      simp only [hs1Bne, ↓reduceIte]
      dsimp only [alignedAllocHookBridgeSpec] at hoomSat
      rw [heffNat, hx0, satisfies_pure_sepConj] at hoomSat
      obtain ⟨⟨hNotFit, hOomPres⟩, hRSat⟩ := hoomSat
      refine ⟨hkf1, hsym1, Or.inr (Or.inr (Or.inr ⟨hoom1, ?_⟩))⟩
      dsimp only [rustCliAllocBudgetSpecBase]
      rw [hevSlow, satisfies_pure_sepConj]
      exact ⟨⟨fun h => hNotFit ⟨heffOk, h.1⟩, hOomPres⟩, Satisfies.of_sep_right hRSat⟩

/-- `(γ, tp)`-independent `mallocng` fallback for `__rust_realloc`. -/
noncomputable def f3ReallocFallbackRaw (mpl : Obj.MultiPlacement) (s0 : State) : State :=
  let p := s0.readReg64 .x0
  let old := (s0.readReg64 .x1).toNat
  let align := (s0.readReg64 .x2).toNat
  let newBv := s0.readReg64 .x3
  let new := newBv.toNat
  if align ≤ 16 ∧ align ≤ new then
    let sCall := s0.writeReg64 .x1 newBv
    let s1 := mallocngHook mpl "realloc" sCall
    if s1.status != .Running then s1
    else
      let q := s1.readReg64 .x0
      retHook (fun st => (st.setMem s1.mem).writeReg64 .x0 q) (restoreCallerRegs s0 s1)
  else
    let effAlign := BitVec.ofNat 64 (max align 8)
    let sCall := (s0.writeReg64 .x0 effAlign).writeReg64 .x1 newBv
    let s1 := mallocngHook mpl "aligned_alloc" sCall
    if s1.status != .Running then s1
    else
      let q := s1.readReg64 .x0
      if q = 0#64 then
        retHook (fun st => (st.setMem s1.mem).writeReg64 .x0 0#64) (restoreCallerRegs s0 s1)
      else
        let copyLen := min old new
        let srcBs := s1.mem.readBytes p copyLen
        let mCopy := s1.mem.writeBytes q srcBs
        let sFreeCall := ((restoreCallerRegs s0 s1).setMem mCopy).writeReg64 .x0 p
        let s2 := mallocngHook mpl "free" sFreeCall
        if s2.status != .Running then s2
        else
          retHook (fun st => (st.setMem s2.mem).writeReg64 .x0 q) (restoreCallerRegs s0 s2)

noncomputable def f3ReallocFallback (mpl : Obj.MultiPlacement) : State → State :=
  keepFsTrace (f3ReallocFallbackRaw mpl)

theorem f3ReallocFallback_fs (mpl : Obj.MultiPlacement) (s : State) :
    (f3ReallocFallback mpl s).fs = s.fs :=
  keepFsTrace_fs _ s

theorem f3ReallocFallback_fsT (mpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (f3ReallocFallback mpl) :=
  keepFsTrace_fsT _

theorem f3ReallocFallback_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {mpl : Obj.MultiPlacement} (brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk (f3ReallocFallback mpl)
      (rustCliReallocBudgetSpecBase M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart)
        lim) := by
  refine keepFsTrace_ok ?_ (fun x R s0 hout => specPreservesFsTraceExact_reallocBase _ lim x R s0 _ hout)
  rintro ⟨p, old, align, new, bs, st⟩ R s0 hrun hpre hsp
  dsimp only [rustCliReallocBudgetSpecBase, mallocngHookRustCliAllocBudget, mallocngLiveM] at hpre
  have hpreEq :
      (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧ (s0.readReg64 .x2).toNat = align ∧
          (s0.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
          bs.length ≤ new⌝ ∗
        mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
        (I.BlockM γ p old (max align 16) ∗
          ⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + old < 2 ^ 64 ∧
            RustLayoutOk old align⌝) ∗
        (p ↦ₛ bs) ∗
        memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
        stackAt s0.sp allocHookStack) ∗ R =
      ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧ (s0.readReg64 .x2).toNat = align ∧
          (s0.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
          bs.length ≤ new⌝ ∗
        (⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + old < 2 ^ 64 ∧
            RustLayoutOk old align⌝ ∗
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
            (I.BlockM γ p old (max align 16) ∗
              (p ↦ₛ bs) ∗
              memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
              stackAt s0.sp allocHookStack ∗ R))) := by sep_ac_rfl
  rw [hpreEq, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, ⟨⟨hNewPos, hPow, hNewSum63⟩, hAlMax⟩, hbsOld, hbsNew⟩, hpre⟩ := hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hpNe, hpAl, hp16, hpFit, hOldLay⟩, hpre⟩ := hpre
  obtain ⟨hAlDvdMax, h16DvdMax⟩ := pow2_align_dvd_props hPow
  let Slack := memRegion (s0.sp - 4096#64) 3072
  rw [stackAt_allocHookStack_split s0.sp] at hpre
  unfold f3ReallocFallbackRaw
  dsimp only
  rw [hx0, hx1, hx2, hx3]
  set newBv := s0.readReg64 .x3
  by_cases hFast : align ≤ 16 ∧ align ≤ new
  · rw [ite_pos hFast]
    have hevFast : rustReallocEvents old new align = [.realloc align old new] := by
      unfold rustReallocEvents; simp [hFast]
    have hMax16 : max align 16 = 16 := Nat.max_eq_right hFast.1
    set sCall := s0.writeReg64 .x1 newBv
    have hvmCall : VmPreserved s0 sCall := vmPreserved_writeReg64 s0 .x1 newBv
    have hpoolCall := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hvmCall
    have hpreR : sCall.mem ⊨
        (reallocHookBridgeSpec M I γ mpl tp brkStart lim).pre
          (p, newBv, old, align, bs, s0.sp, st) sCall ∗ (Slack ∗ R) := by
      dsimp only [reallocHookBridgeSpec]
      change s0.mem ⊨ _
      rw [hpoolCall]
      have hPackPre :
          (⌜sCall.readReg64 .x0 = p ∧ sCall.readReg64 .x1 = newBv ∧ sCall.sp = s0.sp ∧
              p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + old < 2 ^ 64 ∧ bs.length ≤ old⌝ ∗
            mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
            I.BlockM γ p old (max align 16) ∗
            (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
            stackFrameAt s0.sp mallocngStackBytes) ∗ (Slack ∗ R) =
          ⌜sCall.readReg64 .x0 = p ∧ sCall.readReg64 .x1 = newBv ∧ sCall.sp = s0.sp ∧
              p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + old < 2 ^ 64 ∧ bs.length ≤ old⌝ ∗
            (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
              (I.BlockM γ p old (max align 16) ∗
                (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗ R)) := by
        dsimp [Slack]; sep_ac_rfl
      rw [hPackPre, satisfies_pure_sepConj]
      exact ⟨⟨by simpa [sCall, State.writeReg64, State.readReg64, RegFile.read, RegFile.write] using hx0,
        by simp [sCall, State.writeReg64, State.readReg64, RegFile.read, RegFile.write],
        rfl, hpNe, hp16, hpFit, hbsOld⟩, hpre⟩
    obtain ⟨hkf1, hsym1, hout1⟩ := realloc_budget_hookOk hS γ tp brkStart lim hPl
      (p, newBv, old, align, bs, s0.sp, st) (Slack ∗ R) sCall hrun hpreR hsp
    set s1 := mallocngHook mpl "realloc" sCall
    rcases hout1 with ⟨hret1, _, hpost1⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨hoom1, hoomSat⟩
    · have hs1Run : s1.status = .Running := hret1.2.2
      have hs1Bne : (s1.status != .Running) = false := by rw [hs1Run]; rfl
      simp only [hs1Bne, Bool.false_eq_true, ↓reduceIte]
      dsimp only [reallocHookBridgeSpec] at hpost1
      rw [hx3] at hpost1
      set q := s1.readReg64 .x0
      set sKeep := restoreCallerRegs s0 s1
      set sf := retHook (fun st => (st.setMem s1.mem).writeReg64 .x0 q) sKeep
      have hsfX0 : sf.readReg64 .x0 = q := by
        simp [sf, retHook, State.setPC, State.setMem, State.writeReg64, State.readReg64,
          RegFile.read, RegFile.write]
      have hcc := cc_retHook_setMem_writeX0 (s0 := s0) (s := sKeep) s1.mem q rfl rfl rfl hs1Run
      have hvm : VmPreserved s1 sf :=
        (vmPreserved_restoreCallerRegs s0 s1).trans
          (vmPreserved_retHook_setMem_writeX0 (s := sKeep) q rfl)
      refine ⟨hkf1, hsym1, Or.inl ⟨hcc.1, hcc.2, ?_⟩⟩
      dsimp only [rustCliReallocBudgetSpecBase, mallocngHookRustCliAllocBudget, mallocngLiveM]
      rw [hevFast, hsfX0]
      change s1.mem ⊨ _
      cases hok : decide (new ≤ MallocngMaxAllocSize) with
      | true =>
        simp only [hok, ↓reduceIte, List.take_of_length_le hbsNew, sepConj_assoc] at hpost1
        rw [satisfies_pure_sepConj] at hpost1
        obtain ⟨hacp1', hpost1⟩ := hpost1
        have hacp1 : AllocCallPreserved s0 s1 := hacp1'
        have hPull :
            mallocngHookBudgetPool M I γ mpl tp brkStart lim
                (M.step (.realloc align old new) st) s1 ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗
                (⌜q ≠ 0#64 ∧ 16 ∣ q.toNat ∧ q.toNat + new < 2 ^ 64 ∧ bs.length ≤ new⌝ ∗
                  (I.BlockM γ q new (max align 16) ∗
                    ((q ↦ₛ bs) ∗
                      (memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗
                        (Slack ∗ R)))))) =
            ⌜q ≠ 0#64 ∧ 16 ∣ q.toNat ∧ q.toNat + new < 2 ^ 64 ∧ bs.length ≤ new⌝ ∗
              (mallocngHookBudgetPool M I γ mpl tp brkStart lim
                  (M.step (.realloc align old new) st) s1 ∗
                ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                  I.BlockM γ q new (max align 16) ∗
                  (q ↦ₛ bs) ∗
                  memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R)) := by
          dsimp [q, Slack]; sep_ac_rfl
        rw [hPull, satisfies_pure_sepConj] at hpost1
        obtain ⟨⟨hqNe, hq16, hqFit, _⟩, hpost1⟩ := hpost1
        have hqNe0 : q ≠ 0 := hqNe
        have hqAl : align ∣ q.toNat := Nat.dvd_trans (hMax16 ▸ hAlDvdMax) hq16
        have hpoolSf := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim
          (M.step (.realloc align old new) st) hvm
        simp only [hqNe0, ↓reduceIte,
          AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil,
          hpoolSf, stackAt_allocHookStack_split s0.sp]
        have hGoalEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗
              mallocngHookBudgetPool M I γ mpl tp brkStart lim
                (M.step (.realloc align old new) st) s1 ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
              (⌜q.toNat % align = 0⌝ ∗
                (I.BlockM γ q new (max align 16) ∗
                  ⌜q ≠ 0#64 ∧ align ∣ q.toNat ∧ 16 ∣ q.toNat ∧ q.toNat + new < 2 ^ 64 ∧
                    RustLayoutOk new align⌝) ∗
                (q ↦ₛ bs) ∗
                memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length))) ∗ R =
            ⌜AllocCallPreserved s0 sf⌝ ∗
              (⌜q.toNat % align = 0⌝ ∗
                (⌜q ≠ 0#64 ∧ align ∣ q.toNat ∧ 16 ∣ q.toNat ∧ q.toNat + new < 2 ^ 64 ∧
                    RustLayoutOk new align⌝ ∗
                  (mallocngHookBudgetPool M I γ mpl tp brkStart lim
                      (M.step (.realloc align old new) st) s1 ∗
                    ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                      I.BlockM γ q new (max align 16) ∗
                      (q ↦ₛ bs) ∗
                      memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R)))) := by
          dsimp [Slack]; sep_ac_rfl
        rw [hGoalEq, satisfies_pure_sepConj]
        refine ⟨allocCallPreserved_retHook_restore_x0 s1.mem q hacp1, ?_⟩
        rw [satisfies_pure_sepConj]
        refine ⟨Nat.mod_eq_zero_of_dvd hqAl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hqNe, hqAl, hq16, hqFit, ⟨hNewPos, hPow, hNewSum63⟩, hAlMax⟩, hpost1⟩
      | false =>
        simp only [hok, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hpost1
        rw [satisfies_pure_sepConj] at hpost1
        obtain ⟨hacp1', hpost1⟩ := hpost1
        have hacp1 : AllocCallPreserved s0 s1 := hacp1'
        have hPull :
            mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗
                (⌜q = 0#64⌝ ∗
                  (I.BlockM γ p old (max align 16) ∗
                    ((p ↦ₛ bs) ∗
                      (memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
                        (Slack ∗ R)))))) =
            ⌜q = 0#64⌝ ∗
              (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                  I.BlockM γ p old (max align 16) ∗
                  (p ↦ₛ bs) ∗
                  memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R)) := by
          dsimp [q, Slack]; sep_ac_rfl
        rw [hPull, satisfies_pure_sepConj] at hpost1
        obtain ⟨hq0, hpost1⟩ := hpost1
        have hqEq0 : q = 0 := hq0
        have hpoolSf := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hvm
        simp only [hqEq0, ↓reduceIte, hpoolSf, stackAt_allocHookStack_split s0.sp]
        have hGoalEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗
              mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
              (⌜NullAllowed new align⌝ ∗
                (I.BlockM γ p old (max align 16) ∗
                  ⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + old < 2 ^ 64 ∧
                    RustLayoutOk old align⌝) ∗
                (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length))) ∗ R =
            ⌜AllocCallPreserved s0 sf⌝ ∗
              (⌜NullAllowed new align⌝ ∗
                (⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + old < 2 ^ 64 ∧
                    RustLayoutOk old align⌝ ∗
                  (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                    ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                      I.BlockM γ p old (max align 16) ∗
                      (p ↦ₛ bs) ∗
                      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R)))) := by
          dsimp [Slack]; sep_ac_rfl
        rw [hGoalEq, satisfies_pure_sepConj]
        refine ⟨allocCallPreserved_retHook_restore_x0 s1.mem q hacp1, ?_⟩
        rw [satisfies_pure_sepConj]
        refine ⟨nullAllowed_of_not_le_max (of_decide_eq_false hok), ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hpNe, hpAl, hp16, hpFit, hOldLay⟩, hpost1⟩
    · exact False.elim (not_satisfies_false_sepConj hp)
    · exact False.elim (not_satisfies_false_sepConj he)
    · have hs1Bne : (s1.status != .Running) = true := by rw [hoom1]; rfl
      simp only [hs1Bne, ↓reduceIte]
      dsimp only [reallocHookBridgeSpec] at hoomSat
      rw [hx3, satisfies_pure_sepConj] at hoomSat
      obtain ⟨⟨hNotFit, hOomPres⟩, hRSat⟩ := hoomSat
      refine ⟨hkf1, hsym1, Or.inr (Or.inr (Or.inr ⟨hoom1, ?_⟩))⟩
      dsimp only [rustCliReallocBudgetSpecBase]
      rw [hevFast, satisfies_pure_sepConj]
      exact ⟨⟨fun h => hNotFit h.1, hOomPres⟩, Satisfies.of_sep_right hRSat⟩
  · rw [ite_neg hFast]
    have hevSlow : rustReallocEvents old new align = [.aligned (max align 8) new, .free align old] := by
      unfold rustReallocEvents; simp [hFast]
    obtain ⟨heffNat, heffMax, heffOk, _⟩ := effAlign_ok_props hPow hAlMax
    have hMax8_16 : max (max align 8) 16 = max align 16 := by omega
    set effAlign := BitVec.ofNat 64 (max align 8)
    set sCall := (s0.writeReg64 .x0 effAlign).writeReg64 .x1 newBv
    let OldFrame := I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ Slack
    have hvmCall : VmPreserved s0 sCall :=
      (vmPreserved_writeReg64 s0 .x0 effAlign).trans
        (vmPreserved_writeReg64 (s0.writeReg64 .x0 effAlign) .x1 newBv)
    have hpoolCall := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hvmCall
    have hpreA : sCall.mem ⊨
        (alignedAllocHookBridgeSpec M I γ mpl tp brkStart lim).pre
          (effAlign, newBv, s0.sp, st) sCall ∗ (OldFrame ∗ R) := by
      dsimp only [alignedAllocHookBridgeSpec]
      change s0.mem ⊨ _
      rw [hpoolCall, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp [sCall, State.writeReg64, State.readReg64, RegFile.read, RegFile.write],
        by simp [sCall, State.writeReg64, State.readReg64, RegFile.read, RegFile.write],
        rfl, heffMax⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by dsimp [OldFrame, Slack]; sep_ac_rfl)) hpre
    obtain ⟨hkf1, hsym1, hout1⟩ := alignedAlloc_budget_hookOk hS γ tp brkStart lim hPl
      (effAlign, newBv, s0.sp, st) (OldFrame ∗ R) sCall hrun hpreA hsp
    set s1 := mallocngHook mpl "aligned_alloc" sCall
    rcases hout1 with ⟨hret1, _, hpost1⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨hoom1, hoomSat⟩
    · have hs1Run : s1.status = .Running := hret1.2.2
      have hs1Bne : (s1.status != .Running) = false := by rw [hs1Run]; rfl
      simp only [hs1Bne, Bool.false_eq_true, ↓reduceIte]
      dsimp only [alignedAllocHookBridgeSpec] at hpost1
      rw [heffNat, hx3] at hpost1
      set q := s1.readReg64 .x0
      cases hok : mallocngAlignedAllocOk effAlign newBv with
      | false =>
        simp only [hok, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hpost1
        rw [satisfies_pure_sepConj] at hpost1
        obtain ⟨hacp1', hpost1⟩ := hpost1
        have hacp1 : AllocCallPreserved s0 s1 := hacp1'
        have hPull :
            mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗ (⌜q = 0#64⌝ ∗ (OldFrame ∗ R))) =
            ⌜q = 0#64⌝ ∗
              (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                  I.BlockM γ p old (max align 16) ∗
                  (p ↦ₛ bs) ∗
                  memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R)) := by
          dsimp [q, OldFrame, Slack]; sep_ac_rfl
        rw [hPull, satisfies_pure_sepConj] at hpost1
        obtain ⟨hq0, hpost1⟩ := hpost1
        rw [ite_pos hq0]
        set sKeep := restoreCallerRegs s0 s1
        set sf := retHook (fun st => (st.setMem s1.mem).writeReg64 .x0 0#64) sKeep
        have hsfX0 : sf.readReg64 .x0 = 0#64 := by
          simp [sf, retHook, State.setPC, State.setMem, State.writeReg64, State.readReg64,
            RegFile.read, RegFile.write]
        have hcc := cc_retHook_setMem_writeX0 (s0 := s0) (s := sKeep) s1.mem 0#64 rfl rfl rfl hs1Run
        have hvm : VmPreserved s1 sf :=
          (vmPreserved_restoreCallerRegs s0 s1).trans
            (vmPreserved_retHook_setMem_writeX0 (s := sKeep) 0#64 rfl)
        have hpoolSf := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hvm
        refine ⟨hkf1, hsym1, Or.inl ⟨hcc.1, hcc.2, ?_⟩⟩
        dsimp only [rustCliReallocBudgetSpecBase, mallocngHookRustCliAllocBudget, mallocngLiveM]
        rw [hevSlow, hsfX0]
        change s1.mem ⊨ _
        have h0Zero : ((0#64 : BitVec 64) = 0) = True := eq_self 0#64
        simp only [h0Zero, ↓reduceIte, hpoolSf, stackAt_allocHookStack_split s0.sp]
        have hGoalEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗
              mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
              (⌜NullAllowed new align⌝ ∗
                (I.BlockM γ p old (max align 16) ∗
                  ⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + old < 2 ^ 64 ∧
                    RustLayoutOk old align⌝) ∗
                (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length))) ∗ R =
            ⌜AllocCallPreserved s0 sf⌝ ∗
              (⌜NullAllowed new align⌝ ∗
                (⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + old < 2 ^ 64 ∧
                    RustLayoutOk old align⌝ ∗
                  (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s1 ∗
                    ((stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                      I.BlockM γ p old (max align 16) ∗
                      (p ↦ₛ bs) ∗
                      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R)))) := by
          dsimp [Slack]; sep_ac_rfl
        rw [hGoalEq, satisfies_pure_sepConj]
        refine ⟨allocCallPreserved_retHook_restore_x0 s1.mem 0#64 hacp1, ?_⟩
        rw [satisfies_pure_sepConj]
        refine ⟨nullAllowed_of_alignedAllocOk_false hx3 hPow hAlMax hok, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hpNe, hpAl, hp16, hpFit, hOldLay⟩, hpost1⟩
      | true =>
        simp only [hok, ↓reduceIte, hMax8_16, sepConj_assoc] at hpost1
        rw [satisfies_pure_sepConj] at hpost1
        obtain ⟨hacp1', hpost1⟩ := hpost1
        have hacp1 : AllocCallPreserved s0 s1 := hacp1'
        set st1 := M.step (.aligned (max align 8) new) st
        have hPull :
            mallocngHookBudgetPool M I γ mpl tp brkStart lim st1 s1 ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗
                (⌜q ≠ 0#64 ∧ max align 16 ∣ q.toNat ∧ q.toNat + new < 2 ^ 64⌝ ∗
                  (I.BlockM γ q new (max align 16) ∗
                    (memRegion q new ∗ (OldFrame ∗ R))))) =
            ⌜q ≠ 0#64 ∧ max align 16 ∣ q.toNat ∧ q.toNat + new < 2 ^ 64⌝ ∗
              (((p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
                  memRegion q new) ∗
                (mallocngHookBudgetPool M I γ mpl tp brkStart lim st1 s1 ∗
                  stackFrameAt s0.sp mallocngStackBytes ∗
                  I.BlockM γ p old (max align 16) ∗
                  I.BlockM γ q new (max align 16) ∗ Slack ∗ R)) := by
          dsimp [q, st1, OldFrame, Slack]; sep_ac_rfl
        rw [hPull, satisfies_pure_sepConj] at hpost1
        obtain ⟨⟨hqNe, hqMaxAl, hqFit⟩, hpost1⟩ := hpost1
        rw [ite_neg hqNe]
        set copyLen := min old new
        have hPrep := Satisfies.mono
          (sepConj_mono_left (copyPrep_entails p q bs old new copyLen
            (by omega) (Nat.min_le_left old new) (Nat.min_le_right old new) (by omega) (by omega)))
          hpost1
        simp only [sepExists_sepConj_left, satisfies_sepExists] at hPrep
        rcases hPrep with ⟨dstBs, midBs, hPrep⟩
        rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
          satisfies_pure_sepConj] at hPrep
        obtain ⟨⟨hdstLen, hmidLen⟩, hPrep⟩ := hPrep
        have hmRead : s1.mem ⊨ (p ↦ₛ (bs ++ midBs)) ∗
            ((q ↦ₛ dstBs) ∗
              memRegion (p + BitVec.ofNat 64 copyLen) (old - copyLen) ∗
              memRegion (q + BitVec.ofNat 64 copyLen) (new - copyLen) ∗
              mallocngHookBudgetPool M I γ mpl tp brkStart lim st1 s1 ∗
              stackFrameAt s0.sp mallocngStackBytes ∗
              I.BlockM γ p old (max align 16) ∗
              I.BlockM γ q new (max align 16) ∗ Slack ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hPrep
        have hsrcEq : s1.mem.readBytes p copyLen = bs ++ midBs := by
          rw [← hmidLen]
          exact ((IsBlock.pointsToBytes p (bs ++ midBs)).read hmRead).2
        have hmDstReg : s1.mem ⊨ memRegion q (bs ++ midBs).length ∗
            ((p ↦ₛ (bs ++ midBs)) ∗
              memRegion (p + BitVec.ofNat 64 copyLen) (old - copyLen) ∗
              memRegion (q + BitVec.ofNat 64 copyLen) (new - copyLen) ∗
              mallocngHookBudgetPool M I γ mpl tp brkStart lim st1 s1 ∗
              stackFrameAt s0.sp mallocngStackBytes ∗
              I.BlockM γ p old (max align 16) ∗
              I.BlockM γ q new (max align 16) ∗ Slack ∗ R) := by
          have hqEnt : (q ↦ₛ dstBs) ⊢ memRegion q (bs ++ midBs).length := by
            rw [hmidLen, ← hdstLen]; exact pointsToBytes_entails_memRegion q dstBs
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hqEnt)
            (Entails.of_eq (by sep_ac_rfl))) hPrep
        have hbmFit : (bs ++ midBs).length ≤ 2 ^ 64 := by rw [hmidLen]; omega
        set mCopy := s1.mem.writeBytes q (s1.mem.readBytes p copyLen)
        have hmCopyEq : mCopy = s1.mem.writeBytes q (bs ++ midBs) := by
          dsimp [mCopy]; rw [hsrcEq]
        have hkfCopy : s1.mem.KeepsFrozen mCopy := by
          rw [hmCopyEq]
          exact keepsFrozen_writeBytes_of_memRegion (bs ++ midBs) hbmFit hmDstReg
        have hsatCopy0 : mCopy ⊨
            ((q ↦ₛ (bs ++ midBs)) ∗ (p ↦ₛ (bs ++ midBs)) ∗
              memRegion (p + BitVec.ofNat 64 copyLen) (old - copyLen) ∗
              memRegion (q + BitVec.ofNat 64 copyLen) (new - copyLen)) ∗
            (mallocngHookBudgetPool M I γ mpl tp brkStart lim st1 s1 ∗
              stackFrameAt s0.sp mallocngStackBytes ∗
              I.BlockM γ p old (max align 16) ∗
              I.BlockM γ q new (max align 16) ∗ Slack ∗ R) := by
          rw [hmCopyEq]
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
            (satisfies_writeBytes (bs ++ midBs) hbmFit hmDstReg)
        have hsatCopy := Satisfies.mono
          (sepConj_mono_left (copyFinish_entails p q bs midBs old new copyLen
            hmidLen (Nat.min_le_left old new) (Nat.min_le_right old new) (by omega) (by omega)))
          hsatCopy0
        set sFreeCall := ((restoreCallerRegs s0 s1).setMem mCopy).writeReg64 .x0 p
        let NewFrame := I.BlockM γ q new (max align 16) ∗ (q ↦ₛ bs) ∗
          memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ Slack
        have hmCopyPerm : mCopy.perm = s1.mem.perm :=
          Memory.perm_writeBytes s1.mem q (s1.mem.readBytes p copyLen)
        have hvmSetCopy : VmPreserved (restoreCallerRegs s0 s1)
            ((restoreCallerRegs s0 s1).setMem mCopy) :=
          ⟨⟨rfl, rfl, rfl⟩, rfl, fun a => by
            dsimp [State.setMem, restoreCallerRegs]
            exact congrFun hmCopyPerm a, fun _ _ _ => rfl⟩
        have hvmFreeCall : VmPreserved s1 sFreeCall :=
          (vmPreserved_restoreCallerRegs s0 s1).trans
            (hvmSetCopy.trans
              (vmPreserved_writeReg64 ((restoreCallerRegs s0 s1).setMem mCopy) .x0 p))
        have hpoolFreeCall := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim
          st1 hvmFreeCall
        have hsFreeRun : sFreeCall.status = .Running := hs1Run
        have hsFreeSp : sFreeCall.spAligned = true := hsp
        have hpreF : sFreeCall.mem ⊨
            (freeHookBridgeSpec M I γ mpl tp brkStart lim).pre
              (p, old, align, s0.sp, st1) sFreeCall ∗ (NewFrame ∗ R) := by
          dsimp only [freeHookBridgeSpec]
          simp only [hpNe, ↓reduceIte, sepConj_assoc]
          change mCopy ⊨ _
          rw [hpoolFreeCall, satisfies_pure_sepConj]
          refine ⟨⟨by simp [sFreeCall, State.setMem, State.writeReg64, State.readReg64, RegFile.read, RegFile.write],
            by simp [sFreeCall, State.setMem, State.writeReg64, restoreCallerRegs], hp16, hpFit⟩, ?_⟩
          exact Satisfies.mono (Entails.of_eq (by dsimp [NewFrame, Slack]; sep_ac_rfl)) hsatCopy
        obtain ⟨hkf2, hsym2, hout2⟩ := free_budget_hookOk hS γ tp brkStart lim hPl
          (p, old, align, s0.sp, st1) (NewFrame ∗ R) sFreeCall hsFreeRun hpreF hsFreeSp
        set s2 := mallocngHook mpl "free" sFreeCall
        have hkf02 : s0.mem.KeepsFrozen s2.mem := (hkf1.trans hkfCopy).trans hkf2
        have hsym02 : s2.symtab = s0.symtab := hsym2.trans hsym1
        rcases hout2 with ⟨hret2, _, hpost2⟩ | ⟨_, hp2⟩ | ⟨_, _, he2⟩ | ⟨_, ho2⟩
        · have hs2Run : s2.status = .Running := hret2.2.2
          have hs2Bne : (s2.status != .Running) = false := by rw [hs2Run]; rfl
          simp only [hs2Bne, Bool.false_eq_true, ↓reduceIte]
          dsimp only [freeHookBridgeSpec] at hpost2
          rw [beq_eq_false_iff_ne.mpr hpNe] at hpost2
          simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hpost2
          rw [satisfies_pure_sepConj] at hpost2
          obtain ⟨hacp2', hpost2⟩ := hpost2
          have hacpFreeCall : AllocCallPreserved s0 sFreeCall := by
            rcases hacp1 with ⟨hfs, htr, hsig, htp, hbrkS, horc, hsym⟩
            exact ⟨hfs, htr, hsig, htp, hbrkS, horc, hsym⟩
          have hacp02 : AllocCallPreserved s0 s2 :=
            allocCallPreserved_trans hacpFreeCall hacp2'
          set sKeep2 := restoreCallerRegs s0 s2
          set sf := retHook (fun st => (st.setMem s2.mem).writeReg64 .x0 q) sKeep2
          have hsfX0 : sf.readReg64 .x0 = q := by
            simp [sf, retHook, State.setPC, State.setMem, State.writeReg64, State.readReg64,
              RegFile.read, RegFile.write]
          have hcc := cc_retHook_setMem_writeX0 (s0 := s0) (s := sKeep2) s2.mem q rfl rfl rfl hs2Run
          have hvm2 : VmPreserved s2 sf :=
            (vmPreserved_restoreCallerRegs s0 s2).trans
              (vmPreserved_retHook_setMem_writeX0 (s := sKeep2) q rfl)
          have hpoolSf := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim
            (M.step (.free align old) st1) hvm2
          have hqNe0 : q ≠ 0 := hqNe
          have hqAl : align ∣ q.toNat := Nat.dvd_trans hAlDvdMax hqMaxAl
          have hq16 : 16 ∣ q.toNat := Nat.dvd_trans h16DvdMax hqMaxAl
          refine ⟨hkf02, hsym02, Or.inl ⟨hcc.1, hcc.2, ?_⟩⟩
          dsimp only [rustCliReallocBudgetSpecBase, mallocngHookRustCliAllocBudget, mallocngLiveM]
          rw [hevSlow, hsfX0]
          change s2.mem ⊨ _
          have hStep2 : M.stepEvents [.aligned (max align 8) new, .free align old] st =
              M.step (.free align old) st1 := rfl
          simp only [hqNe0, ↓reduceIte, hStep2,
            hpoolSf, stackAt_allocHookStack_split s0.sp]
          have hGoalEq :
              (⌜AllocCallPreserved s0 sf⌝ ∗
                mallocngHookBudgetPool M I γ mpl tp brkStart lim
                  (M.step (.free align old) st1) s2 ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ Slack) ∗
                (⌜q.toNat % align = 0⌝ ∗
                  (I.BlockM γ q new (max align 16) ∗
                    ⌜q ≠ 0#64 ∧ align ∣ q.toNat ∧ 16 ∣ q.toNat ∧ q.toNat + new < 2 ^ 64 ∧
                      RustLayoutOk new align⌝) ∗
                  (q ↦ₛ bs) ∗
                  memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length))) ∗ R =
              ⌜AllocCallPreserved s0 sf⌝ ∗
                (⌜q.toNat % align = 0⌝ ∗
                  (⌜q ≠ 0#64 ∧ align ∣ q.toNat ∧ 16 ∣ q.toNat ∧ q.toNat + new < 2 ^ 64 ∧
                      RustLayoutOk new align⌝ ∗
                    (mallocngHookBudgetPool M I γ mpl tp brkStart lim
                        (M.step (.free align old) st1) s2 ∗
                      (stackFrameAt s0.sp mallocngStackBytes ∗ (NewFrame ∗ R))))) := by
            dsimp [NewFrame, Slack]; sep_ac_rfl
          rw [hGoalEq, satisfies_pure_sepConj]
          refine ⟨allocCallPreserved_retHook_restore_x0 s2.mem q hacp02, ?_⟩
          rw [satisfies_pure_sepConj]
          refine ⟨Nat.mod_eq_zero_of_dvd hqAl, ?_⟩
          rw [satisfies_pure_sepConj]
          exact ⟨⟨hqNe, hqAl, hq16, hqFit, ⟨hNewPos, hPow, hNewSum63⟩, hAlMax⟩, hpost2⟩
        · exact False.elim (not_satisfies_false_sepConj hp2)
        · exact False.elim (not_satisfies_false_sepConj he2)
        · exact False.elim (not_satisfies_false_sepConj ho2)
    · exact False.elim (not_satisfies_false_sepConj hp)
    · exact False.elim (not_satisfies_false_sepConj he)
    · have hs1Bne : (s1.status != .Running) = true := by rw [hoom1]; rfl
      simp only [hs1Bne, ↓reduceIte]
      dsimp only [alignedAllocHookBridgeSpec] at hoomSat
      rw [heffNat, hx3, satisfies_pure_sepConj] at hoomSat
      obtain ⟨⟨hNotFit, hOomPres⟩, hRSat⟩ := hoomSat
      refine ⟨hkf1, hsym1, Or.inr (Or.inr (Or.inr ⟨hoom1, ?_⟩))⟩
      dsimp only [rustCliReallocBudgetSpecBase]
      rw [hevSlow, satisfies_pure_sepConj]
      exact ⟨⟨fun h => hNotFit ⟨heffOk, h.1⟩, hOomPres⟩, Satisfies.of_sep_right hRSat⟩

/-- `(γ, tp)`-independent `mallocng` fallback for `<String as Clone>::clone`. -/
noncomputable def f3StringCloneFallback (mpl : Obj.MultiPlacement) : State → State :=
  keepFsTrace (stringCloneHookMallocng mpl)

theorem f3StringCloneFallback_fs (mpl : Obj.MultiPlacement) (s : State) :
    (f3StringCloneFallback mpl s).fs = s.fs :=
  keepFsTrace_fs _ s

theorem f3StringCloneFallback_fsT (mpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (f3StringCloneFallback mpl) :=
  keepFsTrace_fsT _

private theorem cloneSrc_of_vecGhostAt_local (A0 : RustAlloc) {s : State} {p : BitVec 64}
    {g : VecGhost} {Extra : SepProp}
    (hx0 : s.readReg64 .x0 = p)
    (hmem : s.mem ⊨ vecGhostAt A0 g p ∗ Extra) :
    cloneSrc s = g.bytes ∧ g.bytes.length < 2 ^ 63 := by
  have hm' : s.mem ⊨ ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (vecHeader p g.cap g.ptr (BitVec.ofNat 64 g.bytes.length) ∗
        (if g.cap = 0 then emp
         else A0.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
           memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗
        Extra) :=
    Satisfies.mono (Entails.of_eq (by unfold vecGhostAt vecU8At; sep_ac_rfl)) hmem
  rw [satisfies_pure_sepConj] at hm'
  rcases hm' with ⟨⟨hlen_le, hcap_lt, _⟩, hm⟩
  unfold vecHeader at hm
  have hlen_lt : g.bytes.length < 2 ^ 63 := by omega
  have hlen_nat : (BitVec.ofNat 64 g.bytes.length).toNat = g.bytes.length :=
    Nat.mod_eq_of_lt (by omega)
  have hm_ptr : s.mem ⊨ ((p + 8#64) ↦₆₄ g.ptr) ∗
      ((p ↦₆₄ g.cap) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
        (if g.cap = 0 then emp
         else A0.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
           memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗
        Extra) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  have hread_ptr : s.mem.read64 (p + 8#64) = g.ptr :=
    (IsBlock.pointsTo64 (p + 8#64) g.ptr).read hm_ptr
  have hm_len : s.mem ⊨ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      ((p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗
        (if g.cap = 0 then emp
         else A0.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
           memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗
        Extra) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  have hread_len : s.mem.read64 (p + 16#64) = BitVec.ofNat 64 g.bytes.length :=
    (IsBlock.pointsTo64 (p + 16#64) (BitVec.ofNat 64 g.bytes.length)).read hm_len
  refine ⟨?_, hlen_lt⟩
  unfold cloneSrc
  dsimp only
  rw [hx0, hread_ptr, hread_len, hlen_nat]
  by_cases hcap0 : g.cap = 0
  · have hcap0_nat : g.cap.toNat = 0 := by rw [hcap0]; rfl
    have hlen0 : g.bytes.length = 0 := by omega
    rw [List.eq_nil_of_length_eq_zero hlen0]
    rfl
  · simp only [hcap0, ↓reduceIte] at hm
    have hm_bs : s.mem ⊨ (g.ptr ↦ₛ g.bytes) ∗
        ((p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗
          ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
          A0.live g.ptr g.cap.toNat 1 ∗
          memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) ∗
          Extra) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    exact ((IsBlock.pointsToBytes g.ptr g.bytes).read hm_bs).2

/-- `stringCloneHookMallocng mpl` satisfies `stringCloneNoOomSpec` over any `(M, I)` with
    `MallocngCostModelSound M I` (`AllocCallPreserved s0 sf` in postcondition). -/
theorem stringCloneHookMallocng_noOom_ok [LibsignalPlacement] {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) :
    HookOk (stringCloneHookMallocng mpl)
      (stringCloneNoOomSpec M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim) := by
  let A := mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart
  rintro ⟨p, ret, g, st⟩ R s0 hrun hpre hsp
  have hpre' := hpre
  dsimp only [stringCloneNoOomSpec, A, mallocngHookRustCliAllocBudget] at hpre'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx8, hFitEvs, _hlr⟩, hmem⟩
  obtain ⟨hsrc0, hlen_lt⟩ := cloneSrc_of_vecGhostAt_local (A0 := A.repAlloc) hx0
    (Satisfies.mono (Entails.of_eq (by dsimp [A, mallocngHookRustCliAllocBudget]; sep_ac_rfl)) hmem)
  unfold stringCloneHookMallocng
  dsimp only
  rw [hsrc0]
  by_cases hz : (g.bytes.length == 0) = true
  · simp only [hz, ↓reduceIte]
    have hlen0 : g.bytes.length = 0 := beq_iff_eq.mp hz
    have hbs0 : g.bytes = [] := List.eq_nil_of_length_eq_zero hlen0
    have hevs0 : stringCloneEvents g = [] := by
      unfold stringCloneEvents; simp [hlen0]
    have hmem_ret : s0.mem ⊨ memRegion ret 24 ∗
        (vecGhostAt A.repAlloc g p ∗
          mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
          stackAt s0.sp extHookStack ∗ R) :=
      Satisfies.mono (Entails.of_eq (by dsimp [A, mallocngHookRustCliAllocBudget]; sep_ac_rfl)) hmem
    obtain ⟨hkf_w, hperm_w, hvec⟩ := write_empty_vecU8 (A := A.repAlloc) hmem_ret
    let mf := writeVecHeader s0.mem ret 0#64 1#64 0#64
    rw [show retHook (fun s => s.setMem (writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64)) s0 =
        retHook (fun s => s.setMem mf) s0 by simp [retHook, hx8, mf]]
    obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf rfl rfl rfl hrun
    refine ⟨hkf_w, rfl, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
    dsimp only [stringCloneNoOomSpec]
    have hpool_f :
        A.pool lim (M.stepEvents (stringCloneEvents g) st) (retHook (fun s => s.setMem mf) s0) =
          mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 := by
      rw [hevs0]
      exact mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st
        (vmPreserved_retHook_setMem hperm_w)
    have hacp_f : AllocCallPreserved s0 (retHook (fun s => s.setMem mf) s0) := by
      cases s0; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [hpool_f, hbs0, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hacp_f, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hvec⟩
  · simp only [Bool.eq_false_iff.mpr hz, Bool.false_eq_true, ↓reduceIte]
    have hne0 : g.bytes.length ≠ 0 := fun h => hz (beq_iff_eq.mpr h)
    have hpos : 1 ≤ g.bytes.length := Nat.pos_of_ne_zero hne0
    have hevs1 : stringCloneEvents g = rustAllocEvents g.bytes.length 1 := by
      unfold stringCloneEvents; simp [hne0]
    rw [hevs1] at hFitEvs
    have hFit : LibsignalBinary.Heap.FitsEvent M lim st (.alloc g.bytes.length) :=
      fitsEvent_of_fitsAlloc1 hpos hFitEvs
    have hmem0 : s0.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗ stackAt s0.sp extHookStack ∗
          (vecGhostAt A.repAlloc g p ∗ memRegion ret 24)) ∗ R :=
      Satisfies.mono (Entails.of_eq (by dsimp [A, mallocngHookRustCliAllocBudget]; sep_ac_rfl)) hmem
    refine stepRustAlloc1_budget_cps hS hPl false 48 g.bytes.length
      (by decide) (by decide) hFit hrun rfl rfl rfl hsp
      (Memory.KeepsFrozen.refl _) rfl (allocCallPreserved_refl s0) hmem0 _ ?_
    intro s1 q hq_ne hq_al16 hq_fit64 hs1_run hs1_sp hs1_regs hs1_vregs hkf1 hsym1 hpres1 hmem1
    simp only [Bool.false_eq_true, ↓reduceIte] at hmem1
    have hs1_x0 : s1.readReg64 .x0 = p := by simp [State.readReg64, hs1_regs] at hx0 ⊢; exact hx0
    have hs1_x8 : s1.readReg64 .x8 = ret := by simp [State.readReg64, hs1_regs] at hx8 ⊢; exact hx8
    obtain ⟨hsrc1, _⟩ := cloneSrc_of_vecGhostAt_local (A0 := A.repAlloc) hs1_x0
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1)
    rw [hsrc1]
    obtain ⟨hkf_w, hperm_w, hvec⟩ :=
      write_vecU8_from_alloc hS (mpl := mpl) (tp := tp) (brkStart := brkStart)
        (bs := g.bytes) hq_ne hq_al16 hq_fit64 hpos hlen_lt (Nat.le_refl _)
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1 : s1.mem ⊨
          I.BlockM γ q g.bytes.length 16 ∗ memRegion q g.bytes.length ∗ memRegion ret 24 ∗
            (vecGhostAt A.repAlloc g p ∗
              mallocngHookBudgetPool M I γ mpl tp brkStart lim
                (M.step (.alloc g.bytes.length) st) s1 ∗
              stackAt s0.sp extHookStack ∗ R))
    let mf := writeVecHeader (s1.mem.writeBytes q g.bytes) ret
      (BitVec.ofNat 64 g.bytes.length) q (BitVec.ofNat 64 g.bytes.length)
    rw [show retHook (fun s => s.setMem (writeVecHeader (s.mem.writeBytes q g.bytes)
        (s.readReg64 .x8) (BitVec.ofNat 64 g.bytes.length) q (BitVec.ofNat 64 g.bytes.length))) s1 =
        retHook (fun s => s.setMem mf) s1 by simp [retHook, hs1_x8, mf]]
    obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf hs1_regs hs1_vregs hs1_sp hs1_run
    refine ⟨hkf1.trans hkf_w, hsym1, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
    dsimp only [stringCloneNoOomSpec]
    have hev_step : M.stepEvents (stringCloneEvents g) st =
        M.step (.alloc g.bytes.length) st := by
      rw [hevs1, rustAllocEvents_one hpos]; rfl
    have hpool_f :
        A.pool lim (M.stepEvents (stringCloneEvents g) st)
          (retHook (fun s => s.setMem mf) s1) =
          mallocngHookBudgetPool M I γ mpl tp brkStart lim
            (M.step (.alloc g.bytes.length) st) s1 := by
      dsimp only [A, mallocngHookRustCliAllocBudget]
      rw [hev_step]
      exact mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim _
        (vmPreserved_retHook_setMem hperm_w)
    have hacp_ret : AllocCallPreserved s1 (retHook (fun s => s.setMem mf) s1) := by
      cases s1; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hacp_f : AllocCallPreserved s0 (retHook (fun s => s.setMem mf) s1) :=
      allocCallPreserved_trans hpres1 hacp_ret
    rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hacp_f, Satisfies.mono (Entails.of_eq (by dsimp [A]; sep_ac_rfl)) hvec⟩

theorem specPreservesFsTraceExact_stringCloneNoOom [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BitVec 64 × BitVec 64 × VecGhost × M.σ) (R : SepProp) (s0 sf : State)
    (hout : SubroutineOutcome (stringCloneNoOomSpec M A lim) x R s0 sf) :
    sf.fs = s0.fs ∧ sf.trace = s0.trace := by
  rcases x with ⟨p, ret, g, st⟩
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · dsimp only [stringCloneNoOomSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hpost.1.1, hpost.1.2.1⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

theorem specPreservesFsTrace_stringCloneNoOom [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    SpecPreservesFsTrace (stringCloneNoOomSpec M A lim) := by
  intro x R s0 sf hout
  have h := specPreservesFsTraceExact_stringCloneNoOom A lim x R s0 sf hout
  exact ⟨h.1, FsTraced.of_eq h.2 (congrArg FsState.files h.1)⟩

theorem f3StringCloneFallback_ok_noOom [LibsignalPlacement] {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {mpl : Obj.MultiPlacement} (brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk (f3StringCloneFallback mpl)
      (stringCloneNoOomSpec M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim) :=
  keepFsTrace_ok (stringCloneHookMallocng_noOom_ok hS γ tp brkStart lim hPl)
    (fun x R s0 hout => specPreservesFsTraceExact_stringCloneNoOom _ lim x R s0 _ hout)

theorem hookOk_stringCloneBudget_of_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {f : State → State}
    (hf : HookOk f (stringCloneNoOomSpec M A lim)) :
    HookOk f (stringCloneBudgetSpec M A lim) := by
  rintro ⟨p, ret, g, st⟩ R s0 hrun hpre hsp
  dsimp only [stringCloneBudgetSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hEnv, hlr⟩, hrest⟩
  have hFit : FitsEvents M lim st (stringCloneEvents g) :=
    fitsEvents_stringClone_of_fitsEnv M lim st g hEnv
  have hpreN : s0.mem ⊨ (stringCloneNoOomSpec M A lim).pre (p, ret, g, st) s0 ∗ R := by
    dsimp only [stringCloneNoOomSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8, hFit, hlr⟩, hrest⟩
  obtain ⟨hkf, hsym, hout⟩ := hf (p, ret, g, st) R s0 hrun hpreN hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [stringCloneNoOomSpec] at hpost
    dsimp only [stringCloneBudgetSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨stringCloneEvents g, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.2.1, stringCloneEnv_events g⟩, hpost.2⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

theorem f3DeallocFallback_ok_fine
    {mmpl : Obj.MultiPlacement} (brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk (f3DeallocFallback mmpl)
      (rustCliDeallocBudgetSpecBase fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim) :=
  f3DeallocFallback_ok fineCostModelSound brkStart lim hPl γ tp

theorem f3AllocFallback_ok_fine
    {mmpl : Obj.MultiPlacement} (brkStart : BitVec 64) (lim : BudgetLimits) (zeroed : Bool)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk (f3AllocFallback mmpl zeroed)
      (rustCliAllocBudgetSpecBase fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim zeroed) :=
  f3AllocFallback_ok fineCostModelSound brkStart lim zeroed hPl γ tp

theorem f3ReallocFallback_ok_fine
    {mmpl : Obj.MultiPlacement} (brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk (f3ReallocFallback mmpl)
      (rustCliReallocBudgetSpecBase fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim) :=
  f3ReallocFallback_ok fineCostModelSound brkStart lim hPl γ tp

theorem f3StringCloneFallback_ok_noOom_fine [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} (brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk (f3StringCloneFallback mmpl)
      (stringCloneNoOomSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim) :=
  f3StringCloneFallback_ok_noOom fineCostModelSound brkStart lim hPl γ tp

theorem f3StringCloneFallback_ok_budget_fine [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} (brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk (f3StringCloneFallback mmpl)
      (stringCloneBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim) :=
  hookOk_stringCloneBudget_of_noOom (f3StringCloneFallback_ok_noOom_fine brkStart lim hPl γ tp)

/-! ## `(γ, tp)`-Independent `readStdin` Fallback and Ghost Hook -/

private theorem stackAt_le_two_pow_64_local {m : Memory} {p sp : BitVec 64} {n stk : Nat}
    {R : SepProp} (hn : 0 < n) (hstk : 0 < stk)
    (h : m ⊨ memRegion p n ∗ (stackAt sp stk ∗ R)) : stk ≤ 2 ^ 64 := by
  have hdisj := (IsBlock.memRegion p n).disjoint
    (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk) hn hstk h
  have hlt := (p - (sp - BitVec.ofNat 64 stk)).isLt
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hdisj.2 hlt)

private theorem write_ioVecErr_local {m : Memory} {ret : BitVec 64} {Frame : SepProp}
    (hmem : m ⊨ memRegion ret 24 ∗ Frame) :
    let mf := m.write64 ret 0xFFFFFFFFFFFFFFFF#64
    m.KeepsFrozen mf ∧ (mf.perm = m.perm) ∧
      (mf ⊨ ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (ret + 8#64) 16) ∗ Frame) := by
  have hsplit : memRegion ret 24 =
      (∃∗ w0 : BitVec 64, ret ↦₆₄ w0) ∗ memRegion (ret + 8#64) 16 := by
    rw [memRegion_split' (n := 8) (k := 16) rfl rfl (by decide), memRegion_eight ret]
  rw [hsplit, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hmem
  rcases hmem with ⟨w0, hmem0'⟩
  refine ⟨keepsFrozen_write64_of_pointsTo64 0xFFFFFFFFFFFFFFFF#64 hmem0',
    Memory.perm_write64 m ret 0xFFFFFFFFFFFFFFFF#64, ?_⟩
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
    (satisfies_write64_of_pointsTo64 0xFFFFFFFFFFFFFFFF#64 hmem0')

/-- `(γ, tp)`-independent `mallocng` fallback for `signal_session_io::read_stdin` (`ReadStdinBoundedEnv`). -/
noncomputable def f3ReadStdinFallbackRaw (mmpl : Obj.MultiPlacement) (s0 : State) : State :=
  match cliIo.stdin s0.fs with
  | none => s0
  | some bs =>
    if bs.length ≤ 1048576 then
      if bs.length = 0 then
        retHook (fun s => s.setMem (writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64)) s0
      else
        stepRustAlloc1 mmpl false 0 bs.length
          (fun s1 p =>
            retHook (fun s => s.setMem
              (writeVecHeader (s.mem.writeBytes p bs) (s.readReg64 .x8)
                (BitVec.ofNat 64 bs.length) p (BitVec.ofNat 64 bs.length))) s1)
          s0
    else
      retHook (fun s => s.setMem (s.mem.write64 (s.readReg64 .x8) 0xFFFFFFFFFFFFFFFF#64)) s0

/-- Closed `(γ, tp)`-independent `read_stdin` fallback wrapped with `keepFsTrace`. -/
noncomputable def f3ReadStdinFallback (mmpl : Obj.MultiPlacement) : State → State :=
  keepFsTrace (f3ReadStdinFallbackRaw mmpl)

@[simp]
theorem f3ReadStdinFallback_fs (mmpl : Obj.MultiPlacement) (s0 : State) :
    (f3ReadStdinFallback mmpl s0).fs = s0.fs :=
  keepFsTrace_fs (f3ReadStdinFallbackRaw mmpl) s0

theorem f3ReadStdinFallback_fsT (mmpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (f3ReadStdinFallback mmpl) :=
  keepFsTrace_fsT (f3ReadStdinFallbackRaw mmpl)

/-- `f3ReadStdinFallback mmpl` satisfies `readStdinSpecOfPlaced cliIo ... ReadStdinBoundedEnv`
    at `fineHookRustCliAllocBudget γ mmpl tp brkStart` for every `(γ, tp)` and `extHookStack ≤ stk`. -/
theorem f3ReadStdinFallback_ok_bounded [LibsignalPlacement]
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) {stk : Nat}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hstk : extHookStack ≤ stk) :
    HookOk (f3ReadStdinFallback mmpl)
      (readStdinSpecOfPlaced cliIo (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk
        ReadStdinBoundedEnv) := by
  let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  have hMain :
      (s0.mem.KeepsFrozen (f3ReadStdinFallbackRaw mmpl s0).mem ∧
        (f3ReadStdinFallbackRaw mmpl s0).symtab = s0.symtab ∧
        SubroutineOutcome (readStdinSpecOfPlaced cliIo A lim stk ReadStdinBoundedEnv) (x, st) R s0
          (f3ReadStdinFallbackRaw mmpl s0)) ∧
      (f3ReadStdinFallbackRaw mmpl s0).fs = s0.fs ∧
      (f3ReadStdinFallbackRaw mmpl s0).trace = s0.trace := by
    dsimp only [readStdinSpecOfPlaced, A, fineHookRustCliAllocBudget,
      mallocngHookRustCliAllocBudget] at hpre
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx8, hstdin, hFitEnv, _hlr⟩, hmem⟩
    have hmem_disj : s0.mem ⊨ memRegion x.ret 24 ∗
        (stackAt s0.sp stk ∗
          (mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim st s0 ∗ R)) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    have hpos_ext : 0 < extHookStack := by unfold extHookStack; omega
    have hstk64 : stk ≤ 2 ^ 64 :=
      stackAt_le_two_pow_64_local (by omega) (Nat.lt_of_lt_of_le hpos_ext hstk) hmem_disj
    have hsplit_stk : stackAt s0.sp stk =
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
          stackAt s0.sp extHookStack := by
      have hs := stackAt_split_bottom s0.sp extHookStack (stk - extHookStack) (by omega)
      rwa [Nat.add_sub_of_le hstk] at hs
    let SlackStk : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack)
    unfold f3ReadStdinFallbackRaw
    rw [hstdin]
    dsimp only []
    by_cases hle : x.bs.length ≤ 1048576
    · simp only [hle, ↓reduceIte]
      have hcap_eq : CryptoVerification.SignalSession.stdinCapBytes = 1048576 := by decide
      have hr_ok : readStdinResult x.bs = .ok x.bs := by
        unfold readStdinResult; rw [hcap_eq]; exact ite_pos hle
      by_cases hbs0 : x.bs.length = 0
      · simp only [hbs0, ↓reduceIte]
        have hbs_nil : x.bs = [] := List.eq_nil_of_length_eq_zero hbs0
        have hmem_ret : s0.mem ⊨ memRegion x.ret 24 ∗
            (stackAt s0.sp stk ∗
              mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim st s0 ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
        obtain ⟨hkf_w, hperm_w, hemp_mem⟩ := write_empty_vecU8 (A := A.repAlloc) hmem_ret
        let mf := writeVecHeader s0.mem x.ret 0#64 1#64 0#64
        rw [show retHook (fun s => s.setMem (writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64)) s0 =
            retHook (fun s => s.setMem mf) s0 by simp [retHook, hx8, mf]]
        obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf rfl rfl rfl hrun
        refine ⟨⟨hkf_w, rfl, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩, rfl, rfl⟩
        have henv0 : ReadStdinBoundedEnv x.bs [] :=
          readStdinBoundedEnv_of_hook_le hle (by simp [allocBytes1Events, hbs_nil])
        have hpool_f :
            A.pool lim (fineCostModel.stepEvents [] st) (retHook (fun s => s.setMem mf) s0) =
              mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim st s0 :=
          mallocngHookBudgetPool_transport fineCostModel fineCostModelIface γ mmpl tp brkStart lim st
            (vmPreserved_retHook_setMem hperm_w)
        dsimp only [readStdinSpecOfPlaced]
        rw [sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨[], ?_⟩
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨henv0, ?_⟩
        rw [sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨.ok [], ?_⟩
        rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨rfl, by rw [hr_ok, hbs_nil], rfl⟩,
          Satisfies.mono (Entails.of_eq (by dsimp only [ioVecAt, getResultAt])) hemp_mem⟩
      · simp only [hbs0, ↓reduceIte]
        have hpos : 1 ≤ x.bs.length := Nat.pos_of_ne_zero hbs0
        have hcap_lt : x.bs.length < 2 ^ 63 := by omega
        have henv_ab : ReadStdinBoundedEnv x.bs (rustAllocEvents x.bs.length 1) :=
          readStdinBoundedEnv_of_hook_le hle (by simp [allocBytes1Events, hbs0])
        have hFit : FitsEvent fineCostModel lim st (.alloc x.bs.length) :=
          fitsEvent_of_fitsAlloc1 hpos (hFitEnv (rustAllocEvents x.bs.length 1) henv_ab)
        have hmem0 : s0.mem ⊨
            (mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim st s0 ∗
              stackAt s0.sp extHookStack ∗
              (SlackStk ∗ memRegion x.ret 24)) ∗ R := by
          dsimp only [SlackStk]
          rw [hsplit_stk] at hmem
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
        let kBody : State → BitVec 64 → State := fun s1 p =>
          retHook (fun s => s.setMem
            (writeVecHeader (s.mem.writeBytes p x.bs) (s.readReg64 .x8)
              (BitVec.ofNat 64 x.bs.length) p (BitVec.ofNat 64 x.bs.length))) s1
        let specStrong : Spec (ReadStdinGhost × fineCostModel.σ) :=
          { (readStdinSpecOfPlaced cliIo A lim stk ReadStdinBoundedEnv) with
            post := fun y s_init sf =>
              ⌜sf.fs = s_init.fs ∧ sf.trace = s_init.trace⌝ ∗
                (readStdinSpecOfPlaced cliIo A lim stk ReadStdinBoundedEnv).post y s_init sf }
        have hcps := stepRustAlloc1_budget_cps fineCostModelSound hPl
          (spec := specStrong) (x := (x, st)) (R := R)
          (Rest := SlackStk ∗ memRegion x.ret 24)
          false 0 x.bs.length (by decide) (by decide) hFit hrun rfl rfl rfl hsp
          (Memory.KeepsFrozen.refl _) rfl (allocCallPreserved_refl s0) hmem0 kBody
        have hk_ok :
            s0.mem.KeepsFrozen (stepRustAlloc1 mmpl false 0 x.bs.length kBody s0).mem ∧
              (stepRustAlloc1 mmpl false 0 x.bs.length kBody s0).symtab = s0.symtab ∧
              SubroutineOutcome specStrong (x, st) R s0
                (stepRustAlloc1 mmpl false 0 x.bs.length kBody s0) := by
          refine hcps ?_
          intro s1 p hp_ne hp_al16 hp_fit64 hs1_run hs1_sp hs1_regs hs1_vregs hkf1 hsym1 hpres1 hmem1
          simp only [Bool.false_eq_true, ↓reduceIte] at hmem1
          have hs1_x8 : s1.readReg64 .x8 = x.ret := by
            simp [State.readReg64, hs1_regs] at hx8 ⊢; exact hx8
          have hm_prep : s1.mem ⊨
              fineCostModelIface.BlockM γ p x.bs.length 16 ∗ memRegion p x.bs.length ∗ memRegion x.ret 24 ∗
                (SlackStk ∗
                  mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim
                    (fineCostModel.step (.alloc x.bs.length) st) s1 ∗
                  stackAt s0.sp extHookStack ∗ R) :=
            Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1
          obtain ⟨hkf_w, hperm_w, hvec⟩ :=
            write_vecU8_from_alloc fineCostModelSound (mpl := mmpl) (tp := tp) (brkStart := brkStart)
              (bs := x.bs) hp_ne hp_al16 hp_fit64 hpos hcap_lt (Nat.le_refl _) hm_prep
          let mf := writeVecHeader (s1.mem.writeBytes p x.bs) x.ret
            (BitVec.ofNat 64 x.bs.length) p (BitVec.ofNat 64 x.bs.length)
          have hk_eq : kBody s1 p = retHook (fun s => s.setMem mf) s1 := by
            simp [kBody, retHook, hs1_x8, mf]
          rw [hk_eq]
          obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf hs1_regs hs1_vregs hs1_sp hs1_run
          refine ⟨hkf1.trans hkf_w, hsym1, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
          have hev_step :
              fineCostModel.stepEvents (rustAllocEvents x.bs.length 1) st =
                fineCostModel.step (.alloc x.bs.length) st := by
            rw [rustAllocEvents_one hpos]; rfl
          have hfs_f : (retHook (fun s => s.setMem mf) s1).fs = s0.fs := hpres1.1
          have htr_f : (retHook (fun s => s.setMem mf) s1).trace = s0.trace := hpres1.2.1
          have hpool_f :
              A.pool lim (fineCostModel.stepEvents (rustAllocEvents x.bs.length 1) st)
                (retHook (fun s => s.setMem mf) s1) =
              mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim
                (fineCostModel.step (.alloc x.bs.length) st) s1 := by
            rw [hev_step]
            exact mallocngHookBudgetPool_transport fineCostModel fineCostModelIface γ mmpl
              tp brkStart lim _ (vmPreserved_retHook_setMem hperm_w)
          dsimp only [specStrong, readStdinSpecOfPlaced]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hfs_f, htr_f⟩, ?_⟩
          rw [sepExists_sepConj_left, satisfies_sepExists]
          refine ⟨rustAllocEvents x.bs.length 1, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨henv_ab, ?_⟩
          rw [sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
          refine ⟨.ok x.bs, ?_⟩
          rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨congrArg FsState.files hfs_f, hr_ok.symm, htr_f⟩, ?_⟩
          rw [hsplit_stk]
          exact Satisfies.mono
            (Entails.of_eq (by dsimp only [SlackStk, ioVecAt, getResultAt, A, fineHookRustCliAllocBudget]; sep_ac_rfl))
            hvec
        rcases hk_ok with ⟨hkf_f, hsym_f, hout_s⟩
        rcases hout_s with ⟨hret_f, hcc_f, hpost_s⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
        · dsimp only [specStrong] at hpost_s
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_s
          exact ⟨⟨hkf_f, hsym_f, Or.inl ⟨hret_f, hcc_f, hpost_s.2⟩⟩, hpost_s.1.1, hpost_s.1.2⟩
        · exact False.elim (not_satisfies_false_sepConj hp)
        · exact False.elim (not_satisfies_false_sepConj he)
        · exact False.elim (not_satisfies_false_sepConj ho)
    · simp only [hle, ↓reduceIte]
      have hcap_eq : CryptoVerification.SignalSession.stdinCapBytes = 1048576 := by decide
      have hr_err : readStdinResult x.bs = .error () := by
        unfold readStdinResult; rw [hcap_eq]; exact ite_neg hle
      have hmem_ret : s0.mem ⊨ memRegion x.ret 24 ∗
          (stackAt s0.sp stk ∗
            mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim st s0 ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
      obtain ⟨hkf_w, hperm_w, herr_mem⟩ := write_ioVecErr_local hmem_ret
      let mf := s0.mem.write64 x.ret 0xFFFFFFFFFFFFFFFF#64
      rw [show retHook (fun s => s.setMem (s.mem.write64 (s.readReg64 .x8) 0xFFFFFFFFFFFFFFFF#64)) s0 =
          retHook (fun s => s.setMem mf) s0 by simp [retHook, hx8, mf]]
      obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf rfl rfl rfl hrun
      refine ⟨⟨hkf_w, rfl, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩, rfl, rfl⟩
      have henv0 : ReadStdinBoundedEnv x.bs [] := readStdinBoundedEnv_of_hook_gt hle rfl
      have hpool_f :
          A.pool lim (fineCostModel.stepEvents [] st) (retHook (fun s => s.setMem mf) s0) =
            mallocngHookBudgetPool fineCostModel fineCostModelIface γ mmpl tp brkStart lim st s0 :=
        mallocngHookBudgetPool_transport fineCostModel fineCostModelIface γ mmpl tp brkStart lim st
          (vmPreserved_retHook_setMem hperm_w)
      dsimp only [readStdinSpecOfPlaced]
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨[], ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨henv0, ?_⟩
      rw [sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨.error (), ?_⟩
      rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨rfl, hr_err.symm, rfl⟩,
        Satisfies.mono (Entails.of_eq (by dsimp only [ioVecAt, getResultAt])) herr_mem⟩
  obtain ⟨⟨hkf, hsym, hout⟩, hfs, htr⟩ := hMain
  have heq : f3ReadStdinFallback mmpl s0 = f3ReadStdinFallbackRaw mmpl s0 := by
    unfold f3ReadStdinFallback keepFsTrace
    cases h : f3ReadStdinFallbackRaw mmpl s0
    rw [h] at hfs htr
    dsimp only at hfs htr ⊢
    subst hfs htr
    rfl
  rw [heq]
  exact ⟨hkf, hsym, hout⟩

/-- `(γ, tp)`-existentialized active precondition for `f3ReadStdinGhostHook` at `ReadStdinBoundedEnv`. -/
def ActiveF3ReadStdinPre [LibsignalPlacement] {M : AllocCostModel}
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) (s0 : State) : Prop :=
  s0.status = .Running ∧ s0.spAligned = true ∧
    ∃ (γ : GhostName) (tp : BitVec 64) (y : ReadStdinGhost × M.σ) (R : SepProp),
      s0.mem ⊨ (readStdinSpecOfPlaced cliIo (AOf γ tp) lim stk ReadStdinBoundedEnv).pre y s0 ∗ R

private theorem setPC_mem_local (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by
  cases s; rfl
private theorem setPC_symtab_local (s : State) (pc : BitVec 64) : (s.setPC pc).symtab = s.symtab := by
  cases s; rfl

private theorem pre_compiled_of_bounded [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {x : ReadStdinGhost} {st : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (readStdinSpecOfPlaced cliIo A lim stk ReadStdinBoundedEnv).pre (x, st) s0 ∗ R) :
    s0.mem ⊨ (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv).pre (x, st) s0 ∗ R := by
  dsimp only [readStdinSpecOfPlaced] at hpre ⊢
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨⟨hpre.1.1, hpre.1.2.1,
    fitsEnv_compiled_of_sub (fun _ => compiledReadStdinEnv_sub_bounded) hpre.1.2.2.1,
    hpre.1.2.2.2⟩, hpre.2⟩

private theorem outcome_bounded_of_compiled [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {x : ReadStdinGhost} {st : M.σ} {R : SepProp} {s0 sf : State}
    (hout : SubroutineOutcome
      (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv) (x, st) R s0 sf) :
    SubroutineOutcome
      (readStdinSpecOfPlaced cliIo A lim stk ReadStdinBoundedEnv) (x, st) R s0 sf := by
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [readStdinSpecOfPlaced] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    obtain ⟨evs, hpost⟩ := hpost
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨compiledReadStdinEnv_sub_bounded hpost.1, hpost.2⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- `(γ, tp)`-independent linked ghost hook for `signal_session_io::read_stdin` (`ReadStdinBoundedEnv`). -/
noncomputable def f3ReadStdinGhostHook [LibsignalPlacement] {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) (s0 : State) : State :=
  if _ : ActiveF3ReadStdinPre AOf lim stk s0 then
    if hReal : ActiveReadStdinLinkedRun keep P_real P_sub entry_io s0 then
      Classical.choose hReal.2.2.2
    else
      keepFilesTrace fallback s0
  else
    { s0 with status := .Exception "read_stdin ghost-hook precondition violated" }

theorem f3ReadStdinGhostHook_fsT [LibsignalPlacement] {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) :
    HookFsTraced IsFsC (f3ReadStdinGhostHook keep P_real P_sub entry_io AOf lim stk fallback) := by
  classical
  intro s0
  unfold f3ReadStdinGhostHook
  split
  · split
    · rename_i hReal
      have hspec := Classical.choose_spec hReal.2.2.2
      exact FsTraced.of_eq hspec.2.2.2.1 hspec.2.2.1
    · exact keepFilesTrace_fsT fallback s0
  · exact FsTraced.of_eq rfl rfl

noncomputable def f3ReadStdinGhostHookSub [LibsignalPlacement] {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) :
    { f : State → State // HookFsTraced IsFsC f } :=
  ⟨f3ReadStdinGhostHook keep P_real P_sub entry_io AOf lim stk fallback,
   f3ReadStdinGhostHook_fsT keep P_real P_sub entry_io AOf lim stk fallback⟩

noncomputable def f3ReadStdinGhostHookFine [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) : State → State :=
  f3ReadStdinGhostHook keep P_real P_sub entry_io
    (fun γ tp => fineHookRustCliAllocBudget γ mmpl tp brkStart)
    lim stk (f3ReadStdinFallback mmpl)

noncomputable def f3ReadStdinGhostHookFineSub [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) :
    { f : State → State // HookFsTraced IsFsC f } :=
  f3ReadStdinGhostHookSub keep P_real P_sub entry_io
    (fun γ tp => fineHookRustCliAllocBudget γ mmpl tp brkStart)
    lim stk (f3ReadStdinFallback mmpl)

theorem f3ReadStdinGhostHook_ok_bounded [LibsignalPlacement] {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {AOf : GhostName → BitVec 64 → RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (γ : GhostName) (tp : BitVec 64)
    (hPoolStrip : ∀ st s, (AOf γ tp).pool lim st (stripS keep s) = (AOf γ tp).pool lim st s)
    (hCond : subroutine_ok P_sub entry_io (readStdinBudgetCondSpec (AOf γ tp) lim stk))
    (hFallback : HookOk fallback
      (readStdinSpecOfPlaced cliIo (AOf γ tp) lim stk ReadStdinBoundedEnv)) :
    HookOk (f3ReadStdinGhostHook keep P_real P_sub entry_io AOf lim stk fallback)
      (readStdinSpecOfPlaced cliIo (AOf γ tp) lim stk ReadStdinBoundedEnv) := by
  classical
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  have hActPre : ActiveF3ReadStdinPre AOf lim stk s0 := ⟨hrun, hsp, γ, tp, (x, st), R, hpre⟩
  unfold f3ReadStdinGhostHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hReal : ActiveReadStdinLinkedRun keep P_real P_sub entry_io s0
  · simp only [hReal, ↓reduceDIte]
    have hpreC := pre_compiled_of_bounded hpre
    obtain ⟨sf, huntil, hstop, houtC, _, _, _, _⟩ :=
      real_readStdin_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hCond
        hrun hsp hpreC hReal.1 hReal.2.1 hReal.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    have hkf : s0.mem.KeepsFrozen sf.mem := by
      simpa only [setPC_mem_local] using huntil.toSteps.keepsFrozen
    have hsym : sf.symtab = s0.symtab := by
      simpa only [setPC_symtab_local] using huntil.toSteps.symtab_eq
    exact ⟨hkf, hsym, outcome_bounded_of_compiled houtC⟩
  · simp only [hReal, ↓reduceDIte]
    exact keepFilesTrace_ok_readStdin hFallback (x, st) R s0 hrun hpre hsp

theorem f3ReadStdinGhostHook_steps_of_call [LibsignalPlacement] {M : AllocCostModel}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entry_io : BitVec 64}
    {AOf : GhostName → BitVec 64 → RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hStub : StubReachesTarget P_real stubPc entry_io)
    (hPoolStrip : ∀ γ tp st s, (AOf γ tp).pool lim st (stripS keep s) = (AOf γ tp).pool lim st s)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io (readStdinBudgetCondSpec (AOf γ tp) lim stk))
    {u : State}
    (hpc : u.pc = stubPc)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3ReadStdinGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).status ≠
        .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hlr : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    Steps P_real u (f3ReadStdinGhostHook keep P_real P_sub entry_io AOf lim stk fallback u) ∧
      ExecFrozen (f3ReadStdinGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).mem ∧
      (f3ReadStdinGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).fs.files = u.fs.files ∧
      (f3ReadStdinGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).trace = u.trace ∧
      (FdsGe3Closed u.fs →
        FdsGe3Closed (f3ReadStdinGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).fs) := by
  classical
  have hActPre : ActiveF3ReadStdinPre AOf lim stk u := by
    by_contra hnPre
    have hex :
        (f3ReadStdinGhostHook keep P_real P_sub entry_io AOf lim stk fallback u).status =
          .Exception "read_stdin ghost-hook precondition violated" := by
      unfold f3ReadStdinGhostHook; simp [hnPre]
    exact hnoex _ hex
  obtain ⟨_, hsp, γ, tp, ⟨x, st⟩, R, hpre⟩ := id hActPre
  have hpreC := pre_compiled_of_bounded hpre
  obtain ⟨sf, huntil, hstop, _, hfiles, htr, hfds, hfr_sf⟩ :=
    real_readStdin_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no (hPoolStrip γ tp)
      (hCond γ tp) hrun hsp hpreC hfr hlr hCodeSub
  have hReal : ActiveReadStdinLinkedRun keep P_real P_sub entry_io u :=
    ⟨hfr, hlr, hCodeSub, sf, huntil, hstop, hfiles, htr, hfds, hfr_sf⟩
  have heq :
      f3ReadStdinGhostHook keep P_real P_sub entry_io AOf lim stk fallback u =
        Classical.choose hReal.2.2.2 := by
    unfold f3ReadStdinGhostHook; simp [hActPre, hReal]
  rw [heq]
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hStubSteps : Steps P_real u (u.setPC entry_io) := hStub u hpc hrun hfr
  exact ⟨hStubSteps.trans hchoose.1.toSteps, hchoose.2.2.2.2.2,
    hchoose.2.2.1, hchoose.2.2.2.1, hchoose.2.2.2.2.1⟩

/-! ## `(γ, tp)`-Independent `f3LinkedCallHook` and `f3CliGhostHooksFixed` -/

/-- `(γ, tp)`-existentialized active precondition for `f3LinkedCallHook`: holds at `s0` whenever
there exist `γ : GhostName`, `tp : BitVec 64`, `x`, and `R` satisfying `(specOf γ tp).pre x s0 ∗ R`. -/
def ActiveF3CallPre {α : Type} (specOf : GhostName → BitVec 64 → Spec α) (s0 : State) : Prop :=
  s0.status = .Running ∧ s0.spAligned = true ∧
    ∃ (γ : GhostName) (tp : BitVec 64) (x : α) (R : SepProp),
      s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R

/-- `(γ, tp)`-independent linked ghost-call hook: returns the deterministic first-stop state of
`P_real` from `s0.setPC entryTarget` under `ActiveF3CallPre` and `ActiveRealRun`, delegates to
`keepFsTrace fallback s0` outside `ActiveRealRun`, and sets `.Exception` outside `ActiveF3CallPre`. -/
noncomputable def f3LinkedCallHook {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (specOf : GhostName → BitVec 64 → Spec α)
    (fallback : State → State) (s0 : State) : State :=
  if _ : ActiveF3CallPre specOf s0 then
    if hReal : ActiveRealRun keep P_real P_sub entryTarget s0 then
      Classical.choose hReal.2.2.2
    else
      keepFsTrace fallback s0
  else
    { s0 with status := .Exception "ghost-hook precondition violated" }

theorem f3LinkedCallHook_fs {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (specOf : GhostName → BitVec 64 → Spec α)
    (fallback : State → State) (s0 : State) :
    (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback s0).fs = s0.fs := by
  classical
  unfold f3LinkedCallHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.1
    · rfl
  · rfl

theorem f3LinkedCallHook_fsT {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (specOf : GhostName → BitVec 64 → Spec α)
    (fallback : State → State) :
    HookFsTraced IsFsC (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback) := by
  classical
  intro s0
  unfold f3LinkedCallHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.2.1
    · exact FsTraced.of_eq rfl rfl
  · exact FsTraced.of_eq rfl rfl

/-- Pointwise `HookOk` for `f3LinkedCallHook` at every `(γ : GhostName) (tp : BitVec 64)`. -/
theorem f3LinkedCallHook_ok {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : subroutine_ok P_sub entryTarget (specOf γ tp))
    (hInv : SpecStripSInvariant keep (specOf γ tp))
    (hFsT : SpecPreservesFsTrace (specOf γ tp))
    (hPrePC : ∀ x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    (hFallbackOk : HookOk (keepFsTrace fallback) (specOf γ tp)) :
    HookOk (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback) (specOf γ tp) := by
  classical
  intro x R s0 hrun hpre hsp
  have hActPre : ActiveF3CallPre specOf s0 := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  unfold f3LinkedCallHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hReal : ActiveRealRun keep P_real P_sub entryTarget s0
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hout, _, _, _⟩ :=
      real_subroutine_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no hOk hInv hFsT
        hPrePC hOutPC hrun hsp hpre hReal.1 hReal.2.1 hReal.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq, hout⟩
  · simp only [hReal, ↓reduceDIte]
    exact hFallbackOk x R s0 hrun hpre hsp

/-- Real-machine-code replay (`Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ (f u).fs = u.fs`) for
    any non-`.Exception` call step of `f3LinkedCallHook` behind `StubReachesTarget P_real stubPc entryTarget`. -/
theorem f3LinkedCallHook_steps_of_call {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hStub : StubReachesTarget P_real stubPc entryTarget)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget (specOf γ tp))
    (hSpecInv : ∀ γ tp, SpecStripSInvariant keep (specOf γ tp))
    (hFsT : ∀ γ tp, SpecPreservesFsTrace (specOf γ tp))
    (hPrePC : ∀ γ tp x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ γ tp x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    {u : State}
    (hpc : u.pc = stubPc)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    Steps P_real u (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u) ∧
      ExecFrozen (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u).mem ∧
      (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u).fs = u.fs := by
  classical
  have hActPre : ActiveF3CallPre specOf u := by
    by_contra hnAct
    have hex : (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u).status =
        .Exception "ghost-hook precondition violated" := by
      unfold f3LinkedCallHook
      simp [hnAct]
    exact hnoex _ hex
  obtain ⟨_, hsp, γ, tp, x, R, hpre⟩ := id hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    real_subroutine_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no
      (hOk γ tp) (hSpecInv γ tp) (hFsT γ tp) (hPrePC γ tp) (hOutPC γ tp)
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep P_real P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have hBody :
      Steps P_real (u.setPC entryTarget)
          (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u) ∧
        ExecFrozen (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u).mem := by
    unfold f3LinkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact ⟨hchoose.1.toSteps, hchoose.2.2.2.2⟩
  exact ⟨(hStub u hpc hrun hFr).trans hBody.1, hBody.2, f3LinkedCallHook_fs _ _ _ _ _ _ u⟩

export LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook (
  fineHookRustCliAllocBudget_pool_stripS
)

theorem specStripSInvariant_fine_alloc [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) (zeroed : Bool) :
    SpecStripSInvariant keep
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim zeroed) where
  pre_eq := by
    rintro ⟨sz, al, st⟩ s
    dsimp only [rustCliAllocBudgetSpec]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st s]
    rfl
  post_eq := by
    rintro ⟨sz, al, st⟩ s0 sf
    dsimp only [rustCliAllocBudgetSpec]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim _ sf]
    have hacp : AllocCallPreserved (stripS keep s0) (stripS keep sf) = AllocCallPreserved s0 sf := by
      cases s0; cases sf; rfl
    rw [hacp]; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := by
    rintro ⟨sz, al, st⟩ s0 sf
    dsimp only [rustCliAllocBudgetSpec]
    have hoom : OomPreserved (stripS keep s0) (stripS keep sf) = OomPreserved s0 sf := by
      cases s0; cases sf; rfl
    rw [hoom]

theorem specStripSInvariant_fine_dealloc [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) :
    SpecStripSInvariant keep
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim) where
  pre_eq := by
    rintro ⟨p, sz, al, st⟩ s
    dsimp only [rustCliDeallocBudgetSpec]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st s]
    rfl
  post_eq := by
    rintro ⟨p, sz, al, st⟩ s0 sf
    dsimp only [rustCliDeallocBudgetSpec]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim _ sf]
    have hacp : AllocCallPreserved (stripS keep s0) (stripS keep sf) = AllocCallPreserved s0 sf := by
      cases s0; cases sf; rfl
    rw [hacp]; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specStripSInvariant_fine_realloc [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) :
    SpecStripSInvariant keep
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim) where
  pre_eq := by
    rintro ⟨p, oldSz, al, newSz, bs, st⟩ s
    dsimp only [rustCliReallocBudgetSpec]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st s]
    rfl
  post_eq := by
    rintro ⟨p, oldSz, al, newSz, bs, st⟩ s0 sf
    dsimp only [rustCliReallocBudgetSpec]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim _ sf]
    have hacp : AllocCallPreserved (stripS keep s0) (stripS keep sf) = AllocCallPreserved s0 sf := by
      cases s0; cases sf; rfl
    rw [hacp]; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := by
    rintro ⟨p, oldSz, al, newSz, bs, st⟩ s0 sf
    dsimp only [rustCliReallocBudgetSpec]
    have hoom : OomPreserved (stripS keep s0) (stripS keep sf) = OomPreserved s0 sf := by
      cases s0; cases sf; rfl
    rw [hoom]

theorem specStripSInvariant_fine_stringCloneNoOom [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) :
    SpecStripSInvariant keep
      (stringCloneNoOomSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim) where
  pre_eq := by
    rintro ⟨p, ret, g, st⟩ s
    dsimp only [stringCloneNoOomSpec]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st s]
    rfl
  post_eq := by
    rintro ⟨p, ret, g, st⟩ s0 sf
    dsimp only [stringCloneNoOomSpec]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim _ sf]
    have hacp : AllocCallPreserved (stripS keep s0) (stripS keep sf) = AllocCallPreserved s0 sf := by
      cases s0; cases sf; rfl
    rw [hacp]; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem f3ReadStdinGhostHookFine_ok_bounded [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readStdinBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack))
    (γ : GhostName) (tp : BitVec 64) :
    HookOk (f3ReadStdinGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk)
      (readStdinSpecOfPlaced cliIo (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk
        ReadStdinBoundedEnv) :=
  f3ReadStdinGhostHook_ok_bounded hsvc_real hsvc_sub hreal_no hsub_no γ tp
    (fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim)
    (subroutine_ok_readStdinBudgetCondSpec_of_extHookStack hstk (hCond γ tp))
    (f3ReadStdinFallback_ok_bounded γ tp brkStart lim hPl hstk)

theorem f3ReadStdinGhostHookFine_steps_of_call [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entry_io : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hStub : StubReachesTarget P_real stubPc entry_io)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readStdinBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack))
    {u : State}
    (hpc : u.pc = stubPc)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3ReadStdinGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk u).status ≠
        .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hlr : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    Steps P_real u (f3ReadStdinGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk u) ∧
      ExecFrozen (f3ReadStdinGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk u).mem ∧
      (f3ReadStdinGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk u).fs.files = u.fs.files ∧
      (f3ReadStdinGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk u).trace = u.trace ∧
      (FdsGe3Closed u.fs →
        FdsGe3Closed (f3ReadStdinGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk u).fs) :=
  f3ReadStdinGhostHook_steps_of_call hsvc_real hsvc_sub hreal_no hsub_no hStub
    (fun γ tp => fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim)
    (fun γ tp => subroutine_ok_readStdinBudgetCondSpec_of_extHookStack hstk (hCond γ tp))
    hpc hrun hnoex hfr hlr hCodeSub

theorem f3ReadFileFixedGhostHookFine_steps_of_call
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entry_io : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hStub : StubReachesTarget P_real stubPc entry_io)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hCond : ∀ γ tp, subroutine_ok P_sub entry_io
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack))
    {u : State}
    (hpc : u.pc = stubPc)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3ReadFileFixedGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk u).status ≠
        .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hlr : keep (u.readReg64 .lr) = false)
    (hGuard : F3ReadFileFixedCallGuard u)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    Steps P_real u (f3ReadFileFixedGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk u) ∧
      ExecFrozen (f3ReadFileFixedGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk u).mem ∧
      (f3ReadFileFixedGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk u).fs = u.fs :=
  f3ReadFileFixedGhostHook_steps_of_call hsvc_real hsvc_sub hreal_no hsub_no hStub
    (fun γ tp => fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim)
    (fun γ tp => subroutine_ok_readFileAnyBudgetCondSpec_of_extHookStack hstk (hCond γ tp))
    hpc hrun hnoex hfr hlr hGuard hCodeSub

/-! ### Closed `(γ, tp)`-Independent Allocator and `stringClone` Ghost Hooks -/

noncomputable def f3AllocGhostHookFine [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) : State → State :=
  f3LinkedCallHook keep P_real P_sub entryTarget
    (fun γ tp => rustCliAllocBudgetSpec fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim false)
    (f3AllocFallback mmpl false)

noncomputable def f3DeallocGhostHookFine [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) : State → State :=
  f3LinkedCallHook keep P_real P_sub entryTarget
    (fun γ tp => rustCliDeallocBudgetSpec fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)
    (f3DeallocFallback mmpl)

noncomputable def f3ReallocGhostHookFine [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) : State → State :=
  f3LinkedCallHook keep P_real P_sub entryTarget
    (fun γ tp => rustCliReallocBudgetSpec fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)
    (f3ReallocFallback mmpl)

noncomputable def f3AllocZeroedGhostHookFine [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) : State → State :=
  f3LinkedCallHook keep P_real P_sub entryTarget
    (fun γ tp => rustCliAllocBudgetSpec fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim true)
    (f3AllocFallback mmpl true)

noncomputable def f3StringCloneGhostHookFine [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) : State → State :=
  f3LinkedCallHook keep P_real P_sub entryTarget
    (fun γ tp => stringCloneNoOomSpec fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)
    (f3StringCloneFallback mmpl)

@[simp]
theorem f3AllocGhostHookFine_fs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (s0 : State) :
    (f3AllocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim s0).fs = s0.fs :=
  f3LinkedCallHook_fs _ _ _ _ _ _ s0

@[simp]
theorem f3DeallocGhostHookFine_fs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (s0 : State) :
    (f3DeallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim s0).fs = s0.fs :=
  f3LinkedCallHook_fs _ _ _ _ _ _ s0

@[simp]
theorem f3ReallocGhostHookFine_fs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (s0 : State) :
    (f3ReallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim s0).fs = s0.fs :=
  f3LinkedCallHook_fs _ _ _ _ _ _ s0

@[simp]
theorem f3AllocZeroedGhostHookFine_fs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (s0 : State) :
    (f3AllocZeroedGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim s0).fs = s0.fs :=
  f3LinkedCallHook_fs _ _ _ _ _ _ s0

@[simp]
theorem f3StringCloneGhostHookFine_fs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (s0 : State) :
    (f3StringCloneGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim s0).fs = s0.fs :=
  f3LinkedCallHook_fs _ _ _ _ _ _ s0

theorem f3AllocGhostHookFine_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    HookFsTraced IsFsC (f3AllocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim) :=
  f3LinkedCallHook_fsT _ _ _ _ _ _

theorem f3DeallocGhostHookFine_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    HookFsTraced IsFsC (f3DeallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim) :=
  f3LinkedCallHook_fsT _ _ _ _ _ _

theorem f3ReallocGhostHookFine_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    HookFsTraced IsFsC (f3ReallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim) :=
  f3LinkedCallHook_fsT _ _ _ _ _ _

theorem f3AllocZeroedGhostHookFine_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    HookFsTraced IsFsC (f3AllocZeroedGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim) :=
  f3LinkedCallHook_fsT _ _ _ _ _ _

theorem f3StringCloneGhostHookFine_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    HookFsTraced IsFsC (f3StringCloneGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim) :=
  f3LinkedCallHook_fsT _ _ _ _ _ _

private theorem keepFsTrace_idem (f : State → State) :
    keepFsTrace (keepFsTrace f) = keepFsTrace f := by
  funext s0
  unfold keepFsTrace
  cases f s0
  rfl

private theorem prePC_fine_alloc [LibsignalPlacement] (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits) (zeroed : Bool)
    (x : Nat × Nat × fineCostModel.σ) (s : State) (pc : BitVec 64) :
    (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim zeroed).pre
        x (s.setPC pc) =
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim zeroed).pre
        x s := by
  cases s; rfl

private theorem outPC_fine_alloc [LibsignalPlacement] (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits) (zeroed : Bool)
    (x : Nat × Nat × fineCostModel.σ) (R : SepProp) (s0 sf : State) (pc : BitVec 64) :
    SubroutineOutcome
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim zeroed)
      x R (s0.setPC pc) sf →
    SubroutineOutcome
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim zeroed)
      x R s0 sf := by
  cases s0; exact id

private theorem prePC_fine_dealloc [LibsignalPlacement] (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (x : BitVec 64 × Nat × Nat × fineCostModel.σ) (s : State) (pc : BitVec 64) :
    (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim).pre
        x (s.setPC pc) =
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim).pre
        x s := by
  cases s; rfl

private theorem outPC_fine_dealloc [LibsignalPlacement] (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (x : BitVec 64 × Nat × Nat × fineCostModel.σ) (R : SepProp) (s0 sf : State) (pc : BitVec 64) :
    SubroutineOutcome
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)
      x R (s0.setPC pc) sf →
    SubroutineOutcome
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)
      x R s0 sf := by
  cases s0; exact id

private theorem prePC_fine_realloc [LibsignalPlacement] (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (x : BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × fineCostModel.σ)
    (s : State) (pc : BitVec 64) :
    (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim).pre
        x (s.setPC pc) =
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim).pre
        x s := by
  cases s; rfl

private theorem outPC_fine_realloc [LibsignalPlacement] (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (x : BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × fineCostModel.σ)
    (R : SepProp) (s0 sf : State) (pc : BitVec 64) :
    SubroutineOutcome
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)
      x R (s0.setPC pc) sf →
    SubroutineOutcome
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)
      x R s0 sf := by
  cases s0; exact id

private theorem prePC_fine_stringCloneNoOom [LibsignalPlacement] (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (x : BitVec 64 × BitVec 64 × VecGhost × fineCostModel.σ) (s : State) (pc : BitVec 64) :
    (stringCloneNoOomSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim).pre
        x (s.setPC pc) =
      (stringCloneNoOomSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim).pre
        x s := by
  cases s; rfl

private theorem outPC_fine_stringCloneNoOom [LibsignalPlacement] (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (x : BitVec 64 × BitVec 64 × VecGhost × fineCostModel.σ)
    (R : SepProp) (s0 sf : State) (pc : BitVec 64) :
    SubroutineOutcome
      (stringCloneNoOomSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)
      x R (s0.setPC pc) sf →
    SubroutineOutcome
      (stringCloneNoOomSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)
      x R s0 sf := by
  cases s0; exact id

theorem f3AllocGhostHookFine_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : subroutine_ok P_sub entryTarget
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim false)) :
    HookOk (f3AllocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim)
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim false) := by
  refine f3LinkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no γ tp hOk
    (specStripSInvariant_fine_alloc γ mmpl tp brkStart hKeepMallocng lim false)
    (specPreservesFsTrace_alloc _ lim false)
    (prePC_fine_alloc γ mmpl tp brkStart lim false)
    (outPC_fine_alloc γ mmpl tp brkStart lim false) ?_
  unfold f3AllocFallback
  rw [keepFsTrace_idem]
  exact hookOk_rustCliAllocBudget_of_base (f3AllocFallback_ok_fine brkStart lim false hPl γ tp)

theorem f3DeallocGhostHookFine_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : subroutine_ok P_sub entryTarget
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim)) :
    HookOk (f3DeallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim)
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim) := by
  refine f3LinkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no γ tp hOk
    (specStripSInvariant_fine_dealloc γ mmpl tp brkStart hKeepMallocng lim)
    (specPreservesFsTrace_dealloc _ lim)
    (prePC_fine_dealloc γ mmpl tp brkStart lim)
    (outPC_fine_dealloc γ mmpl tp brkStart lim) ?_
  unfold f3DeallocFallback
  rw [keepFsTrace_idem]
  exact hookOk_rustCliDeallocBudget_of_base (f3DeallocFallback_ok_fine brkStart lim hPl γ tp)

theorem f3ReallocGhostHookFine_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : subroutine_ok P_sub entryTarget
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim)) :
    HookOk (f3ReallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim)
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim) := by
  refine f3LinkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no γ tp hOk
    (specStripSInvariant_fine_realloc γ mmpl tp brkStart hKeepMallocng lim)
    (specPreservesFsTrace_realloc _ lim)
    (prePC_fine_realloc γ mmpl tp brkStart lim)
    (outPC_fine_realloc γ mmpl tp brkStart lim) ?_
  unfold f3ReallocFallback
  rw [keepFsTrace_idem]
  exact hookOk_rustCliReallocBudget_of_base (f3ReallocFallback_ok_fine brkStart lim hPl γ tp)

theorem f3AllocZeroedGhostHookFine_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : subroutine_ok P_sub entryTarget
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim true)) :
    HookOk (f3AllocZeroedGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim)
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim true) := by
  refine f3LinkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no γ tp hOk
    (specStripSInvariant_fine_alloc γ mmpl tp brkStart hKeepMallocng lim true)
    (specPreservesFsTrace_alloc _ lim true)
    (prePC_fine_alloc γ mmpl tp brkStart lim true)
    (outPC_fine_alloc γ mmpl tp brkStart lim true) ?_
  unfold f3AllocFallback
  rw [keepFsTrace_idem]
  exact hookOk_rustCliAllocBudget_of_base (f3AllocFallback_ok_fine brkStart lim true hPl γ tp)

theorem f3StringCloneGhostHookFine_ok_noOom [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hCond : subroutine_ok P_sub entryTarget
      (stringCloneBudgetCondSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim)) :
    HookOk (f3StringCloneGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim)
      (stringCloneNoOomSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim) := by
  refine f3LinkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no γ tp
    (subroutine_ok_stringCloneNoOom_of_cond hCond)
    (specStripSInvariant_fine_stringCloneNoOom γ mmpl tp brkStart hKeepMallocng lim)
    (specPreservesFsTrace_stringCloneNoOom _ lim)
    (prePC_fine_stringCloneNoOom γ mmpl tp brkStart lim)
    (outPC_fine_stringCloneNoOom γ mmpl tp brkStart lim) ?_
  unfold f3StringCloneFallback
  rw [keepFsTrace_idem]
  exact f3StringCloneFallback_ok_noOom_fine brkStart lim hPl γ tp

theorem f3StringCloneGhostHookFine_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hCond : subroutine_ok P_sub entryTarget
      (stringCloneBudgetCondSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim)) :
    HookOk (f3StringCloneGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim)
      (stringCloneBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim) :=
  hookOk_stringCloneBudget_of_noOom
    (f3StringCloneGhostHookFine_ok_noOom hsvc_real hsvc_sub hreal_no hsub_no
      hPl hKeepMallocng γ tp hCond)

theorem f3AllocGhostHookFine_steps_of_call [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hStub : StubReachesTarget P_real stubPc entryTarget)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim false))
    {u : State}
    (hpc : u.pc = stubPc) (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3AllocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    Steps P_real u (f3AllocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u) ∧
      ExecFrozen (f3AllocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).mem ∧
      (f3AllocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).fs = u.fs :=
  f3LinkedCallHook_steps_of_call hsvc_real hsvc_sub hreal_no hsub_no hStub hOk
    (fun γ tp => specStripSInvariant_fine_alloc γ mmpl tp brkStart hKeepMallocng lim false)
    (fun _ _ => specPreservesFsTrace_alloc _ lim false)
    (fun γ tp => prePC_fine_alloc γ mmpl tp brkStart lim false)
    (fun γ tp => outPC_fine_alloc γ mmpl tp brkStart lim false)
    hpc hrun hnoex hFr hlr_out hCodeSub

theorem f3DeallocGhostHookFine_steps_of_call [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hStub : StubReachesTarget P_real stubPc entryTarget)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim))
    {u : State}
    (hpc : u.pc = stubPc) (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3DeallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    Steps P_real u (f3DeallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u) ∧
      ExecFrozen (f3DeallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).mem ∧
      (f3DeallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).fs = u.fs :=
  f3LinkedCallHook_steps_of_call hsvc_real hsvc_sub hreal_no hsub_no hStub hOk
    (fun γ tp => specStripSInvariant_fine_dealloc γ mmpl tp brkStart hKeepMallocng lim)
    (fun _ _ => specPreservesFsTrace_dealloc _ lim)
    (fun γ tp => prePC_fine_dealloc γ mmpl tp brkStart lim)
    (fun γ tp => outPC_fine_dealloc γ mmpl tp brkStart lim)
    hpc hrun hnoex hFr hlr_out hCodeSub

theorem f3ReallocGhostHookFine_steps_of_call [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hStub : StubReachesTarget P_real stubPc entryTarget)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim))
    {u : State}
    (hpc : u.pc = stubPc) (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3ReallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    Steps P_real u (f3ReallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u) ∧
      ExecFrozen (f3ReallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).mem ∧
      (f3ReallocGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).fs = u.fs :=
  f3LinkedCallHook_steps_of_call hsvc_real hsvc_sub hreal_no hsub_no hStub hOk
    (fun γ tp => specStripSInvariant_fine_realloc γ mmpl tp brkStart hKeepMallocng lim)
    (fun _ _ => specPreservesFsTrace_realloc _ lim)
    (fun γ tp => prePC_fine_realloc γ mmpl tp brkStart lim)
    (fun γ tp => outPC_fine_realloc γ mmpl tp brkStart lim)
    hpc hrun hnoex hFr hlr_out hCodeSub

theorem f3AllocZeroedGhostHookFine_steps_of_call [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hStub : StubReachesTarget P_real stubPc entryTarget)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim true))
    {u : State}
    (hpc : u.pc = stubPc) (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3AllocZeroedGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    Steps P_real u (f3AllocZeroedGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u) ∧
      ExecFrozen (f3AllocZeroedGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).mem ∧
      (f3AllocZeroedGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).fs = u.fs :=
  f3LinkedCallHook_steps_of_call hsvc_real hsvc_sub hreal_no hsub_no hStub hOk
    (fun γ tp => specStripSInvariant_fine_alloc γ mmpl tp brkStart hKeepMallocng lim true)
    (fun _ _ => specPreservesFsTrace_alloc _ lim true)
    (fun γ tp => prePC_fine_alloc γ mmpl tp brkStart lim true)
    (fun γ tp => outPC_fine_alloc γ mmpl tp brkStart lim true)
    hpc hrun hnoex hFr hlr_out hCodeSub

theorem f3StringCloneGhostHookFine_steps_of_call [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hStub : StubReachesTarget P_real stubPc entryTarget)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hCond : ∀ γ tp, subroutine_ok P_sub entryTarget
      (stringCloneBudgetCondSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim))
    {u : State}
    (hpc : u.pc = stubPc) (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3StringCloneGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    Steps P_real u (f3StringCloneGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u) ∧
      ExecFrozen (f3StringCloneGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).mem ∧
      (f3StringCloneGhostHookFine keep P_real P_sub entryTarget mmpl brkStart lim u).fs = u.fs :=
  f3LinkedCallHook_steps_of_call hsvc_real hsvc_sub hreal_no hsub_no hStub
    (fun γ tp => subroutine_ok_stringCloneNoOom_of_cond (hCond γ tp))
    (fun γ tp => specStripSInvariant_fine_stringCloneNoOom γ mmpl tp brkStart hKeepMallocng lim)
    (fun _ _ => specPreservesFsTrace_stringCloneNoOom _ lim)
    (fun γ tp => prePC_fine_stringCloneNoOom γ mmpl tp brkStart lim)
    (fun γ tp => outPC_fine_stringCloneNoOom γ mmpl tp brkStart lim)
    hpc hrun hnoex hFr hlr_out hCodeSub

/-! ### `F3GhostEntryTargets` and `f3CliGhostHooksFixed` -/

/-- Entry-PC bundle for the 7 compiled Rust/allocator subroutines replayed by `f3CliGhostHooksFixed`. -/
structure F3GhostEntryTargets where
  alloc : BitVec 64
  dealloc : BitVec 64
  realloc : BitVec 64
  allocZeroed : BitVec 64
  stringClone : BitVec 64
  readFile : BitVec 64
  readStdin : BitVec 64

/-- `(γ, tp)`-independent 8-field `CliGhostHooks` bundle populating all five Rust allocator
symbols, `stringClone`, `readFile` (`f3ReadFileFixedGhostHookFineSub`), and `readStdin`
(`f3ReadStdinGhostHookFineSub`). -/
noncomputable def f3CliGhostHooksFixed [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (T : F3GhostEntryTargets)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat)
    (fMemset fMemcpy : Option (State → State) := none) : CliGhostHooks where
  alloc := f3AllocGhostHookFine keep P_real P_sub T.alloc mmpl brkStart lim
  dealloc := f3DeallocGhostHookFine keep P_real P_sub T.dealloc mmpl brkStart lim
  realloc := f3ReallocGhostHookFine keep P_real P_sub T.realloc mmpl brkStart lim
  allocZeroed := f3AllocZeroedGhostHookFine keep P_real P_sub T.allocZeroed mmpl brkStart lim
  shim := hookNoop
  stringClone := some (f3StringCloneGhostHookFine keep P_real P_sub T.stringClone mmpl brkStart lim)
  readFile := some (f3ReadFileFixedGhostHookFineSub keep P_real P_sub T.readFile mmpl brkStart lim stk)
  readStdin := some (f3ReadStdinGhostHookFineSub keep P_real P_sub T.readStdin mmpl brkStart lim stk)
  memset := fMemset
  memcpy := fMemcpy

theorem cliGhostHooksFs_f3CliGhostHooksFixed [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (T : F3GhostEntryTargets)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat)
    (fMemset fMemcpy : Option (State → State))
    (hMsFsT : ∀ f, fMemset = some f → HookFsTraced IsFsC f := by intro _ h; cases h)
    (hMcFsT : ∀ f, fMemcpy = some f → HookFsTraced IsFsC f := by intro _ h; cases h) :
    CliGhostHooksFs
      (f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk fMemset fMemcpy) where
  alloc_fsT := f3AllocGhostHookFine_fsT keep P_real P_sub T.alloc mmpl brkStart lim
  dealloc_fsT := f3DeallocGhostHookFine_fsT keep P_real P_sub T.dealloc mmpl brkStart lim
  realloc_fsT := f3ReallocGhostHookFine_fsT keep P_real P_sub T.realloc mmpl brkStart lim
  allocZeroed_fsT := f3AllocZeroedGhostHookFine_fsT keep P_real P_sub T.allocZeroed mmpl brkStart lim
  shim_fsT := hookNoop_fsT
  stringClone_fsT := by
    intro f hf
    dsimp only [f3CliGhostHooksFixed] at hf
    injection hf with hfeq
    subst hfeq
    exact f3StringCloneGhostHookFine_fsT keep P_real P_sub T.stringClone mmpl brkStart lim
  memset_fsT := hMsFsT
  memcpy_fsT := hMcFsT

theorem fsTHooks_f3CliGhostHooksFixed [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (T : F3GhostEntryTargets)
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat)
    (fMemset fMemcpy : Option (State → State))
    (hMsFsT : ∀ f, fMemset = some f → HookFsTraced IsFsC f := by intro _ h; cases h)
    (hMcFsT : ∀ f, fMemcpy = some f → HookFsTraced IsFsC f := by intro _ h; cases h) :
    FsTHooks
      (cliGhostExterns
        (f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk fMemset fMemcpy)
        (cliExternsPlaced mmpl W)) :=
  fsTHooks_cliGhostExterns_of_fs
    (cliGhostHooksFs_f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk
      fMemset fMemcpy hMsFsT hMcFsT)
    (fsTHooks_cliExternsPlaced mmpl W)

open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookExactMemcpy)

theorem cliGhostSpqrAllocHooks_f3CliGhostHooksFixed [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {T : F3GhostEntryTargets}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hAlloc : subroutine_ok P_sub T.alloc
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim false))
    (hDealloc : subroutine_ok P_sub T.dealloc
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hRealloc : subroutine_ok P_sub T.realloc
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hAllocZeroed : subroutine_ok P_sub T.allocZeroed
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim true))
    (hMemset : ∃ f, fMemset = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpy : ∃ f, fMemcpy = some f ∧
      (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
      (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
      HookOk f memcpyRegionSpec ∧
      HookOk f sessionMemcpyRegionSpec ∧
      HookOk f framelessMemcpySpec ∧
      HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpyExact : ∀ f, fMemcpy = some f → HookExactMemcpy f)
    (hMemsetAcp : ∀ f, fMemset = some f →
      ∀ s : State, (f s).sigActions = s.sigActions ∧ (f s).oracle = s.oracle) :
    CliGhostSpqrAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk fMemset fMemcpy) where
  alloc := f3AllocGhostHookFine_ok hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng γ tp hAlloc
  dealloc := f3DeallocGhostHookFine_ok hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng γ tp hDealloc
  realloc := f3ReallocGhostHookFine_ok hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng γ tp hRealloc
  alloc_fs := f3AllocGhostHookFine_fs keep P_real P_sub T.alloc mmpl brkStart lim
  dealloc_fs := f3DeallocGhostHookFine_fs keep P_real P_sub T.dealloc mmpl brkStart lim
  realloc_fs := f3ReallocGhostHookFine_fs keep P_real P_sub T.realloc mmpl brkStart lim
  alloc_fsT := f3AllocGhostHookFine_fsT keep P_real P_sub T.alloc mmpl brkStart lim
  dealloc_fsT := f3DeallocGhostHookFine_fsT keep P_real P_sub T.dealloc mmpl brkStart lim
  realloc_fsT := f3ReallocGhostHookFine_fsT keep P_real P_sub T.realloc mmpl brkStart lim
  shim_eq := rfl
  memset := hMemset
  memcpy := hMemcpy
  memcpy_exact := hMemcpyExact
  memset_acp := hMemsetAcp
  allocZeroed :=
    f3AllocZeroedGhostHookFine_ok hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng γ tp hAllocZeroed
  allocZeroed_fs := f3AllocZeroedGhostHookFine_fs keep P_real P_sub T.allocZeroed mmpl brkStart lim
  allocZeroed_fsT := f3AllocZeroedGhostHookFine_fsT keep P_real P_sub T.allocZeroed mmpl brkStart lim

theorem cliGhostAllocHooks_f3CliGhostHooksFixed [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {T : F3GhostEntryTargets}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hAlloc : subroutine_ok P_sub T.alloc
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim false))
    (hDealloc : subroutine_ok P_sub T.dealloc
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hRealloc : subroutine_ok P_sub T.realloc
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hMemset : ∃ f, fMemset = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpy : ∃ f, fMemcpy = some f ∧
      (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
      (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
      HookOk f memcpyRegionSpec ∧
      HookOk f sessionMemcpyRegionSpec ∧
      HookOk f framelessMemcpySpec ∧
      HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpyExact : ∀ f, fMemcpy = some f → HookExactMemcpy f)
    (hMemsetAcp : ∀ f, fMemset = some f →
      ∀ s : State, (f s).sigActions = s.sigActions ∧ (f s).oracle = s.oracle) :
    CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk fMemset fMemcpy) where
  alloc := f3AllocGhostHookFine_ok hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng γ tp hAlloc
  dealloc := f3DeallocGhostHookFine_ok hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng γ tp hDealloc
  realloc := f3ReallocGhostHookFine_ok hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng γ tp hRealloc
  alloc_fs := f3AllocGhostHookFine_fs keep P_real P_sub T.alloc mmpl brkStart lim
  dealloc_fs := f3DeallocGhostHookFine_fs keep P_real P_sub T.dealloc mmpl brkStart lim
  realloc_fs := f3ReallocGhostHookFine_fs keep P_real P_sub T.realloc mmpl brkStart lim
  alloc_fsT := f3AllocGhostHookFine_fsT keep P_real P_sub T.alloc mmpl brkStart lim
  dealloc_fsT := f3DeallocGhostHookFine_fsT keep P_real P_sub T.dealloc mmpl brkStart lim
  realloc_fsT := f3ReallocGhostHookFine_fsT keep P_real P_sub T.realloc mmpl brkStart lim
  shim_eq := rfl
  memset := hMemset
  memcpy := hMemcpy
  memcpy_exact := hMemcpyExact
  memset_acp := hMemsetAcp

theorem stringClone_hookSat_f3CliGhostHooksFixed [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {T : F3GhostEntryTargets}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (baseExt : LibsignalHooks)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hStrClone : subroutine_ok P_sub T.stringClone
      (stringCloneBudgetCondSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :
    HookSat
      (cliGhostExterns
        (f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk fMemset fMemcpy) baseExt)
      lsStringCloneSym
      (stringCloneBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim) :=
  ⟨f3StringCloneGhostHookFine keep P_real P_sub T.stringClone mmpl brkStart lim,
   cliGhostExterns_stringClone_some _ baseExt rfl,
   f3StringCloneGhostHookFine_ok hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng γ tp hStrClone⟩

theorem allocContractsXCliPlaced_f3CliGhostHooksFixed [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {T : F3GhostEntryTargets}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hAlloc : subroutine_ok P_sub T.alloc
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim false))
    (hDealloc : subroutine_ok P_sub T.dealloc
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hRealloc : subroutine_ok P_sub T.realloc
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hMemset : ∃ f, fMemset = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpy : ∃ f, fMemcpy = some f ∧
      (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
      (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
      HookOk f memcpyRegionSpec ∧
      HookOk f sessionMemcpyRegionSpec ∧
      HookOk f framelessMemcpySpec ∧
      HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpyExact : ∀ f, fMemcpy = some f → HookExactMemcpy f)
    (hMemsetAcp : ∀ f, fMemset = some f →
      ∀ s : State, (f s).sigActions = s.sigActions ∧ (f s).oracle = s.oracle) :
    AllocContractsXCliPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns
        (f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk fMemset fMemcpy)
        (cliExternsPlaced mmpl W)) :=
  allocContractsXCliPlaced_of_hooks mmpl _ W
    (cliGhostAllocHooks_f3CliGhostHooksFixed hsvc_real hsvc_sub hreal_no hsub_no
      hPl hKeepMallocng γ tp hAlloc hDealloc hRealloc hMemset hMemcpy hMemcpyExact hMemsetAcp)

theorem allocContractsFsPlaced_f3CliGhostHooksFixed [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {T : F3GhostEntryTargets}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hAlloc : subroutine_ok P_sub T.alloc
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim false))
    (hDealloc : subroutine_ok P_sub T.dealloc
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hRealloc : subroutine_ok P_sub T.realloc
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hMemset : ∃ f, fMemset = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpy : ∃ f, fMemcpy = some f ∧
      (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
      (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
      HookOk f memcpyRegionSpec ∧
      HookOk f sessionMemcpyRegionSpec ∧
      HookOk f framelessMemcpySpec ∧
      HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpyExact : ∀ f, fMemcpy = some f → HookExactMemcpy f)
    (hMemsetAcp : ∀ f, fMemset = some f →
      ∀ s : State, (f s).sigActions = s.sigActions ∧ (f s).oracle = s.oracle) :
    AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns
        (f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk fMemset fMemcpy)
        (cliExternsPlaced mmpl W)) :=
  allocContractsFsPlaced_of_hooks mmpl _ W
    (cliGhostAllocHooks_f3CliGhostHooksFixed hsvc_real hsvc_sub hreal_no hsub_no
      hPl hKeepMallocng γ tp hAlloc hDealloc hRealloc hMemset hMemcpy hMemcpyExact hMemsetAcp)

theorem stage2ContractsMinPlaced_f3CliGhostHooksFixed [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {T : F3GhostEntryTargets}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hAlloc : subroutine_ok P_sub T.alloc
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim false))
    (hDealloc : subroutine_ok P_sub T.dealloc
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hRealloc : subroutine_ok P_sub T.realloc
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hMemset : ∃ f, fMemset = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpy : ∃ f, fMemcpy = some f ∧
      (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
      (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
      HookOk f memcpyRegionSpec ∧
      HookOk f sessionMemcpyRegionSpec ∧
      HookOk f framelessMemcpySpec ∧
      HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpyExact : ∀ f, fMemcpy = some f → HookExactMemcpy f)
    (hMemsetAcp : ∀ f, fMemset = some f →
      ∀ s : State, (f s).sigActions = s.sigActions ∧ (f s).oracle = s.oracle) :
    Stage2ContractsMinPlaced fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns
        (f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk fMemset fMemcpy)
        (cliExternsPlaced mmpl W)) :=
  stage2ContractsMinPlaced_of_hooks mmpl _ W
    (cliGhostAllocHooks_f3CliGhostHooksFixed hsvc_real hsvc_sub hreal_no hsub_no
      hPl hKeepMallocng γ tp hAlloc hDealloc hRealloc hMemset hMemcpy hMemcpyExact hMemsetAcp)

theorem codecHooksPlaced_f3CliGhostHooksFixed [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {T : F3GhostEntryTargets}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hAlloc : subroutine_ok P_sub T.alloc
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim false))
    (hDealloc : subroutine_ok P_sub T.dealloc
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hRealloc : subroutine_ok P_sub T.realloc
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hMemset : ∃ f, fMemset = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpy : ∃ f, fMemcpy = some f ∧
      (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
      (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
      HookOk f memcpyRegionSpec ∧
      HookOk f sessionMemcpyRegionSpec ∧
      HookOk f framelessMemcpySpec ∧
      HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpyExact : ∀ f, fMemcpy = some f → HookExactMemcpy f)
    (hMemsetAcp : ∀ f, fMemset = some f →
      ∀ s : State, (f s).sigActions = s.sigActions ∧ (f s).oracle = s.oracle) :
    CodecHooksPlaced fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns
        (f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk fMemset fMemcpy)
        (cliExternsPlaced mmpl W)) :=
  codecHooksPlaced_of_hooks mmpl _ W
    (cliGhostAllocHooks_f3CliGhostHooksFixed hsvc_real hsvc_sub hreal_no hsub_no
      hPl hKeepMallocng γ tp hAlloc hDealloc hRealloc hMemset hMemcpy hMemcpyExact hMemsetAcp)

theorem publicApiDecHooksPlaced_f3CliGhostHooksFixed [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {T : F3GhostEntryTargets}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hAlloc : subroutine_ok P_sub T.alloc
      (rustCliAllocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim false))
    (hDealloc : subroutine_ok P_sub T.dealloc
      (rustCliDeallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hRealloc : subroutine_ok P_sub T.realloc
      (rustCliReallocBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hStrClone : subroutine_ok P_sub T.stringClone
      (stringCloneBudgetCondSpec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim))
    (hMemset : ∃ f, fMemset = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpy : ∃ f, fMemcpy = some f ∧
      (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
      (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
      HookOk f memcpyRegionSpec ∧
      HookOk f sessionMemcpyRegionSpec ∧
      HookOk f framelessMemcpySpec ∧
      HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpyExact : ∀ f, fMemcpy = some f → HookExactMemcpy f)
    (hMemsetAcp : ∀ f, fMemset = some f →
      ∀ s : State, (f s).sigActions = s.sigActions ∧ (f s).oracle = s.oracle) :
    PublicApiDecHooksPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns
        (f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk fMemset fMemcpy)
        (cliExternsPlaced mmpl W)) :=
  publicApiDecHooksPlaced_of_hooks mmpl _ W
    (cliGhostAllocHooks_f3CliGhostHooksFixed hsvc_real hsvc_sub hreal_no hsub_no
      hPl hKeepMallocng γ tp hAlloc hDealloc hRealloc hMemset hMemcpy hMemcpyExact hMemsetAcp)
    (stringClone_hookSat_f3CliGhostHooksFixed (cliExternsPlaced mmpl W)
      hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng γ tp hStrClone)

private theorem ls_hook_617_rocl_ok [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ sym) (withLsRoCl lsmpl spec) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hsat hmem

/-- Block-`617` `MainIoOfPlaced` on `cliGhostExterns (f3CliGhostHooksFixed ...) (cliExternsPlaced mmpl W)`
at `(ReadStdinBoundedEnv, ReadFileRuleEnvFixed cliIo.rd)`. -/
theorem mainIoOfPlaced_f3CliGhostHooksFixed [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {T : F3GhostEntryTargets}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hReadFileCond : ∀ γ tp, subroutine_ok P_sub T.readFile
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack))
    (hReadStdinCond : ∀ γ tp, subroutine_ok P_sub T.readStdin
      (readStdinBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack))
    (γ : GhostName) (tp : BitVec 64) :
    MainIoOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns
        (f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk fMemset fMemcpy)
        (cliExternsPlaced mmpl W))
      cliIo stk ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd) where
  readStdin := ls_hook_617_rocl_ok
    ⟨f3ReadStdinGhostHookFine keep P_real P_sub T.readStdin mmpl brkStart lim stk,
     cliGhostExterns_readStdin_some _ _ rfl,
     f3ReadStdinGhostHookFine_ok_bounded hsvc_real hsvc_sub hreal_no hsub_no
       hPl hKeepMallocng hstk hReadStdinCond γ tp⟩
  readFile := ls_hook_617_rocl_ok
    ⟨f3ReadFileFixedGhostHookFine keep P_real P_sub T.readFile mmpl brkStart lim stk,
     cliGhostExterns_readFile_some _ _ rfl,
     f3ReadFileFixedGhostHookFine_ok_lit hsvc_real hsvc_sub hreal_no hsub_no
       hPl hKeepMallocng hstk hReadFileCond γ tp⟩
  writeFile := ls_hook_617_rocl_ok
    ⟨writeFileHook,
     (cliGhostExterns_other _ _
       (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
       (cliExternsPlaced_writeFile mmpl W),
     writeFileHook_ok_placed _ lim stk⟩
  writeStdout := ls_hook_617_rocl_ok
    ⟨writeStdoutHook,
     (cliGhostExterns_other _ _
       (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
       (cliExternsPlaced_writeStdout mmpl W),
     writeStdoutHook_ok_placed _ lim stk⟩

theorem hReadFixed_of_f3CliGhostHooksFixed [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {T : F3GhostEntryTargets}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {fMemset fMemcpy : Option (State → State)}
    {baseExt : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i
      (cliGhostExterns
        (f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk fMemset fMemcpy) baseExt)]
    [CryptoVerification.LsBlockBound bi]
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hReadFileCond : ∀ γ tp, subroutine_ok P_sub T.readFile
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack))
    (γ : GhostName) (tp : BitVec 64)
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk (ReadFileRuleEnvFixed cliIo.rd)) :=
  hRead_of_f3ReadFileFixedGhostHookFine
    (cliGhostExterns_readFile_some _ baseExt rfl)
    hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng hstk hReadFileCond γ tp hi hunmut

theorem hReadFixed_withPanics_of_f3CliGhostHooksFixed [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {T : F3GhostEntryTargets}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat}
    {fMemset fMemcpy : Option (State → State)}
    {baseExt : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i
      (Rust.withPanics
        (cliGhostExterns
          (f3CliGhostHooksFixed keep P_real P_sub T mmpl brkStart lim stk fMemset fMemcpy) baseExt))]
    [CryptoVerification.LsBlockBound bi]
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hstk : extHookStack ≤ stk)
    (hReadFileCond : ∀ γ tp, subroutine_ok P_sub T.readFile
      (readFileAnyBudgetCondSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim extHookStack))
    (γ : GhostName) (tp : BitVec 64)
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk (ReadFileRuleEnvFixed cliIo.rd)) :=
  hRead_withPanics_of_f3ReadFileFixedGhostHookFine
    (cliGhostExterns_readFile_some _ baseExt rfl)
    hsvc_real hsvc_sub hreal_no hsub_no hPl hKeepMallocng hstk hReadFileCond γ tp hi hunmut

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
