/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.IoSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M6Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `main` Hop M6 (`M+0xf70 .. M+0xfb4` + `free_args`, Block `617`)

Verifies `main`'s output/cleanup epilogue (`M+0xf70 → M+0xb80`) on Block `617` under
`[LibsignalPlacement]` and `RustCliAllocBudget M`, threading `A.pool` across `write_stdout`, `out`
and `input` deallocation, and `free_args` into `ExitKPoolPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M6PlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.SignalSession (lsRustDeallocSymCli lsWriteStdoutSym)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtM6Placed AtRetPlaced IoModel LsCodeInv WriteStdoutGhost argsBuf locals
   m6CellsPlaced mPcPlaced mProgPlaced mainFrameSize mainOom mainSaved main_call_rocl ownedBytes)
open CryptoVerification.SignalSession.Cli.MainHops.M6PlacedHelpers
  (argsBuf_free_ne argsBuf_free_zero bit0_of_getLsbD0 extractLsb0_of_getLsbD0
   layoutOk_slice_of_ne layoutOk_u8_of_ne m6CellsPlacedRest m6CellsPlacedRest_entails_memRegion
   m6CellsPlaced_eq ownedBytesRest ownedBytes_free_ne ownedBytes_free_zero ownedBytes_unpack
   shl4_toNat_eq spAligned_of_s0 stackAt_split_ge)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget RustLayoutOk
   SeqEnv rustDeallocEvents rustCliDeallocBudgetExternSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (WriteStdoutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced mainIoBoundedPlaced_iff_mainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (ExitKPlaced MainCalleesBlk617 retMem_of_pool)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
  (main_dealloc_fs_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced exitKPoolPlaced_of_exitKPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (MainIoPlaced writeStdoutSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem m5_seq_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => sm.pc = mid → sm.status = .Running → CodeOk sm.mem →
        SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont hpcm hrunm (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

namespace M6Helpers

theorem step_writeStdout_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {hookStack : Nat} {fsp ret_pc ret outPtr : BitVec 64}
    {out : List (BitVec 8)}
    {files0 : String → Option FsEntry} {tr0 : List TraceEvent}
    {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hw : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlaced A lim hookStack)))
    (hpc : s.pc = lsρ lsWriteStdoutSym)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = fsp)
    (hal : s.spAligned = true)
    (hinv : CodeOk s.mem)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = outPtr)
    (hx1 : (s.readReg64 .x1).toNat = out.length)
    (hfit : FitsEnv M lim st WriteStdoutEnv)
    (hfiles_eq : s.fs.files = files0)
    (htr_eq : s.trace = tr0)
    (hP : P ⊢ (outPtr ↦ₛ out) ∗ stackAt fsp hookStack ∗ A.pool lim st s ∗ F)
    (hk : ∀ (sm : State) (evs : List AllocEvent),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      CalleeSavedPreserved s sm →
      CodeOk sm.mem →
      WriteStdoutEnv evs →
      sm.readReg64 .x0 = 0#64 →
      sm.fs.files = files0 →
      tr0 <+: sm.trace →
      ProcessOutcome.traceStreamBytes .stdout sm.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 ++ out →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sm
        ((outPtr ↦ₛ out) ∗ stackAt fsp hookStack ∗ A.pool lim (M.stepEvents evs st) sm ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s P Q Qp oom := by
  refine main_call_rocl (x := (WriteStdoutGhost.mk outPtr out, st)) hw hinv hpc hrun hal hlr
    (F := F) ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    dsimp only [writeStdoutSpecPlaced]
    simp only [hsp_eq, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    dsimp only [writeStdoutSpecPlaced]
    rw [hsp_eq]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => ?_
    refine SepWPp.pure_elim fun ⟨hevs, hx0m, hfiles, hpref, hstdout⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hk sm evs hpcm hrunm (hspm.trans hsp_eq) hcsm hinv_m hevs hx0m
        (hfiles.trans hfiles_eq) (htr_eq ▸ hpref) (htr_eq ▸ hstdout))

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

theorem step_dealloc_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {fsp p ret_pc ret : BitVec 64} {size align : Nat}
    {files0 : String → Option FsEntry} {tr0 : List TraceEvent}
    {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hda : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs))
    (hpc : s.pc = lsρ lsRustDeallocSymCli)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = fsp)
    (hal : s.spAligned = true)
    (hinv : CodeOk s.mem)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hlay : LayoutOk size align)
    (hal_le : align ≤ 2 ^ 31 := by decide)
    (hfiles_eq : s.fs.files = files0)
    (htr_eq : s.trace = tr0)
    (hP : P ⊢ A.pool lim st s ∗ A.live p size align ∗ memRegion p size ∗
      stackAt fsp extHookStack ∗ F)
    (hk : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      CalleeSavedPreserved s sm →
      CodeOk sm.mem →
      sm.trace = tr0 →
      sm.fs.files = files0 →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sm
        (A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sm ∗
          stackAt fsp extHookStack ∗ F) Q Qp oom)
    (hlr_ls : LsRetAddr624 ret_pc := by simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s P Q Qp oom := by
  have hrlay : RustLayoutOk size align := ⟨hlay, hal_le⟩
  refine main_call_rocl (x := (p, size, align, st)) hda hinv hpc hrun hal hlr (F := F)
    ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    simp only [hsp_eq, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hrlay, by rwa [hlr]⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    rw [hsp_eq]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_eq => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hk sm hpcm hrunm (hspm.trans hsp_eq) hcsm hinv_m
        (htrm.trans htr_eq) ((congrArg FsState.files hfs_eq).trans hfiles_eq))

end M6Helpers

/-! ## Factored Tail Stages (`M+0xb6c`, `M+0xfa0`, `M+0xf8c`) & End-to-End `main_m6_pool_proof_placed` -/

private theorem main_m6_from_b6c_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st3 : M.σ}
    {s0 s s1 s3 : State} {ok : Bool} {n code : Nat}
    {stk : Nat} {buf outCap outPtr inCap inPtr : BitVec 64}
    {out : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hdealloc : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs))
    (hsp0 : s0.spAligned = true)
    (hsub_le64 : stk - mainFrameSize ≤ 2 ^ 64)
    (hext_le : extHookStack ≤ stk - mainFrameSize)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => s'.fs.files = s.fs.files ∧
        (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
            ProcessOutcome.traceStreamBytes .stdout s'.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
         else code = 2 ∧ s'.trace = s.trace)) Q Qp)
    (hfiles1 : s1.fs.files = s.fs.files)
    (hout_post1 : if ok then code = 0 ∧ s.trace <+: s1.trace ∧
        ProcessOutcome.traceStreamBytes .stdout s1.trace =
          ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
      else code = 2 ∧ s1.trace = s.trace)
    (hpc3 : s3.pc = (blkPl_617).base + 2924#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 1248#64)
    (hfp3 : s3.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hinv3 : CodeOk s3.mem)
    (hvregs3 : s3.vregs.calleeSaved = s0.vregs.calleeSaved)
    (hx19_3 : s3.readReg64 (.gpr 19#5) = buf)
    (hx26_3 : (s3.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx24_3 : s3.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (htr3 : s3.trace = s1.trace)
    (hfiles3 : s3.fs.files = s1.fs.files) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s3
      (argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
        ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
        ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
        m6CellsPlacedRest (s0.sp - 1248#64) ∗
        stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗
        A.pool lim st3 s3 ∗ anyHeap)
      Q Qp (mainOom s0) := by
  set cap := BitVec.ofNat 64 n
  by_cases hcap0 : cap = 0#64
  · apply m5_seq_placed hinv3 (mid := (blkPl_617).base + 2944#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro hpcm hrunm hinv_m
    refine SepWPp.weaken_pre ?_ (hexit _ st3 code ?_ ?_)
    · rw [hcap0]
      refine Entails.trans
        (sepConj_mono_left (argsBuf_free_zero A.repAlloc buf ps)) ?_
      rw [emp_sepConj]
      have hcells :=
        m6CellsPlacedRest_entails_memRegion
          (s0.sp - 1248#64) outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr
      have hreord0 :
          mainSaved s0 ∗
            ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
            ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗
            ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
            ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗
            ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
            m6CellsPlacedRest (s0.sp - 1248#64) ∗
            stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗ A.pool lim st3 s3 ∗ anyHeap =
          (((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
            ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗
            ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
            ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗
            ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
            m6CellsPlacedRest (s0.sp - 1248#64)) ∗
          mainSaved s0 ∗ stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗
          A.pool lim st3 s3 ∗ anyHeap := by
        sep_ac_rfl
      rw [hreord0]
      refine Entails.trans (sepConj_mono_left hcells) ?_
      unfold CryptoVerification.SignalSession.Cli.MainHops.retMem mainFrameSize
      simp only [RustCliAllocBudget.atState_pool, RustCliAllocBudget.pool_setPC,
        RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPState,
        RustCliAllocBudget.pool_advancePC]
      exact Entails.of_eq (by sep_ac_rfl)
    · refine ⟨⟨hpcm,
          hrunm, by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], hinv_m,
          by simp only [arm64_norm, *], hsp0⟩,
        by simp only [arm64_norm, *]⟩
    · refine ⟨by simp only [arm64_norm, hfiles3, hfiles1], ?_⟩
      simp only [arm64_norm, htr3]
      exact hout_post1
  · have hbeq : (cap == 0#64) = false := beq_false_of_ne hcap0
    refine SepWPp.weaken_pre
      (sepConj_mono_left (argsBuf_free_ne A.repAlloc hcap0)) ?_
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hcap_lt => ?_
    apply m5_seq_placed hinv3 (mid := lsρ lsRustDeallocSymCli)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro _ _ hinv_d
    rw [stackAt_split_ge (s0.sp - 1248#64) hext_le hsub_le64]
    refine M6Helpers.step_dealloc_placed hdealloc (st := st3)
      (fsp := s0.sp - 1248#64) (p := buf) (size := cap.toNat * 16) (align := 8)
      (ret_pc := (blkPl_617).base + 2944#64) (files0 := s.fs.files) (tr0 := s1.trace)
      (F := mainSaved s0 ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
        ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
        ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
        m6CellsPlacedRest (s0.sp - 1248#64) ∗
        memRegion ((s0.sp - 1248#64) - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - extHookStack) ∗ anyHeap)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (spAligned_of_s0 hsp0 (by simp only [arm64_norm, hsp3]))
      hinv_d
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; exact shl4_toNat_eq hcap_lt)
      (by simp only [arm64_norm, *])
      (layoutOk_slice_of_ne hcap0 hcap_lt)
      (by decide)
      (by simp only [arm64_norm, hfiles3, hfiles1])
      (by simp only [arm64_norm, htr3])
      ?_
      fun sm hpcm hrunm hspm hcsm hinvm htrm hfilesm => ?_
    · simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64]
      dsimp only [RustCliAllocBudget.repAlloc]
      exact Entails.of_eq (by sep_ac_rfl)
    · rcases hcsm with ⟨_, _, _, _, _, _, _, hx26m, _, _, hfpm, hvregsm⟩
      simp only [arm64_norm, *] at hx26m hfpm hvregsm
      have hatRet : AtRetPlaced CodeOk s0 sm code :=
        ⟨⟨hpcm, hrunm, hspm, hfpm, hinvm, hvregsm, hsp0⟩,
         by rw [hx26m]; exact hx26_3⟩
      let st4 := M.stepEvents (rustDeallocEvents (cap.toNat * 16) 8) st3
      refine SepWPp.weaken_pre ?_
        (hexit sm st4 code hatRet ⟨hfilesm, by rw [htrm]; exact hout_post1⟩)
      have hcells :=
        m6CellsPlacedRest_entails_memRegion
          (s0.sp - 1248#64) outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr
      have hreord :
          A.pool lim st4 sm ∗ stackAt (s0.sp - 1248#64) extHookStack ∗
            (mainSaved s0 ∗
              ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
              ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
              ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
              m6CellsPlacedRest (s0.sp - 1248#64) ∗
              memRegion ((s0.sp - 1248#64) - BitVec.ofNat 64 (stk - mainFrameSize))
                (stk - mainFrameSize - extHookStack) ∗ anyHeap) =
          ((((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
            ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
            ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
            m6CellsPlacedRest (s0.sp - 1248#64)) ∗
            mainSaved s0 ∗
            (memRegion ((s0.sp - 1248#64) - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - extHookStack) ∗ stackAt (s0.sp - 1248#64) extHookStack) ∗
            A.pool lim st4 sm ∗ anyHeap) := by
        sep_ac_rfl
      rw [hreord, ← stackAt_split_ge (s0.sp - 1248#64) hext_le hsub_le64]
      refine Entails.trans (sepConj_mono_left hcells) ?_
      unfold CryptoVerification.SignalSession.Cli.MainHops.retMem mainFrameSize
      simp only [RustCliAllocBudget.atState_pool]
      exact Entails.of_eq (by sep_ac_rfl)

private theorem main_m6_from_fa0_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st2 : M.σ}
    {s0 s s1 s2 : State} {ok : Bool} {n code : Nat}
    {stk : Nat} {buf outCap outPtr inCap inPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hdealloc : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs))
    (hsp0 : s0.spAligned = true)
    (hsub_le64 : stk - mainFrameSize ≤ 2 ^ 64)
    (hext_le : extHookStack ≤ stk - mainFrameSize)
    (hin_le : inp.length ≤ inCap.toNat)
    (hin_lt : inCap.toNat < 2 ^ 63)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => s'.fs.files = s.fs.files ∧
        (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
            ProcessOutcome.traceStreamBytes .stdout s'.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
         else code = 2 ∧ s'.trace = s.trace)) Q Qp)
    (hfiles1 : s1.fs.files = s.fs.files)
    (hout_post1 : if ok then code = 0 ∧ s.trace <+: s1.trace ∧
        ProcessOutcome.traceStreamBytes .stdout s1.trace =
          ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
      else code = 2 ∧ s1.trace = s.trace)
    (hpc2 : s2.pc = (blkPl_617).base + 4000#64)
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 1248#64)
    (hfp2 : s2.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hinv2 : CodeOk s2.mem)
    (hvregs2 : s2.vregs.calleeSaved = s0.vregs.calleeSaved)
    (hx19_2 : s2.readReg64 (.gpr 19#5) = buf)
    (hx20_2 : s2.readReg64 (.gpr 20#5) = inCap)
    (hx26_2 : (s2.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx24_2 : s2.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (htr2 : s2.trace = s1.trace)
    (hfiles2 : s2.fs.files = s1.fs.files) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s2
      (((inPtr ↦ₛ inp) ∗ ownedBytesRest A.repAlloc inCap inPtr inp) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
        ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
        ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
        m6CellsPlacedRest (s0.sp - 1248#64) ∗
        stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗
        A.pool lim st2 s2 ∗ anyHeap)
      Q Qp (mainOom s0) := by
  by_cases hin0 : inCap = 0#64
  · subst hin0
    rw [← hsp2]
    apply m5_seq_placed hinv2 (mid := (blkPl_617).base + 2924#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro _ _ hinv_m
    rw [hsp2]
    refine SepWPp.weaken_pre ?_
      (main_m6_from_b6c_placed (st3 := st2) (n := n) (buf := buf) (outCap := outCap)
        (outPtr := outPtr) (inCap := 0#64) (inPtr := inPtr) (out := out) (ps := ps)
        hdealloc hsp0 hsub_le64 hext_le hexit hfiles1 hout_post1
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        hinv_m
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]))
    simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64]
    refine Entails.trans
      (sepConj_mono_left (ownedBytes_free_zero A.repAlloc inPtr inp hin_le)) ?_
    rw [emp_sepConj]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hbeq : (inCap == 0#64) = false := beq_false_of_ne hin0
    rw [← hsp2]
    apply m5_seq_placed hinv2 (mid := lsρ lsRustDeallocSymCli)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro _ _ hinv_d
    rw [hsp2, stackAt_split_ge (s0.sp - 1248#64) hext_le hsub_le64]
    refine M6Helpers.step_dealloc_placed hdealloc (st := st2)
      (fsp := s0.sp - 1248#64) (p := inPtr) (size := inCap.toNat) (align := 1)
      (ret_pc := (blkPl_617).base + 4020#64) (files0 := s1.fs.files) (tr0 := s1.trace)
      (F := argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
        ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
        ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
        m6CellsPlacedRest (s0.sp - 1248#64) ∗
        memRegion ((s0.sp - 1248#64) - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - extHookStack) ∗ anyHeap)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (spAligned_of_s0 hsp0 (by simp only [arm64_norm, hsp2]))
      hinv_d
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (layoutOk_u8_of_ne hin0 hin_lt)
      (by decide)
      (by simp only [arm64_norm, hfiles2])
      (by simp only [arm64_norm, htr2])
      ?_
      fun sm hpcm hrunm hspm hcsm hinvm htrm hfilesm => ?_
    · simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64]
      have hfree := ownedBytes_free_ne A.repAlloc (ptr := inPtr) hin0 hin_le hin_lt
      refine Entails.trans (sepConj_mono_left hfree) ?_
      dsimp only [RustCliAllocBudget.repAlloc]
      exact Entails.of_eq (by sep_ac_rfl)
    · rcases hcsm with ⟨hx19m, _, _, _, _, hx24m, _, hx26m, _, _, hfpm, hvregsm⟩
      simp only [arm64_norm, *] at hx19m hx24m hx26m hfpm hvregsm
      have hw26m : (sm.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code := by
        rw [hx26m]; exact hx26_2
      apply m5_seq_placed hinvm (mid := (blkPl_617).base + 2924#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      intro _ _ hinvm2
      refine SepWPp.weaken_pre ?_
        (main_m6_from_b6c_placed
          (st3 := M.stepEvents (rustDeallocEvents inCap.toNat 1) st2)
          (n := n) (buf := buf) (outCap := outCap) (outPtr := outPtr)
          (inCap := inCap) (inPtr := inPtr) (out := out) (ps := ps)
          hdealloc hsp0 hsub_le64 hext_le hexit hfiles1 hout_post1
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          hinvm2
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, hw26m])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]))
      simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64]
      rw [stackAt_split_ge (s0.sp - 1248#64) hext_le hsub_le64]
      exact Entails.of_eq (by sep_ac_rfl)

private theorem main_m6_from_f8c_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st1 : M.σ}
    {s0 s s1 : State} {ok : Bool} {n code : Nat}
    {stk : Nat} {buf outCap outPtr inCap inPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hdealloc : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs))
    (hsp0 : s0.spAligned = true)
    (hsub_le64 : stk - mainFrameSize ≤ 2 ^ 64)
    (hext_le : extHookStack ≤ stk - mainFrameSize)
    (hout_le : out.length ≤ outCap.toNat)
    (hout_lt : outCap.toNat < 2 ^ 63)
    (hin_le : inp.length ≤ inCap.toNat)
    (hin_lt : inCap.toNat < 2 ^ 63)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => s'.fs.files = s.fs.files ∧
        (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
            ProcessOutcome.traceStreamBytes .stdout s'.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
         else code = 2 ∧ s'.trace = s.trace)) Q Qp)
    (hpc1 : s1.pc = (blkPl_617).base + 3980#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1248#64)
    (hfp1 : s1.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hinv1 : CodeOk s1.mem)
    (hvregs1 : s1.vregs.calleeSaved = s0.vregs.calleeSaved)
    (hx19_1 : s1.readReg64 (.gpr 19#5) = buf)
    (hx26_1 : (s1.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx24_1 : s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hfiles1 : s1.fs.files = s.fs.files)
    (hout_post1 : if ok then code = 0 ∧ s.trace <+: s1.trace ∧
        ProcessOutcome.traceStreamBytes .stdout s1.trace =
          ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
      else code = 2 ∧ s1.trace = s.trace) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s1
      (((outPtr ↦ₛ out) ∗ ownedBytesRest A.repAlloc outCap outPtr out) ∗
        ((inPtr ↦ₛ inp) ∗ ownedBytesRest A.repAlloc inCap inPtr inp) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
        ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
        ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
        m6CellsPlacedRest (s0.sp - 1248#64) ∗
        stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗
        A.pool lim st1 s1 ∗ anyHeap)
      Q Qp (mainOom s0) := by
  by_cases hout0 : outCap = 0#64
  · subst hout0
    rw [← hsp1]
    apply m5_seq_placed hinv1 (mid := (blkPl_617).base + 4000#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro _ _ hinv_m
    rw [hsp1]
    refine SepWPp.weaken_pre ?_
      (main_m6_from_fa0_placed (st2 := st1) (n := n) (buf := buf) (outCap := 0#64)
        (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr) (out := out) (inp := inp) (ps := ps)
        hdealloc hsp0 hsub_le64 hext_le hin_le hin_lt
        hexit hfiles1 hout_post1
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        hinv_m
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm]))
    simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64]
    refine Entails.trans
      (sepConj_mono_left (ownedBytes_free_zero A.repAlloc outPtr out hout_le)) ?_
    rw [emp_sepConj]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hbeq : (outCap == 0#64) = false := beq_false_of_ne hout0
    rw [← hsp1]
    apply m5_seq_placed hinv1 (mid := lsρ lsRustDeallocSymCli)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro _ _ hinv_d
    rw [hsp1, stackAt_split_ge (s0.sp - 1248#64) hext_le hsub_le64]
    refine M6Helpers.step_dealloc_placed hdealloc (st := st1)
      (fsp := s0.sp - 1248#64) (p := outPtr) (size := outCap.toNat) (align := 1)
      (ret_pc := (blkPl_617).base + 4000#64) (files0 := s1.fs.files) (tr0 := s1.trace)
      (F := ((inPtr ↦ₛ inp) ∗ ownedBytesRest A.repAlloc inCap inPtr inp) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
        ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
        ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
        m6CellsPlacedRest (s0.sp - 1248#64) ∗
        memRegion ((s0.sp - 1248#64) - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - extHookStack) ∗ anyHeap)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (spAligned_of_s0 hsp0 (by simp only [arm64_norm, hsp1]))
      hinv_d
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (layoutOk_u8_of_ne hout0 hout_lt)
      (by decide)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      ?_
      fun sm hpcm hrunm hspm hcsm hinvm htrm hfilesm => ?_
    · simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64]
      have hfree :=
        ownedBytes_free_ne A.repAlloc (ptr := outPtr) hout0 hout_le hout_lt
      refine Entails.trans (sepConj_mono_left hfree) ?_
      dsimp only [RustCliAllocBudget.repAlloc]
      exact Entails.of_eq (by sep_ac_rfl)
    · rcases hcsm with ⟨hx19m, hx20m, _, _, _, hx24m, _, hx26m, _, _, hfpm, hvregsm⟩
      simp only [arm64_norm, *] at hx19m hx20m hx24m hx26m hfpm hvregsm
      refine SepWPp.weaken_pre ?_
        (main_m6_from_fa0_placed
          (st2 := M.stepEvents (rustDeallocEvents outCap.toNat 1) st1)
          (n := n) (buf := buf) (outCap := outCap) (outPtr := outPtr)
          (inCap := inCap) (inPtr := inPtr) (out := out) (inp := inp) (ps := ps)
          hdealloc hsp0 hsub_le64 hext_le hin_le hin_lt hexit hfiles1 hout_post1
          hpcm hrunm hspm hfpm hinvm hvregsm hx19m hx20m
          (by rw [hx26m]; exact hx26_1) hx24m htrm hfilesm)
      rw [stackAt_split_ge (s0.sp - 1248#64) hext_le hsub_le64]
      exact Entails.of_eq (by sep_ac_rfl)

/-- `{StdinEnv ReadEnv}`-parametric `MainIoOfPlaced` pool-retaining M6 proof from `M+0xf70`
(`AtM6Placed`) to `ExitKPoolPlaced` at `M+0xb80`. -/
theorem main_m6_of_pool_proof_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {s0 s : State} {ok : Bool} {n : Nat}
    {stk hookStack resStack : Nat} {buf outCap outPtr inCap inPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hfit : ok = true → FitsEnv M lim st WriteStdoutEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs : AtM6Placed CodeOk s0 s ok n buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => s'.fs.files = s.fs.files ∧
        (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
            ProcessOutcome.traceStreamBytes .stdout s'.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
         else code = 2 ∧ s'.trace = s.trace)) Q Qp) :
    ProofLib.SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
            (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) := by
  have hdealloc : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs) :=
    main_dealloc_fs_placed_ok hc.allocFs
  have hwstdout : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlaced A lim hookStack)) :=
    hio.writeStdout
  clear hc hio
  refine SepWPp.weaken_pre
    (sepConj_mono
      (ownedBytes_unpack A.repAlloc outCap outPtr out)
      (sepConj_mono_left (ownedBytes_unpack A.repAlloc inCap inPtr inp))) ?_
  rw [m6CellsPlaced_eq]
  change SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
    ((⌜out.length ≤ outCap.toNat ∧ outCap.toNat < 2 ^ 63 ∧ outPtr ≠ 0⌝ ∗
      ((outPtr ↦ₛ out) ∗ ownedBytesRest A.repAlloc outCap outPtr out)) ∗
      ((⌜inp.length ≤ inCap.toNat ∧ inCap.toNat < 2 ^ 63 ∧ inPtr ≠ 0⌝ ∗
        ((inPtr ↦ₛ inp) ∗ ownedBytesRest A.repAlloc inCap inPtr inp)) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        (((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
          ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
          m6CellsPlacedRest (s0.sp - 1248#64)) ∗
        stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗ A.pool lim st s ∗ anyHeap))
    Q Qp (mainOom s0)
  have hpure_pull :
      (⌜out.length ≤ outCap.toNat ∧ outCap.toNat < 2 ^ 63 ∧ outPtr ≠ 0⌝ ∗
        ((outPtr ↦ₛ out) ∗ ownedBytesRest A.repAlloc outCap outPtr out)) ∗
        ((⌜inp.length ≤ inCap.toNat ∧ inCap.toNat < 2 ^ 63 ∧ inPtr ≠ 0⌝ ∗
          ((inPtr ↦ₛ inp) ∗ ownedBytesRest A.repAlloc inCap inPtr inp)) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          (((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
            ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
            ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
            m6CellsPlacedRest (s0.sp - 1248#64)) ∗
          stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗ A.pool lim st s ∗ anyHeap) =
      ⌜out.length ≤ outCap.toNat ∧ outCap.toNat < 2 ^ 63 ∧ outPtr ≠ 0⌝ ∗
        ⌜inp.length ≤ inCap.toNat ∧ inCap.toNat < 2 ^ 63 ∧ inPtr ≠ 0⌝ ∗
        (((outPtr ↦ₛ out) ∗ ownedBytesRest A.repAlloc outCap outPtr out) ∗
          ((inPtr ↦ₛ inp) ∗ ownedBytesRest A.repAlloc inCap inPtr inp) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
          ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
          m6CellsPlacedRest (s0.sp - 1248#64) ∗
          stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗
          A.pool lim st s ∗ anyHeap) := by
    sep_ac_rfl
  rw [hpure_pull]
  refine SepWPp.pure_elim fun ⟨hout_le, hout_lt, _⟩ => ?_
  refine SepWPp.pure_elim fun ⟨hin_le, hin_lt, _⟩ => ?_
  rcases hs with ⟨⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩, hw22, hx19, hx24⟩
  change s.pc = (blkPl_617).base + 3952#64 at hpc
  change s.sp = s0.sp - 1248#64 at hsp
  change s.readReg64 (.gpr 29#5) = s0.sp - 96#64 at hfp
  change s.vregs.calleeSaved = s0.vregs.calleeSaved at hvregs
  have hsub_le64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  have hhook_le : hookStack ≤ stk - mainFrameSize := by omega
  have hext_le : extHookStack ≤ stk - mainFrameSize := by omega
  cases ok
  · have hbit := extractLsb0_of_getLsbD0 hw22
    have hb0 := bit0_of_getLsbD0 hw22
    rw [← hsp]
    apply m5_seq_placed hinv (mid := (blkPl_617).base + 3980#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro _ _ hinv_m
    rw [hsp]
    refine SepWPp.weaken_pre ?_
      (main_m6_from_f8c_placed (st1 := st) (ok := false) (n := n) (code := 2)
        (buf := buf) (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
        (out := out) (inp := inp) (ps := ps)
        hdealloc hsp0 hsub_le64 hext_le hout_le hout_lt hin_le hin_lt hexit
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        hinv_m
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm])
        ⟨rfl, by simp only [arm64_norm]⟩)
    simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64]
    exact Entails.refl _
  · have hfit_w : FitsEnv M lim st WriteStdoutEnv := hfit rfl
    have hbit := extractLsb0_of_getLsbD0 hw22
    have hb0 := bit0_of_getLsbD0 hw22
    rw [← hsp]
    apply m5_seq_placed hinv (mid := lsρ lsWriteStdoutSym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro _ _ hinv_w
    rw [hsp, stackAt_split_ge (s0.sp - 1248#64) hhook_le hsub_le64]
    refine M6Helpers.step_writeStdout_placed hwstdout (st := st)
      (fsp := s0.sp - 1248#64) (ret_pc := (blkPl_617).base + 3972#64) (outPtr := outPtr)
      (out := out) (files0 := s.fs.files) (tr0 := s.trace)
      (F := ownedBytesRest A.repAlloc outCap outPtr out ∗
        ((inPtr ↦ₛ inp) ∗ ownedBytesRest A.repAlloc inCap inPtr inp) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
        ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
        ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
        m6CellsPlacedRest (s0.sp - 1248#64) ∗
        memRegion ((s0.sp - 1248#64) - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - hookStack) ∗
        anyHeap)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (spAligned_of_s0 hsp0 (by simp only [arm64_norm, hsp]))
      hinv_w
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
      hfit_w
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by
        simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
          RustCliAllocBudget.pool_writeReg64]
        exact Entails.of_eq (by sep_ac_rfl))
      fun sm evs hpcm hrunm hspm hcsm hinvm _hevs hx0m hfilesm hprefm hstdoutm => ?_
    rcases hcsm with ⟨hx19m, _, _, _, _, hx24m, _, hx26m, _, _, hfpm, hvregsm⟩
    simp only [arm64_norm, *] at hx19m hx24m hx26m hfpm hvregsm
    apply m5_seq_placed hinvm (mid := (blkPl_617).base + 3980#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro _ _ hinvm2
    refine SepWPp.weaken_pre ?_
      (main_m6_from_f8c_placed (st1 := M.stepEvents evs st) (ok := true) (n := n) (code := 0)
        (buf := buf) (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
        (out := out) (inp := inp) (ps := ps)
        hdealloc hsp0 hsub_le64 hext_le hout_le hout_lt hin_le hin_lt hexit
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        hinvm2
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        ⟨rfl, by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩)
    simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
      RustCliAllocBudget.pool_writeReg64]
    rw [stackAt_split_ge (s0.sp - 1248#64) hhook_le hsub_le64]
    exact Entails.of_eq (by sep_ac_rfl)

theorem main_m6_of_m6Env_pool_proof_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {s0 s : State} {ok : Bool} {n : Nat}
    {stk hookStack resStack : Nat} {buf outCap outPtr inCap inPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hfit : FitsEnv M lim st (SeqEnv (if ok then WriteStdoutEnv else (· = [])) FreeOnlyEvs))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs : AtM6Placed CodeOk s0 s ok n buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => s'.fs.files = s.fs.files ∧
        (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
            ProcessOutcome.traceStreamBytes .stdout s'.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
         else code = 2 ∧ s'.trace = s.trace)) Q Qp) :
    ProofLib.SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
            (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) :=
  main_m6_of_pool_proof_placed hc hio (fun hok => by subst hok; exact hfit.seq_left)
    hstk hstk64 hs hexit

theorem main_m6_of_proof_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {s0 s : State} {ok : Bool} {n : Nat}
    {stk hookStack resStack : Nat} {buf outCap outPtr inCap inPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hfit : ok = true → FitsEnv M lim st WriteStdoutEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs : AtM6Placed CodeOk s0 s ok n buf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => s'.fs.files = s.fs.files ∧
        (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
            ProcessOutcome.traceStreamBytes .stdout s'.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
         else code = 2 ∧ s'.trace = s.trace)) Q Qp) :
    ProofLib.SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
            (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) :=
  main_m6_of_pool_proof_placed hc hio hfit hstk hstk64 hs (exitKPoolPlaced_of_exitKPlaced hexit)

theorem main_m6_of_m6Env_proof_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {s0 s : State} {ok : Bool} {n : Nat}
    {stk hookStack resStack : Nat} {buf outCap outPtr inCap inPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hfit : FitsEnv M lim st (SeqEnv (if ok then WriteStdoutEnv else (· = [])) FreeOnlyEvs))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs : AtM6Placed CodeOk s0 s ok n buf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => s'.fs.files = s.fs.files ∧
        (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
            ProcessOutcome.traceStreamBytes .stdout s'.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
         else code = 2 ∧ s'.trace = s.trace)) Q Qp) :
    ProofLib.SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
            (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) :=
  main_m6_of_m6Env_pool_proof_placed hc hio hfit hstk hstk64 hs
    (exitKPoolPlaced_of_exitKPlaced hexit)

/-- Primary pool-retaining M6 proof from `M+0xf70` (`AtM6Placed`) to `ExitKPoolPlaced` at `M+0xb80`. -/
theorem main_m6_pool_proof_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {io : IoModel} {s0 s : State} {ok : Bool} {n : Nat}
    {stk hookStack resStack : Nat} {buf outCap outPtr inCap inPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hfit : ok = true → FitsEnv M lim st WriteStdoutEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs : AtM6Placed CodeOk s0 s ok n buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => s'.fs.files = s.fs.files ∧
        (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
            ProcessOutcome.traceStreamBytes .stdout s'.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
         else code = 2 ∧ s'.trace = s.trace)) Q Qp) :
    ProofLib.SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
            (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) :=
  main_m6_of_pool_proof_placed
    (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
    (out := out) (inp := inp) (ps := ps)
    hc ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio)
    hfit hstk hstk64 hs hexit

theorem main_m6_m6Env_pool_proof_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {io : IoModel} {s0 s : State} {ok : Bool} {n : Nat}
    {stk hookStack resStack : Nat} {buf outCap outPtr inCap inPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hfit : FitsEnv M lim st (SeqEnv (if ok then WriteStdoutEnv else (· = [])) FreeOnlyEvs))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs : AtM6Placed CodeOk s0 s ok n buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => s'.fs.files = s.fs.files ∧
        (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
            ProcessOutcome.traceStreamBytes .stdout s'.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
         else code = 2 ∧ s'.trace = s.trace)) Q Qp) :
    ProofLib.SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
            (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) :=
  main_m6_pool_proof_placed hc hio (fun hok => by subst hok; exact hfit.seq_left) hstk hstk64 hs hexit

theorem main_m6_proof_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {io : IoModel} {s0 s : State} {ok : Bool} {n : Nat}
    {stk hookStack resStack : Nat} {buf outCap outPtr inCap inPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hfit : ok = true → FitsEnv M lim st WriteStdoutEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs : AtM6Placed CodeOk s0 s ok n buf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => s'.fs.files = s.fs.files ∧
        (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
            ProcessOutcome.traceStreamBytes .stdout s'.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
         else code = 2 ∧ s'.trace = s.trace)) Q Qp) :
    ProofLib.SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
            (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) :=
  main_m6_pool_proof_placed hc hio hfit hstk hstk64 hs (exitKPoolPlaced_of_exitKPlaced hexit)

theorem main_m6_m6Env_proof_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {io : IoModel} {s0 s : State} {ok : Bool} {n : Nat}
    {stk hookStack resStack : Nat} {buf outCap outPtr inCap inPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hfit : FitsEnv M lim st (SeqEnv (if ok then WriteStdoutEnv else (· = [])) FreeOnlyEvs))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs : AtM6Placed CodeOk s0 s ok n buf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => s'.fs.files = s.fs.files ∧
        (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
            ProcessOutcome.traceStreamBytes .stdout s'.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
         else code = 2 ∧ s'.trace = s.trace)) Q Qp) :
    ProofLib.SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
            (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) :=
  main_m6_m6Env_pool_proof_placed hc hio hfit hstk hstk64 hs (exitKPoolPlaced_of_exitKPlaced hexit)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M6PlacedBudget
