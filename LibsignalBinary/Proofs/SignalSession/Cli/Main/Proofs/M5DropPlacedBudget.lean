/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropLoopCorePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropLoopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPanicsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopDropPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPanicsPlaced -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropStepsPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPlacedBudget

/-!
# Budget-Threaded Write-Error Cleanup Path `m5_drop_placed` (Block `617`)

Budget-threaded verification of `main`'s write-error cleanup path (`M+0xbcc / 0xbdc / 0xbf4 → M+0xf70`)
on Block `617`, advancing `A.pool` by `m5ErrEntryDropEvents errE ++ evsRest` with
`FreeOnlyEvs evsRest`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPlacedBudget

set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack reserveCap)
open CryptoVerification.RustHeap (RustAlloc arrayAt vecBuf)
open CryptoVerification.SignalSession (Inputs lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost dirEntryAt pathOf)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkLib_eq_617 blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtM6Placed CallV InMainPlaced IoModel LsCodeInv M5ErrEntryPlaced M5LoopErrPlaced argsBuf cell
   codeOk_pure commitFiles dirsAt dirsAt_nil inputOf locals localsBound localsCtx localsEnd
   localsFrom locals_carve_cell locals_focus locals_forget_cell
   locals_m5ErrCellsPlaced_forget_to_m6CellsPlaced m5ErrCellsPlaced m5ErrCellsPlaced_focus_tail
   m5ErrCellsPlaced_open_spills m5ErrMemPlaced m6CellsPlaced mPcPlaced mPcPlaced_bl_dealloc
   mPcPlaced_eq mProgPlaced mProgPlaced_eq mainFrameSize mainSaved ownedBytes seq_frozen_codeOk
   sepWPp_with_stk_le_two_pow_64 storesDirs storesDirs_length)
open CryptoVerification.SignalSession.Cli.MainHops.M5DropPlacedHelpers
  (layoutOk_dirBuf_of_cap_ne_zero layoutOk_u8_of_cap_ne_zero mul48_toNat_of_lt ofNat_ne_of_ne_lt
   seq_sepWP_pl)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget SeqEnv rustAllocEvents
   rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (writeFileEnv_nil)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropLoopCorePlacedBudget
  (m5_drop_loop_body_0xc04_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropLoopsPlacedBudget
  (m5_drop_dirs_tail_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPanicsPlacedBudget
  (step_dealloc_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPlacedBudget
  (M5LoopARestErrEnv M5LoopARestOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPathPlacedBudget
  (m5LoopABuildPathEvents m5LoopAPathCap)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopDropPlacedBudget
  (m5ErrEntryDropEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
  (argsBuf_atState_eq_repAlloc m5ErrCellsPlaced_atState_eq_repAlloc
   m5ErrEntryPlaced_heap_atState_eq_repAlloc ownedBytes_atState_eq_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)

attribute [local m5_st_pl ↓]
  RustCliAllocBudget.pool_setPC
  RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState
  RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32
  RustCliAllocBudget.pool_writeReg

local macro "m5_drop_fetch_vm" : term =>
  `(by simp only [arm64_norm]; try rfl)

/-- Split allocator event envelope for `m5_drop_placed` / `m5_drop_for_m5_placed` starting from
`errE : M5ErrEntryPlaced`. -/
def M5DropFromErrEnv (errE : M5ErrEntryPlaced) (evsDrop : List AllocEvent) : Prop :=
  ∃ evsRest, evsDrop = m5ErrEntryDropEvents errE ++ evsRest ∧ FreeOnlyEvs evsRest

-- Non-vacuity witness: path allocation on `Dir` (`"a"`, `"b"`) followed by `0xbdc` write-error
-- cleanup emits both `AllocEvent.alloc` and `m5ErrEntryDropEvents errE` inside
-- `SeqEnv (M5LoopARestOkEnv dir changed) FreeOnlyEvs`.
example :
    let dir : List (BitVec 8) := [0x61#8]
    let name : List (BitVec 8) := [0x62#8]
    let errE : M5ErrEntryPlaced :=
      .bdc (BitVec.ofNat 64 (m5LoopAPathCap dir name)) 1#64 []
    ∃ evsErr evsDrop evsRest,
      (∃ sz, AllocEvent.alloc sz ∈ evsErr ++ evsDrop) ∧
      m5ErrEntryDropEvents errE ≠ [] ∧
      (∀ ev ∈ m5ErrEntryDropEvents errE, ev ∈ evsErr ++ evsDrop) ∧
      (evsDrop = m5ErrEntryDropEvents errE ++ evsRest ∧ FreeOnlyEvs evsRest) ∧
      M5LoopARestErrEnv dir errE [(name, [])] evsErr ∧
      M5LoopARestOkEnv dir [(name, [])] (evsErr ++ evsDrop) := by
  refine ⟨m5LoopABuildPathEvents [0x61#8] [0x62#8] ++ [],
    m5ErrEntryDropEvents (.bdc (BitVec.ofNat 64 (m5LoopAPathCap [0x61#8] [0x62#8])) 1#64 []),
    [], ?_, ?_, ?_, ⟨by simp, FreeOnlyEvs.nil⟩, ?_, ?_⟩
  · exact ⟨1, by simp [m5LoopABuildPathEvents, rustAllocEvents]⟩
  · simp [m5ErrEntryDropEvents, rustDeallocEvents]
  · intro ev hev
    exact List.mem_append_right _ hev
  · exact Or.inl ⟨ConcatEnv.append rfl (writeFileEnv_nil (pathOf [0x61#8] [0x62#8]).length), rfl⟩
  · exact Or.inl (Or.inl
      (ConcatEnv.append
        (ConcatEnv.append rfl (writeFileEnv_nil (pathOf [0x61#8] [0x62#8]).length))
        rfl))

/-- Budget-threaded separation-logic memory at `M5LoopErrPlaced` (`M+0xbcc` / `M+0xbdc` / `M+0xbf4`),
pairing `MainHops.m5ErrMemPlaced A.repAlloc` (`A.repAlloc.pool = emp`) with `A.pool lim st s`. -/
def m5ErrMem {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 s : State) (stk n : Nat)
    (outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64)
    (out inp : List (BitVec 8))
    (ps : List (BitVec 64 × List (BitVec 8)))
    (g : StoresGhost) (k : Nat)
    (curEntries : List (List (BitVec 8) × List (BitVec 8)))
    (errE : M5ErrEntryPlaced) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  errE.heap A.repAlloc ∗
    vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr curEntries ∗
    ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
    ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
    argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
    mainSaved s0 ∗
    locals fsp
      (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
        inCap inPtr curCap curPtr g k) ∗
    stackAt fsp (stk - mainFrameSize) ∗
    A.pool lim st s ∗ anyHeap

theorem m5ErrMem_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State) (stk n : Nat)
    (outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64)
    (out inp : List (BitVec 8))
    (ps : List (BitVec 64 × List (BitVec 8)))
    (g : StoresGhost) (k : Nat)
    (curEntries : List (List (BitVec 8) × List (BitVec 8)))
    (errE : M5ErrEntryPlaced) :
    m5ErrMem A lim st s0 s stk n outCap outPtr inCap inPtr buf curCap curPtr
      out inp ps g k curEntries errE =
    m5ErrMemPlaced A.repAlloc s0 stk n
      outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k curEntries errE ∗
      A.pool lim st s := by
  unfold m5ErrMem m5ErrMemPlaced
  rw [A.repAlloc_pool, emp_sepConj]
  sep_ac_rfl

theorem m5ErrMem_eq_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State) (stk n : Nat)
    (outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64)
    (out inp : List (BitVec 8))
    (ps : List (BitVec 64 × List (BitVec 8)))
    (g : StoresGhost) (k : Nat)
    (curEntries : List (List (BitVec 8) × List (BitVec 8)))
    (errE : M5ErrEntryPlaced) :
    m5ErrMem A lim st s0 s stk n outCap outPtr inCap inPtr buf curCap curPtr
      out inp ps g k curEntries errE =
    m5ErrMemPlaced (A.atState lim st s) s0 stk n
      outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k curEntries errE := by
  dsimp only [m5ErrMem, m5ErrMemPlaced]
  rw [m5ErrEntryPlaced_heap_atState_eq_repAlloc,
    ownedBytes_atState_eq_repAlloc, ownedBytes_atState_eq_repAlloc,
    argsBuf_atState_eq_repAlloc, m5ErrCellsPlaced_atState_eq_repAlloc]
  rfl

/-! ## 0. Pure & Stack-Store Basic-Block Helpers Preserving `tpidrEl0` / `A.pool` -/

private theorem sepWPp_seq_codeOk_vm [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {H : LibsignalHooks} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_617).rebase (blkPl_617).base (hooksException H)) mid (s.setMem m_strip) Pre
        (fun sm' Pm =>
          ∀ m_real : Memory,
            ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            CodeOk (sm'.setMem m_real).mem →
            SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret (sm'.setMem m_real) Pm Q Qp oom)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s Pre Q Qp oom := by
  refine seq_frozen_codeOk (mid := mid) hinv ?_
  apply sepWP_seg_ls_vm
    (Q := (blkPC_617).rebase (blkPl_617).base (hooksException H))
    blkLib_eq_617 (mid := mid)
  intro m_strip
  refine SepWP.mono (hseg m_strip) fun sm' Pm hpc_m' hrun_m' hcont m_real hnsp => ?_
  exact SepWP.done hpc_m' hrun_m' (fun _ _ hfz => hcont m_real hnsp hfz)

private theorem step_bcc_zero_vm {prog : Program} {fnBase v38 v1b8 : BitVec 64}
    {s : State} {R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3020#64) (hrun : s.status = .Running) (hal : s.spAligned)
    (hx23 : s.readReg64 (.gpr 23#5) = 0#64)
    (f0 : prog.fetch (fnBase + 3020#64) =
      some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 8#5) (AddrMode.Offset Reg.sp 56#64)))
    (f1 : prog.fetch (fnBase + 3024#64) =
      some (Instr.str MemWidth.X64 (Reg.gpr 8#5) (AddrMode.Offset Reg.sp 440#64)))
    (f2 : prog.fetch (fnBase + 3028#64) =
      some (Instr.cbz RegWidth.W64 true (Reg.gpr 23#5) 16#64))
    (f3 : prog.fetch (fnBase + 3032#64) =
      some (Instr.b 28#64))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3060#64 → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.symtab = s.symtab → s'.vregs = s.vregs → s'.fs = s.fs → s'.trace = s.trace →
      s'.tpidrEl0 = s.tpidrEl0 →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      Q s' (((s.sp + 56#64) ↦₆₄ v38) ∗ ((s.sp + 440#64) ↦₆₄ v38) ∗ R)) :
    SepWP prog (fnBase + 3060#64) s
      (((s.sp + 56#64) ↦₆₄ v38) ∗ ((s.sp + 440#64) ↦₆₄ v1b8) ∗ R) Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl])
    (by simp only [wp_norm, arm64_norm])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])

private theorem step_bcc_dealloc_vm {prog : Program} {fnBase v38 v1b8 pathPtr pathCap bl : BitVec 64}
    {s : State} {R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3020#64) (hrun : s.status = .Running) (hal : s.spAligned)
    (hx22 : s.readReg64 (.gpr 22#5) = pathPtr) (hx23 : s.readReg64 (.gpr 23#5) = pathCap)
    (hnez : pathCap ≠ 0#64)
    (f0 : prog.fetch (fnBase + 3020#64) =
      some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 8#5) (AddrMode.Offset Reg.sp 56#64)))
    (f1 : prog.fetch (fnBase + 3024#64) =
      some (Instr.str MemWidth.X64 (Reg.gpr 8#5) (AddrMode.Offset Reg.sp 440#64)))
    (f2 : prog.fetch (fnBase + 3028#64) =
      some (Instr.cbz RegWidth.W64 true (Reg.gpr 23#5) 16#64))
    (f4 : prog.fetch (fnBase + 3044#64) =
      some (Instr.logicalShift RegWidth.W64 LogicalOp.ORR (Reg.gpr 0#5) Reg.xzr (Reg.gpr 22#5)
        ShiftType.LSL 0))
    (f5 : prog.fetch (fnBase + 3048#64) =
      some (Instr.logicalShift RegWidth.W64 LogicalOp.ORR (Reg.gpr 1#5) Reg.xzr (Reg.gpr 23#5)
        ShiftType.LSL 0))
    (f6 : prog.fetch (fnBase + 3052#64) =
      some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 2#5) (1#16) 0))
    (f7 : prog.fetch (fnBase + 3056#64) =
      some (Instr.bl bl))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3056#64 + bl → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.symtab = s.symtab → s'.vregs = s.vregs → s'.fs = s.fs → s'.trace = s.trace →
      s'.tpidrEl0 = s.tpidrEl0 →
      s'.readReg64 .lr = fnBase + 3060#64 →
      s'.readReg64 (.gpr 0#5) = pathPtr → s'.readReg64 (.gpr 1#5) = pathCap →
      s'.readReg64 (.gpr 2#5) = 1#64 →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      Q s' (((s.sp + 56#64) ↦₆₄ v38) ∗ ((s.sp + 440#64) ↦₆₄ v38) ∗ R)) :
    SepWP prog (fnBase + 3056#64 + bl) s
      (((s.sp + 56#64) ↦₆₄ v38) ∗ ((s.sp + 440#64) ↦₆₄ v1b8) ∗ R) Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl])
    (by simp only [wp_norm, arm64_norm])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])

private theorem step_bdc_dealloc_vm {prog : Program} {fnBase v38 v1b8 pathPtr pathCap bl : BitVec 64}
    {s : State} {R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3036#64) (hrun : s.status = .Running) (hal : s.spAligned)
    (hx22 : s.readReg64 (.gpr 22#5) = pathPtr) (hx23 : s.readReg64 (.gpr 23#5) = pathCap)
    (f0 : prog.fetch (fnBase + 3036#64) =
      some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 8#5) (AddrMode.Offset Reg.sp 56#64)))
    (f1 : prog.fetch (fnBase + 3040#64) =
      some (Instr.str MemWidth.X64 (Reg.gpr 8#5) (AddrMode.Offset Reg.sp 440#64)))
    (f4 : prog.fetch (fnBase + 3044#64) =
      some (Instr.logicalShift RegWidth.W64 LogicalOp.ORR (Reg.gpr 0#5) Reg.xzr (Reg.gpr 22#5)
        ShiftType.LSL 0))
    (f5 : prog.fetch (fnBase + 3048#64) =
      some (Instr.logicalShift RegWidth.W64 LogicalOp.ORR (Reg.gpr 1#5) Reg.xzr (Reg.gpr 23#5)
        ShiftType.LSL 0))
    (f6 : prog.fetch (fnBase + 3052#64) =
      some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 2#5) (1#16) 0))
    (f7 : prog.fetch (fnBase + 3056#64) =
      some (Instr.bl bl))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3056#64 + bl → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.symtab = s.symtab → s'.vregs = s.vregs → s'.fs = s.fs → s'.trace = s.trace →
      s'.tpidrEl0 = s.tpidrEl0 →
      s'.readReg64 .lr = fnBase + 3060#64 →
      s'.readReg64 (.gpr 0#5) = pathPtr → s'.readReg64 (.gpr 1#5) = pathCap →
      s'.readReg64 (.gpr 2#5) = 1#64 →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      Q s' (((s.sp + 56#64) ↦₆₄ v38) ∗ ((s.sp + 440#64) ↦₆₄ v38) ∗ R)) :
    SepWP prog (fnBase + 3056#64 + bl) s
      (((s.sp + 56#64) ↦₆₄ v38) ∗ ((s.sp + 440#64) ↦₆₄ v1b8) ∗ R) Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl])
    (by simp only [wp_norm, arm64_norm])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])

private theorem step_bf4_pre_b {prog : Program} {fnBase curCap curPtr v30 : BitVec 64}
    {s : State} {R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3060#64) (hrun : s.status = .Running) (hal : s.spAligned)
    (f0 : prog.fetch (fnBase + 3060#64) =
      some (Instr.ldp RegWidth.W64 false (Reg.gpr 22#5) (Reg.gpr 25#5) (AddrMode.Offset Reg.sp 40#64)))
    (f1 : prog.fetch (fnBase + 3064#64) =
      some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 23#5) (AddrMode.Offset Reg.sp 32#64)))
    (f2 : prog.fetch (fnBase + 3068#64) =
      some (Instr.addSubImm RegWidth.W64 AddSubOp.ADD (Reg.gpr 21#5) (Reg.gpr 22#5) (32#12) false))
    (f3 : prog.fetch (fnBase + 3072#64) =
      some (Instr.b 16#64))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3088#64 → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.mem = s.mem → s'.symtab = s.symtab → s'.vregs = s.vregs →
      s'.fs = s.fs → s'.trace = s.trace →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 21#5) = curPtr + 32#64 →
      s'.readReg64 (.gpr 22#5) = curPtr →
      s'.readReg64 (.gpr 23#5) = curCap →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      s'.readReg64 (.gpr 25#5) = v30 →
      (∀ (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ),
        A.pool lim st s' = A.pool lim st s) →
      Q s' (((s.sp + 32#64) ↦₆₄ curCap) ∗ ((s.sp + 40#64) ↦₆₄ curPtr) ∗
        ((s.sp + 48#64) ↦₆₄ v30) ∗ R)) :
    SepWP prog (fnBase + 3088#64) s
      (((s.sp + 32#64) ↦₆₄ curCap) ∗ ((s.sp + 40#64) ↦₆₄ curPtr) ∗
        ((s.sp + 48#64) ↦₆₄ v30) ∗ R) Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (fun _ _ _ _ => by simp only [m5_st_pl])

private theorem step_c3c_dealloc_b {prog : Program} {fnBase curPtr curCap bl : BitVec 64}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3132#64) (hrun : s.status = .Running)
    (hx22 : s.readReg64 (.gpr 22#5) = curPtr) (hx23 : s.readReg64 (.gpr 23#5) = curCap)
    (hnez : curCap ≠ 0#64)
    (c0 : prog.fetch (fnBase + 3132#64) =
      some (Instr.cbz RegWidth.W64 false (Reg.gpr 23#5) 24#64))
    (c1 : prog.fetch (fnBase + 3136#64) =
      some (Instr.addSubShift RegWidth.W64 AddSubOp.ADD (Reg.gpr 8#5) (Reg.gpr 23#5) (Reg.gpr 23#5)
        ShiftType.LSL 1))
    (c2 : prog.fetch (fnBase + 3140#64) =
      some (Instr.logicalShift RegWidth.W64 LogicalOp.ORR (Reg.gpr 0#5) Reg.xzr (Reg.gpr 22#5)
        ShiftType.LSL 0))
    (c3 : prog.fetch (fnBase + 3144#64) =
      some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 2#5) (8#16) 0))
    (c4 : prog.fetch (fnBase + 3148#64) =
      some (Instr.bitfield RegWidth.W64 BitfieldOp.UBFM (Reg.gpr 1#5) (Reg.gpr 8#5) 60 59))
    (c5 : prog.fetch (fnBase + 3152#64) =
      some (Instr.bl bl))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3152#64 + bl → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.mem = s.mem → s'.symtab = s.symtab → s'.vregs = s.vregs →
      s'.fs = s.fs → s'.trace = s.trace →
      s'.readReg64 .lr = fnBase + 3156#64 →
      s'.readReg64 (.gpr 0#5) = curPtr → s'.readReg64 (.gpr 1#5) = curCap * 48#64 →
      s'.readReg64 (.gpr 2#5) = 8#64 →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      s'.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) →
      (∀ (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ),
        A.pool lim st s' = A.pool lim st s) →
      Q s' P) :
    SepWP prog (fnBase + 3152#64 + bl) s P Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]; bv_bits) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (fun _ _ _ _ => by simp only [m5_st_pl])

private theorem step_c54_post_b {prog : Program} {fnBase v38 : BitVec 64}
    {s : State} {R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3156#64) (hrun : s.status = .Running) (hal : s.spAligned)
    (m0 : prog.fetch (fnBase + 3156#64) =
      some (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 23#5) (AddrMode.Offset Reg.sp 56#64)))
    (m1 : prog.fetch (fnBase + 3160#64) =
      some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 22#5) (1#16) 0))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3164#64 → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.mem = s.mem → s'.symtab = s.symtab → s'.vregs = s.vregs →
      s'.fs = s.fs → s'.trace = s.trace →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 22#5) = 1#64 →
      s'.readReg64 (.gpr 23#5) = v38 →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      s'.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) →
      (∀ (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ),
        A.pool lim st s' = A.pool lim st s) →
      Q s' (((s.sp + 56#64) ↦₆₄ v38) ∗ R)) :
    SepWP prog (fnBase + 3164#64) s (((s.sp + 56#64) ↦₆₄ v38) ∗ R) Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (fun _ _ _ _ => by simp only [m5_st_pl])

private theorem step_c5c_eq8_b {prog : Program} {fnBase : BitVec 64}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3164#64) (hrun : s.status = .Running)
    (hx23 : s.readReg64 (.gpr 23#5) = 8#64)
    (d0 : prog.fetch (fnBase + 3164#64) =
      some (Instr.addSubImm RegWidth.W64 AddSubOp.SUBS Reg.xzr (Reg.gpr 23#5) (8#12) false))
    (d1 : prog.fetch (fnBase + 3168#64) =
      some (Instr.bCond CondCode.EQ 784#64))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3952#64 → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.mem = s.mem → s'.symtab = s.symtab → s'.vregs = s.vregs →
      s'.fs = s.fs → s'.trace = s.trace →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      (∀ (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ),
        A.pool lim st s' = A.pool lim st s) →
      Q s' P) :
    SepWP prog (fnBase + 3952#64) s P Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (fun _ _ _ _ => by simp only [m5_st_pl])

private theorem step_c5c_ne8_b {prog : Program} {fnBase v23 v25 : BitVec 64}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 3164#64) (hrun : s.status = .Running)
    (hx23 : s.readReg64 (.gpr 23#5) = v23) (hx25 : s.readReg64 (.gpr 25#5) = v25)
    (hne8 : v23 ≠ 8#64)
    (d0 : prog.fetch (fnBase + 3164#64) =
      some (Instr.addSubImm RegWidth.W64 AddSubOp.SUBS Reg.xzr (Reg.gpr 23#5) (8#12) false))
    (d1 : prog.fetch (fnBase + 3168#64) =
      some (Instr.bCond CondCode.EQ 784#64))
    (d2 : prog.fetch (fnBase + 3172#64) =
      some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 8#5) (40#16) 0))
    (d3 : prog.fetch (fnBase + 3176#64) =
      some (Instr.logicalShift RegWidth.W64 LogicalOp.ORR (Reg.gpr 26#5) Reg.xzr (Reg.gpr 23#5)
        ShiftType.LSL 0))
    (d4 : prog.fetch (fnBase + 3180#64) =
      some (Instr.dataProc3 RegWidth.W64 DataProc3Op.MADD (Reg.gpr 23#5) (Reg.gpr 23#5) (Reg.gpr 8#5)
        (Reg.gpr 25#5)))
    (hdone : ∀ s' : State,
      s'.pc = fnBase + 3184#64 → s'.status = .Running →
      s'.sp = s.sp → s'.readReg64 .fp = s.readReg64 .fp →
      s'.mem = s.mem → s'.symtab = s.symtab → s'.vregs = s.vregs →
      s'.fs = s.fs → s'.trace = s.trace →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      s'.readReg64 (.gpr 23#5) = v25 + v23 * 40#64 →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      s'.readReg64 (.gpr 26#5) = v23 →
      (∀ (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ),
        A.pool lim st s' = A.pool lim st s) →
      Q s' P) :
    SepWP prog (fnBase + 3184#64) s P Q oom := by
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (fun _ _ _ _ => by simp only [m5_st_pl])

/-! ## 1. Step A: Exact-Event `M5ErrEntryPlaced` (`0xbcc` / `0xbdc` / `0xbf4`) → `0xbf4` -/

private theorem m5ErrCellsPlaced_open_38_1b8 (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64)
    (g : StoresGhost) {k : Nat} (hk : k < 8) :
    ∃ Ctx : SepProp,
      (locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) =
        ∃∗ v : BitVec 64,
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ ((fsp + 440#64) ↦₆₄ v) ∗ Ctx) ∧
      (∀ w : BitVec 64,
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ ((fsp + 440#64) ↦₆₄ w) ∗ Ctx ⊢
          locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k)) := by
  let pre38 : List (Nat × Nat × SepProp) :=
    [cell fsp 0x0 outLen, cell fsp 0x8 outCap, cell fsp 0x10 inCap, cell fsp 0x18 outPtr,
     cell fsp 0x20 curCap, cell fsp 0x28 curPtr, cell fsp 0x30 (fsp + 0x1c8#64)]
  let mid : List (Nat × Nat × SepProp) :=
    [cell fsp 0x50 inPtr]
  let tail : List (Nat × Nat × SepProp) :=
    [(0x1c8 + 0x28 * (k + 1), 0x28 * (8 - (k + 1)),
      dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)))]
  let cs1 : List (Nat × Nat × SepProp) :=
    pre38 ++ (cell fsp 0x38 (BitVec.ofNat 64 (k + 1)) :: mid)
  have heq_cells :
      m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k = cs1 ++ tail := rfl
  have hcarve := locals_carve_cell fsp cs1 0x1b8 tail
    (by simp [cs1, pre38, mid, localsEnd])
    (by simp [tail, localsBound]; omega)
    (by simp [tail, localsBound]; omega)
  have hfoc_both :
      ∀ w : BitVec 64,
        locals fsp (cs1 ++ cell fsp 0x1b8 w :: tail) =
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
            localsCtx fsp 0 pre38 0x38 8 (mid ++ cell fsp 0x1b8 w :: tail) :=
    fun w => locals_focus fsp pre38 0x38 8 ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1))
      (mid ++ cell fsp 0x1b8 w :: tail)
  let ctx : SepProp :=
    memRegion (fsp + BitVec.ofNat 64 0) 0 ∗
      ((fsp + 0#64) ↦₆₄ outLen) ∗
      memRegion (fsp + 8#64) 0 ∗
      ((fsp + 8#64) ↦₆₄ outCap) ∗
      memRegion (fsp + 16#64) 0 ∗
      ((fsp + 16#64) ↦₆₄ inCap) ∗
      memRegion (fsp + 24#64) 0 ∗
      ((fsp + 24#64) ↦₆₄ outPtr) ∗
      memRegion (fsp + 32#64) 0 ∗
      ((fsp + 32#64) ↦₆₄ curCap) ∗
      memRegion (fsp + 40#64) 0 ∗
      ((fsp + 40#64) ↦₆₄ curPtr) ∗
      memRegion (fsp + 48#64) 0 ∗
      ((fsp + 48#64) ↦₆₄ (fsp + 0x1c8#64)) ∗
      memRegion (fsp + 56#64) 0 ∗
      memRegion (fsp + 64#64) 16 ∗
      ((fsp + 80#64) ↦₆₄ inPtr) ∗
      memRegion (fsp + 88#64) 352 ∗
      localsFrom fsp 448 tail
  have hctx_split :
      ∀ w : BitVec 64,
        localsCtx fsp 0 pre38 0x38 8 (mid ++ cell fsp 0x1b8 w :: tail) =
          ((fsp + 440#64) ↦₆₄ w) ∗ ctx := by
    intro w
    dsimp only [pre38, mid, cell, ctx, localsCtx, localsFrom,
      List.cons_append, List.nil_append, Nat.reduceAdd, Nat.reduceSub]
    sep_ac_rfl
  refine ⟨ctx, ?_, ?_⟩
  · rw [heq_cells, hcarve]
    congr 1; funext v
    rw [hfoc_both v, hctx_split v]
  · intro w
    rw [← hctx_split w, ← hfoc_both w, heq_cells]
    exact locals_forget_cell fsp cs1 0x1b8 w tail
      (by simp [cs1, pre38, mid, localsEnd])
      (by simp [tail, localsBound]; omega)
      (by simp [tail, localsBound]; omega)

private theorem m5ErrCellsPlaced_open_frame (A : RustAlloc)
    {fsp sp outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64}
    (hsp : sp = fsp) (g : StoresGhost) {k : Nat} (hk : k < 8)
    (Pre Pool Post : SepProp) (stk : Nat) :
    ∃ Ctx : SepProp,
      (Pre ∗ (locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
          (Pool ∗ (stackAt fsp (stk - mainFrameSize) ∗ Post))) =
        Pre ∗ ((∃∗ v : BitVec 64,
          ((sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ ((sp + 440#64) ↦₆₄ v) ∗ Ctx) ∗
          (Pool ∗ (stackAt sp (stk - mainFrameSize) ∗ Post)))) ∧
      (∀ w : BitVec 64,
        ((sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ ((sp + 440#64) ↦₆₄ w) ∗ Ctx ⊢
          locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k)) := by
  subst hsp
  obtain ⟨Ctx, hopen, hclose⟩ :=
    m5ErrCellsPlaced_open_38_1b8 A sp outCap outPtr outLen inCap inPtr curCap curPtr g hk
  exact ⟨Ctx, by rw [hopen], hclose⟩

private theorem m5_err_to_bf4_exact_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {ret : BitVec 64} {s0 s : State} {stk k : Nat}
    {outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64}
    {g : StoresGhost} {e : M5ErrEntryPlaced}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hext : mainFrameSize + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hk : k < 8)
    (hs : InMainPlaced CodeOk s0 s e.pcOff)
    (herr : e.regs s)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm 0xbf4 →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5ErrCellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
            outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
          A.pool lim (M.stepEvents (m5ErrEntryDropEvents e) st) sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (e.heap A.repAlloc ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5ErrCellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
            outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
        A.pool lim st s ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
      Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hsp : s.sp = fsp := hs.sp
  cases e with
  | bf4 =>
    dsimp only [M5ErrEntryPlaced.heap, M5ErrEntryPlaced.pcOff, m5ErrEntryDropEvents] at hs ⊢
    refine SepWPp.weaken_pre (Entails.of_eq (emp_sepConj _)) ?_
    have h := hnext s hs rfl rfl rfl rfl rfl
    simpa only [m5ErrEntryDropEvents, AllocCostModel.stepEvents_nil] using h
  | bcc pathCap pathPtr pathBs =>
    dsimp only [M5ErrEntryPlaced.heap, M5ErrEntryPlaced.pcOff, M5ErrEntryPlaced.regs] at hs herr ⊢
    rcases herr with ⟨hx22, hx23⟩
    unfold ownedBytes
    simp only [sepConj_assoc, RustCliAllocBudget.repAlloc_live]
    apply SepWPp.pure_elim
    rintro ⟨_, hlen, hcap_lt, _⟩
    obtain ⟨Ctx, hopen, hclose⟩ :=
      m5ErrCellsPlaced_open_frame A.repAlloc hs.sp g hk _ (A.pool lim st s) F stk
    refine SepWPp.weaken_pre (Entails.of_eq hopen) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro v1b8
    by_cases hcap0 : pathCap = 0#64
    · subst hcap0
      have hz0 : (0#64 : BitVec 64) = 0 := rfl
      simp only [hz0, ite_true, emp_sepConj, sepConj_assoc]
      rw [mProgPlaced_eq]
      refine sepWPp_seq_codeOk_vm (mid := mPcPlaced 0xbf4) hs.inv fun m_strip => ?_
      rw [mPcPlaced_eq]
      refine step_bcc_zero_vm (fnBase := (blkPl_617).base) (s := s.setMem m_strip)
        (by simpa only [wp_norm, arm64_norm, mPcPlaced_eq] using hs.pc)
        (by simpa only [wp_norm, arm64_norm] using hs.run)
        (by simpa only [State.spAligned, wp_norm, arm64_norm] using hs.spAligned_state)
        (by simpa only [wp_norm, arm64_norm] using hx23)
        m5_drop_fetch_vm m5_drop_fetch_vm
        m5_drop_fetch_vm m5_drop_fetch_vm ?_
      intro s1 hpcm hrunm hsp1 hfp1 _hsym1 hv1 hfs1 htr1 htp1 hx19_1 hx20_1 hx24_1 m_real hnsp hfz
      have hsp1_s : (s1.setMem m_real).sp = s.sp := by
        simpa only [wp_norm, arm64_norm] using hsp1
      have hfp1_s : (s1.setMem m_real).readReg64 .fp = s.readReg64 .fp := by
        simpa only [wp_norm, arm64_norm] using hfp1
      have hv1_s : (s1.setMem m_real).vregs = s.vregs := hv1
      have hfs1_s : (s1.setMem m_real).fs = s.fs := by
        simpa only [wp_norm, arm64_norm] using hfs1
      have htr1_s : (s1.setMem m_real).trace = s.trace := by
        simpa only [wp_norm, arm64_norm] using htr1
      have htp1_s : (s1.setMem m_real).tpidrEl0 = s.tpidrEl0 := by
        simpa only [wp_norm, arm64_norm] using htp1
      have hpool1 : A.pool lim st (s1.setMem m_real) = A.pool lim st s :=
        A.pool_transport lim st s (s1.setMem m_real) (hnsp.toVmPreserved htp1_s)
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre (P' :=
        locals fsp (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr outLen inCap inPtr
            curCap curPtr g k) ∗
          A.pool lim (M.stepEvents (m5ErrEntryDropEvents (.bcc 0#64 pathPtr pathBs)) st)
            (s1.setMem m_real) ∗
          stackAt fsp (stk - mainFrameSize) ∗ F) ?_ ?_
      · simp only [m5ErrEntryDropEvents, ↓reduceIte, AllocCostModel.stepEvents_nil,
          hpool1, wp_norm, arm64_norm]
        refine Entails.trans (Entails.of_eq (show
          ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
            ((s.sp + 440#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
            (Ctx ∗ (A.pool lim st s ∗ (stackAt s.sp (stk - mainFrameSize) ∗ F))) =
          (((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
            ((s.sp + 440#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ Ctx) ∗
            (A.pool lim st s ∗ stackAt fsp (stk - mainFrameSize) ∗ F) by rw [hsp]; sep_ac_rfl)) ?_
        exact sepConj_mono_left (hclose (BitVec.ofNat 64 (k + 1)))
      · exact hnext (s1.setMem m_real)
          (InMainPlaced.step_store hs
            (by simpa only [wp_norm, arm64_norm, mPcPlaced_eq] using hpcm)
            (by simpa only [wp_norm, arm64_norm] using hrunm)
            hfz hsp1_s hfp1_s
            (by simp only [calleeSavedVRegs, hv1_s]))
          (by simpa only [wp_norm, arm64_norm] using hx19_1)
          (by simpa only [wp_norm, arm64_norm] using hx20_1)
          (by simpa only [wp_norm, arm64_norm] using hx24_1)
          hfs1_s htr1_s
    · have hcap0' : pathCap ≠ 0 := hcap0
      simp only [hcap0', ite_false, sepConj_assoc]
      have hlay := layoutOk_u8_of_cap_ne_zero hcap0 hcap_lt
      have hmerge :
          (pathPtr ↦ₛ pathBs) ∗
            memRegion (pathPtr + BitVec.ofNat 64 pathBs.length) (pathCap.toNat - pathBs.length) ⊢
          memRegion pathPtr pathCap.toNat :=
        ProofLib.pointsToBytes_memRegion_entails pathPtr pathBs pathCap.toNat hlen (by omega)
      let bl : BitVec 64 := (lsρ lsRustDeallocSymCli - (blkPl_617).base) - 3056#64
      have hbl : (blkPl_617).base + 3056#64 + bl = lsρ lsRustDeallocSymCli :=
        mPcPlaced_bl_dealloc 3056
      refine SepWPp.weaken_pre (Entails.of_eq (show
        A.live pathPtr pathCap.toNat 1 ∗ (pathPtr ↦ₛ pathBs) ∗
          memRegion (pathPtr + BitVec.ofNat 64 pathBs.length) (pathCap.toNat - pathBs.length) ∗
          ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          ((s.sp + 440#64) ↦₆₄ v1b8) ∗ Ctx ∗
          A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F =
        ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          ((s.sp + 440#64) ↦₆₄ v1b8) ∗
          (A.live pathPtr pathCap.toNat 1 ∗
            ((pathPtr ↦ₛ pathBs) ∗
              memRegion (pathPtr + BitVec.ofNat 64 pathBs.length)
                (pathCap.toNat - pathBs.length)) ∗
            Ctx ∗ A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) by sep_ac_rfl)) ?_
      rw [mProgPlaced_eq]
      refine sepWPp_seq_codeOk_vm (mid := (blkPl_617).base + 3056#64 + bl) hs.inv fun m_strip => ?_
      refine step_bcc_dealloc_vm (fnBase := (blkPl_617).base) (bl := bl) (s := s.setMem m_strip)
        (by simpa only [wp_norm, arm64_norm, mPcPlaced_eq] using hs.pc)
        (by simpa only [wp_norm, arm64_norm] using hs.run)
        (by simpa only [State.spAligned, wp_norm, arm64_norm] using hs.spAligned_state)
        (by simpa only [wp_norm, arm64_norm] using hx22)
        (by simpa only [wp_norm, arm64_norm] using hx23)
        hcap0
        m5_drop_fetch_vm m5_drop_fetch_vm
        m5_drop_fetch_vm m5_drop_fetch_vm
        m5_drop_fetch_vm m5_drop_fetch_vm
        m5_drop_fetch_vm ?_
      intro s1 hpcm hrunm hsp1 hfp1 _hsym1 hv1 hfs1 htr1 htp1 hlr1 hx0_1 hx1_1 hx2_1
        hx19_1 hx20_1 hx24_1 m_real hnsp hfz
      have hsp1_s : (s1.setMem m_real).sp = s.sp := by
        simpa only [wp_norm, arm64_norm] using hsp1
      have hfp1_s : (s1.setMem m_real).readReg64 .fp = s.readReg64 .fp := by
        simpa only [wp_norm, arm64_norm] using hfp1
      have hv1_s : (s1.setMem m_real).vregs = s.vregs := hv1
      have hfs1_s : (s1.setMem m_real).fs = s.fs := by
        simpa only [wp_norm, arm64_norm] using hfs1
      have htr1_s : (s1.setMem m_real).trace = s.trace := by
        simpa only [wp_norm, arm64_norm] using htr1
      have htp1_s : (s1.setMem m_real).tpidrEl0 = s.tpidrEl0 := by
        simpa only [wp_norm, arm64_norm] using htp1
      have hpool1 : A.pool lim st (s1.setMem m_real) = A.pool lim st s :=
        A.pool_transport lim st s (s1.setMem m_real) (hnsp.toVmPreserved htp1_s)
      rw [← mProgPlaced_eq]
      refine step_dealloc_placed (st := st) (sub := stk - mainFrameSize)
        (F := locals fsp (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr outLen inCap inPtr
          curCap curPtr g k) ∗ F)
        hA (by omega) (by omega)
        hfz
        ((by simpa only [wp_norm, arm64_norm] using hpcm :
          (s1.setMem m_real).pc = (blkPl_617).base + 3056#64 + bl).trans hbl)
        (by simpa only [wp_norm, arm64_norm] using hrunm)
        (by simpa only [State.spAligned, hsp1_s] using hs.spAligned_state)
        (by simpa only [wp_norm, arm64_norm] using hlr1)
        (by simpa only [wp_norm, arm64_norm] using hx0_1)
        (congrArg BitVec.toNat (by simpa only [wp_norm, arm64_norm] using hx1_1))
        (by
          have hx2_r : (s1.setMem m_real).readReg64 .x2 = 1#64 := by
            simpa only [wp_norm, arm64_norm] using hx2_1
          rw [hx2_r]; decide)
        hlay
        (hP := ?_) (hnext := ?_)
      · simp only [hpool1, wp_norm, arm64_norm]
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live pathPtr pathCap.toNat 1 ∗
            ((pathPtr ↦ₛ pathBs) ∗
              memRegion (pathPtr + BitVec.ofNat 64 pathBs.length)
                (pathCap.toNat - pathBs.length))) ∗
            ((((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
              ((s.sp + 440#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ Ctx) ∗
              A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) by sep_ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono (sepConj_mono_right hmerge)
            (sepConj_mono_left (hclose (BitVec.ofNat 64 (k + 1))))) ?_
        exact Entails.of_eq (by
          have hsp1_eq : s1.sp = s.sp := by simpa only [wp_norm, arm64_norm] using hsp1
          rw [hsp1_eq]
          dsimp +zetaDelta only [fsp]
          sep_ac_rfl)
      · intro sm hpcm' hrunm' hspm' hcsm hinv' hfsm htrm
        have hevs : m5ErrEntryDropEvents (.bcc pathCap pathPtr pathBs) =
            rustDeallocEvents pathCap.toNat 1 := by
          simp only [m5ErrEntryDropEvents, hcap0, ↓reduceIte]
        refine SepWPp.weaken_pre (P' :=
          locals fsp (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr outLen inCap inPtr
              curCap curPtr g k) ∗
            A.pool lim (M.stepEvents (m5ErrEntryDropEvents (.bcc pathCap pathPtr pathBs)) st) sm ∗
            stackAt fsp (stk - mainFrameSize) ∗ F)
          (Entails.of_eq (by rw [hevs, hsp1_s, hsp]; sep_ac_rfl)) ?_
        exact hnext sm
          (hs.mk_step (by simpa only [mPcPlaced_eq] using hpcm') hrunm' (hspm'.trans hsp1_s)
            (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp1_s) hinv'
            (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, hv1_s])))
          (hcsm.1.trans (by simpa only [wp_norm, arm64_norm] using hx19_1))
          (hcsm.2.1.trans (by simpa only [wp_norm, arm64_norm] using hx20_1))
          (hcsm.2.2.2.2.2.1.trans (by simpa only [wp_norm, arm64_norm] using hx24_1))
          (hfsm.trans hfs1_s) (htrm.trans htr1_s)
  | bdc pathCap pathPtr pathBs =>
    dsimp only [M5ErrEntryPlaced.heap, M5ErrEntryPlaced.pcOff, M5ErrEntryPlaced.regs,
      m5ErrEntryDropEvents] at hs herr ⊢
    rcases herr with ⟨hx22, hx23, hcap0⟩
    have hcap0' : pathCap ≠ 0 := hcap0
    unfold ownedBytes
    simp only [hcap0', ite_false, sepConj_assoc, RustCliAllocBudget.repAlloc_live]
    apply SepWPp.pure_elim
    rintro ⟨_, hlen, hcap_lt, _⟩
    have hlay := layoutOk_u8_of_cap_ne_zero hcap0 hcap_lt
    have hmerge :
        (pathPtr ↦ₛ pathBs) ∗
          memRegion (pathPtr + BitVec.ofNat 64 pathBs.length) (pathCap.toNat - pathBs.length) ⊢
        memRegion pathPtr pathCap.toNat :=
      ProofLib.pointsToBytes_memRegion_entails pathPtr pathBs pathCap.toNat hlen (by omega)
    obtain ⟨Ctx, hopen, hclose⟩ :=
      m5ErrCellsPlaced_open_38_1b8 A.repAlloc s.sp outCap outPtr outLen inCap inPtr curCap curPtr g hk
    refine SepWPp.weaken_pre (P' :=
      A.live pathPtr pathCap.toNat 1 ∗ (pathPtr ↦ₛ pathBs) ∗
        memRegion (pathPtr + BitVec.ofNat 64 pathBs.length) (pathCap.toNat - pathBs.length) ∗
        (∃∗ v : BitVec 64,
          ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ ((s.sp + 440#64) ↦₆₄ v) ∗ Ctx) ∗
        A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F)
      (Entails.of_eq (by rw [← hs.sp, hopen])) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro v1b8
    let bl : BitVec 64 := (lsρ lsRustDeallocSymCli - (blkPl_617).base) - 3056#64
    have hbl : (blkPl_617).base + 3056#64 + bl = lsρ lsRustDeallocSymCli :=
      mPcPlaced_bl_dealloc 3056
    refine SepWPp.weaken_pre (Entails.of_eq (show
      A.live pathPtr pathCap.toNat 1 ∗ (pathPtr ↦ₛ pathBs) ∗
        memRegion (pathPtr + BitVec.ofNat 64 pathBs.length) (pathCap.toNat - pathBs.length) ∗
        ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
        ((s.sp + 440#64) ↦₆₄ v1b8) ∗ Ctx ∗
        A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F =
      ((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
        ((s.sp + 440#64) ↦₆₄ v1b8) ∗
        (A.live pathPtr pathCap.toNat 1 ∗
          ((pathPtr ↦ₛ pathBs) ∗
            memRegion (pathPtr + BitVec.ofNat 64 pathBs.length)
              (pathCap.toNat - pathBs.length)) ∗
          Ctx ∗ A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) by sep_ac_rfl)) ?_
    rw [mProgPlaced_eq]
    refine sepWPp_seq_codeOk_vm (mid := (blkPl_617).base + 3056#64 + bl) hs.inv fun m_strip => ?_
    refine step_bdc_dealloc_vm (fnBase := (blkPl_617).base) (bl := bl) (s := s.setMem m_strip)
      (by simpa only [wp_norm, arm64_norm, mPcPlaced_eq] using hs.pc)
      (by simpa only [wp_norm, arm64_norm] using hs.run)
      (by simpa only [State.spAligned, wp_norm, arm64_norm] using hs.spAligned_state)
      (by simpa only [wp_norm, arm64_norm] using hx22)
      (by simpa only [wp_norm, arm64_norm] using hx23)
      m5_drop_fetch_vm m5_drop_fetch_vm
      m5_drop_fetch_vm m5_drop_fetch_vm
      m5_drop_fetch_vm m5_drop_fetch_vm ?_
    intro s1 hpcm hrunm hsp1 hfp1 _hsym1 hv1 hfs1 htr1 htp1 hlr1 hx0_1 hx1_1 hx2_1
      hx19_1 hx20_1 hx24_1 m_real hnsp hfz
    have hsp1_s : (s1.setMem m_real).sp = s.sp := by
      simpa only [wp_norm, arm64_norm] using hsp1
    have hfp1_s : (s1.setMem m_real).readReg64 .fp = s.readReg64 .fp := by
      simpa only [wp_norm, arm64_norm] using hfp1
    have hv1_s : (s1.setMem m_real).vregs = s.vregs := hv1
    have hfs1_s : (s1.setMem m_real).fs = s.fs := by
      simpa only [wp_norm, arm64_norm] using hfs1
    have htr1_s : (s1.setMem m_real).trace = s.trace := by
      simpa only [wp_norm, arm64_norm] using htr1
    have htp1_s : (s1.setMem m_real).tpidrEl0 = s.tpidrEl0 := by
      simpa only [wp_norm, arm64_norm] using htp1
    have hpool1 : A.pool lim st (s1.setMem m_real) = A.pool lim st s :=
      A.pool_transport lim st s (s1.setMem m_real) (hnsp.toVmPreserved htp1_s)
    rw [← mProgPlaced_eq]
    refine step_dealloc_placed (st := st) (sub := stk - mainFrameSize)
      (F := locals fsp (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr outLen inCap inPtr
        curCap curPtr g k) ∗ F)
      hA (by omega) (by omega)
      hfz
      ((by simpa only [wp_norm, arm64_norm] using hpcm :
        (s1.setMem m_real).pc = (blkPl_617).base + 3056#64 + bl).trans hbl)
      (by simpa only [wp_norm, arm64_norm] using hrunm)
      (by simpa only [State.spAligned, hsp1_s] using hs.spAligned_state)
      (by simpa only [wp_norm, arm64_norm] using hlr1)
      (by simpa only [wp_norm, arm64_norm] using hx0_1)
      (congrArg BitVec.toNat (by simpa only [wp_norm, arm64_norm] using hx1_1))
      (by
        have hx2_r : (s1.setMem m_real).readReg64 .x2 = 1#64 := by
          simpa only [wp_norm, arm64_norm] using hx2_1
        rw [hx2_r]; decide)
      hlay
      (hP := ?_) (hnext := ?_)
    · simp only [hpool1, wp_norm, arm64_norm]
      refine Entails.trans (Entails.of_eq (show _ =
        (A.live pathPtr pathCap.toNat 1 ∗
          ((pathPtr ↦ₛ pathBs) ∗
            memRegion (pathPtr + BitVec.ofNat 64 pathBs.length)
              (pathCap.toNat - pathBs.length))) ∗
          ((((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
            ((s.sp + 440#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ Ctx) ∗
            A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) by sep_ac_rfl)) ?_
      refine Entails.trans
        (sepConj_mono (sepConj_mono_right hmerge)
          (sepConj_mono_left (hclose (BitVec.ofNat 64 (k + 1))))) ?_
      exact Entails.of_eq (by
        have hsp1_eq : s1.sp = s.sp := by simpa only [wp_norm, arm64_norm] using hsp1
        rw [hsp1_eq, hsp]
        sep_ac_rfl)
    · intro sm hpcm' hrunm' hspm' hcsm hinv' hfsm htrm
      refine SepWPp.weaken_pre (P' :=
        locals fsp (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr outLen inCap inPtr
            curCap curPtr g k) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents pathCap.toNat 1) st) sm ∗
          stackAt fsp (stk - mainFrameSize) ∗ F)
        (Entails.of_eq (by rw [hsp1_s, hsp]; sep_ac_rfl)) ?_
      exact hnext sm
        (hs.mk_step (by simpa only [mPcPlaced_eq] using hpcm') hrunm' (hspm'.trans hsp1_s)
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp1_s) hinv'
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, hv1_s])))
        (hcsm.1.trans (by simpa only [wp_norm, arm64_norm] using hx19_1))
        (hcsm.2.1.trans (by simpa only [wp_norm, arm64_norm] using hx20_1))
        (hcsm.2.2.2.2.2.1.trans (by simpa only [wp_norm, arm64_norm] using hx24_1))
        (hfsm.trans hfs1_s) (htrm.trans htr1_s)

/-! ## 2. Step B: Current `Dir` Buffer Cleanup `0xbf4 → 0xc5c` -/

theorem m5_cur_dir_to_c5c_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {ret : BitVec 64} {s0 s : State} {stk k : Nat}
    {outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64}
    {g : StoresGhost} {curEntries : List (List (BitVec 8) × List (BitVec 8))}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hext : mainFrameSize + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hne : curEntries ≠ [])
    (hs : InMainPlaced CodeOk s0 s 0xbf4)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 curEntries.length)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      InMainPlaced CodeOk s0 sm 0xc5c →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 22#5) = 1#64 →
      sm.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (k + 1) →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.readReg64 (.gpr 25#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64 →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5ErrCellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
            outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr curEntries ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5ErrCellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
            outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
        A.pool lim st s ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
      Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hsp : s.sp = fsp := hs.sp
  unfold vecBuf
  simp only [sepConj_assoc]
  apply SepWPp.pure_elim
  rintro ⟨hlen, hcap_lt, _⟩
  have hpos : 0 < curEntries.length := List.length_pos_of_ne_nil hne
  have hcap_ne : curCap ≠ 0#64 := by
    intro hc0; subst hc0; change curEntries.length ≤ 0 at hlen; omega
  have hcap_ne0 : curCap ≠ 0 := hcap_ne
  simp only [hcap_ne0, ite_false, sepConj_assoc, RustCliAllocBudget.repAlloc_live]
  obtain ⟨Ctx, hopen⟩ :=
    m5ErrCellsPlaced_open_spills A.repAlloc s.sp outCap outPtr outLen inCap inPtr curCap curPtr g k
  refine SepWPp.weaken_pre (Entails.of_eq (show
    A.live curPtr (curCap.toNat * 48) 8 ∗
      arrayAt (dirEntryAt A.repAlloc) 48 curPtr curEntries ∗
      memRegion (curPtr + BitVec.ofNat 64 (curEntries.length * 48))
        ((curCap.toNat - curEntries.length) * 48) ∗
      locals fsp (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
      A.pool lim st s ∗ stackAt fsp (stk - mainFrameSize) ∗ F =
    ((s.sp + 32#64) ↦₆₄ curCap) ∗
      ((s.sp + 40#64) ↦₆₄ curPtr) ∗
      ((s.sp + 48#64) ↦₆₄ (s.sp + 0x1c8#64)) ∗
      (((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
        (arrayAt (dirEntryAt A.repAlloc) 48 curPtr curEntries ∗
          A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗
          (A.live curPtr (curCap.toNat * 48) 8 ∗
            memRegion (curPtr + BitVec.ofNat 64 (curEntries.length * 48))
              ((curCap.toNat - curEntries.length) * 48) ∗
            Ctx ∗ F))) by
      dsimp +zetaDelta only [fsp]
      rw [← hs.sp, hopen]
      sep_ac_rfl)) ?_
  apply seq_sepWP_pl (mid := mPcPlaced (0xc04 + 12))
  refine step_bf4_pre_b (fnBase := (blkPl_617).base) hs.pc hs.run hs.spAligned_state
    m5_drop_fetch_placed m5_drop_fetch_placed
    m5_drop_fetch_placed m5_drop_fetch_placed ?_
  intro s1 hpcm1 hrunm1 hsp1 hfp1 hm1 hsym1 hv1 hfs1 htr1
    hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hpool1 _ _
  have hs1 : InMainPlaced CodeOk s0 s1 (0xc04 + 12) :=
    InMainPlaced.step_pure hs hpcm1 hrunm1 hsp1 hfp1 hm1
      (by simp only [calleeSavedVRegs, hv1])
  refine SepWPp.weaken_pre (P' :=
    arrayAt (dirEntryAt A.repAlloc) 48 curPtr curEntries ∗
      A.pool lim st s1 ∗ stackAt s1.sp (stk - mainFrameSize) ∗
      (A.live curPtr (curCap.toNat * 48) 8 ∗
        memRegion (curPtr + BitVec.ofNat 64 (curEntries.length * 48))
          ((curCap.toNat - curEntries.length) * 48) ∗
        locals fsp (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr outLen inCap inPtr
          curCap curPtr g k) ∗
        F))
    (Entails.of_eq (by
      dsimp +zetaDelta only [fsp]
      rw [hsp1, ← hs.sp, hopen, hpool1 M A lim st]
      sep_ac_rfl)) ?_
  refine m5_drop_loop_body_0xc04_placed (st := st) hA hext hstk64 hne (by omega) hs1
    (hx20_1.trans hx20) hx21_1 ?_
  intro s2 evs1 hf1 hs2 hkeeps hfs2 htr2
  have hx19_2 : s2.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) :=
    (hkeeps 19#5 (by decide) (by decide) (by decide) (by decide)).trans hx19_1
  have hx22_2 : s2.readReg64 (.gpr 22#5) = curPtr :=
    (hkeeps 22#5 (by decide) (by decide) (by decide) (by decide)).trans hx22_1
  have hx23_2 : s2.readReg64 (.gpr 23#5) = curCap :=
    (hkeeps 23#5 (by decide) (by decide) (by decide) (by decide)).trans hx23_1
  have hx24_2 : s2.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) :=
    (hkeeps 24#5 (by decide) (by decide) (by decide) (by decide)).trans hx24_1
  have hx25_2 : s2.readReg64 (.gpr 25#5) = fsp + 0x1c8#64 :=
    (hkeeps 25#5 (by decide) (by decide) (by decide) (by decide)).trans
      (hx25_1.trans (congrArg (· + 0x1c8#64) hsp))
  have hbuf_merge :
      memRegion curPtr (curEntries.length * 48) ∗
        memRegion (curPtr + BitVec.ofNat 64 (curEntries.length * 48))
          ((curCap.toNat - curEntries.length) * 48) =
        memRegion curPtr (curCap.toNat * 48) :=
    (ProofLib.memRegion_split' (by omega) rfl (by omega)).symm
  have hlay := layoutOk_dirBuf_of_cap_ne_zero hcap_ne hcap_lt
  let bl : BitVec 64 := (lsρ lsRustDeallocSymCli - (blkPl_617).base) - 3152#64
  have hbl : (blkPl_617).base + 3152#64 + bl = lsρ lsRustDeallocSymCli :=
    mPcPlaced_bl_dealloc 3152
  apply seq_sepWP_pl (mid := (blkPl_617).base + 3152#64 + bl)
  refine step_c3c_dealloc_b (fnBase := (blkPl_617).base) (bl := bl)
    hs2.pc hs2.run hx22_2 hx23_2 hcap_ne
    m5_drop_fetch_placed m5_drop_fetch_placed
    m5_drop_fetch_placed m5_drop_fetch_placed
    m5_drop_fetch_placed m5_drop_fetch_placed ?_
  intro s2' hpcm2 hrunm2 hsp2' hfp2' hm2' hsym2' hv2' hfs2' htr2'
    hlr2' hx0_2 hx1_2 hx2_2 hx19_2' hx24_2' hx25_2' hpool2' _ _
  refine step_dealloc_placed (sub := stk - mainFrameSize) (st := M.stepEvents evs1 st)
    (F := locals fsp (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr outLen inCap inPtr
      curCap curPtr g k) ∗ F)
    hA (by omega) (by omega)
    (codeOk_pure hs2.inv hm2') (hpcm2.trans hbl) hrunm2
    (by simpa only [State.spAligned, hsp2'] using hs2.spAligned_state)
    hlr2' hx0_2
    ((congrArg BitVec.toNat hx1_2).trans (mul48_toNat_of_lt curCap hcap_lt))
    (by rw [hx2_2]; decide)
    hlay
    (hP := ?_) (hnext := ?_)
  · exact Entails.of_eq (by
      rw [hsp2', hs2.sp, hs1.sp, hpool2' M A lim (M.stepEvents evs1 st), ← hbuf_merge]
      sep_ac_rfl)
  · intro s3 hpcm3 hrunm3 hspm3 hcsm3 hinv3 hfs3 htr3
    have hs3 : InMainPlaced CodeOk s0 s3 0xc54 :=
      hs2.mk_step hpcm3 hrunm3 (hspm3.trans hsp2')
        (hcsm3.2.2.2.2.2.2.2.2.2.2.1.trans hfp2') hinv3
        (hcsm3.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, hv2']))
    let evs_dealloc := rustDeallocEvents (curCap.toNat * 48) 8
    rw [← M.stepEvents_append evs1 evs_dealloc st]
    refine SepWPp.weaken_pre (P' :=
      ((s3.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
        (((s.sp + 32#64) ↦₆₄ curCap) ∗
          ((s.sp + 40#64) ↦₆₄ curPtr) ∗
          ((s.sp + 48#64) ↦₆₄ (s.sp + 0x1c8#64)) ∗
          Ctx ∗ A.pool lim (M.stepEvents (evs1 ++ evs_dealloc) st) s3 ∗
          stackAt fsp (stk - mainFrameSize) ∗ F))
      (Entails.of_eq (by
        dsimp +zetaDelta only [fsp]
        rw [hs3.sp, hsp2', hs2.sp, ← hs.sp, hopen]
        sep_ac_rfl)) ?_
    apply seq_sepWP_pl (mid := mPcPlaced 0xc5c)
    refine step_c54_post_b (fnBase := (blkPl_617).base) hs3.pc hs3.run hs3.spAligned_state
      m5_drop_fetch_placed m5_drop_fetch_placed ?_
    intro s4 hpcm4 hrunm4 hsp4 hfp4 hm4 hsym4 hv4 hfs4 htr4
      hx19_4 hx22_4 hx23_4 hx24_4 hx25_4 hpool4 _ _
    refine SepWPp.weaken_pre (P' :=
      locals fsp (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr outLen inCap inPtr
          curCap curPtr g k) ∗
        A.pool lim (M.stepEvents (evs1 ++ evs_dealloc) st) s4 ∗
        stackAt fsp (stk - mainFrameSize) ∗ F)
      (Entails.of_eq (by
        dsimp +zetaDelta only [fsp]
        rw [hs3.sp, ← hs.sp, hopen, hpool4 M A lim (M.stepEvents (evs1 ++ evs_dealloc) st)]
        sep_ac_rfl)) ?_
    exact hnext s4 (evs1 ++ evs_dealloc)
      (hf1.append (FreeOnlyEvs.singleton 8 (curCap.toNat * 48)))
      (InMainPlaced.step_pure hs3 hpcm4 hrunm4 hsp4 hfp4 hm4
        (by simp only [calleeSavedVRegs, hv4]))
      (hx19_4.trans (hcsm3.1.trans (hx19_2'.trans hx19_2)))
      hx22_4
      hx23_4
      (hx24_4.trans (hcsm3.2.2.2.2.2.1.trans (hx24_2'.trans hx24_2)))
      (hx25_4.trans (hcsm3.2.2.2.2.2.2.1.trans (hx25_2'.trans hx25_2)))
      (hfs4.trans (hfs3.trans (hfs2'.trans (hfs2.trans hfs1))))
      (htr4.trans (htr3.trans (htr2'.trans (htr2.trans htr1))))

/-! ## 3. Top-Level Write-Error Cleanup `m5_drop_placed` and `m5_drop_for_m5_placed` -/

theorem m5_drop_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {io : IoModel} {F0 : FsFiles} {tr0 : List TraceEvent}
    {g : StoresGhost} {s0 s : State} {stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64}
    {out inp : List (BitVec 8)}
    {ps : List (BitVec 64 × List (BitVec 8))}
    {curEntries : List (List (BitVec 8) × List (BitVec 8))}
    {errE : M5ErrEntryPlaced}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hext : mainFrameSize + extHookStack ≤ stk)
    (herr : M5LoopErrPlaced CodeOk io F0 tr0 g s0 s n buf k curEntries errE)
    (hnext : ∀ (sm : State) (evsDrop evsRest : List AllocEvent),
      (evsDrop = m5ErrEntryDropEvents errE ++ evsRest ∧ FreeOnlyEvs evsRest) →
      AtM6Placed CodeOk s0 sm false n buf →
      sm.fs = s.fs →
      sm.trace = s.trace →
      commitFiles io.wr F0 g.writes = none →
      tr0 <+: sm.trace →
      ProcessOutcome.traceStreamBytes .stdout sm.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) sm
        (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
              (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evsDrop st) sm ∗ anyHeap)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (m5ErrMem A lim st s0 s stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
        curEntries errE)
      Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hk : k < 8 := herr.hk
  let Rest : SepProp :=
    ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      mainSaved s0 ∗ anyHeap
  refine sepWPp_with_stk_le_two_pow_64 (s0 := s0) (stk := stk)
    (F := errE.heap A.repAlloc ∗
      vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr curEntries ∗
      ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      locals fsp (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
        inCap inPtr curCap curPtr g k) ∗
      A.pool lim st s ∗ anyHeap)
    (by omega)
    (Entails.of_eq (by unfold m5ErrMem; sep_ac_rfl)) ?_
  intro hstk64
  refine SepWPp.weaken_pre (P' :=
    errE.heap A.repAlloc ∗
      locals fsp (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
        inCap inPtr curCap curPtr g k) ∗
      A.pool lim st s ∗ stackAt fsp (stk - mainFrameSize) ∗
      (vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr curEntries ∗ Rest))
    (Entails.of_eq (by unfold m5ErrMem Rest; sep_ac_rfl)) ?_
  refine m5_err_to_bf4_exact_placed (st := st) hA hext hstk64 hk herr.base herr.errRegs ?_
  intro s1 hs1 hx19_1 hx20_1 hx24_1 hfs1 htr1
  rw [herr.x19] at hx19_1
  rw [herr.x20] at hx20_1
  rw [herr.x24] at hx24_1
  let evs1 := m5ErrEntryDropEvents errE
  refine SepWPp.weaken_pre (P' :=
    vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr curEntries ∗
      locals fsp (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
        inCap inPtr curCap curPtr g k) ∗
      A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt fsp (stk - mainFrameSize) ∗ Rest)
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine m5_cur_dir_to_c5c_placed (st := M.stepEvents evs1 st) hA hext hstk64 herr.hne hs1
    hx20_1 ?_
  intro s2 evs2 hf2 hs2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2 hfs2 htr2
  rw [hx19_1] at hx19_2
  rw [hx24_1] at hx24_2
  rw [← M.stepEvents_append evs1 evs2 st]
  let evs12 := evs1 ++ evs2
  by_cases hk7 : k = 7
  · subst hk7
    apply seq_sepWP_pl (mid := mPcPlaced 0xf70)
    refine step_c5c_eq8_b (fnBase := (blkPl_617).base) hs2.pc hs2.run hx23_2
      m5_drop_fetch_placed m5_drop_fetch_placed ?_
    intro s3 hpcm3 hrunm3 hsp3 hfp3 hm3 hsym3 hv3 hfs3 htr3
      hx19_3 hx22_3 hx24_3 hpool3 _ _
    have hs3 : InMainPlaced CodeOk s0 s3 0xf70 :=
      InMainPlaced.step_pure hs2 hpcm3 hrunm3 hsp3 hfp3 hm3
        (by simp only [calleeSavedVRegs, hv3])
    have hlen8 : (storesDirs g).length ≤ 8 := Nat.le_of_eq (storesDirs_length g)
    have hdrop8 : (storesDirs g).drop 8 = [] := List.drop_of_length_le hlen8
    have hforget :
        locals fsp (m5ErrCellsPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
          inCap inPtr curCap curPtr g 7) ⊢
        locals fsp (m6CellsPlaced fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) := by
      unfold m5ErrCellsPlaced
      have h71 : 7 + 1 = 8 := rfl
      rw [h71, hdrop8, dirsAt_nil,
        show (emp : SepProp) = memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * 8)) (0x28 * (8 - 8))
          from (memRegion_zero _).symm]
      exact locals_m5ErrCellsPlaced_forget_to_m6CellsPlaced fsp outCap outPtr
        (BitVec.ofNat 64 out.length) inCap inPtr curCap curPtr (fsp + 456#64) 8#64 (m := 8)
        (by decide)
    refine SepWPp.weaken_pre (P' :=
      ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗
        locals fsp (m6CellsPlaced fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt fsp (stk - mainFrameSize) ∗
        A.pool lim (M.stepEvents evs12 st) s3 ∗ anyHeap)
      (Entails.trans (sepConj_mono_left hforget)
        (Entails.of_eq (by
          rw [hpool3 M A lim (M.stepEvents evs12 st)]
          unfold Rest
          sep_ac_rfl))) ?_
    have htr_eq : s3.trace = s.trace := htr3.trans (htr2.trans htr1)
    have hfs_eq : s3.fs = s.fs := hfs3.trans (hfs2.trans hfs1)
    exact hnext s3 evs12 evs2 ⟨rfl, hf2⟩
      { base := hs3
        w22 := by
          have hw := hx22_3.trans hx22_2
          rw [hw]; decide
        x19 := hx19_3.trans hx19_2
        x24 := hx24_3.trans hx24_2 }
      hfs_eq htr_eq herr.commitNone
      (htr_eq.symm ▸ herr.trace)
      (by rw [htr_eq]; exact herr.stdout)
  · have hne8 : BitVec.ofNat 64 (k + 1) ≠ 8#64 :=
      ofNat_ne_of_ne_lt (by omega) (by omega) (by decide)
    apply seq_sepWP_pl (mid := mPcPlaced 0xc70)
    refine step_c5c_ne8_b (fnBase := (blkPl_617).base) hs2.pc hs2.run hx23_2 hx25_2 hne8
      m5_drop_fetch_placed m5_drop_fetch_placed
      m5_drop_fetch_placed m5_drop_fetch_placed
      m5_drop_fetch_placed ?_
    intro s3 hpcm3 hrunm3 hsp3 hfp3 hm3 hsym3 hv3 hfs3 htr3
      hx19_3 hx22_3 hx23_3 hx24_3 hx26_3 hpool3 _ _
    have hs3 : InMainPlaced CodeOk s0 s3 0xc70 :=
      InMainPlaced.step_pure hs2 hpcm3 hrunm3 hsp3 hfp3 hm3
        (by simp only [calleeSavedVRegs, hv3])
    let pre9 : List (Nat × Nat × SepProp) :=
      [cell fsp 0x0 (BitVec.ofNat 64 out.length), cell fsp 0x8 outCap, cell fsp 0x10 inCap,
       cell fsp 0x18 outPtr, cell fsp 0x20 curCap, cell fsp 0x28 curPtr,
       cell fsp 0x30 (fsp + 0x1c8#64), cell fsp 0x38 (BitVec.ofNat 64 (k + 1)), cell fsp 0x50 inPtr]
    have hfoc := m5ErrCellsPlaced_focus_tail A.repAlloc fsp outCap outPtr
      (BitVec.ofNat 64 out.length) inCap inPtr curCap curPtr g k
    refine SepWPp.weaken_pre (P' :=
      dirsAt A.repAlloc (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1)))
          ((storesDirs g).drop (k + 1)) ∗
        A.pool lim (M.stepEvents evs12 st) s3 ∗ stackAt s3.sp (stk - mainFrameSize) ∗ anyHeap ∗
        (localsCtx fsp 0 pre9 (0x1c8 + 0x28 * (k + 1)) (0x28 * (8 - (k + 1))) [] ∗
          ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0))
      (Entails.of_eq (by
        rw [hfoc, hs3.sp, hpool3 M A lim (M.stepEvents evs12 st)]
        dsimp +zetaDelta only [fsp, Rest]
        sep_ac_rfl)) ?_
    refine m5_drop_dirs_tail_placed (m := k + 1) (st := M.stepEvents evs12 st)
      (by omega) (by omega)
      (by simp [storesDirs_length]) hA hext hstk64 hs3
      (hx23_3.trans (by
        have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
        clear * - hk_cases
        rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (dsimp +zetaDelta only [fsp]; bv_omega)))
      hx26_3 ?_
    intro sm evs3 hf3 hsm hx19_m hx22_m hx24_m hfs_m htr_m
    rw [← M.stepEvents_append evs12 evs3 st]
    have hunfoc :
        memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) (0x28 * (8 - (k + 1))) ∗
          localsCtx fsp 0 pre9 (0x1c8 + 0x28 * (k + 1)) (0x28 * (8 - (k + 1))) [] ⊢
        locals fsp (m6CellsPlaced fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) := by
      rw [← locals_focus fsp pre9 (0x1c8 + 0x28 * (k + 1)) (0x28 * (8 - (k + 1)))
        (memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) (0x28 * (8 - (k + 1)))) []]
      exact locals_m5ErrCellsPlaced_forget_to_m6CellsPlaced fsp outCap outPtr
        (BitVec.ofNat 64 out.length) inCap inPtr curCap curPtr (fsp + 0x1c8#64)
        (BitVec.ofNat 64 (k + 1)) (by omega)
    refine SepWPp.weaken_pre (P' :=
      ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗
        locals fsp (m6CellsPlaced fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt fsp (stk - mainFrameSize) ∗
        A.pool lim (M.stepEvents (evs12 ++ evs3) st) sm ∗ anyHeap) ?_ ?_
    · refine Entails.trans (Entails.of_eq (show
        memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) (0x28 * (8 - (k + 1))) ∗
          A.pool lim (M.stepEvents (evs12 ++ evs3) st) sm ∗
          stackAt s3.sp (stk - mainFrameSize) ∗ anyHeap ∗
          (localsCtx fsp 0 pre9 (0x1c8 + 0x28 * (k + 1)) (0x28 * (8 - (k + 1))) [] ∗
            ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0) =
        (memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) (0x28 * (8 - (k + 1))) ∗
          localsCtx fsp 0 pre9 (0x1c8 + 0x28 * (k + 1)) (0x28 * (8 - (k + 1))) []) ∗
          (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
            stackAt fsp (stk - mainFrameSize) ∗
            A.pool lim (M.stepEvents (evs12 ++ evs3) st) sm ∗ anyHeap) by
          rw [hs3.sp]; dsimp +zetaDelta only [fsp]; sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hunfoc) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    · have htr_eq : sm.trace = s.trace := htr_m.trans (htr3.trans (htr2.trans htr1))
      have hfs_eq : sm.fs = s.fs := hfs_m.trans (hfs3.trans (hfs2.trans hfs1))
      exact hnext sm (evs12 ++ evs3) (evs2 ++ evs3)
        ⟨by simp only [evs12, evs1, List.append_assoc], hf2.append hf3⟩
        { base := hsm
          w22 := by
            have hw := hx22_m.trans (hx22_3.trans hx22_2)
            rw [hw]; decide
          x19 := hx19_m.trans (hx19_3.trans hx19_2)
          x24 := hx24_m.trans (hx24_3.trans hx24_2) }
        hfs_eq htr_eq herr.commitNone
        (htr_eq.symm ▸ herr.trace)
        (by rw [htr_eq]; exact herr.stdout)

/-- Continuation wrapper matching `main_m5_proof_placed`'s `hnext` obligation when a `write_file`
call in `main`'s M5 commit loop exits on `Err`, exposing
`evsDrop = m5ErrEntryDropEvents errE ++ evsRest ∧ FreeOnlyEvs evsRest`. -/
theorem m5_drop_for_m5_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {io : IoModel} {i : Inputs} {c : CallV} {g : StoresGhost}
    {out : List (BitVec 8)} {s0 s sErr : State} {stk k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))}
    {curEntries : List (List (BitVec 8) × List (BitVec 8))}
    {errE : M5ErrEntryPlaced}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hext : mainFrameSize + extHookStack ≤ stk)
    (herr : M5LoopErrPlaced CodeOk io s.fs.files s.trace g s0 sErr i.argv.length buf k curEntries errE)
    (hnext : ∀ (s' : State) (evsDrop evsRest : List AllocEvent) (ok : Bool)
        (outCap' outPtr' : BitVec 64),
      (evsDrop = m5ErrEntryDropEvents errE ++ evsRest ∧ FreeOnlyEvs evsRest) →
      (match commitFiles io.wr s.fs.files g.writes with
       | some F => ok = true ∧ s'.fs.files = F
       | none => ok = false) →
      s.trace <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout s.trace →
      AtM6Placed CodeOk s0 s' ok i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc outCap' outPtr' (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap' outPtr'
              (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evsDrop st) s' ∗ anyHeap)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) sErr
      (m5ErrMem A lim st s0 sErr stk i.argv.length outCap outPtr inCap inPtr buf curCap curPtr
        out (inputOf i c) ps g k curEntries errE)
      Q Qp oom := by
  refine m5_drop_placed (st := st) hA hext herr ?_
  intro sm evsDrop evsRest hsplit hatM6 _ _ hcommit htr hstdout
  exact hnext sm evsDrop evsRest false outCap outPtr hsplit (by rw [hcommit]) htr hstdout hatM6

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPlacedBudget
