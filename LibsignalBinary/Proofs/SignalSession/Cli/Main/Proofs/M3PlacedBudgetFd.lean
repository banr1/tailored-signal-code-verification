/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Descriptor-Threaded `MainIoOfPlacedFd` & `main` Hop M3 (`M+0x568 → M+0x5dc`, Block `617`)

Threads `FdsGe3Closed` from initial filesystem state across `main`'s Hop M3 (`read_stdin` and
`read_file("coins")`) into `AtM4Placed`, and projects a write-only `MainIoOfPlaced` bundle for
downstream hops `M5` and `M6`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession
  (Inputs lsReadFileSym lsReadStdinSym lsWriteFileSym lsWriteStdoutSym
   readStdinResult stdinCapBytes)
open CryptoVerification.SignalSession.Cli
  (CoinsReadable cliInputs cliStaticsPlaced ioVecAt utf8)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkLib_eq_617 blkPC_617 blkPl_617 lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtCallPlaced AtM4Placed CallV CallW InMainPlaced IoModel LsCodeInv ReadStdinGhost
   addrWords argsBuf callCellsPlaced callHeap cell coinsOf inputOf locals localsBound
   localsCtx localsEnd localsFrom locals_carve_cell locals_carve_region locals_focus
   locals_forget_cell m4CellsPlaced mPcPlaced_eq mProgPlaced mProgPlaced_eq mainFrameSize
   mainLitsBlk617 mainSaved main_call_rocl ownedBytes parseArgs sepWPp_seq_codeOk)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
  (emp_entails_ownedBytes_nil entails_pure_elim_left entails_pure_intro_left inInv inInvOpt
   memRegion_16_cells stackAt_sub_split vecU8_to_ownedBytes)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit (withLsRetAddr624AndFds)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed fdsGe3Closed_initFsState withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced ReadStdinBoundedEnv readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudget (M3EnvReadOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudget
  (M3StdinEnvReadOf ReadCoinsEnvOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudgetFd
  (step_from_0x5b0_readOf_pool_placed_subroutine_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget (ExitKPoolPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (ReadFileRuleEnv readFileLitSpecPlaced writeFileSpecPlaced writeStdoutSpecPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit

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
  refine sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := mid) hinv ?_
  apply sepWP_seg_ls_vm
    (Q := (blkPC_617).rebase (blkPl_617).base (hooksException H))
    blkLib_eq_617 (mid := mid)
  intro m_strip
  refine SepWP.mono (hseg m_strip) fun sm' Pm hpc_m' hrun_m' hcont m_real hnsp => ?_
  exact SepWP.done hpc_m' hrun_m' (hcont m_real hnsp)

/-- Descriptor-threaded Block-`617` I/O bundle:
- `readStdin` preserves `FdsGe3Closed` across `M3`'s optional `read_stdin` call;
- `readFile` consumes `LsRetAddr624 lr ∧ FdsGe3Closed s.fs` and preserves `FdsGe3Closed`
  across `M3`'s `read_file("coins")` call;
- `writeFile` and `writeStdout` remain plain (`M5` and `M6` perform no reads). -/
structure MainIoOfPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    (StdinEnv : List (BitVec 8) → List AllocEvent → Prop := ReadStdinBoundedEnv)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv io.rd) :
    Prop where
  readStdin : subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
    (withLsRoCl lsmpl (withFdsGe3Closed (readStdinSpecOfPlaced io A lim hookStack StdinEnv)))
  readFile : subroutine_ok (lsProg_617 H) (lsρ lsReadFileSym)
    (withLsRoCl lsmpl (withLsRetAddr624AndFds (readFileLitSpecPlaced io A lim hookStack ReadEnv)))
  writeFile : subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
    (withLsRoCl lsmpl (writeFileSpecPlaced io A lim hookStack))
  writeStdout : subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
    (withLsRoCl lsmpl (writeStdoutSpecPlaced A lim hookStack))

/-- Over-max `AllocEvent` environment (`req = 2 ^ 64`), whose `FitsEnv` is impossible under any
    `M : AllocCostModel`, `lim : BudgetLimits`, and `st : M.σ`. Used to instantiate the unused
    `{StdinEnv, ReadEnv}` parameters of `main_m5_of_proof_placed` and
    `main_m6_of_m6Env_pool_proof_placed` without re-proving `M5` or `M6`. -/
def VacuousIoAllocEnv : List AllocEvent → Prop :=
  fun evs => evs = [.alloc (2 ^ 64)]

private theorem not_fitsEnv_vacuousIoAllocEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (h : FitsEnv M lim st VacuousIoAllocEnv) : False := by
  have hev := (h [.alloc (2 ^ 64)] rfl).1.1
  exact absurd hev (by decide)

/-- Project `MainIoOfPlacedFd` to a write-only `MainIoOfPlaced` at `VacuousIoAllocEnv` for
    hops `M5` and `M6` (which never invoke `readStdin` or `readFile`). -/
theorem MainIoOfPlacedFd.toWriteOnlyMainIo [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoOfPlacedFd A lim H io hookStack StdinEnv ReadEnv) :
    MainIoOfPlaced A lim H io hookStack
      (fun _ => VacuousIoAllocEnv) (fun _ _ => VacuousIoAllocEnv) where
  readStdin := by
    refine subroutine_ok_intro fun (x, st) s0 R _ _ hpre => False.elim ?_
    dsimp only [withLsRoCl, readStdinSpecOfPlaced] at hpre
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact not_fitsEnv_vacuousIoAllocEnv hpre.1.2.2.1
  readFile := by
    refine subroutine_ok_intro fun (x, st) s0 R _ _ hpre => False.elim ?_
    dsimp only [withLsRoCl, readFileLitSpecPlaced] at hpre
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact not_fitsEnv_vacuousIoAllocEnv hpre.1.2.2.2.2.2
  writeFile := hio.writeFile
  writeStdout := hio.writeStdout

private theorem pool_congr_vm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ms : M.σ) (s : State) {s' : State}
    (hbs : s'.brkStart = s.brkStart) (hbrk : s'.brk = s.brk)
    (htp : s'.tpidrEl0 = s.tpidrEl0) (hphys : s'.physMemAvail = s.physMemAvail)
    (hperm : ∀ a : BitVec 64, s'.mem.perm a = s.mem.perm a)
    (hfs : s'.fs = s.fs := by first | rfl | simp +zetaDelta only [wp_norm, arm64_norm]) :
    A.pool lim ms s' = A.pool lim ms s :=
  A.pool_of_vmPreserved ⟨⟨hbs, hbrk, htp⟩, hphys, hperm, LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩

private theorem zext32_eq_self_of_lt {x : BitVec 64} (hlt : x.toNat < 2 ^ 32) :
    (x.setWidth 32).setWidth 64 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, Nat.reducePow]
  omega

private theorem msb_false_of_lt {x : BitVec 64} (hlt : x.toNat < 2 ^ 63) :
    x.msb = false := by
  rw [BitVec.msb_eq_false_iff_two_mul_lt]
  omega

set_option maxHeartbeats 1200000 in
/-- `FdsGe3Closed`-threaded twin of `M3ReadPlacedBudget.step_stdin_0x59c_readOf_pool_placed`:
    discharges `FdsGe3Closed` at `read_stdin` from `hs0fs`, preserves `FdsGe3Closed` across
    `read_stdin` via `hio.readStdin`, and threads it through `read_file("coins")` into `hnext`. -/
theorem step_stdin_0x59c_readOf_pool_placed_fd [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {stk hookStack resStack : Nat}
    {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlacedFd A lim H io hookStack StdinEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i))
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (M3StdinEnvReadOf StdinEnv ReadEnv i))
    (htag_gt1 : 1 < c.tag)
    (hs_tr : s.trace = s0.trace)
    (hst : InMainPlaced CodeOk s0 st 0x59c)
    (hst_tr : st.trace = s.trace)
    (hst_fs : st.fs = s0.fs)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx26 : st.readReg64 (.gpr 26#5) = w.w6)
    (hw5_orr : (st.readReg64 (.gpr 28#5) ||| st.readReg64 (.gpr 21#5)) = w.w5)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      M3StdinEnvReadOf StdinEnv ReadEnv i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
      FdsGe3Closed s'.fs →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvFrame ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs ms) s' ∗
          cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom := by
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hstdin_ok :
      subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadStdinSym)
        (withLsRoCl lsmpl (withFdsGe3Closed (readStdinSpecOfPlaced io A lim hookStack StdinEnv))) :=
    hio.readStdin
  have hread_ok :
      subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadFileSym)
        (withLsRoCl lsmpl (withLsRetAddr624AndFds (readFileLitSpecPlaced io A lim hookStack ReadEnv))) :=
    hio.readFile
  have hsub_le : hookStack ≤ stk - mainFrameSize := by omega
  have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  have hfit_stdin_env : FitsEnv M lim ms (StdinEnv i.stdin) :=
    FitsEnv.seq_left (E₁ := StdinEnv i.stdin) (E₂ := ReadCoinsEnvOf ReadEnv i) hfit
  have hcarve50 := locals_carve_cell fsp
    [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 [cell fsp 0x58 w.w1]
  rw [show callCellsPlaced fsp w =
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] ++ [cell fsp 0x58 w.w1] by rfl,
    hcarve50]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun old50 => ?_
  have hcarve60 := locals_carve_region fsp
    [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 old50, cell fsp 0x58 w.w1]
    0x60 24 []
  rw [List.append_nil] at hcarve60
  rw [show [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] ++
        cell fsp 0x50 old50 :: [cell fsp 0x58 w.w1] =
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 old50, cell fsp 0x58 w.w1] by rfl,
    hcarve60,
    locals_focus fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 old50, cell fsp 0x58 w.w1]
      0x60 24 (memRegion (fsp + 96#64) 24) []]
  have hal : st.spAligned = true := hst.spAligned_state
  have hsp : st.sp = fsp := hst.sp
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsReadStdinSym) hinv
  wp_steps
  apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
    (by (try simp only [arm64_norm, *]); try rfl)
  intro hinv1
  refine main_call_rocl (CodeOk := CodeOk)
    (spec := withFdsGe3Closed (readStdinSpecOfPlaced io A lim hookStack StdinEnv))
    (({ ret := fsp + 96#64, bs := i.stdin } : ReadStdinGhost), ms)
    hstdin_ok
    hinv1 (by (try simp only [arm64_norm, *]); try rfl)
    (by (try simp only [arm64_norm, *]); try rfl)
    (by simp only [arm64_norm]; exact hal)
    (ret_pc := (blkPl_617).base + 1444#64) (by (try simp only [arm64_norm, *]); try rfl)
    (F := callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
      ArgvFrame ∗
      mainSaved s0 ∗
      localsCtx fsp 0
        [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 old50, cell fsp 0x58 w.w1]
        0x60 24 [] ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - hookStack) ∗
      cliStaticsPlaced ∗ mainLitsBlk617)
    ?_ (hnext := ?_)
  · dsimp only [withFdsGe3Closed, readStdinSpecOfPlaced]
    conv => arg 2; rw [pool_congr_vm A lim ms st (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm])]
    simp only [arm64_norm, hst_fs, hs0fs, hsp]
    rw [stackAt_sub_split fsp hsub_le hsub64]
    apply entails_pure_intro_left ⟨fdsGe3Closed_initFsState (cliInputs i), hstdin,
      hfit_stdin_env, lsRetAddr624_base_add 617 1444#64 (by decide) (by decide)⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [withFdsGe3Closed, readStdinSpecOfPlaced]
    have hx19_f : sf.readReg64 (.gpr 19#5) = buf := by rw [hcs_f.1]; simp only [arm64_norm, hx19]
    have hx20_f : sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag := by
      rw [hcs_f.2.1]; simp only [arm64_norm, hx20]
    have hw5_f : (sf.readReg64 (.gpr 28#5) ||| sf.readReg64 (.gpr 21#5)) = w.w5 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.1, hcs_f.2.2.1]; simp only [arm64_norm, hw5_orr]
    have hx22_f : sf.readReg64 (.gpr 22#5) = w.w2 := by
      rw [hcs_f.2.2.2.1]; simp only [arm64_norm, hx22]
    have hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length := by
      rw [hcs_f.2.2.2.2.2.1]; simp only [arm64_norm, hx24]
    have hx25_f : sf.readReg64 (.gpr 25#5) = w.w0 := by
      rw [hcs_f.2.2.2.2.2.2.1]; simp only [arm64_norm, hx25]
    have hx26_f : sf.readReg64 (.gpr 26#5) = w.w6 := by
      rw [hcs_f.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hx26]
    have hsp_sf : sf.sp = fsp := by rw [hsp_f]; simp only [arm64_norm, hsp]
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf, fsp, mainFrameSize]
      exact ProofLib.spAligned_sub s0.sp 1248#64 hst.spAligned
    have hfp_sf : sf.readReg64 .fp = s0.sp - 96#64 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hst.fp]
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.2.2]; simp only [calleeSavedVRegs, arm64_norm, hst.vregs]
    have hsp_pre : (_ : State).sp = fsp := hsp_f.symm.trans hsp_sf
    rw [hsp_pre, sepConj_assoc]
    refine SepWPp.pure_elim fun hfds_sf => ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evsIn => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hevsIn => ?_
    have hfit_coins : FitsEnv M lim (M.stepEvents evsIn ms) (ReadCoinsEnvOf ReadEnv i) :=
      FitsEnv.seq_right (E₁ := StdinEnv i.stdin) (E₂ := ReadCoinsEnvOf ReadEnv i) hfit hevsIn
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    refine SepWPp.exists_elim fun rIn => ?_
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hfiles_f, hok_in, htr_sf⟩ => ?_
    subst hok_in
    have hfiles_sf : sf.fs.files = (initFsState (cliInputs i)).files :=
      hfiles_f.trans (by simp only [arm64_norm, hst_fs, hs0fs])
    have htr_sf_eq : sf.trace = s.trace :=
      htr_sf.trans (by simp only [arm64_norm, hst_tr])
    have hin_of_eq : inputOf i c = i.stdin := by simp only [inputOf, htag_gt1, ↓reduceIte]
    have hctx_open :
        localsCtx fsp 0
          [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 old50, cell fsp 0x58 w.w1]
          0x60 24 [] =
        ((fsp + 80#64) ↦₆₄ old50) ∗
          localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8
            [cell fsp 0x58 w.w1, (0x60, 24, emp)] := by
      simp only [localsCtx, localsFrom, emp_sepConj]
      sep_ac_rfl
    have hloc_merge : ∀ (inPtr' c60 c70 : BitVec 64),
        ((fsp + 80#64) ↦₆₄ inPtr') ∗ ((fsp + 96#64) ↦₆₄ c60) ∗
          ((fsp + 104#64) ↦₆₄ inPtr') ∗ ((fsp + 112#64) ↦₆₄ c70) ∗
          localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8
            [cell fsp 0x58 w.w1, (0x60, 24, emp)] ⊢
        locals fsp
          [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr', cell fsp 0x58 w.w1] := by
      intro inPtr' c60 c70
      have h24 :
          ((fsp + 96#64) ↦₆₄ c60) ∗ ((fsp + 104#64) ↦₆₄ inPtr') ∗
            ((fsp + 112#64) ↦₆₄ c70) ⊢
            memRegion (fsp + 96#64) 24 := by
        rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
          memRegion_split (fsp + 96#64) 8 (8 + 8) (by decide),
          memRegion_split ((fsp + 96#64) + 8#64) 8 8 (by decide)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
      have hctx2 :
          ((fsp + 80#64) ↦₆₄ inPtr') ∗ memRegion (fsp + 96#64) 24 ∗
            localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8
              [cell fsp 0x58 w.w1, (0x60, 24, emp)] =
          locals fsp
            [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr', cell fsp 0x58 w.w1] := by
        have hc2 := locals_carve_region fsp
          [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr', cell fsp 0x58 w.w1]
          0x60 24 []
        rw [List.append_nil] at hc2
        rw [hc2]
        simp only [locals, localsFrom, localsCtx, cell, List.cons_append, List.nil_append,
          emp_sepConj]
        sep_ac_rfl
      rw [← hctx2]
      exact sepConj_mono_right (by
        rw [← sepConj_assoc, ← sepConj_assoc]
        exact sepConj_mono_left (by simpa only [sepConj_assoc] using h24))
    by_cases hcap_in : i.stdin.length ≤ stdinCapBytes
    · have hr_in : readStdinResult i.stdin = .ok i.stdin := by
        simp only [readStdinResult, hcap_in, ↓reduceIte]
      rw [hr_in]
      dsimp only [ioVecAt]
      refine SepWPp.weaken_pre
        (sepConj_mono_left (vecU8_to_ownedBytes A.repAlloc (fsp + 96#64) i.stdin)) ?_
      simp only [sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd]
      refine SepWPp.exists_elim fun inCap => ?_
      refine SepWPp.exists_elim fun inPtr => ?_
      rw [hctx_open]
      refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 1456#64) hinv_f
        fun _m_strip => ?_
      have hal_strip : (sf.setMem _m_strip).spAligned = true := hal_sf
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro _m_real hnsp_5b0 hinv_5b0
      have hin_5b0 : InMainPlaced CodeOk s0 _ 0x5b0 := {
        inv := hinv_5b0
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by simp only [arm64_norm, *]
        sp := by (try simp only [arm64_norm]); exact hsp_sf
        fp := by (try simp only [arm64_norm]); exact hfp_sf
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hvregs_sf
        spAligned := hst.spAligned
      }
      refine SepWPp.weaken_pre ?_
        (step_from_0x5b0_readOf_pool_placed_subroutine_fd (ms := M.stepEvents evsIn ms)
          (inOk := true) (buf := buf) (inCap := inCap) (inPtr := inPtr)
          (x27 := BitVec.ofNat 64 i.stdin.length)
          (c := c) (w := w) (ps := ps) (ArgvFrame := ArgvFrame)
          hc hread_ok hstk hstk64 hcoinsOk hcoins hfit_coins hs_tr hin_5b0
          (by simpa only [arm64_norm] using hfds_sf)
          (by (try simp only [arm64_norm, hx19_f]); try rfl)
          (by (try simp only [arm64_norm, hx20_f]); try rfl)
          (by (try simp only [arm64_norm, hx22_f]); try rfl)
          (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hx24_f]); try rfl)
          (by (try simp only [arm64_norm, hx25_f]); try rfl)
          (by (try simp only [arm64_norm, hx26_f]); try rfl)
          (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hw5_f]); try rfl)
          (by (try simp only [arm64_norm, hfiles_sf]); try rfl)
          (by simpa only [arm64_norm] using htr_sf_eq)
          hexit
          (fun s' cc cp ic ip evsCoins hevsCoins hin_le hat hfds' => by
            rw [← M.stepEvents_append evsIn evsCoins ms]
            exact hnext s' cc cp ic ip (evsIn ++ evsCoins)
              (SeqEnv.append (E₁ := StdinEnv i.stdin) (E₂ := ReadCoinsEnvOf ReadEnv i)
                hevsIn hevsCoins)
              hin_le hat hfds'))
      conv => arg 2; rw [pool_congr_vm A lim (M.stepEvents evsIn ms) sf
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (fun a => congrFun hnsp_5b0.2.1 a)]
      have hin_inv :
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 i.stdin.length) i.stdin ⊢
            inInvOpt true A.repAlloc i c inCap inPtr (BitVec.ofNat 64 i.stdin.length) := by
        dsimp only [inInvOpt, inInv]
        rw [hin_of_eq]
        exact entails_pure_intro_left hcap_in (entails_pure_intro_left rfl (Entails.refl _))
      rw [stackAt_sub_split fsp hsub_le hsub64]
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 80#64) ↦₆₄ inPtr) ∗ ((fsp + 96#64) ↦₆₄ inCap) ∗
          ((fsp + 104#64) ↦₆₄ inPtr) ∗ ((fsp + 112#64) ↦₆₄ BitVec.ofNat 64 i.stdin.length) ∗
          localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8
            [cell fsp 0x58 w.w1, (0x60, 24, emp)]) ∗
        (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 i.stdin.length) i.stdin ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvFrame ∗
          mainSaved s0 ∗
          (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - hookStack) ∗ stackAt fsp hookStack) ∗
          A.pool lim (M.stepEvents evsIn ms) sf ∗ cliStaticsPlaced ∗ mainLitsBlk617) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono (hloc_merge inPtr inCap (BitVec.ofNat 64 i.stdin.length))
        (sepConj_mono_left hin_inv)) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    · have hr_in : readStdinResult i.stdin = .error () := by
        simp only [readStdinResult, hcap_in, ↓reduceIte]
      rw [hr_in]
      dsimp only [ioVecAt]
      refine SepWPp.weaken_pre
        (sepConj_mono_left (sepConj_mono_right (memRegion_16_cells (fsp + 96#64)))) ?_
      simp only [sepExists_sepConj_right, sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd]
      refine SepWPp.exists_elim fun errInPtr => ?_
      refine SepWPp.exists_elim fun errInLen => ?_
      rw [hctx_open]
      refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 1456#64) hinv_f
        fun _m_strip => ?_
      have hal_strip : (sf.setMem _m_strip).spAligned = true := hal_sf
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro _m_real hnsp_5b0 hinv_5b0
      have hin_5b0 : InMainPlaced CodeOk s0 _ 0x5b0 := {
        inv := hinv_5b0
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by simp only [arm64_norm, *]
        sp := by (try simp only [arm64_norm]); exact hsp_sf
        fp := by (try simp only [arm64_norm]); exact hfp_sf
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hvregs_sf
        spAligned := hst.spAligned
      }
      refine SepWPp.weaken_pre ?_
        (step_from_0x5b0_readOf_pool_placed_subroutine_fd (ms := M.stepEvents evsIn ms)
          (inOk := false) (buf := buf) (inCap := 0xffffffffffffffff#64)
          (inPtr := errInPtr) (x27 := errInLen)
          (c := c) (w := w) (ps := ps) (ArgvFrame := ArgvFrame)
          hc hread_ok hstk hstk64 hcoinsOk hcoins hfit_coins hs_tr hin_5b0
          (by simpa only [arm64_norm] using hfds_sf)
          (by (try simp only [arm64_norm, hx19_f]); try rfl)
          (by (try simp only [arm64_norm, hx20_f]); try rfl)
          (by (try simp only [arm64_norm, hx22_f]); try rfl)
          (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hx24_f]); try rfl)
          (by (try simp only [arm64_norm, hx25_f]); try rfl)
          (by (try simp only [arm64_norm, hx26_f]); try rfl)
          (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hw5_f]); try rfl)
          (by (try simp only [arm64_norm, hfiles_sf]); try rfl)
          (by simpa only [arm64_norm] using htr_sf_eq)
          hexit
          (fun s' cc cp ic ip evsCoins hevsCoins hin_le hat hfds' => by
            rw [← M.stepEvents_append evsIn evsCoins ms]
            exact hnext s' cc cp ic ip (evsIn ++ evsCoins)
              (SeqEnv.append (E₁ := StdinEnv i.stdin) (E₂ := ReadCoinsEnvOf ReadEnv i)
                hevsIn hevsCoins)
              hin_le hat hfds'))
      conv => arg 2; rw [pool_congr_vm A lim (M.stepEvents evsIn ms) sf
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (fun a => congrFun hnsp_5b0.2.1 a)]
      have hin_inv : emp ⊢ inInvOpt false A.repAlloc i c 0xffffffffffffffff#64 errInPtr errInLen := by
        dsimp only [inInvOpt]
        rw [← sepConj_emp ⌜_⌝]
        exact entails_pure_intro_left ⟨rfl, htag_gt1, Nat.lt_of_not_ge hcap_in⟩ (Entails.refl emp)
      rw [stackAt_sub_split fsp hsub_le hsub64]
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 80#64) ↦₆₄ errInPtr) ∗ ((fsp + 96#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((fsp + 104#64) ↦₆₄ errInPtr) ∗ ((fsp + 112#64) ↦₆₄ errInLen) ∗
          localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8
            [cell fsp 0x58 w.w1, (0x60, 24, emp)]) ∗
        (emp ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvFrame ∗
          mainSaved s0 ∗
          (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - hookStack) ∗ stackAt fsp hookStack) ∗
          A.pool lim (M.stepEvents evsIn ms) sf ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        by simp only [emp_sepConj]; sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono (hloc_merge errInPtr 0xffffffffffffffff#64 errInLen)
        (sepConj_mono_left hin_inv)) ?_
      exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
private theorem step_empty_in_0x57c_pool_placed_fd [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ} {uuidParse : UuidParser}
    {io : IoModel} {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlacedFd A lim H io hookStack StdinEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i))
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (ReadCoinsEnvOf ReadEnv i))
    (htag_le1 : ¬ (1 < c.tag))
    (hs_tr : s.trace = s0.trace)
    (hst : InMainPlaced CodeOk s0 st 0x57c)
    (hst_tr : st.trace = s.trace)
    (hst_fs : st.fs = s0.fs)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx26 : st.readReg64 (.gpr 26#5) = w.w6)
    (hw5_orr : (st.readReg64 (.gpr 28#5) ||| st.readReg64 (.gpr 21#5)) = w.w5)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      ReadCoinsEnvOf ReadEnv i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
      FdsGe3Closed s'.fs →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvFrame ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs ms) s' ∗
          cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom := by
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hc1 := locals_carve_cell fsp
    [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 [cell fsp 0x58 w.w1]
  rw [show callCellsPlaced fsp w =
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] ++ [cell fsp 0x58 w.w1] by rfl,
    hc1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun c50 => ?_
  rw [show [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] ++ cell fsp 0x50 c50 :: [cell fsp 0x58 w.w1] =
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 c50, cell fsp 0x58 w.w1] by rfl]
  have hc2 := locals_carve_cell fsp
    [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 c50, cell fsp 0x58 w.w1] 0x60 []
  rw [List.append_nil] at hc2; rw [hc2]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun c60 => ?_
  have hc3 := locals_carve_cell fsp
    ([cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 c50, cell fsp 0x58 w.w1] ++
      [cell fsp 0x60 c60]) 0x68 []
  rw [List.append_nil] at hc3; rw [hc3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun c68 => ?_
  have hc4 := locals_carve_cell fsp
    ([cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 c50, cell fsp 0x58 w.w1] ++
      [cell fsp 0x60 c60] ++ [cell fsp 0x68 c68]) 0x70 []
  rw [List.append_nil] at hc4; rw [hc4]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun c70 => ?_
  have hloc_open :
      locals fsp
        ([cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 c50, cell fsp 0x58 w.w1] ++
          [cell fsp 0x60 c60] ++ [cell fsp 0x68 c68] ++ [cell fsp 0x70 c70]) =
      ((fsp + 80#64) ↦₆₄ c50) ∗ ((fsp + 96#64) ↦₆₄ c60) ∗
        ((fsp + 104#64) ↦₆₄ c68) ∗ ((fsp + 112#64) ↦₆₄ c70) ∗
        ((fsp + 64#64) ↦₆₄ w.w3) ∗ ((fsp + 72#64) ↦₆₄ w.w4) ∗
        ((fsp + 88#64) ↦₆₄ w.w1) ∗ memRegion fsp 0x40 ∗
        memRegion (fsp + 120#64) (0x480 - 0x78) := by
    simp only [locals, localsFrom, List.nil_append, List.cons_append,
      Nat.reduceAdd, Nat.reduceSub, ProofLib.memRegion_zero, emp_sepConj]
    sep_ac_rfl
  rw [hloc_open]
  have hal : st.spAligned = true := hst.spAligned_state
  have hsp : st.sp = fsp := hst.sp
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 1456#64) hinv
    fun _m_strip => ?_
  have hal_strip : (st.setMem _m_strip).spAligned = true := hal
  wp_steps
  apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
    (by (try simp only [arm64_norm, *]); try rfl)
  intro _m_real hnsp_5b0 hinv1
  have hin1 : InMainPlaced CodeOk s0 _ 0x5b0 := {
    inv := hinv1
    pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
    run := by simp only [arm64_norm, *]
    sp := by (try simp only [arm64_norm]); exact hst.sp
    fp := by (try simp only [arm64_norm]); exact hst.fp
    vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
    spAligned := hst.spAligned
  }
  have hin_nil : inputOf i c = [] := by simp only [inputOf, htag_le1, ↓reduceIte]
  refine SepWPp.weaken_pre ?_
    (step_from_0x5b0_readOf_pool_placed_subroutine_fd
      (inOk := true) (inCap := 0#64) (inPtr := 1#64) (x27 := 0#64)
      (c := c) (w := w) (ps := ps) (ArgvFrame := ArgvFrame)
      hc hio.readFile hstk hstk64 hcoinsOk hcoins hfit hs_tr hin1
      (by simpa only [arm64_norm, hst_fs, hs0fs] using fdsGe3Closed_initFsState (cliInputs i))
      (by (try simp only [arm64_norm, hx19]); try rfl)
      (by (try simp only [arm64_norm, hx20]); try rfl)
      (by (try simp only [arm64_norm, hx22]); try rfl)
      (by (try simp only [arm64_norm]); try rfl)
      (by (try simp only [arm64_norm, hx24]); try rfl)
      (by (try simp only [arm64_norm, hx25]); try rfl)
      (by (try simp only [arm64_norm, hx26]); try rfl)
      (by (try simp only [arm64_norm]); try rfl)
      (by (try simp only [arm64_norm, hw5_orr]); try rfl)
      (by (try simp only [arm64_norm, hst_fs, hs0fs]); try rfl)
      (by (try simp only [arm64_norm, hst_tr]); try rfl)
      hexit hnext)
  conv => arg 2; rw [pool_congr_vm A lim ms st
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (fun a => congrFun hnsp_5b0.2.1 a)]
  have hloc_close :
      ((fsp + 80#64) ↦₆₄ 1#64) ∗ ((fsp + 96#64) ↦₆₄ 0#64) ∗
        ((fsp + 104#64) ↦₆₄ 1#64) ∗ ((fsp + 112#64) ↦₆₄ 0#64) ∗
        ((fsp + 64#64) ↦₆₄ w.w3) ∗ ((fsp + 72#64) ↦₆₄ w.w4) ∗
        ((fsp + 88#64) ↦₆₄ w.w1) ∗ memRegion fsp 0x40 ∗
        memRegion (fsp + 120#64) (0x480 - 0x78) ⊢
      locals fsp
        [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 1#64, cell fsp 0x58 w.w1] := by
    have hpack :
        locals fsp
          [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 1#64, cell fsp 0x58 w.w1,
           cell fsp 0x60 0#64, cell fsp 0x68 1#64, cell fsp 0x70 0#64] =
        ((fsp + 80#64) ↦₆₄ 1#64) ∗ ((fsp + 96#64) ↦₆₄ 0#64) ∗
          ((fsp + 104#64) ↦₆₄ 1#64) ∗ ((fsp + 112#64) ↦₆₄ 0#64) ∗
          ((fsp + 64#64) ↦₆₄ w.w3) ∗ ((fsp + 72#64) ↦₆₄ w.w4) ∗
          ((fsp + 88#64) ↦₆₄ w.w1) ∗ memRegion fsp 0x40 ∗
          memRegion (fsp + 120#64) (0x480 - 0x78) := by
      simp only [locals, localsFrom, Nat.reduceAdd, Nat.reduceSub, ProofLib.memRegion_zero,
        emp_sepConj]
      sep_ac_rfl
    rw [← hpack]
    have hf1 := locals_forget_cell fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 1#64, cell fsp 0x58 w.w1,
       cell fsp 0x60 0#64, cell fsp 0x68 1#64] 0x70 0#64 []
    have hf2 := locals_forget_cell fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 1#64, cell fsp 0x58 w.w1,
       cell fsp 0x60 0#64] 0x68 1#64 []
    have hf3 := locals_forget_cell fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 1#64, cell fsp 0x58 w.w1]
      0x60 0#64 []
    simp only [List.append_nil, List.cons_append, List.nil_append] at hf1 hf2 hf3
    exact Entails.trans hf1 (Entails.trans hf2 hf3)
  have hin_inv : emp ⊢ inInvOpt true A.repAlloc i c 0#64 1#64 0#64 := by
    dsimp only [inInvOpt, inInv]
    rw [hin_nil]
    exact entails_pure_intro_left (Nat.zero_le _)
      (entails_pure_intro_left rfl (emp_entails_ownedBytes_nil A.repAlloc))
  refine Entails.trans (Entails.of_eq (show _ =
    emp ∗
      (((fsp + 80#64) ↦₆₄ 1#64) ∗ ((fsp + 96#64) ↦₆₄ 0#64) ∗
        ((fsp + 104#64) ↦₆₄ 1#64) ∗ ((fsp + 112#64) ↦₆₄ 0#64) ∗
        ((fsp + 64#64) ↦₆₄ w.w3) ∗ ((fsp + 72#64) ↦₆₄ w.w4) ∗
        ((fsp + 88#64) ↦₆₄ w.w1) ∗ memRegion fsp 0x40 ∗
        memRegion (fsp + 120#64) (0x480 - 0x78)) ∗
      (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ cliStaticsPlaced ∗ mainLitsBlk617) by simp only [emp_sepConj]; sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hin_inv (sepConj_mono_left hloc_close)) ?_
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 1200000 in
/-- `FdsGe3Closed`-threaded twin of `M3PlacedBudget.main_m3_readOf_pool_placed_proof`:
    steps `M+0x568 → M+0x5dc` on Block `617`, delivering `FdsGe3Closed s'.fs` alongside
    `AtM4Placed` to `hnext`. -/
theorem main_m3_readOf_pool_placed_proof_fd [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {ArgvFrame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlacedFd A lim H io hookStack StdinEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i)) (hs0tr : s0.trace = [])
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim ms (M3EnvReadOf StdinEnv ReadEnv i c))
    (hs : AtCallPlaced CodeOk s0 s w i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      M3EnvReadOf StdinEnv ReadEnv i c evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
      FdsGe3Closed s'.fs →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvFrame ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs ms) s' ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom := by
  let _ := hs0tr
  let _ := hparse
  have hw5_orr : (s.readReg64 (.gpr 28#5) ||| s.readReg64 (.gpr 21#5)) = w.w5 := by
    have hz := zext32_eq_self_of_lt hs.x21lo
    simpa only [hz] using hs.w5
  cases c with
  | keygen me k =>
    have hfit0 : FitsEnv M lim ms (ReadCoinsEnvOf ReadEnv i) := by
      simpa only [M3EnvReadOf, ReadCoinsEnvOf, CallV.tag, show ¬ ((1 : Nat) < 0) by decide,
        ↓reduceIte] using hfit
    have hch_pure :
        callHeap A.repAlloc w (.keygen me k) =
          (⌜w.w0 = 0x8000000000000000#64⌝ ∗ callHeap A.repAlloc w (.keygen me k)) := by
      dsimp only [callHeap]
      apply ProofLib.sepProp_ext
      · exact entails_pure_elim_left fun hp =>
          entails_pure_intro_left hp.1 (entails_pure_intro_left hp (Entails.refl _))
      · exact entails_pure_elim_left fun _ => Entails.refl _
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_eq => ?_
    have hcond : ConditionHolds .MI (subsPState64 0x8000000000000000#64 0#64) = true := by
      rw [conditionHolds_mi_subsPState64]; rfl
    have hult : (1#64).ult 0#64 = false := rfl
    have hpc := hs.base.pc; have hrun := hs.base.run; have hinv := hs.base.inv
    have hx25 := hs.w0
    rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1404#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0x57c := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, hrun]
      sp := by (try simp only [arm64_norm]); exact hs.base.sp
      fp := by (try simp only [arm64_norm]); exact hs.base.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hs.base.vregs
      spAligned := hs.base.spAligned
    }
    refine SepWPp.weaken_pre ?_
      (step_empty_in_0x57c_pool_placed_fd (ArgvFrame := ArgvFrame)
        hc hio hstk hstk64 hs0fs hcoinsOk hcoins hfit0
        (by simp [CallV.tag]) hs.trace hin1
        (by (try simp only [arm64_norm]); try rfl)
        (by (try simp only [arm64_norm, hs.fs]); try rfl)
        (by (try simp only [arm64_norm, hs.x19]); try rfl)
        (by simp only [arm64_norm, CallV.tag, *])
        (by (try simp only [arm64_norm, hs.w2]); try rfl)
        (by (try simp only [arm64_norm, hs.x24]); try rfl)
        (by (try simp only [arm64_norm, hs.w0]); try rfl)
        (by (try simp only [arm64_norm, hs.w6]); try rfl)
        (by (try simp only [arm64_norm, hw5_orr]); try rfl)
        hexit
        (fun s' cc cp ic ip evs hevs hin_le ha hfds' =>
          hnext s' cc cp ic ip evs
            (by simpa only [M3EnvReadOf, ReadCoinsEnvOf, CallV.tag,
                  show ¬ ((1 : Nat) < 0) by decide, ↓reduceIte] using hevs)
            hin_le ha hfds'))
    conv => arg 2; rw [pool_congr_vm A lim ms s
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
    exact Entails.refl _
  | init peer bundle =>
    have hfit1 : FitsEnv M lim ms (ReadCoinsEnvOf ReadEnv i) := by
      simpa only [M3EnvReadOf, ReadCoinsEnvOf, CallV.tag, show ¬ ((1 : Nat) < 1) by decide,
        ↓reduceIte] using hfit
    have hch_pure :
        callHeap A.repAlloc w (.init peer bundle) =
          (⌜w.w0.toNat < 2 ^ 63⌝ ∗ callHeap A.repAlloc w (.init peer bundle)) := by
      dsimp only [callHeap, addrWords, ownedBytes]
      apply ProofLib.sepProp_ext
      · rw [sepConj_assoc, sepConj_assoc]
        exact entails_pure_elim_left fun hp =>
          entails_pure_intro_left hp.2.2.1 (entails_pure_intro_left hp (Entails.refl _))
      · exact entails_pure_elim_left fun _ => Entails.refl _
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_lt => ?_
    have hmsb := msb_false_of_lt hw0_lt
    have hcond : ConditionHolds .MI (subsPState64 w.w0 0#64) = false := by
      rw [conditionHolds_mi_subsPState64, BitVec.sub_zero]
      exact hmsb
    have hult : (1#64).ult 1#64 = false := rfl
    have hpc := hs.base.pc; have hrun := hs.base.run; have hinv := hs.base.inv
    have hx25 := hs.w0
    rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1404#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0x57c := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, hrun]
      sp := by (try simp only [arm64_norm]); exact hs.base.sp
      fp := by (try simp only [arm64_norm]); exact hs.base.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hs.base.vregs
      spAligned := hs.base.spAligned
    }
    refine SepWPp.weaken_pre ?_
      (step_empty_in_0x57c_pool_placed_fd (ArgvFrame := ArgvFrame)
        hc hio hstk hstk64 hs0fs hcoinsOk hcoins hfit1
        (by simp [CallV.tag]) hs.trace hin1
        (by (try simp only [arm64_norm]); try rfl)
        (by (try simp only [arm64_norm, hs.fs]); try rfl)
        (by (try simp only [arm64_norm, hs.x19]); try rfl)
        (by simp only [arm64_norm, CallV.tag, *])
        (by (try simp only [arm64_norm, hs.w2]); try rfl)
        (by (try simp only [arm64_norm, hs.x24]); try rfl)
        (by (try simp only [arm64_norm, hs.w0]); try rfl)
        (by (try simp only [arm64_norm, hs.w6]); try rfl)
        (by (try simp only [arm64_norm, hw5_orr]); try rfl)
        hexit
        (fun s' cc cp ic ip evs hevs hin_le ha hfds' =>
          hnext s' cc cp ic ip evs
            (by simpa only [M3EnvReadOf, ReadCoinsEnvOf, CallV.tag,
                  show ¬ ((1 : Nat) < 1) by decide, ↓reduceIte] using hevs)
            hin_le ha hfds'))
    conv => arg 2; rw [pool_congr_vm A lim ms s
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
    exact Entails.refl _
  | send peer =>
    have hfit2 : FitsEnv M lim ms (M3StdinEnvReadOf StdinEnv ReadEnv i) := by
      simpa only [M3EnvReadOf, M3StdinEnvReadOf, ReadCoinsEnvOf, CallV.tag,
        show (1 : Nat) < 2 by decide, ↓reduceIte] using hfit
    have hch_pure :
        callHeap A.repAlloc w (.send peer) =
          (⌜w.w0 = 0x8000000000000002#64⌝ ∗ callHeap A.repAlloc w (.send peer)) := by
      dsimp only [callHeap]
      apply ProofLib.sepProp_ext
      · exact entails_pure_elim_left fun hp =>
          entails_pure_intro_left hp (entails_pure_intro_left hp (Entails.refl _))
      · exact entails_pure_elim_left fun _ => Entails.refl _
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_eq => ?_
    have hcond : ConditionHolds .MI (subsPState64 0x8000000000000002#64 0#64) = true := by
      rw [conditionHolds_mi_subsPState64]; rfl
    have hult : (1#64).ult 2#64 = true := rfl
    have hpc := hs.base.pc; have hrun := hs.base.run; have hinv := hs.base.inv
    have hx25 := hs.w0
    rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1436#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0x59c := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, hrun]
      sp := by (try simp only [arm64_norm]); exact hs.base.sp
      fp := by (try simp only [arm64_norm]); exact hs.base.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hs.base.vregs
      spAligned := hs.base.spAligned
    }
    refine SepWPp.weaken_pre ?_
      (step_stdin_0x59c_readOf_pool_placed_fd (ArgvFrame := ArgvFrame)
        hc hio hstk hstk64 hs0fs hstdin hcoinsOk hcoins hfit2
        (by simp [CallV.tag]) hs.trace hin1
        (by (try simp only [arm64_norm]); try rfl)
        (by (try simp only [arm64_norm, hs.fs]); try rfl)
        (by (try simp only [arm64_norm, hs.x19]); try rfl)
        (by simp only [arm64_norm, CallV.tag, *])
        (by (try simp only [arm64_norm, hs.w2]); try rfl)
        (by (try simp only [arm64_norm, hs.x24]); try rfl)
        (by (try simp only [arm64_norm, hs.w0]); try rfl)
        (by (try simp only [arm64_norm, hs.w6]); try rfl)
        (by (try simp only [arm64_norm, hw5_orr]); try rfl)
        hexit
        (fun s' cc cp ic ip evs hevs hin_le ha hfds' =>
          hnext s' cc cp ic ip evs
            (by simpa only [M3EnvReadOf, M3StdinEnvReadOf, ReadCoinsEnvOf, CallV.tag,
                  show (1 : Nat) < 2 by decide, ↓reduceIte] using hevs)
            hin_le ha hfds'))
    conv => arg 2; rw [pool_congr_vm A lim ms s
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
    exact Entails.refl _
  | recv peer =>
    have hfit3 : FitsEnv M lim ms (M3StdinEnvReadOf StdinEnv ReadEnv i) := by
      simpa only [M3EnvReadOf, M3StdinEnvReadOf, ReadCoinsEnvOf, CallV.tag,
        show (1 : Nat) < 3 by decide, ↓reduceIte] using hfit
    have hch_pure :
        callHeap A.repAlloc w (.recv peer) =
          (⌜w.w0 = 0x8000000000000003#64⌝ ∗ callHeap A.repAlloc w (.recv peer)) := by
      dsimp only [callHeap]
      apply ProofLib.sepProp_ext
      · exact entails_pure_elim_left fun hp =>
          entails_pure_intro_left hp (entails_pure_intro_left hp (Entails.refl _))
      · exact entails_pure_elim_left fun _ => Entails.refl _
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_eq => ?_
    have hcond : ConditionHolds .MI (subsPState64 0x8000000000000003#64 0#64) = true := by
      rw [conditionHolds_mi_subsPState64]; rfl
    have hult : (1#64).ult 3#64 = true := rfl
    have hpc := hs.base.pc; have hrun := hs.base.run; have hinv := hs.base.inv
    have hx25 := hs.w0
    rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1436#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0x59c := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, hrun]
      sp := by (try simp only [arm64_norm]); exact hs.base.sp
      fp := by (try simp only [arm64_norm]); exact hs.base.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hs.base.vregs
      spAligned := hs.base.spAligned
    }
    refine SepWPp.weaken_pre ?_
      (step_stdin_0x59c_readOf_pool_placed_fd (ArgvFrame := ArgvFrame)
        hc hio hstk hstk64 hs0fs hstdin hcoinsOk hcoins hfit3
        (by simp [CallV.tag]) hs.trace hin1
        (by (try simp only [arm64_norm]); try rfl)
        (by (try simp only [arm64_norm, hs.fs]); try rfl)
        (by (try simp only [arm64_norm, hs.x19]); try rfl)
        (by simp only [arm64_norm, CallV.tag, *])
        (by (try simp only [arm64_norm, hs.w2]); try rfl)
        (by (try simp only [arm64_norm, hs.x24]); try rfl)
        (by (try simp only [arm64_norm, hs.w0]); try rfl)
        (by (try simp only [arm64_norm, hs.w6]); try rfl)
        (by (try simp only [arm64_norm, hw5_orr]); try rfl)
        hexit
        (fun s' cc cp ic ip evs hevs hin_le ha hfds' =>
          hnext s' cc cp ic ip evs
            (by simpa only [M3EnvReadOf, M3StdinEnvReadOf, ReadCoinsEnvOf, CallV.tag,
                  show (1 : Nat) < 3 by decide, ↓reduceIte] using hevs)
            hin_le ha hfds'))
    conv => arg 2; rw [pool_congr_vm A lim ms s
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
    exact Entails.refl _

theorem main_m3_bounded_readOf_pool_placed_proof_fd [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {ArgvFrame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlacedFd A lim H io hookStack ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i)) (hs0tr : s0.trace = [])
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim ms (M3EnvReadOf ReadStdinBoundedEnv ReadEnv i c))
    (hs : AtCallPlaced CodeOk s0 s w i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      M3EnvReadOf ReadStdinBoundedEnv ReadEnv i c evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
      FdsGe3Closed s'.fs →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvFrame ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs ms) s' ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom :=
  main_m3_readOf_pool_placed_proof_fd hc hio hstk hstk64 hs0fs hs0tr hstdin hcoinsOk hcoins hparse
    hfit hs hexit hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd
