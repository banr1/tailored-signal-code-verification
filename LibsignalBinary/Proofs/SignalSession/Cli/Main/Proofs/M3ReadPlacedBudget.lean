/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.IoSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ErrPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5Iface
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `read_stdin` and `read_file("coins")` Continuations for `main` Hop M3

Budget-threaded verification of `M+0x59c` (`read_stdin`) and `M+0x5b0 .. M+0x5d8`
(`read_file("coins")` and error-branch dispatch) on Block `617` under `RustCliAllocBudget M`,
threading `A.pool` and `ReadCoinsEnv` / `M3StdinEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession
  (Inputs lsReadFileSym lsReadStdinSym readStdinResult stdinCapBytes)
open CryptoVerification.SignalSession.Cli (CoinsReadable cliInputs cliStaticsPlaced ioVecAt utf8)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkLib_eq_617 blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtM4Placed CallV CallW InMainPlaced IoModel LsCodeInv ReadFileLitGhost ReadStdinGhost argsBuf
   callCellsPlaced callHeap cell coinsLitSym coinsOf inputOf locals localsBound localsCtx
   localsEnd localsFrom locals_carve_cell locals_carve_region locals_focus m4CellsPlaced
   mPcPlaced_eq mProgPlaced mProgPlaced_eq mainFrameSize mainLitsBlk617 mainSaved main_call_rocl
   ownedBytes sepWPp_of_mainOom sepWPp_seq_codeOk)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
  (beq_add_one_zero_false_of_lt entails_pure_elim_left entails_pure_intro_left inInv inInvOpt
   mainLitsBlk617Rest mainLitsBlk617_eq memRegion_16_cells optOwnedBytes optOwnedBytes_false
   ownedBytes_entails_optOwned ownedBytes_pure stackAt_sub_split vecU8_to_ownedBytes)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudget

open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget (ReadStdinEnv allocBytes1Events)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (MainIoPlaced ReadFileRuleEnv readFileLitSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoBoundedPlaced MainIoOfPlaced ReadStdinBoundedEnv mainIoBoundedPlaced_iff_mainIoPlaced
   main_readFile_of_placed_ok main_readStdin_bounded_placed_ok main_readStdin_of_placed_ok
   readStdinBoundedEnv_of_hook_gt readStdinBoundedEnv_of_hook_le readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (ExitKPlaced MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ErrPlacedBudget
  (step_err_0x624_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced exitKPoolPlaced_of_exitKPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private def kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hi' : i < xs.length := hi
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi']
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8_eq_kutf8 (s : String) : utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

private theorem utf8_coins_length : (utf8 "coins").length = 5 := by
  rw [utf8_eq_kutf8]; decide

private theorem pool_congr_vm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ms : M.σ) (s : State) {s' : State}
    (hbs : s'.brkStart = s.brkStart) (hbrk : s'.brk = s.brk)
    (htp : s'.tpidrEl0 = s.tpidrEl0) (hphys : s'.physMemAvail = s.physMemAvail)
    (hperm : ∀ a : BitVec 64, s'.mem.perm a = s.mem.perm a)
    (hfs : s'.fs = s.fs := by first | rfl | simp +zetaDelta only [wp_norm, arm64_norm]) :
    A.pool lim ms s' = A.pool lim ms s :=
  A.pool_of_vmPreserved ⟨⟨hbs, hbrk, htp⟩, hphys, hperm, LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩

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

/-- Hook-path `AllocEvent` list emitted by `read_file("coins")` under `io.rd`:
`allocBytes1Events bs` on `.ok bs`, and `[]` on `.error ()`. -/
def readCoinsEvents (io : IoModel) (i : Inputs) : List AllocEvent :=
  match io.rd (initFsState (cliInputs i)).files (utf8 "coins") with
  | .ok bs => allocBytes1Events bs
  | .error () => []

/-- `ReadEnv`-parameterized `AllocEvent` envelope of `step_from_0x5b0_readOf_pool_placed`
(`read_file("coins")`). -/
def ReadCoinsEnvOf (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (i : Inputs) : List AllocEvent → Prop :=
  ReadEnv (initFsState (cliInputs i)).files (utf8 "coins")

/-- `AllocEvent` envelope of `step_from_0x5b0_pool_placed` (`read_file("coins")`), matching both
`CliRun` hooks and compiled `signal_session_io::read_file`. -/
def ReadCoinsEnv (io : IoModel) (i : Inputs) : List AllocEvent → Prop :=
  ReadFileRuleEnv io.rd (initFsState (cliInputs i)).files (utf8 "coins")

/-- `(StdinEnv, ReadEnv)`-parameterized `AllocEvent` envelope of
`step_stdin_0x59c_readOf_pool_placed` (`read_stdin` followed by `read_file("coins")`). -/
def M3StdinEnvReadOf (StdinEnv : List (BitVec 8) → List AllocEvent → Prop)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (i : Inputs) : List AllocEvent → Prop :=
  SeqEnv (StdinEnv i.stdin) (ReadCoinsEnvOf ReadEnv i)

/-- `StdinEnv`-parameterized `AllocEvent` envelope of `step_stdin_0x59c_of_pool_placed`
(`read_stdin` followed by `read_file("coins")`). -/
def M3StdinEnvOf (StdinEnv : List (BitVec 8) → List AllocEvent → Prop)
    (io : IoModel) (i : Inputs) : List AllocEvent → Prop :=
  SeqEnv (StdinEnv i.stdin) (ReadCoinsEnv io i)

/-- Bounded-stdin `AllocEvent` envelope (`StdinEnv := ReadStdinBoundedEnv`). -/
abbrev M3StdinBoundedEnv (io : IoModel) (i : Inputs) : List AllocEvent → Prop :=
  M3StdinEnvOf ReadStdinBoundedEnv io i

/-- Hook-path `AllocEvent` list emitted by `step_stdin_0x59c_pool_placed` (`read_stdin` followed by
`read_file("coins")`). -/
def m3StdinEvents (io : IoModel) (i : Inputs) : List AllocEvent :=
  allocBytes1Events i.stdin ++ readCoinsEvents io i

/-- Bounded-hook `AllocEvent` list emitted by `step_stdin_0x59c_bounded_pool_placed` (`[]` on
`i.stdin.length > 1048576`). -/
def m3StdinBoundedEvents (io : IoModel) (i : Inputs) : List AllocEvent :=
  (if i.stdin.length ≤ 1048576 then allocBytes1Events i.stdin else []) ++ readCoinsEvents io i

/-- `AllocEvent` envelope of `step_stdin_0x59c_pool_placed` (`read_stdin` followed by
`read_file("coins")`), matching both `CliRun` hooks and compiled `signal_session_io`. -/
abbrev M3StdinEnv (io : IoModel) (i : Inputs) : List AllocEvent → Prop :=
  M3StdinEnvOf ReadStdinEnv io i

theorem readCoinsEvents_mem_env (io : IoModel) (i : Inputs) :
    ReadCoinsEnv io i (readCoinsEvents io i) := by
  dsimp only [ReadCoinsEnv, ReadFileRuleEnv, readCoinsEvents]
  cases io.rd (initFsState (cliInputs i)).files (utf8 "coins") with
  | ok bs => exact Or.inl rfl
  | error u => cases u; rfl

theorem m3StdinBoundedEvents_mem_env (io : IoModel) (i : Inputs) :
    M3StdinBoundedEnv io i (m3StdinBoundedEvents io i) := by
  refine SeqEnv.append (E₁ := ReadStdinBoundedEnv i.stdin) (E₂ := ReadCoinsEnv io i) ?_
    (readCoinsEvents_mem_env io i)
  by_cases hle : i.stdin.length ≤ 1048576
  · simp only [hle, ↓reduceIte]
    exact readStdinBoundedEnv_of_hook_le hle rfl
  · simp only [hle, ↓reduceIte]
    exact readStdinBoundedEnv_of_hook_gt hle rfl

theorem m3StdinEvents_mem_env (io : IoModel) (i : Inputs) :
    M3StdinEnv io i (m3StdinEvents io i) :=
  SeqEnv.append (E₁ := ReadStdinEnv i.stdin) (E₂ := ReadCoinsEnv io i)
    (Or.inl rfl) (readCoinsEvents_mem_env io i)

set_option maxHeartbeats 1200000 in
/-- `(StdinEnv, ReadEnv)`-parameterized budget-threaded continuation across `read_file("coins")`
(`M+0x5b0 .. M+0x5d8`) and both error tests on Block `617`, generic in `{ArgvFrame : SepProp}` and
retaining `A.pool` at exit via `ExitKPoolPlaced`. -/
theorem step_from_0x5b0_readOf_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {stk hookStack resStack : Nat}
    {buf inCap inPtr x27 : BitVec 64} {inOk : Bool}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (ReadCoinsEnvOf ReadEnv i))
    (hs_tr : s.trace = s0.trace)
    (hst : InMainPlaced CodeOk s0 st 0x5b0)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx23 : st.readReg64 (.gpr 23#5) = inCap)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx26 : st.readReg64 (.gpr 26#5) = w.w6)
    (hx27 : st.readReg64 (.gpr 27#5) = x27)
    (hw5_orr : (st.readReg64 (.gpr 28#5) ||| st.readReg64 (.gpr 21#5)) = w.w5)
    (hfiles : st.fs.files = (initFsState (cliInputs i)).files)
    (hst_tr : st.trace = s.trace)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      ReadCoinsEnvOf ReadEnv i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
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
      (inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom := by
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hread := main_readFile_of_placed_ok hio
  have hsub_le : hookStack ≤ stk - mainFrameSize := by omega
  have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  have hcarve_open :=
    (locals_carve_region fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
      0x1b8 24 []).trans
    (locals_focus fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
      0x1b8 24 (memRegion (fsp + 0x1b8#64) 24) [])
  rw [List.append_nil] at hcarve_open
  rw [hcarve_open, mainLitsBlk617_eq]
  have hal : st.spAligned = true := hst.spAligned_state
  have hsp : st.sp = fsp := hst.sp
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsReadFileSym) hinv
  wp_steps
  apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
    (by (try simp only [arm64_norm, *]); try rfl)
  intro hinv1
  refine main_call_rocl (CodeOk := CodeOk)
    (spec := readFileLitSpecPlaced io A lim hookStack ReadEnv)
    (({ pathA := lsρ coinsLitSym, path := utf8 "coins", ret := fsp + 0x1b8#64 } : ReadFileLitGhost), ms)
    hread
    hinv1 (by (try simp only [arm64_norm, *]); try rfl) (by (try simp only [arm64_norm, *]); try rfl)
    (by simp only [arm64_norm]; exact hal)
    (ret_pc := (blkPl_617).base + 0x5c8#64) (by (try simp only [arm64_norm, *]); try rfl)
    (F := inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗ callHeap A.repAlloc w c ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
      ArgvFrame ∗
      mainSaved s0 ∗
      localsCtx fsp 0
        [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
        0x1b8 24 [] ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - hookStack) ∗
      cliStaticsPlaced ∗ mainLitsBlk617Rest)
    ?_ (hnext := ?_)
  · dsimp only [readFileLitSpecPlaced]
    conv => arg 2; rw [pool_congr_vm A lim ms st (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm])]
    simp only [arm64_norm, hsp, hfiles]
    rw [stackAt_sub_split fsp hsub_le hsub64]
    apply entails_pure_intro_left ⟨utf8_coins_length.symm, by rw [utf8_coins_length]; decide, hcoinsOk, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [readFileLitSpecPlaced]
    have hx19_f : sf.readReg64 (.gpr 19#5) = buf := by rw [hcs_f.1]; simp only [arm64_norm, hx19]
    have hx20_f : sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag := by
      rw [hcs_f.2.1]; simp only [arm64_norm, hx20]
    have hx21_f : sf.readReg64 (.gpr 21#5) = w.w5 := by
      rw [hcs_f.2.2.1]; simp only [arm64_norm]
    have hx22_f : sf.readReg64 (.gpr 22#5) = w.w2 := by
      rw [hcs_f.2.2.2.1]; simp only [arm64_norm, hx22]
    have hx23_f : sf.readReg64 (.gpr 23#5) = inCap := by
      rw [hcs_f.2.2.2.2.1]; simp only [arm64_norm, hx23]
    have hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length := by
      rw [hcs_f.2.2.2.2.2.1]; simp only [arm64_norm, hx24]
    have hx25_f : sf.readReg64 (.gpr 25#5) = w.w0 := by
      rw [hcs_f.2.2.2.2.2.2.1]; simp only [arm64_norm, hx25]
    have hx26_f : sf.readReg64 (.gpr 26#5) = w.w6 := by
      rw [hcs_f.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hx26]
    have hx27_f : sf.readReg64 (.gpr 27#5) = x27 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hx27]
    have hsp_sf : sf.sp = fsp := by rw [hsp_f]; simp only [arm64_norm, hsp]
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf, fsp, mainFrameSize]
      exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hst.spAligned
    have hfp_sf : sf.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hst.fp]
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.2.2]; simp only [calleeSavedVRegs, arm64_norm, hst.vregs]
    have hsp_pre : (_ : State).sp = fsp := hsp_f.symm.trans hsp_sf
    rw [hsp_pre]
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hevs => ?_
    have hevs' : ReadCoinsEnvOf ReadEnv i evs := by
      simpa only [ReadCoinsEnvOf, arm64_norm, hfiles] using hevs
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    refine SepWPp.exists_elim fun rCoins => ?_
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hfiles_f, hrd_rf, htr_sf⟩ => ?_
    have hfiles_sf : sf.fs.files = (initFsState (cliInputs i)).files :=
      hfiles_f.trans (by simp only [arm64_norm, hfiles])
    have hrd_rf' : rCoins = io.rd (initFsState (cliInputs i)).files (utf8 "coins") := by
      simpa only [arm64_norm, hfiles] using hrd_rf
    cases rCoins with
    | ok cBs =>
      have hc_eq : cBs = coinsOf i := by
        rcases hcoins _ hrd_rf'.symm with hok_c | ⟨herr_c, -⟩
        · exact Except.ok.inj hok_c
        · cases herr_c
      subst hc_eq
      dsimp only [ioVecAt]
      refine SepWPp.weaken_pre
        (sepConj_mono_left (vecU8_to_ownedBytes A.repAlloc (fsp + 0x1b8#64) (coinsOf i))) ?_
      rw [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun coinsCap => ?_
      rw [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun coinsPtr => ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          (((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
            inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗
            (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ stackAt fsp hookStack ∗
            A.pool lim (M.stepEvents evs ms) sf ∗
            (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
              ArgvFrame ∗
              mainSaved s0 ∗
              localsCtx fsp 0
                [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                0x1b8 24 [] ∗
              memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
                (stk - mainFrameSize - hookStack) ∗
              cliStaticsPlaced ∗ mainLitsBlk617Rest)) by sep_ac_rfl)) ?_
      rw [ownedBytes_pure A.repAlloc coinsCap coinsPtr
            (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i),
          sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_, _, hcoins_lt, _⟩ => ?_
      have hcoins_nzero := beq_add_one_zero_false_of_lt hcoins_lt
      cases inOk with
      | true =>
        dsimp only [inInvOpt, inInv]
        refine SepWPp.weaken_pre (Entails.of_eq (show _ =
          ⌜(inputOf i c).length ≤ stdinCapBytes⌝ ∗
            (⌜x27 = BitVec.ofNat 64 (inputOf i c).length⌝ ∗
              (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
                ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
                ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
                ownedBytes A.repAlloc coinsCap coinsPtr
                  (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
                (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ stackAt fsp hookStack ∗
                A.pool lim (M.stepEvents evs ms) sf ∗
                (callHeap A.repAlloc w c ∗
                  argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
                  ArgvFrame ∗
                  mainSaved s0 ∗
                  localsCtx fsp 0
                    [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                    0x1b8 24 [] ∗
                  memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
                    (stk - mainFrameSize - hookStack) ∗
                  cliStaticsPlaced ∗ mainLitsBlk617Rest))) by sep_ac_rfl)) ?_
        refine SepWPp.pure_elim fun hin_cap_le => ?_
        refine SepWPp.pure_elim fun hx27_len => ?_
        rw [ownedBytes_pure A.repAlloc inCap inPtr
              (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c),
            sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨_, _, hin_lt, _⟩ => ?_
        have hin_nzero := beq_add_one_zero_false_of_lt hin_lt
        apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x5dc#64) hinv_f
        wp_steps
        apply SepWP.done
          (by (try simp only [arm64_norm, *]); try rfl)
          (by (try simp only [arm64_norm, *]); try rfl)
        intro hinv_5dc
        have hin_5dc : InMainPlaced CodeOk s0 _ 0x5dc := {
          inv := hinv_5dc
          pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
          run := by simp only [arm64_norm, *]
          sp := by (try simp only [arm64_norm]); exact hsp_sf
          fp := by (try simp only [arm64_norm]); exact hfp_sf
          vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hvregs_sf
          spAligned := hst.spAligned
        }
        have hatM4 : AtM4Placed CodeOk i s0 _ w c i.argv.length buf coinsCap coinsPtr inCap := {
          base := hin_5dc
          x0 := by simp only [arm64_norm]
          x1 := by simp only [arm64_norm]
          x19 := by simp only [arm64_norm, hx19_f]
          x20 := by simp only [arm64_norm, hx20_f]
          x23 := by simp only [arm64_norm, hx23_f]
          x24 := by simp only [arm64_norm, hx24_f]
          x27 := by simp only [arm64_norm, hx27_f, hx27_len]
          w0 := by simp only [arm64_norm, hx25_f]
          w2 := by simp only [arm64_norm, hx22_f]
          w5 := by simp only [arm64_norm, hx21_f]
          w6 := by simp only [arm64_norm, hx26_f]
          fs := by simp only [arm64_norm, hfiles_sf]
          trace := by
            simp only [arm64_norm]
            exact htr_sf.trans ((by simp only [arm64_norm] : _ = st.trace).trans (hst_tr.trans hs_tr))
        }
        refine SepWPp.weaken_pre ?_
          (hnext _ coinsCap coinsPtr inCap inPtr evs hevs' hin_cap_le hatM4)
        conv => arg 2; rw [pool_congr_vm A lim (M.stepEvents evs ms) sf
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
        have hm4_merge :
            ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
              ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
              localsCtx fsp 0
                [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                0x1b8 24 [] ⊢
              locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) := by
          have h24 :
              ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ⊢
                memRegion (fsp + 0x1b8#64) 16 := by
            rw [memRegion_split (fsp + 0x1b8#64) 8 8 (by decide),
              show (fsp + 0x1b8#64) + 8#64 = fsp + 0x1c0#64 by rw [BitVec.add_assoc]; rfl]
            exact sepConj_mono
              (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
          have hctx_eq :
              memRegion (fsp + 0x1b8#64) 16 ∗
                ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
                localsCtx fsp 0
                  [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                  0x1b8 24 [] =
                locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) := by
            simp only [locals, localsFrom, localsCtx, Nat.reduceAdd, Nat.reduceSub]
            rw [ProofLib.memRegion_split' (b := fsp + 0x60#64) (b' := fsp + 0x1b8#64)
              (N := 0x168) (n := 0x158) (k := 16) (by decide) (by rw [BitVec.add_assoc]; rfl)
              (by decide)]
            sep_ac_rfl
          rw [← hctx_eq, ← sepConj_assoc]
          exact sepConj_mono_left h24
        rw [stackAt_sub_split fsp hsub_le hsub64, mainLitsBlk617_eq]
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
            localsCtx fsp 0
              [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
              0x1b8 24 []) ∗
          (ownedBytes A.repAlloc coinsCap coinsPtr
              (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
            ownedBytes A.repAlloc inCap inPtr
              (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            ArgvFrame ∗
            mainSaved s0 ∗
            (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - hookStack) ∗ stackAt fsp hookStack) ∗
            A.pool lim (M.stepEvents evs ms) sf ∗ cliStaticsPlaced ∗
            ((lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ mainLitsBlk617Rest)) by sep_ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left hm4_merge) ?_
        exact Entails.of_eq (by sep_ac_rfl)
      | false =>
        dsimp only [inInvOpt]
        refine SepWPp.weaken_pre (Entails.of_eq (show _ =
          ⌜inCap = 0xffffffffffffffff#64 ∧ 1 < c.tag ∧ stdinCapBytes < i.stdin.length⌝ ∗
            (((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
              ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
              ownedBytes A.repAlloc coinsCap coinsPtr
                (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
              (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ stackAt fsp hookStack ∗
              A.pool lim (M.stepEvents evs ms) sf ∗
              (callHeap A.repAlloc w c ∗
                argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
                ArgvFrame ∗
                mainSaved s0 ∗
                localsCtx fsp 0
                  [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                  0x1b8 24 [] ∗
                memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
                  (stk - mainFrameSize - hookStack) ∗
                cliStaticsPlaced ∗ mainLitsBlk617Rest)) by sep_ac_rfl)) ?_
        refine SepWPp.pure_elim fun ⟨hin_neg1, htag_gt1, hstdin_gt⟩ => ?_
        subst hin_neg1
        apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x624#64) hinv_f
        wp_steps
        apply SepWP.done
          (by (try simp only [arm64_norm, *]); try rfl)
          (by (try simp only [arm64_norm, *]); try rfl)
        intro hinv_624
        have hin_624 : InMainPlaced CodeOk s0 _ 0x624 := {
          inv := hinv_624
          pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
          run := by simp only [arm64_norm, *]
          sp := by (try simp only [arm64_norm]); exact hsp_sf
          fp := by (try simp only [arm64_norm]); exact hfp_sf
          vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hvregs_sf
          spAligned := hst.spAligned
        }
        have htr_sf_eq : sf.trace = s.trace :=
          htr_sf.trans (by simp only [arm64_norm, hst_tr])
        refine SepWPp.weaken_pre ?_
          (sepWPp_of_mainOom (step_err_0x624_pool_placed
            (ms := M.stepEvents evs ms)
            (P := ¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length))
            (i := i) (s := s) (n := i.argv.length) (buf := buf)
            (coinsOk := true) (inOk := false)
            (coinsCap := coinsCap) (coinsPtr := coinsPtr)
            (inCap := 0xffffffffffffffff#64) (inPtr := inPtr)
            (c := c) (w := w) (ps := ps) hc hstk hstk64 hin_624
            (by (try simp only [arm64_norm]); try rfl) (by (try simp only [arm64_norm]); try rfl)
            (by (try simp only [arm64_norm, hx19_f]); try rfl)
            (by (try simp only [arm64_norm, hx20_f]); try rfl)
            (by (try simp only [arm64_norm, hx21_f]); try rfl)
            (by (try simp only [arm64_norm, hx22_f]); try rfl)
            (by (try simp only [arm64_norm, hx23_f]); try rfl)
            (by (try simp only [arm64_norm, hx24_f]); try rfl)
            (by (try simp only [arm64_norm, hx25_f]); try rfl)
            (by exact ⟨by simpa only [arm64_norm] using hfiles_sf, Or.inr ⟨htag_gt1, hstdin_gt⟩,
              by simpa only [arm64_norm] using htr_sf_eq⟩)
            hexit))
        conv => arg 2; rw [pool_congr_vm A lim (M.stepEvents evs ms) sf
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
        have hloc_back :
            ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
              ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
              localsCtx fsp 0
                [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                0x1b8 24 [] ⊢
              locals fsp
                [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] := by
          have h24 :
              ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
                ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ⊢
                memRegion (fsp + 0x1b8#64) 24 := by
            rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
              memRegion_split (fsp + 0x1b8#64) 8 (8 + 8) (by decide),
              memRegion_split ((fsp + 0x1b8#64) + 8#64) 8 8 (by decide)]
            simp only [BitVec.add_assoc, BitVec.reduceAdd]
            exact sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
          rw [hcarve_open]
          rw [← sepConj_assoc, ← sepConj_assoc]
          exact sepConj_mono_left (by simpa only [sepConj_assoc] using h24)
        have hcoins_opt :
            ownedBytes A.repAlloc coinsCap coinsPtr
              (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ⊢
              optOwnedBytes A.repAlloc true coinsCap coinsPtr :=
          ownedBytes_entails_optOwned _ _ _ _ _
        have hin_opt : emp ⊢ optOwnedBytes A.repAlloc false 0xffffffffffffffff#64 inPtr := by
          rw [optOwnedBytes_false, ← sepConj_emp ⌜_⌝]
          exact entails_pure_intro_left rfl (Entails.refl emp)
        rw [stackAt_sub_split fsp hsub_le hsub64]
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
            localsCtx fsp 0
              [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
              0x1b8 24 []) ∗
          ownedBytes A.repAlloc coinsCap coinsPtr
            (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          emp ∗
          (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            mainSaved s0 ∗
            (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - hookStack) ∗ stackAt fsp hookStack) ∗
            A.pool lim (M.stepEvents evs ms) sf ∗
            ((lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗
              ArgvFrame ∗
              cliStaticsPlaced ∗ mainLitsBlk617Rest)) by simp only [emp_sepConj]; sep_ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hloc_back
          (sepConj_mono hcoins_opt (sepConj_mono hin_opt
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (ProofLib.entails_anyHeap _))))))))) ?_
        exact Entails.of_eq (by sep_ac_rfl)
    | error u =>
      cases u
      dsimp only [ioVecAt]
      refine SepWPp.weaken_pre
        (sepConj_mono_left (sepConj_mono_right (memRegion_16_cells (fsp + 0x1b8#64)))) ?_
      simp only [sepExists_sepConj_right, sepExists_sepConj_left]
      refine SepWPp.exists_elim fun errCoinsPtr => ?_
      refine SepWPp.exists_elim fun errCoinsLen => ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x624#64) hinv_f
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv_624
      have hin_624 : InMainPlaced CodeOk s0 _ 0x624 := {
        inv := hinv_624
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by simp only [arm64_norm, *]
        sp := by (try simp only [arm64_norm]); exact hsp_sf
        fp := by (try simp only [arm64_norm]); exact hfp_sf
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hvregs_sf
        spAligned := hst.spAligned
      }
      have htr_sf_eq : sf.trace = s.trace :=
        htr_sf.trans (by simp only [arm64_norm, hst_tr])
      have hnr_coins : ¬ CoinsReadable i := by
        rcases hcoins _ hrd_rf'.symm with hok_c | ⟨-, hnr⟩
        · cases hok_c
        · exact hnr
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_mainOom (step_err_0x624_pool_placed
          (ms := M.stepEvents evs ms)
          (P := ¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length))
          (i := i) (s := s) (n := i.argv.length) (buf := buf)
          (coinsOk := false) (inOk := inOk)
          (coinsCap := 0xffffffffffffffff#64) (coinsPtr := errCoinsPtr)
          (inCap := inCap) (inPtr := inPtr)
          (c := c) (w := w) (ps := ps) hc hstk hstk64 hin_624
          (by (try simp only [arm64_norm]); try rfl) (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hx19_f]); try rfl)
          (by (try simp only [arm64_norm, hx20_f]); try rfl)
          (by (try simp only [arm64_norm, hx21_f]); try rfl)
          (by (try simp only [arm64_norm, hx22_f]); try rfl)
          (by (try simp only [arm64_norm, hx23_f]); try rfl)
          (by (try simp only [arm64_norm, hx24_f]); try rfl)
          (by (try simp only [arm64_norm, hx25_f]); try rfl)
          (by exact ⟨by simpa only [arm64_norm] using hfiles_sf, Or.inl hnr_coins,
            by simpa only [arm64_norm] using htr_sf_eq⟩)
          hexit))
      conv => arg 2; rw [pool_congr_vm A lim (M.stepEvents evs ms) sf
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
      have hloc_back :
          ((fsp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((fsp + 0x1c0#64) ↦₆₄ errCoinsPtr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ errCoinsLen) ∗
            localsCtx fsp 0
              [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
              0x1b8 24 [] ⊢
            locals fsp
              [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] := by
        have h24 :
            ((fsp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((fsp + 0x1c0#64) ↦₆₄ errCoinsPtr) ∗
              ((fsp + 0x1c8#64) ↦₆₄ errCoinsLen) ⊢
              memRegion (fsp + 0x1b8#64) 24 := by
          rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
            memRegion_split (fsp + 0x1b8#64) 8 (8 + 8) (by decide),
            memRegion_split ((fsp + 0x1b8#64) + 8#64) 8 8 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
        rw [hcarve_open]
        rw [← sepConj_assoc, ← sepConj_assoc]
        exact sepConj_mono_left (by simpa only [sepConj_assoc] using h24)
      have hin_opt :
          inInvOpt inOk A.repAlloc i c inCap inPtr x27 ⊢
            optOwnedBytes A.repAlloc inOk inCap inPtr := by
        cases inOk with
        | false =>
          dsimp only [inInvOpt]
          rw [optOwnedBytes_false, ← sepConj_emp ⌜_ ∧ _⌝]
          exact entails_pure_elim_left fun h => by
            rw [← sepConj_emp ⌜_⌝]
            exact entails_pure_intro_left h.1 (Entails.refl emp)
        | true =>
          dsimp only [inInvOpt, inInv]
          exact entails_pure_elim_left fun _ =>
            entails_pure_elim_left fun _ => ownedBytes_entails_optOwned _ _ _ _ _
      have hcoins_opt : emp ⊢ optOwnedBytes A.repAlloc false 0xffffffffffffffff#64 errCoinsPtr := by
        rw [optOwnedBytes_false, ← sepConj_emp ⌜_⌝]
        exact entails_pure_intro_left rfl (Entails.refl emp)
      rw [stackAt_sub_split fsp hsub_le hsub64]
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((fsp + 0x1c0#64) ↦₆₄ errCoinsPtr) ∗
          ((fsp + 0x1c8#64) ↦₆₄ errCoinsLen) ∗
          localsCtx fsp 0
            [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
            0x1b8 24 []) ∗
        emp ∗
        inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - hookStack) ∗ stackAt fsp hookStack) ∗
          A.pool lim (M.stepEvents evs ms) sf ∗
          ((lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗
            ArgvFrame ∗
            cliStaticsPlaced ∗ mainLitsBlk617Rest)) by simp only [emp_sepConj]; sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hloc_back
        (sepConj_mono hcoins_opt (sepConj_mono hin_opt
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (ProofLib.entails_anyHeap _))))))))) ?_
      exact Entails.of_eq (by sep_ac_rfl)

/-- `StdinEnv`-parameterized budget-threaded continuation across `read_file("coins")`
(`M+0x5b0 .. M+0x5d8`) and both error tests on Block `617`, generic in `{ArgvFrame : SepProp}` and
retaining `A.pool` at exit via `ExitKPoolPlaced`. -/
theorem step_from_0x5b0_of_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {stk hookStack resStack : Nat}
    {buf inCap inPtr x27 : BitVec 64} {inOk : Bool}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoBoundedPlaced A lim H io hookStack StdinEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (ReadCoinsEnv io i))
    (hs_tr : s.trace = s0.trace)
    (hst : InMainPlaced CodeOk s0 st 0x5b0)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx23 : st.readReg64 (.gpr 23#5) = inCap)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx26 : st.readReg64 (.gpr 26#5) = w.w6)
    (hx27 : st.readReg64 (.gpr 27#5) = x27)
    (hw5_orr : (st.readReg64 (.gpr 28#5) ||| st.readReg64 (.gpr 21#5)) = w.w5)
    (hfiles : st.fs.files = (initFsState (cliInputs i)).files)
    (hst_tr : st.trace = s.trace)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      ReadCoinsEnv io i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
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
      (inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom :=
  step_from_0x5b0_readOf_pool_placed hc hio hstk hstk64 hcoinsOk hcoins hfit hs_tr hst
    hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27 hw5_orr hfiles hst_tr hexit hnext

theorem step_from_0x5b0_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {stk hookStack resStack : Nat}
    {buf inCap inPtr x27 : BitVec 64} {inOk : Bool}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (ReadCoinsEnv io i))
    (hs_tr : s.trace = s0.trace)
    (hst : InMainPlaced CodeOk s0 st 0x5b0)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx23 : st.readReg64 (.gpr 23#5) = inCap)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx26 : st.readReg64 (.gpr 26#5) = w.w6)
    (hx27 : st.readReg64 (.gpr 27#5) = x27)
    (hw5_orr : (st.readReg64 (.gpr 28#5) ||| st.readReg64 (.gpr 21#5)) = w.w5)
    (hfiles : st.fs.files = (initFsState (cliInputs i)).files)
    (hst_tr : st.trace = s.trace)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      ReadCoinsEnv io i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
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
      (inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom :=
  step_from_0x5b0_of_pool_placed hc
    ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio)
    hstk hstk64 hcoinsOk hcoins hfit hs_tr hst
    hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27 hw5_orr hfiles hst_tr hexit hnext

theorem step_from_0x5b0_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {stk hookStack resStack : Nat}
    {buf inCap inPtr x27 : BitVec 64} {inOk : Bool}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (ReadCoinsEnv io i))
    (hs_tr : s.trace = s0.trace)
    (hst : InMainPlaced CodeOk s0 st 0x5b0)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx23 : st.readReg64 (.gpr 23#5) = inCap)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx26 : st.readReg64 (.gpr 26#5) = w.w6)
    (hx27 : st.readReg64 (.gpr 27#5) = x27)
    (hw5_orr : (st.readReg64 (.gpr 28#5) ||| st.readReg64 (.gpr 21#5)) = w.w5)
    (hfiles : st.fs.files = (initFsState (cliInputs i)).files)
    (hst_tr : st.trace = s.trace)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      ReadCoinsEnv io i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
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
      (inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom :=
  step_from_0x5b0_pool_placed hc hio hstk hstk64 hcoinsOk hcoins hfit hs_tr hst
    hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27 hw5_orr hfiles hst_tr
    (exitKPoolPlaced_of_exitKPlaced (lim := lim) hexit) hnext

set_option maxHeartbeats 1200000 in
/-- `(StdinEnv, ReadEnv)`-parameterized budget-threaded continuation at `M+0x59c .. M+0x5ac`
(`read_stdin(&fsp+0x60)` when `1 < c.tag`, spilling `inPtr` to `[sp+0x50]`) →
`step_from_0x5b0_readOf_pool_placed`, generic in `{ArgvFrame : SepProp}` and retaining `A.pool` at
exit via `ExitKPoolPlaced`. -/
theorem step_stdin_0x59c_readOf_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
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
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
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
  have hstdin_ok := main_readStdin_of_placed_ok hio
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
      0x60 24 (memRegion (fsp + 0x60#64) 24) []]
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
    (spec := readStdinSpecOfPlaced io A lim hookStack StdinEnv)
    (({ ret := fsp + 0x60#64, bs := i.stdin } : ReadStdinGhost), ms)
    hstdin_ok
    hinv1 (by (try simp only [arm64_norm, *]); try rfl)
    (by (try simp only [arm64_norm, *]); try rfl)
    (by simp only [arm64_norm]; exact hal)
    (ret_pc := (blkPl_617).base + 0x5a4#64) (by (try simp only [arm64_norm, *]); try rfl)
    (F := callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
      ArgvFrame ∗
      mainSaved s0 ∗
      localsCtx fsp 0
        [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 old50, cell fsp 0x58 w.w1]
        0x60 24 [] ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - hookStack) ∗
      cliStaticsPlaced ∗ mainLitsBlk617)
    ?_ (hnext := ?_)
  · dsimp only [readStdinSpecOfPlaced]
    conv => arg 2; rw [pool_congr_vm A lim ms st (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm])]
    simp only [arm64_norm, hst_fs, hs0fs, hsp]
    rw [stackAt_sub_split fsp hsub_le hsub64]
    apply entails_pure_intro_left ⟨hstdin, hfit_stdin_env,
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 617 0x5a4#64 (by decide) (by decide)⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [readStdinSpecOfPlaced]
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
      exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hst.spAligned
    have hfp_sf : sf.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hst.fp]
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.2.2]; simp only [calleeSavedVRegs, arm64_norm, hst.vregs]
    have hsp_pre : (_ : State).sp = fsp := hsp_f.symm.trans hsp_sf
    rw [hsp_pre]
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
        ((fsp + 0x50#64) ↦₆₄ old50) ∗
          localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8
            [cell fsp 0x58 w.w1, (0x60, 24, emp)] := by
      simp only [localsCtx, localsFrom, emp_sepConj]
      sep_ac_rfl
    have hloc_merge : ∀ (inPtr' c60 c70 : BitVec 64),
        ((fsp + 0x50#64) ↦₆₄ inPtr') ∗ ((fsp + 0x60#64) ↦₆₄ c60) ∗
          ((fsp + 0x68#64) ↦₆₄ inPtr') ∗ ((fsp + 0x70#64) ↦₆₄ c70) ∗
          localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8
            [cell fsp 0x58 w.w1, (0x60, 24, emp)] ⊢
        locals fsp
          [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr', cell fsp 0x58 w.w1] := by
      intro inPtr' c60 c70
      have h24 :
          ((fsp + 0x60#64) ↦₆₄ c60) ∗ ((fsp + 0x68#64) ↦₆₄ inPtr') ∗
            ((fsp + 0x70#64) ↦₆₄ c70) ⊢
            memRegion (fsp + 0x60#64) 24 := by
        rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
          memRegion_split (fsp + 0x60#64) 8 (8 + 8) (by decide),
          memRegion_split ((fsp + 0x60#64) + 8#64) 8 8 (by decide)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
      have hctx2 :
          ((fsp + 0x50#64) ↦₆₄ inPtr') ∗ memRegion (fsp + 0x60#64) 24 ∗
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
        (sepConj_mono_left (vecU8_to_ownedBytes A.repAlloc (fsp + 0x60#64) i.stdin)) ?_
      simp only [sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd]
      refine SepWPp.exists_elim fun inCap => ?_
      refine SepWPp.exists_elim fun inPtr => ?_
      rw [hctx_open]
      refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x5b0#64) hinv_f
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
        (step_from_0x5b0_readOf_pool_placed (ms := M.stepEvents evsIn ms)
          (inOk := true) (buf := buf) (inCap := inCap) (inPtr := inPtr)
          (x27 := BitVec.ofNat 64 i.stdin.length)
          (c := c) (w := w) (ps := ps) (ArgvFrame := ArgvFrame)
          hc hio hstk hstk64 hcoinsOk hcoins hfit_coins hs_tr hin_5b0
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
          (fun s' cc cp ic ip evsCoins hevsCoins hin_le hat => by
            rw [← M.stepEvents_append evsIn evsCoins ms]
            exact hnext s' cc cp ic ip (evsIn ++ evsCoins)
              (SeqEnv.append (E₁ := StdinEnv i.stdin) (E₂ := ReadCoinsEnvOf ReadEnv i)
                hevsIn hevsCoins)
              hin_le hat))
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
        (((fsp + 0x50#64) ↦₆₄ inPtr) ∗ ((fsp + 0x60#64) ↦₆₄ inCap) ∗
          ((fsp + 0x68#64) ↦₆₄ inPtr) ∗ ((fsp + 0x70#64) ↦₆₄ BitVec.ofNat 64 i.stdin.length) ∗
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
        (sepConj_mono_left (sepConj_mono_right (memRegion_16_cells (fsp + 0x60#64)))) ?_
      simp only [sepExists_sepConj_right, sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd]
      refine SepWPp.exists_elim fun errInPtr => ?_
      refine SepWPp.exists_elim fun errInLen => ?_
      rw [hctx_open]
      refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x5b0#64) hinv_f
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
        (step_from_0x5b0_readOf_pool_placed (ms := M.stepEvents evsIn ms)
          (inOk := false) (buf := buf) (inCap := 0xffffffffffffffff#64)
          (inPtr := errInPtr) (x27 := errInLen)
          (c := c) (w := w) (ps := ps) (ArgvFrame := ArgvFrame)
          hc hio hstk hstk64 hcoinsOk hcoins hfit_coins hs_tr hin_5b0
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
          (fun s' cc cp ic ip evsCoins hevsCoins hin_le hat => by
            rw [← M.stepEvents_append evsIn evsCoins ms]
            exact hnext s' cc cp ic ip (evsIn ++ evsCoins)
              (SeqEnv.append (E₁ := StdinEnv i.stdin) (E₂ := ReadCoinsEnvOf ReadEnv i)
                hevsIn hevsCoins)
              hin_le hat))
      conv => arg 2; rw [pool_congr_vm A lim (M.stepEvents evsIn ms) sf
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (fun a => congrFun hnsp_5b0.2.1 a)]
      have hin_inv : emp ⊢ inInvOpt false A.repAlloc i c 0xffffffffffffffff#64 errInPtr errInLen := by
        dsimp only [inInvOpt]
        rw [← sepConj_emp ⌜_⌝]
        exact entails_pure_intro_left ⟨rfl, htag_gt1, Nat.lt_of_not_ge hcap_in⟩ (Entails.refl emp)
      rw [stackAt_sub_split fsp hsub_le hsub64]
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 0x50#64) ↦₆₄ errInPtr) ∗ ((fsp + 0x60#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((fsp + 0x68#64) ↦₆₄ errInPtr) ∗ ((fsp + 0x70#64) ↦₆₄ errInLen) ∗
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

/-- `StdinEnv`-parameterized budget-threaded continuation at `M+0x59c .. M+0x5ac`
(`read_stdin(&fsp+0x60)` when `1 < c.tag`, spilling `inPtr` to `[sp+0x50]`) →
`step_from_0x5b0_of_pool_placed`, generic in `{ArgvFrame : SepProp}` and retaining `A.pool` at exit
via `ExitKPoolPlaced`. -/
theorem step_stdin_0x59c_of_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {stk hookStack resStack : Nat}
    {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoBoundedPlaced A lim H io hookStack StdinEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i))
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (M3StdinEnvOf StdinEnv io i))
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
      M3StdinEnvOf StdinEnv io i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
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
      Q Qp oom :=
  step_stdin_0x59c_readOf_pool_placed hc hio hstk hstk64 hs0fs hstdin hcoinsOk hcoins hfit htag_gt1
    hs_tr hst hst_tr hst_fs hx19 hx20 hx22 hx24 hx25 hx26 hw5_orr hexit hnext

theorem step_stdin_0x59c_bounded_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {stk hookStack resStack : Nat}
    {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoBoundedPlaced A lim H io hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i))
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (M3StdinBoundedEnv io i))
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
      M3StdinBoundedEnv io i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
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
      Q Qp oom :=
  step_stdin_0x59c_of_pool_placed hc hio hstk hstk64 hs0fs hstdin hcoinsOk hcoins hfit htag_gt1
    hs_tr hst hst_tr hst_fs hx19 hx20 hx22 hx24 hx25 hx26 hw5_orr hexit hnext

theorem step_stdin_0x59c_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {stk hookStack resStack : Nat}
    {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i))
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (M3StdinEnv io i))
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
      M3StdinEnv io i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
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
      Q Qp oom :=
  step_stdin_0x59c_of_pool_placed hc
    ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio)
    hstk hstk64 hs0fs hstdin hcoinsOk hcoins hfit htag_gt1
    hs_tr hst hst_tr hst_fs hx19 hx20 hx22 hx24 hx25 hx26 hw5_orr hexit hnext

theorem step_stdin_0x59c_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {stk hookStack resStack : Nat}
    {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i))
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (M3StdinEnv io i))
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
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      M3StdinEnv io i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
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
      Q Qp oom :=
  step_stdin_0x59c_pool_placed hc hio hstk hstk64 hs0fs hstdin hcoinsOk hcoins hfit htag_gt1
    hs_tr hst hst_tr hst_fs hx19 hx20 hx22 hx24 hx25 hx26 hw5_orr
    (exitKPoolPlaced_of_exitKPlaced (lim := lim) hexit) hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudget
