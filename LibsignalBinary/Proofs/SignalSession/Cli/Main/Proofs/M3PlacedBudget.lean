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
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `main` Hop M3 (`M+0x568 → M+0x5dc`, Block `617`)

Verifies `main`'s third hop (`read_stdin` on `send`/`recv` and `read_file("coins")`) on Block `617`
under `[LibsignalPlacement]` and `RustCliAllocBudget M`, threading `A.pool` and `M3Env` into
`AtM4Placed` or `ExitKPoolPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (Inputs stdinCapBytes)
open CryptoVerification.SignalSession.Cli (CoinsReadable cliInputs cliStaticsPlaced utf8)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkLib_eq_617 blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtCallPlaced AtM4Placed CallV CallW InMainPlaced IoModel LsCodeInv addrWords argsBuf
   callCellsPlaced callHeap cell coinsOf inputOf locals localsBound
   localsEnd localsFrom locals_carve_cell locals_forget_cell m4CellsPlaced mPcPlaced_eq mProgPlaced
   mProgPlaced_eq mainFrameSize mainLitsBlk617 mainSaved ownedBytes parseArgs
   sepWPp_seq_codeOk)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
  (emp_entails_ownedBytes_nil entails_pure_elim_left entails_pure_intro_left inInv inInvOpt)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudget

open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget (ReadStdinEnv allocBytes1Events)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (MainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoBoundedPlaced MainIoOfPlaced ReadStdinBoundedEnv mainIoBoundedPlaced_iff_mainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (ExitKPlaced MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudget
  (M3StdinBoundedEnv M3StdinEnv M3StdinEnvOf M3StdinEnvReadOf ReadCoinsEnv ReadCoinsEnvOf
   m3StdinBoundedEvents m3StdinBoundedEvents_mem_env m3StdinEvents m3StdinEvents_mem_env
   readCoinsEvents readCoinsEvents_mem_env step_from_0x5b0_readOf_pool_placed
   step_stdin_0x59c_readOf_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced exitKPoolPlaced_of_exitKPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

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

/-- `(StdinEnv, ReadEnv)`-parameterized `AllocEvent` envelope of `main_m3_readOf_pool_placed_proof`:
`SeqEnv (StdinEnv i.stdin) (ReadEnv (initFsState (cliInputs i)).files (utf8 "coins"))` on
`send` / `recv` (`1 < c.tag`), and `ReadEnv (initFsState (cliInputs i)).files (utf8 "coins")` on
`keygen` / `init` (`¬(1 < c.tag)`). Definitionally (`rfl`) equal to `M3EnvOf StdinEnv io i c` at
`ReadEnv := ReadFileRuleEnv io.rd`. -/
def M3EnvReadOf (StdinEnv : List (BitVec 8) → List AllocEvent → Prop)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (i : Inputs) (c : CallV) : List AllocEvent → Prop :=
  if 1 < c.tag then
    SeqEnv (StdinEnv i.stdin) (ReadEnv (initFsState (cliInputs i)).files (utf8 "coins"))
  else
    ReadEnv (initFsState (cliInputs i)).files (utf8 "coins")

/-- `StdinEnv`-parameterized `AllocEvent` envelope of `main_m3_of_pool_placed_proof`:
`M3StdinEnvOf StdinEnv io i` on `send` / `recv` (`1 < c.tag`), and `ReadCoinsEnv io i` on
`keygen` / `init` (`¬(1 < c.tag)`). -/
def M3EnvOf (StdinEnv : List (BitVec 8) → List AllocEvent → Prop)
    (io : IoModel) (i : Inputs) (c : CallV) : List AllocEvent → Prop :=
  if 1 < c.tag then M3StdinEnvOf StdinEnv io i else ReadCoinsEnv io i

/-- Bounded-stdin `AllocEvent` envelope of `main_m3` (`StdinEnv := ReadStdinBoundedEnv`,
≤ 1 MiB cap on `read_stdin`), matching `MainEntryBudgetFits`. -/
abbrev M3Env (io : IoModel) (i : Inputs) (c : CallV) : List AllocEvent → Prop :=
  M3EnvOf ReadStdinBoundedEnv io i c

abbrev M3BoundedEnv (io : IoModel) (i : Inputs) (c : CallV) : List AllocEvent → Prop :=
  M3Env io i c

/-- Legacy unbounded-stdin `AllocEvent` envelope (`StdinEnv := ReadStdinEnv`). -/
abbrev M3UnboundedEnv (io : IoModel) (i : Inputs) (c : CallV) : List AllocEvent → Prop :=
  M3EnvOf ReadStdinEnv io i c

/-- Bounded-hook `AllocEvent` list emitted by `main_m3` (`m3StdinBoundedEvents io i` on
`send` / `recv`, and `readCoinsEvents io i` on `keygen` / `init`). -/
def m3BoundedEvents (io : IoModel) (i : Inputs) (c : CallV) : List AllocEvent :=
  if 1 < c.tag then m3StdinBoundedEvents io i else readCoinsEvents io i

abbrev m3Events (io : IoModel) (i : Inputs) (c : CallV) : List AllocEvent :=
  m3BoundedEvents io i c

/-- Legacy unbounded hook-path `AllocEvent` list (`m3StdinEvents io i` on `send` / `recv`). -/
def m3UnboundedEvents (io : IoModel) (i : Inputs) (c : CallV) : List AllocEvent :=
  if 1 < c.tag then m3StdinEvents io i else readCoinsEvents io i

/-- Hook-path `AllocEvent` list emitted on the `.ok (coinsOf i)` continuation path of `main_m3`
(`AtM4Placed` at `M+0x5dc`). -/
def m3OkEvents (i : Inputs) (c : CallV) : List AllocEvent :=
  allocBytes1Events (inputOf i c) ++ allocBytes1Events (coinsOf i)

theorem m3BoundedEvents_mem_env (io : IoModel) (i : Inputs) (c : CallV) :
    M3BoundedEnv io i c (m3BoundedEvents io i c) := by
  dsimp only [M3BoundedEnv, M3Env, M3EnvOf, m3BoundedEvents]
  split_ifs with h
  · exact m3StdinBoundedEvents_mem_env io i
  · exact readCoinsEvents_mem_env io i

theorem m3Events_mem_env (io : IoModel) (i : Inputs) (c : CallV) :
    M3Env io i c (m3Events io i c) :=
  m3BoundedEvents_mem_env io i c

theorem m3UnboundedEvents_mem_env (io : IoModel) (i : Inputs) (c : CallV) :
    M3UnboundedEnv io i c (m3UnboundedEvents io i c) := by
  dsimp only [M3UnboundedEnv, M3EnvOf, m3UnboundedEvents]
  split_ifs with h
  · exact m3StdinEvents_mem_env io i
  · exact readCoinsEvents_mem_env io i

theorem m3UnboundedEvents_eq_append (io : IoModel) (i : Inputs) (c : CallV) :
    m3UnboundedEvents io i c = allocBytes1Events (inputOf i c) ++ readCoinsEvents io i := by
  dsimp only [m3UnboundedEvents, m3StdinEvents, inputOf]
  split_ifs <;> simp [allocBytes1Events]

theorem m3BoundedEvents_eq_m3OkEvents_of_ok {io : IoModel} {i : Inputs} (c : CallV)
    (hcap : (inputOf i c).length ≤ stdinCapBytes)
    (hok : io.rd (initFsState (cliInputs i)).files (utf8 "coins") = .ok (coinsOf i)) :
    m3BoundedEvents io i c = m3OkEvents i c := by
  dsimp only [m3BoundedEvents, m3StdinBoundedEvents, readCoinsEvents, m3OkEvents, inputOf] at *
  rw [hok]
  split_ifs with htag hle
  · rfl
  · exfalso
    have hcap' : i.stdin.length ≤ stdinCapBytes := by simpa only [htag, ↓reduceIte] using hcap
    exact hle (by change i.stdin.length ≤ 1048576; exact hcap')
  · simp [allocBytes1Events]

theorem m3UnboundedEvents_eq_m3OkEvents_of_ok {io : IoModel} {i : Inputs} (c : CallV)
    (hok : io.rd (initFsState (cliInputs i)).files (utf8 "coins") = .ok (coinsOf i)) :
    m3UnboundedEvents io i c = m3OkEvents i c := by
  rw [m3UnboundedEvents_eq_append]
  dsimp only [readCoinsEvents, m3OkEvents]
  rw [hok]

set_option maxHeartbeats 800000 in
private theorem step_empty_in_0x57c_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ} {uuidParse : UuidParser}
    {io : IoModel} {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
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
      ((fsp + 0x50#64) ↦₆₄ c50) ∗ ((fsp + 0x60#64) ↦₆₄ c60) ∗
        ((fsp + 0x68#64) ↦₆₄ c68) ∗ ((fsp + 0x70#64) ↦₆₄ c70) ∗
        ((fsp + 0x40#64) ↦₆₄ w.w3) ∗ ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
        ((fsp + 0x58#64) ↦₆₄ w.w1) ∗ memRegion fsp 0x40 ∗
        memRegion (fsp + 0x78#64) (0x480 - 0x78) := by
    simp only [locals, localsFrom, List.nil_append, List.cons_append,
      Nat.reduceAdd, Nat.reduceSub, ProofLib.memRegion_zero, emp_sepConj]
    sep_ac_rfl
  rw [hloc_open]
  have hal : st.spAligned = true := hst.spAligned_state
  have hsp : st.sp = fsp := hst.sp
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x5b0#64) hinv
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
    (step_from_0x5b0_readOf_pool_placed (inOk := true) (inCap := 0#64) (inPtr := 1#64) (x27 := 0#64)
      (c := c) (w := w) (ps := ps) (ArgvFrame := ArgvFrame)
      hc hio hstk hstk64 hcoinsOk hcoins hfit hs_tr hin1
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
      ((fsp + 0x50#64) ↦₆₄ 1#64) ∗ ((fsp + 0x60#64) ↦₆₄ 0#64) ∗
        ((fsp + 0x68#64) ↦₆₄ 1#64) ∗ ((fsp + 0x70#64) ↦₆₄ 0#64) ∗
        ((fsp + 0x40#64) ↦₆₄ w.w3) ∗ ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
        ((fsp + 0x58#64) ↦₆₄ w.w1) ∗ memRegion fsp 0x40 ∗
        memRegion (fsp + 0x78#64) (0x480 - 0x78) ⊢
      locals fsp
        [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 1#64, cell fsp 0x58 w.w1] := by
    have hpack :
        locals fsp
          [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 1#64, cell fsp 0x58 w.w1,
           cell fsp 0x60 0#64, cell fsp 0x68 1#64, cell fsp 0x70 0#64] =
        ((fsp + 0x50#64) ↦₆₄ 1#64) ∗ ((fsp + 0x60#64) ↦₆₄ 0#64) ∗
          ((fsp + 0x68#64) ↦₆₄ 1#64) ∗ ((fsp + 0x70#64) ↦₆₄ 0#64) ∗
          ((fsp + 0x40#64) ↦₆₄ w.w3) ∗ ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
          ((fsp + 0x58#64) ↦₆₄ w.w1) ∗ memRegion fsp 0x40 ∗
          memRegion (fsp + 0x78#64) (0x480 - 0x78) := by
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
      (((fsp + 0x50#64) ↦₆₄ 1#64) ∗ ((fsp + 0x60#64) ↦₆₄ 0#64) ∗
        ((fsp + 0x68#64) ↦₆₄ 1#64) ∗ ((fsp + 0x70#64) ↦₆₄ 0#64) ∗
        ((fsp + 0x40#64) ↦₆₄ w.w3) ∗ ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
        ((fsp + 0x58#64) ↦₆₄ w.w1) ∗ memRegion fsp 0x40 ∗
        memRegion (fsp + 0x78#64) (0x480 - 0x78)) ∗
      (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ cliStaticsPlaced ∗ mainLitsBlk617) by simp only [emp_sepConj]; sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hin_inv (sepConj_mono_left hloc_close)) ?_
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 1200000 in
/-- `(StdinEnv, ReadEnv)`-parameterized budget-threaded relocatable proof of `main_m3`
(`M+0x568 → M+0x5dc`) on Block `617`, generic in `{ArgvFrame : SepProp}` and retaining `A.pool`
at exit via `ExitKPoolPlaced`. -/
theorem main_m3_readOf_pool_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
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
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
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
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x57c#64) hinv
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
      (step_empty_in_0x57c_pool_placed (ArgvFrame := ArgvFrame)
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
        (fun s' cc cp ic ip evs hevs hin_le ha =>
          hnext s' cc cp ic ip evs
            (by simpa only [M3EnvReadOf, ReadCoinsEnvOf, CallV.tag,
                  show ¬ ((1 : Nat) < 0) by decide, ↓reduceIte] using hevs)
            hin_le ha))
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
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x57c#64) hinv
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
      (step_empty_in_0x57c_pool_placed (ArgvFrame := ArgvFrame)
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
        (fun s' cc cp ic ip evs hevs hin_le ha =>
          hnext s' cc cp ic ip evs
            (by simpa only [M3EnvReadOf, ReadCoinsEnvOf, CallV.tag,
                  show ¬ ((1 : Nat) < 1) by decide, ↓reduceIte] using hevs)
            hin_le ha))
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
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x59c#64) hinv
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
      (step_stdin_0x59c_readOf_pool_placed (ArgvFrame := ArgvFrame)
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
        (fun s' cc cp ic ip evs hevs hin_le ha =>
          hnext s' cc cp ic ip evs
            (by simpa only [M3EnvReadOf, M3StdinEnvReadOf, ReadCoinsEnvOf, CallV.tag,
                  show (1 : Nat) < 2 by decide, ↓reduceIte] using hevs)
            hin_le ha))
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
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x59c#64) hinv
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
      (step_stdin_0x59c_readOf_pool_placed (ArgvFrame := ArgvFrame)
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
        (fun s' cc cp ic ip evs hevs hin_le ha =>
          hnext s' cc cp ic ip evs
            (by simpa only [M3EnvReadOf, M3StdinEnvReadOf, ReadCoinsEnvOf, CallV.tag,
                  show (1 : Nat) < 3 by decide, ↓reduceIte] using hevs)
            hin_le ha))
    conv => arg 2; rw [pool_congr_vm A lim ms s
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
    exact Entails.refl _

theorem main_m3_bounded_readOf_pool_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {ArgvFrame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack ReadStdinBoundedEnv ReadEnv)
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
  main_m3_readOf_pool_placed_proof hc hio hstk hstk64 hs0fs hs0tr hstdin hcoinsOk hcoins hparse
    hfit hs hexit hnext

/-- `StdinEnv`-parameterized budget-threaded relocatable proof of `main_m3` (`M+0x568 → M+0x5dc`)
on Block `617`, generic in `{ArgvFrame : SepProp}` and retaining `A.pool` at exit via
`ExitKPoolPlaced`. -/
theorem main_m3_of_pool_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {ArgvFrame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoBoundedPlaced A lim H io hookStack StdinEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i)) (hs0tr : s0.trace = [])
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim ms (M3EnvOf StdinEnv io i c))
    (hs : AtCallPlaced CodeOk s0 s w i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      M3EnvOf StdinEnv io i c evs →
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
  main_m3_readOf_pool_placed_proof hc hio hstk hstk64 hs0fs hs0tr hstdin hcoinsOk hcoins hparse
    hfit hs hexit hnext

theorem main_m3_bounded_pool_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {ArgvFrame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoBoundedPlaced A lim H io hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i)) (hs0tr : s0.trace = [])
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim ms (M3BoundedEnv io i c))
    (hs : AtCallPlaced CodeOk s0 s w i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      M3BoundedEnv io i c evs →
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
  main_m3_of_pool_placed_proof hc hio hstk hstk64 hs0fs hs0tr hstdin hcoinsOk hcoins hparse hfit
    hs hexit hnext

theorem main_m3_bounded_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {ArgvFrame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoBoundedPlaced A lim H io hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i)) (hs0tr : s0.trace = [])
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim ms (M3BoundedEnv io i c))
    (hs : AtCallPlaced CodeOk s0 s w i.argv.length buf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      M3BoundedEnv io i c evs →
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
  main_m3_bounded_pool_placed_proof hc hio hstk hstk64 hs0fs hs0tr hstdin hcoinsOk hcoins hparse
    hfit hs (exitKPoolPlaced_of_exitKPlaced (lim := lim) hexit) hnext

theorem main_m3_bounded_pool_placed_proof_any_st [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {ArgvFrame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoBoundedPlaced A lim H io hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i)) (hs0tr : s0.trace = [])
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim ms (M3BoundedEnv io i c))
    (hs : AtCallPlaced CodeOk s0 s w i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (ms' : M.σ) (coinsCap coinsPtr inCap inPtr : BitVec 64),
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
          A.pool lim ms' s' ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom :=
  main_m3_bounded_pool_placed_proof hc hio hstk hstk64 hs0fs hs0tr hstdin hcoinsOk hcoins hparse
    hfit hs hexit fun s' cc cp ic ip _ _ hin_le ha => hnext s' _ cc cp ic ip hin_le ha

theorem main_m3_pool_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {ArgvFrame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i)) (hs0tr : s0.trace = [])
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim ms (M3UnboundedEnv io i c))
    (hs : AtCallPlaced CodeOk s0 s w i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      M3UnboundedEnv io i c evs →
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
  main_m3_of_pool_placed_proof hc
    ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio)
    hstk hstk64 hs0fs hs0tr hstdin hcoinsOk hcoins hparse hfit hs hexit hnext

theorem main_m3_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {ArgvFrame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i)) (hs0tr : s0.trace = [])
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim ms (M3UnboundedEnv io i c))
    (hs : AtCallPlaced CodeOk s0 s w i.argv.length buf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      M3UnboundedEnv io i c evs →
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
  main_m3_pool_placed_proof hc hio hstk hstk64 hs0fs hs0tr hstdin hcoinsOk hcoins hparse hfit hs
    (exitKPoolPlaced_of_exitKPlaced (lim := lim) hexit) hnext

theorem main_m3_pool_placed_proof_any_st [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {ArgvFrame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i)) (hs0tr : s0.trace = [])
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim ms (M3UnboundedEnv io i c))
    (hs : AtCallPlaced CodeOk s0 s w i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (ms' : M.σ) (coinsCap coinsPtr inCap inPtr : BitVec 64),
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
          A.pool lim ms' s' ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom :=
  main_m3_pool_placed_proof hc hio hstk hstk64 hs0fs hs0tr hstdin hcoinsOk hcoins hparse hfit hs
    hexit fun s' cc cp ic ip _ _ hin_le ha => hnext s' _ cc cp ic ip hin_le ha

theorem main_m3_placed_proof_any_st [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {ArgvFrame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i)) (hs0tr : s0.trace = [])
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim ms (M3UnboundedEnv io i c))
    (hs : AtCallPlaced CodeOk s0 s w i.argv.length buf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (ms' : M.σ) (coinsCap coinsPtr inCap inPtr : BitVec 64),
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
          A.pool lim ms' s' ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom :=
  main_m3_pool_placed_proof_any_st hc hio hstk hstk64 hs0fs hs0tr hstdin hcoinsOk hcoins hparse
    hfit hs (exitKPoolPlaced_of_exitKPlaced (lim := lim) hexit) hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudget
