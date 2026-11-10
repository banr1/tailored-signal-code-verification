/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBWritePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopDropPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5CallsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget

/-!
# Budget-Threaded M5 Inner Loop B Non-Empty Entry Write (`M+0x9e8 .. M+0xa48`, Block `617`)

Budget-threaded verification of `m5_loop_b_write_nonempty_placed` (`d.path = []`, `0 < name.length`)
on Block `617` under `FitsEnv`, advancing `A.pool` by `M5LoopBNonemptyStepEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBWritePlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.RustHeap (LayoutOk vecBuf vecHeader)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession
  (lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsWriteFileSym)
open CryptoVerification.SignalSession.Cli (StoresGhost dirEntryAt pathOf)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (InMainPlaced IoModel LsCodeInv M5ErrEntryPlaced M5LoopErrPlaced argsBuf commitFiles
   locals m5ErrCellsPlaced m5ErrMemPlaced mPcPlaced mainFrameSize mainSaved ownedBytes storesDirs
   writesBefore)
open CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
  (bytes_entails_memRegion commitFiles_entry_err dir_entry_path_ok_len entryBorrowRest
   entryBorrowRest_pure m5ScratchPlaced m5WorkRestPlaced m5Work_exit_to_err_placed
   m5_run_placed m5_seq_placed mPcPlaced_eq_blkPl mkStepPlaced ownedBytes_of_live_bytes
   pathOf_nil vecBuf_borrow_eq vecBuf_unborrow)
open scoped CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
open CryptoVerification.SignalSession.Cli.Path.Helpers
  (ofNat_beq_zero_false ofNat_getElem_63_false ofNat_getLsbD_63_false ofNat_ne_zero)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget fitsEvents_append
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (WriteFileEnv writeFileEnv_nil)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced mainIoBoundedPlaced_iff_mainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced MainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5CallsPlacedBudget
  (m5_call_alloc_placed m5_call_dealloc_placed m5_call_memcpy_pool_placed m5_call_shim_pool_placed
   m5_call_write_file_of_placed m5_call_write_file_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopDropPlacedBudget
  (m5ErrEntryDropEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
  (m5ErrCellsPlaced_atState_eq_repAlloc m5ErrEntryPlaced_heap_atState_eq_repAlloc)

attribute [local arm64_norm]
  RustCliAllocBudget.pool_setPC
  RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState
  RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32
  RustCliAllocBudget.pool_writeReg

attribute [local irreducible] Program.fetch Program.externAt?

/-- Error-exit allocator event envelope at `M+0xbdc` for a non-empty entry `name` in Loop B
(`__rust_alloc(name.length, 1)` followed by `write_file`). -/
def M5LoopBErrNonemptyEnv (name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ConcatEnv (· = rustAllocEvents name.length 1) (WriteFileEnv name.length) evs

example : ∃ evs, M5LoopBErrNonemptyEnv [0x61#8] evs :=
  ⟨rustAllocEvents 1 1 ++ [], ConcatEnv.append rfl (writeFileEnv_nil 1)⟩

/-- Full Ok-step allocator event envelope at `M+0xa60` for a non-empty entry `name` in Loop B
(`__rust_alloc(name.length, 1)` + `write_file` + `__rust_dealloc(name.length, 1)`). -/
def M5LoopBNonemptyStepEnv (name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ConcatEnv (M5LoopBErrNonemptyEnv name) (· = rustDeallocEvents name.length 1) evs

example : ∃ evs, M5LoopBNonemptyStepEnv [0x61#8] evs :=
  ⟨(rustAllocEvents 1 1 ++ []) ++ rustDeallocEvents 1 1,
    ConcatEnv.append (ConcatEnv.append rfl (writeFileEnv_nil 1)) rfl⟩

set_option maxHeartbeats 1600000 in
/-- `{StdinEnv ReadEnv}`-parametric budget-threaded execution of `M+0x9e8 .. M+0xa48` for a single
non-empty entry `e` of `Dir k` (`d.path = []`) under `FitsEnv`, handing write failure to `herr`
(`0xbdc`) or write success to `hcont_a60` at `M+0xa60`. -/
theorem m5_loop_b_write_nonempty_of_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {io : IoModel} {uuidParse : UuidParser}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr v40 v48 v58 v458 v460 v468 : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {done rest : List (List (BitVec 8) × List (BitVec 8))}
    {e : List (BitVec 8) × List (BitVec 8)}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hfit : FitsEnv M lim st (M5LoopBNonemptyStepEnv e.1))
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_hook : mainFrameSize + hookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk : k < 8)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hdpath : ((storesDirs g)[k]'(by simp [hk])).path = [])
    (hpos : 0 < e.1.length)
    (hsplit : ((storesDirs g)[k]'(by simp [hk])).changed = done ++ e :: rest)
    (hs : InMainPlaced CodeOk s0 s 0x9e8)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : s.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 ((e :: rest).length * 48))
    (hfiles : commitFiles io.wr F0
      (writesBefore g k ++
        done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
      some s.fs.files)
    (htr0 : tr0 <+: s.trace)
    (hstdout : ProcessOutcome.traceStreamBytes .stdout s.trace =
      ProcessOutcome.traceStreamBytes .stdout tr0)
    (hP : P ⊢ vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ e :: rest) ∗
      m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
        curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
        v40 v48 v58 v458 v460 v468 ∗
      m5WorkRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
        outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
      ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      mainSaved s0 ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
      A.pool lim st s ∗ anyHeap)
    (herr : ∀ (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced),
      M5LoopBErrNonemptyEnv e.1 evsErr →
      m5ErrEntryDropEvents errE = rustDeallocEvents e.1.length 1 →
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k
        ((storesDirs g)[k]'(by simp [hk])).changed errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
          s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          ((storesDirs g)[k]'(by simp [hk])).changed errE)
        Q Qp oom)
    (hcont_a60 : ∀ (s_end : State) (evs : List AllocEvent) (F' : FsFiles),
      M5LoopBNonemptyStepEnv e.1 evs →
      (done ++ e :: rest).length ≤ curCap.toNat →
      curCap.toNat * 48 < 2 ^ 63 →
      InMainPlaced CodeOk s0 s_end 0xa60 →
      s_end.fs.files = F' →
      io.wr s.fs.files e.1 e.2 = some F' →
      tr0 <+: s_end.trace →
      ProcessOutcome.traceStreamBytes .stdout s_end.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      s_end.readReg64 (.gpr 19#5) = buf →
      s_end.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s_end.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s_end.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 →
      s_end.readReg64 (.gpr 26#5) = BitVec.ofNat 64 ((e :: rest).length * 48) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s_end
        (vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ e :: rest) ∗
          m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
            curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
            v40 v48 v58 v458 v460 v468 ∗
          m5WorkRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
            outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
          ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s_end ∗ anyHeap)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hfit_alloc : FitsEvents M lim st (rustAllocEvents e.1.length 1) := by
    have htot := hfit ((rustAllocEvents e.1.length 1 ++ []) ++ rustDeallocEvents e.1.length 1)
      (ConcatEnv.append (ConcatEnv.append rfl (writeFileEnv_nil e.1.length)) rfl)
    exact ((fitsEvents_append M lim _ _ st).mp
      (((fitsEvents_append M lim _ _ st).mp htot).1)).1
  let st1 := M.stepEvents (rustAllocEvents e.1.length 1) st
  have hfit_wr : FitsEnv M lim st1 (WriteFileEnv e.1.length) := by
    intro evs_wr hwr
    have htot := hfit ((rustAllocEvents e.1.length 1 ++ evs_wr) ++ rustDeallocEvents e.1.length 1)
      (ConcatEnv.append (ConcatEnv.append rfl hwr) rfl)
    exact ((fitsEvents_append M lim _ _ st).mp
      (((fitsEvents_append M lim _ _ st).mp htot).1)).2
  have hne_cur : ((storesDirs g)[k]'(by simp [hk])).changed ≠ [] := by rw [hsplit]; simp
  have he_mem : e ∈ ((storesDirs g)[k]'(by simp [hk])).changed := by
    rw [hsplit]; exact List.mem_append_right _ (.head _)
  have ⟨he_ok, he_lt⟩ : io.pathOk e.1 ∧ e.1.length < 2 ^ 32 := by
    simpa only [hdpath, pathOf_nil] using dir_entry_path_ok_len hk hpaths he_mem
  have hbit63a : (BitVec.ofNat 64 e.1.length).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (by m5_omega)
  have hbit63b : (BitVec.ofNat 64 e.1.length)[63] = false :=
    ofNat_getElem_63_false (by m5_omega)
  refine SepWPp.weaken_pre hP ?_
  rw [vecBuf_borrow_eq A.repAlloc curCap curPtr done e rest]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun c1 => ?_
  refine SepWPp.exists_elim fun p1 => ?_
  refine SepWPp.exists_elim fun c2 => ?_
  refine SepWPp.exists_elim fun p2 => ?_
  rw [entryBorrowRest_pure A.repAlloc curCap curPtr done e rest c1 p1 c2 p2]
  have hpure_front :
      (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
        vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
          (BitVec.ofNat 64 e.2.length) ∗
        (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
        (⌜e.2.length < 2 ^ 63 ∧
          (done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63⌝ ∗
          entryBorrowRest A.repAlloc curCap curPtr done e rest c1 p1 c2 p2)) =
      ⌜e.2.length < 2 ^ 63 ∧
        (done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63⌝ ∗
      (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
        vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
          (BitVec.ofNat 64 e.2.length) ∗
        (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
        entryBorrowRest A.repAlloc curCap curPtr done e rest c1 p1 c2 p2) := by
    sep_ac_rfl
  rw [hpure_front]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨he2_lt63, hle_tot, hcap_lt⟩ => ?_
  have he2_toNat : (BitVec.ofNat 64 e.2.length).toNat = e.2.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by m5_omega)]
  let invFrame : SepProp :=
    entryBorrowRest A.repAlloc curCap curPtr done e rest c1 p1 c2 p2 ∗
      m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
        v40 v48 v58 v458 v460 v468 ∗
      m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
      ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗ anyHeap
  have hunb_loop : ∀ (stCur : M.σ) (sCur : State),
      (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
        vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
          (BitVec.ofNat 64 e.2.length) ∗
        (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim stCur sCur ∗ invFrame) ⊢
      vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ e :: rest) ∗
        m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
          v40 v48 v58 v458 v460 v468 ∗
        m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
        ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim stCur sCur ∗ anyHeap := by
    intro stCur sCur
    dsimp only [invFrame]
    have hord :
        vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
          vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
            (BitVec.ofNat 64 e.2.length) ∗
          (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
          stackAt fsp (stk - mainFrameSize) ∗ A.pool lim stCur sCur ∗
          (entryBorrowRest A.repAlloc curCap curPtr done e rest c1 p1 c2 p2 ∗
            m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
              v40 v48 v58 v458 v460 v468 ∗
            m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
            ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗ anyHeap) =
        (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
          vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
            (BitVec.ofNat 64 e.2.length) ∗
          (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
          entryBorrowRest A.repAlloc curCap curPtr done e rest c1 p1 c2 p2) ∗
        (m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
            v40 v48 v58 v458 v460 v468 ∗
          m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
          ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim stCur sCur ∗ anyHeap) := by
      sep_ac_rfl
    rw [hord]
    exact sepConj_mono_left (vecBuf_unborrow A.repAlloc curCap curPtr done e rest c1 p1 c2 p2)
  have herrMem_eq : ∀ (stErr : M.σ) (se : State)
      (curEntries : List (List (BitVec 8) × List (BitVec 8))) (errE : M5ErrEntryPlaced),
      m5ErrMemPlaced (A.atState lim stErr se) s0 stk n outCap outPtr inCap inPtr buf curCap curPtr
        out inp ps g k curEntries errE =
      errE.heap A.repAlloc ∗
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr curEntries ∗
        ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗
        locals fsp
          (m5ErrCellsPlaced A.repAlloc fsp
            outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr curCap curPtr g k) ∗
        stackAt fsp (stk - mainFrameSize) ∗
        A.pool lim stErr se ∗ anyHeap := fun _ _ _ _ => by
    dsimp only [m5ErrMemPlaced, fsp]
    rw [m5ErrEntryPlaced_heap_atState_eq_repAlloc, m5ErrCellsPlaced_atState_eq_repAlloc]
    rfl
  have to_err_mem : ∀ (stErr : M.σ) (se : State) (errE : M5ErrEntryPlaced),
      errE.heap A.repAlloc ∗
        (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
          vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
            (BitVec.ofNat 64 e.2.length) ∗
          (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
          stackAt fsp (stk - mainFrameSize) ∗ A.pool lim stErr se ∗ invFrame) ⊢
      m5ErrMemPlaced (A.atState lim stErr se) s0 stk n outCap outPtr inCap inPtr buf curCap curPtr
        out inp ps g k ((storesDirs g)[k]'(by simp [hk])).changed errE := by
    intro stErr se errE
    refine Entails.trans (sepConj_mono_right (hunb_loop stErr se)) ?_
    have hmem_rhs :
        m5ErrMemPlaced (A.atState lim stErr se) s0 stk n outCap outPtr inCap inPtr buf curCap curPtr
          out inp ps g k ((storesDirs g)[k]'(by simp [hk])).changed errE =
        errE.heap A.repAlloc ∗
          vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ e :: rest) ∗
          ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗
          locals fsp
            (m5ErrCellsPlaced A.repAlloc fsp
              outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr curCap curPtr g k) ∗
          stackAt fsp (stk - mainFrameSize) ∗
          A.pool lim stErr se ∗ anyHeap :=
      (congrArg (fun es => m5ErrMemPlaced (A.atState lim stErr se) s0 stk n outCap outPtr inCap inPtr
        buf curCap curPtr out inp ps g k es errE) hsplit).trans
        (herrMem_eq stErr se (done ++ e :: rest) errE)
    refine Entails.trans ?_ (Entails.of_eq hmem_rhs.symm)
    have hexit := m5Work_exit_to_err_placed A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
      inCap inPtr curCap curPtr g hk v40 v48 v58 v458 v460 v468
    have hord :
        errE.heap A.repAlloc ∗
          (vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ e :: rest) ∗
            m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
              v40 v48 v58 v458 v460 v468 ∗
            m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
            ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
            stackAt fsp (stk - mainFrameSize) ∗ A.pool lim stErr se ∗ anyHeap) =
        (m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
            v40 v48 v58 v458 v460 v468 ∗
          m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k) ∗
        (errE.heap A.repAlloc ∗
          vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ e :: rest) ∗
          ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          stackAt fsp (stk - mainFrameSize) ∗ A.pool lim stErr se ∗ anyHeap) := by sep_ac_rfl
    rw [hord]
    exact Entails.trans (sepConj_mono_left hexit) (Entails.of_eq (by sep_ac_rfl))
  have off_m24 : (curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64) + (-24#64) =
      (curPtr + BitVec.ofNat 64 (done.length * 48)) + 16#64 := by rw [BitVec.add_assoc]; rfl
  have off_m32 : (curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64) + (-32#64) =
      (curPtr + BitVec.ofNat 64 (done.length * 48)) + 8#64 := by rw [BitVec.add_assoc]; rfl
  have off_m8 : (curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64) + (-8#64) =
      (curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64 := by rw [BitVec.add_assoc]; rfl
  have off_hdr2 :
      vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
          (BitVec.ofNat 64 e.2.length) =
      (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) ↦₆₄ c2) ∗
        (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64) ↦₆₄ p2) ∗
        ((((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64) + 8#64) ↦₆₄
          BitVec.ofNat 64 e.2.length) := by
    unfold vecHeader
    have ha : ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) + 8#64 =
        (curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64 := by m5_bv_omega
    have hb : ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) + 16#64 =
        ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64) + 8#64 := by m5_bv_omega
    rw [ha, hb]
  have hpc := hs.pc; have hrun := hs.run
  have he1_beq0 : (BitVec.ofNat 64 e.1.length == 0#64) = false :=
    ofNat_beq_zero_false hpos (by m5_omega)
  have he1_toNat : (BitVec.ofNat 64 e.1.length).toNat = e.1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by m5_omega)]
  have hlay1 : LayoutOk e.1.length 1 := ⟨hpos, ⟨0, rfl⟩, by m5_omega⟩
  refine m5_run_placed hs.inv (mid := lsρ lsRustNoAllocShimSymCli)
    (P0 := (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 8#64) ↦₆₄ p1) ∗
      (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length))
    (F := ((curPtr + BitVec.ofNat 64 (done.length * 48)) ↦₆₄ c1) ∗
      vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
        (BitVec.ofNat 64 e.2.length) ∗
      (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ invFrame)
    (by unfold vecHeader; dsimp only [invFrame, fsp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  m5_steps
  apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
    (by simp only [arm64_norm, *])
  intro hpcm1 hrunm1 hinv_m1
  refine m5_call_shim_pool_placed hA hstk_ext hstk64 hpcm1 hrunm1 hinv_m1
    (by simp only [arm64_norm, hs.sp]) (by simp only [arm64_norm, hs.fp])
    (by simp only [calleeSavedVRegs, arm64_norm, hs.vregs]) hs.spAligned
    (retOff := 0x9fc) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
    (st := st)
    (F := vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
      vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
        (BitVec.ofNat 64 e.2.length) ∗
      (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗ invFrame)
    (by
      simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
        RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
        RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
      unfold vecHeader; dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  intro s1 hs1 _hvm1 hfs1 htr1 hcsm1
  have hpc1 := hs1.pc; have hrun1 := hs1.run
  have r21_1 : s1.readReg64 (.gpr 21#5) = p1 := by simp only [hcsm1.2.2.1, arm64_norm]
  have r25_1 : s1.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 :=
    hcsm1.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx25])
  have r23_1 : s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 e.1.length := by
    simp only [hcsm1.2.2.2.2.1, arm64_norm]
  apply m5_seq_placed hs1.inv (mid := lsρ lsRustAllocSymCli)
  m5_steps
  apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
    (by simp only [arm64_norm, *])
  intro hpcm2 hrunm2 hinv_m2
  refine m5_call_alloc_placed hA hstk_ext hstk64 hlay1 hfit_alloc hpcm2 hrunm2 hinv_m2
    (by simp only [arm64_norm, hs1.sp]) (by simp only [arm64_norm, hs1.fp])
    (by simp only [calleeSavedVRegs, arm64_norm, hs1.vregs]) hs1.spAligned
    (retOff := 0xa08) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
    (by simp only [arm64_norm, r23_1, he1_toNat]) (by simp only [arm64_norm]; try rfl)
    (F := vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
      vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
        (BitVec.ofNat 64 e.2.length) ∗
      (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗ invFrame)
    (by
      simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
        RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
        RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  intro s2 hs2 htmp_ne _hacp2 hfs2 htr2 hcsm2
  let tmpPtr := s2.readReg64 .x0
  have htmp_beq : (s2.readReg64 .x0 == 0#64) = false := beq_false_of_ne htmp_ne
  have hpc2 := hs2.pc; have hrun2 := hs2.run
  have r21_2 : s2.readReg64 (.gpr 21#5) = p1 := hcsm2.2.2.1.trans (by simp only [arm64_norm, r21_1])
  have r25_2 : s2.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 :=
    hcsm2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r25_1])
  have r23_2 : s2.readReg64 (.gpr 23#5) = BitVec.ofNat 64 e.1.length :=
    hcsm2.2.2.2.2.1.trans (by simp only [arm64_norm, r23_1])
  apply m5_seq_placed hs2.inv (mid := lsρ memcpyName)
  m5_steps
  apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
    (by simp only [arm64_norm, *])
  intro hpcm3 hrunm3 hinv_m3
  refine m5_call_memcpy_pool_placed hA hstk_ext hstk64 hpcm3 hrunm3 hinv_m3
    (by simp only [arm64_norm, hs2.sp]) (by simp only [arm64_norm, hs2.fp])
    (by simp only [calleeSavedVRegs, arm64_norm, hs2.vregs]) hs2.spAligned
    (retOff := 0xa24) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
    (st := st1) (dst := tmpPtr) (src := p1) (bs := e.1)
    (by simp only [arm64_norm]; try rfl) (by simp only [arm64_norm, r21_2])
    (by simp only [arm64_norm, r23_2, he1_toNat])
    (F := A.live tmpPtr e.1.length 1 ∗
      vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
      vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
        (BitVec.ofNat 64 e.2.length) ∗
      (p2 ↦ₛ e.2) ∗ invFrame)
    (by
      simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
        RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
        RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
      dsimp only [tmpPtr, st1, fsp]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  intro s3 hs3 _hvm3 hfs3 htr3 hcsm3
  have hpc3 := hs3.pc; have hrun3 := hs3.run
  have r25_3 : s3.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 :=
    hcsm3.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r25_2])
  have r22_3 : s3.readReg64 (.gpr 22#5) = tmpPtr :=
    hcsm3.2.2.2.1.trans (by simp only [arm64_norm]; try rfl)
  have r23_3 : s3.readReg64 (.gpr 23#5) = BitVec.ofNat 64 e.1.length :=
    hcsm3.2.2.2.2.1.trans (by simp only [arm64_norm, r23_2])
  refine m5_run_placed hs3.inv (mid := lsρ lsWriteFileSym)
    (P0 := (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64) ↦₆₄ p2) ∗
      ((((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x20#64) + 8#64) ↦₆₄
        BitVec.ofNat 64 e.2.length))
    (F := (tmpPtr ↦ₛ e.1) ∗ (p1 ↦ₛ e.1) ∗
      stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st1 s3 ∗ A.live tmpPtr e.1.length 1 ∗
      vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
      (((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) ↦₆₄ c2) ∗
      (p2 ↦ₛ e.2) ∗ invFrame)
    (by rw [off_hdr2]; dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  m5_steps
  apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
    (by simp only [arm64_norm, *])
  intro hpcm4 hrunm4 hinv_m4
  refine m5_call_write_file_of_placed hio hstk_hook hstk64 hpcm4 hrunm4 hinv_m4
    (by simp only [arm64_norm, hs3.sp]) (by simp only [arm64_norm, hs3.fp])
    (by simp only [calleeSavedVRegs, arm64_norm, hs3.vregs]) hs3.spAligned
    (retOff := 0xa34) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
    (pathA := tmpPtr) (path := e.1) (buf := p2) (bs := e.2)
    (by simp only [arm64_norm, r22_3]) (by simp only [arm64_norm, r23_3, he1_toNat])
    (by simp only [arm64_norm]) (by simp only [arm64_norm, he2_toNat])
    he_lt he_ok hfit_wr
    (F := A.live tmpPtr e.1.length 1 ∗
      vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
      vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
        (BitVec.ofNat 64 e.2.length) ∗
      (p1 ↦ₛ e.1) ∗ invFrame)
    (by
      simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
        RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
        RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
      rw [off_hdr2]; dsimp only [fsp]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  intro s4 evs_wr hs4 hwr_env hwr4 htr4 hout4 hcsm4
  let st2 := M.stepEvents evs_wr st1
  have hst2_eq : st2 = M.stepEvents (rustAllocEvents e.1.length 1 ++ evs_wr) st :=
    (M.stepEvents_append (rustAllocEvents e.1.length 1) evs_wr st).symm
  have hfs_chain : s3.fs.files = s.fs.files := by simp only [hfs3, arm64_norm, hfs2, hfs1]
  simp only [arm64_norm, hfs_chain] at hwr4
  have htr_chain : tr0 <+: s4.trace := by
    have h3t : s3.trace = s.trace := by simp only [htr3, arm64_norm, htr2, htr1]
    have h4t : s3.trace <+: s4.trace := by simpa only [arm64_norm] using htr4
    exact htr0.trans (h3t ▸ h4t)
  have hout_chain : ProcessOutcome.traceStreamBytes .stdout s4.trace =
      ProcessOutcome.traceStreamBytes .stdout tr0 := by
    have h3t : s3.trace = s.trace := by simp only [htr3, arm64_norm, htr2, htr1]
    simpa only [arm64_norm, h3t, hstdout] using hout4
  have r19_4 : s4.readReg64 (.gpr 19#5) = buf := by
    simp only [hcsm4.1, arm64_norm, hcsm3.1, hcsm2.1, hcsm1.1, hx19]
  have r20_4 : s4.readReg64 (.gpr 20#5) =
      BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length := by
    simp only [hcsm4.2.1, arm64_norm, hcsm3.2.1, hcsm2.2.1, hcsm1.2.1, hx20]
  have r22_4 : s4.readReg64 (.gpr 22#5) = tmpPtr :=
    hcsm4.2.2.2.1.trans (by simp only [arm64_norm, r22_3])
  have r23_4 : s4.readReg64 (.gpr 23#5) = BitVec.ofNat 64 e.1.length :=
    hcsm4.2.2.2.2.1.trans (by simp only [arm64_norm, r23_3])
  have r24_4 : s4.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
    simp only [hcsm4.2.2.2.2.2.1, arm64_norm, hcsm3.2.2.2.2.2.1,
      hcsm2.2.2.2.2.2.1, hcsm1.2.2.2.2.2.1, hx24]
  have r25_4 : s4.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 :=
    hcsm4.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r25_3])
  have r26_4 : s4.readReg64 (.gpr 26#5) = BitVec.ofNat 64 ((e :: rest).length * 48) := by
    simp only [hcsm4.2.2.2.2.2.2.2.1, arm64_norm, hcsm3.2.2.2.2.2.2.2.1,
      hcsm2.2.2.2.2.2.2.2.1, hcsm1.2.2.2.2.2.2.2.1, hx26]
  have hpc4 := hs4.pc; have hrun4 := hs4.run
  cases hwr_eq : io.wr s.fs.files e.1 e.2 with
  | none =>
    rw [hwr_eq] at hwr4; rcases hwr4 with ⟨hx0_4, _⟩
    apply m5_seq_placed hs4.inv (mid := mPcPlaced 0xbdc)
    m5_steps
    apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
      (by simp only [arm64_norm, *])
    intro hpcm5 hrunm5 hinv_m5
    let errBdc := M5ErrEntryPlaced.bdc (BitVec.ofNat 64 e.1.length) tmpPtr e.1
    have herr_st : M5LoopErrPlaced CodeOk io F0 tr0 g s0 _ n buf k
        ((storesDirs g)[k]'(by simp [hk])).changed errBdc :=
      { hk := hk, hne := hne_cur
        errRegs := ⟨by simp only [arm64_norm, r22_4], by simp only [arm64_norm, r23_4],
          ofNat_ne_zero hpos (by m5_omega)⟩
        base := mkStepPlaced hs4
          (by simpa only [mPcPlaced_eq_blkPl, errBdc, M5ErrEntryPlaced.pcOff] using hpcm5) hrunm5
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv_m5 (by simp only [calleeSavedVRegs, arm64_norm])
        x19 := by simp only [arm64_norm, r19_4]
        x24 := by simp only [arm64_norm, r24_4]
        x20 := by simp only [arm64_norm, r20_4]
        commitNone := commitFiles_entry_err hk hsplit hfiles
          (by simpa only [hdpath, pathOf_nil] using hwr_eq)
        trace := by simp only [arm64_norm]; exact htr_chain
        stdout := by simp only [arm64_norm, hout_chain] }
    have herr_env : M5LoopBErrNonemptyEnv e.1 (rustAllocEvents e.1.length 1 ++ evs_wr) :=
      ConcatEnv.append rfl hwr_env
    have herr_drop : m5ErrEntryDropEvents errBdc = rustDeallocEvents e.1.length 1 := by
      dsimp only [errBdc, m5ErrEntryDropEvents]; rw [he1_toNat]
    refine SepWPp.weaken_pre ?_
      (herr _ (rustAllocEvents e.1.length 1 ++ evs_wr) errBdc herr_env herr_drop herr_st)
    refine Entails.trans ?_ (to_err_mem (M.stepEvents (rustAllocEvents e.1.length 1 ++ evs_wr) st) _ errBdc)
    dsimp only [errBdc, M5ErrEntryPlaced.heap, fsp]
    dsimp only [st2] at hst2_eq
    rw [hst2_eq]
    simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
      RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
      RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
    have hlive_eq : A.live tmpPtr e.1.length 1 = A.repAlloc.live tmpPtr e.1.length 1 := rfl
    rw [hlive_eq]
    have hord :
        (tmpPtr ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
          A.pool lim (M.stepEvents (rustAllocEvents e.1.length 1 ++ evs_wr) st) s4 ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          (A.repAlloc.live tmpPtr e.1.length 1 ∗
            vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
            vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
              (BitVec.ofNat 64 e.2.length) ∗
            (p1 ↦ₛ e.1) ∗ invFrame) =
        (A.repAlloc.live tmpPtr e.1.length 1 ∗ (tmpPtr ↦ₛ e.1)) ∗
          (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
            vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
              (BitVec.ofNat 64 e.2.length) ∗
            (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim (M.stepEvents (rustAllocEvents e.1.length 1 ++ evs_wr) st) s4 ∗ invFrame) := by
      sep_ac_rfl
    rw [hord]
    exact sepConj_mono_left (ownedBytes_of_live_bytes A.repAlloc tmpPtr e.1 hpos (by m5_omega) htmp_ne)
  | some F' =>
    rw [hwr_eq] at hwr4; rcases hwr4 with ⟨hx0_4, hfs_4⟩
    apply m5_seq_placed hs4.inv (mid := lsρ lsRustDeallocSymCli)
    m5_steps
    apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
      (by simp only [arm64_norm, *])
    intro hpcm5 hrunm5 hinv_m5
    refine m5_call_dealloc_placed hA hstk_ext hstk64 hlay1 (by decide) hpcm5 hrunm5 hinv_m5
      (by simp only [arm64_norm, hs4.sp]) (by simp only [arm64_norm, hs4.fp])
      (by simp only [calleeSavedVRegs, arm64_norm, hs4.vregs]) hs4.spAligned
      (retOff := 0xa48) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
      (st := st2) (ptr := tmpPtr) (by simp only [arm64_norm, r22_4])
      (by simp only [arm64_norm, r23_4, he1_toNat]) (by simp only [arm64_norm]; try rfl)
      (F := vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
        vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
          (BitVec.ofNat 64 e.2.length) ∗
        (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗ invFrame)
      (by
        simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
          RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
          RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
        dsimp only [st2, fsp]
        have hord :
            (tmpPtr ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗ A.pool lim (M.stepEvents evs_wr st1) s4 ∗
              stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
              (A.live tmpPtr e.1.length 1 ∗
                vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1
                  (BitVec.ofNat 64 e.1.length) ∗
                vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
                  (BitVec.ofNat 64 e.2.length) ∗
                (p1 ↦ₛ e.1) ∗ invFrame) =
            (tmpPtr ↦ₛ e.1) ∗
              (A.live tmpPtr e.1.length 1 ∗ A.pool lim (M.stepEvents evs_wr st1) s4 ∗
                stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
                vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1
                  (BitVec.ofNat 64 e.1.length) ∗
                vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
                  (BitVec.ofNat 64 e.2.length) ∗
                (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗ invFrame) := by sep_ac_rfl
        rw [hord]
        exact Entails.trans (sepConj_mono_left (bytes_entails_memRegion tmpPtr e.1))
          (Entails.of_eq (by sep_ac_rfl))) ?_
    intro s5 hs5 hfs5 htr5 hcsm5
    have hpc5 := hs5.pc; have hrun5 := hs5.run
    apply m5_seq_placed hs5.inv (mid := mPcPlaced 0xa60)
    m5_steps
    apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
      (by simp only [arm64_norm, *])
    intro hpcm6 hrunm6 hinv_m6
    let evsOk := (rustAllocEvents e.1.length 1 ++ evs_wr) ++ rustDeallocEvents e.1.length 1
    have hevsOk : M5LoopBNonemptyStepEnv e.1 evsOk :=
      ConcatEnv.append (ConcatEnv.append rfl hwr_env) rfl
    have hst3_eq : M.stepEvents (rustDeallocEvents e.1.length 1) st2 = M.stepEvents evsOk st := by
      rw [hst2_eq]; exact (M.stepEvents_append _ _ st).symm
    refine SepWPp.weaken_pre ?_
      (hcont_a60 _ evsOk F' hevsOk hle_tot hcap_lt
        (mkStepPlaced hs5 (by simpa only [mPcPlaced_eq_blkPl] using hpcm6) hrunm6
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          hinv_m6 (by simp only [calleeSavedVRegs, arm64_norm]))
        (by simp only [arm64_norm, hfs5, hfs_4])
        hwr_eq
        (by simp only [arm64_norm]; exact htr5 ▸ htr_chain)
        (by simp only [arm64_norm, htr5, hout_chain])
        (by simp only [arm64_norm, hcsm5.1, r19_4])
        (by simp only [arm64_norm, hcsm5.2.1, r20_4])
        (by simp only [arm64_norm, hcsm5.2.2.2.2.2.1, r24_4])
        (by simp only [arm64_norm, hcsm5.2.2.2.2.2.2.1, r25_4])
        (by simp only [arm64_norm, hcsm5.2.2.2.2.2.2.2.1, r26_4]))
    refine Entails.trans ?_ (hunb_loop (M.stepEvents evsOk st) _)
    dsimp only [st2] at hst3_eq
    rw [hst3_eq]
    simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
      RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
      RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
    dsimp only [fsp]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Budget-threaded execution of `M+0x9e8 .. M+0xa48` for a single non-empty entry `e` of `Dir k`
(`d.path = []`) under `FitsEnv`, handing write failure to `herr` (`0xbdc`) or write success to
`hcont_a60` at `M+0xa60`. -/
theorem m5_loop_b_write_nonempty_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {io : IoModel} {uuidParse : UuidParser}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr v40 v48 v58 v458 v460 v468 : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {done rest : List (List (BitVec 8) × List (BitVec 8))}
    {e : List (BitVec 8) × List (BitVec 8)}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hfit : FitsEnv M lim st (M5LoopBNonemptyStepEnv e.1))
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_hook : mainFrameSize + hookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk : k < 8)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hdpath : ((storesDirs g)[k]'(by simp [hk])).path = [])
    (hpos : 0 < e.1.length)
    (hsplit : ((storesDirs g)[k]'(by simp [hk])).changed = done ++ e :: rest)
    (hs : InMainPlaced CodeOk s0 s 0x9e8)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : s.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 ((e :: rest).length * 48))
    (hfiles : commitFiles io.wr F0
      (writesBefore g k ++
        done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
      some s.fs.files)
    (htr0 : tr0 <+: s.trace)
    (hstdout : ProcessOutcome.traceStreamBytes .stdout s.trace =
      ProcessOutcome.traceStreamBytes .stdout tr0)
    (hP : P ⊢ vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ e :: rest) ∗
      m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
        curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
        v40 v48 v58 v458 v460 v468 ∗
      m5WorkRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
        outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
      ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      mainSaved s0 ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
      A.pool lim st s ∗ anyHeap)
    (herr : ∀ (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced),
      M5LoopBErrNonemptyEnv e.1 evsErr →
      m5ErrEntryDropEvents errE = rustDeallocEvents e.1.length 1 →
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k
        ((storesDirs g)[k]'(by simp [hk])).changed errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
          s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          ((storesDirs g)[k]'(by simp [hk])).changed errE)
        Q Qp oom)
    (hcont_a60 : ∀ (s_end : State) (evs : List AllocEvent) (F' : FsFiles),
      M5LoopBNonemptyStepEnv e.1 evs →
      (done ++ e :: rest).length ≤ curCap.toNat →
      curCap.toNat * 48 < 2 ^ 63 →
      InMainPlaced CodeOk s0 s_end 0xa60 →
      s_end.fs.files = F' →
      io.wr s.fs.files e.1 e.2 = some F' →
      tr0 <+: s_end.trace →
      ProcessOutcome.traceStreamBytes .stdout s_end.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      s_end.readReg64 (.gpr 19#5) = buf →
      s_end.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s_end.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s_end.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 →
      s_end.readReg64 (.gpr 26#5) = BitVec.ofNat 64 ((e :: rest).length * 48) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s_end
        (vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ e :: rest) ∗
          m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
            curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
            v40 v48 v58 v458 v460 v468 ∗
          m5WorkRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
            outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
          ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s_end ∗ anyHeap)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom :=
  m5_loop_b_write_nonempty_of_placed (curPtr := curPtr) hA hc
    ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio)
    hfit hstk_ext hstk_hook hstk64 hk hpaths hdpath hpos hsplit hs
    hx19 hx20 hx24 hx25 hx26 hfiles htr0 hstdout hP herr hcont_a60

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBWritePlacedBudget
