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
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5AfterPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5CallsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPathPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopDropPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlaced
meta import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common

/-!
# Budget-Threaded M5 Inner Loop A Iteration (`M+0x8fc .. M+0x9b4`, Block `617`)

Budget-threaded verification of one iteration (`m5_loop_a_one_placed`) of `main`'s inner commit
Loop A (`d.path ≠ []`) on Block `617` under `FitsEnv`, advancing `A.pool` by `M5LoopAStepEnv` (or
`M5LoopAErrStepEnv` on `write_file` failure).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.RustHeap (LayoutOk RustAlloc vecBuf vecHeader)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (lsRustDeallocSymCli lsWriteFileSym)
open CryptoVerification.SignalSession.Cli (StoresGhost dirEntryAt pathOf)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtM5LoopPlaced InMainPlaced IoModel LsCodeInv M5ErrEntryPlaced M5LoopErrPlaced argsBuf
   commitFiles m5ErrMemPlaced m5LoopMemPlaced mPcPlaced mainFrameSize mainSaved ownedBytes
   storesDirs writesBefore)
open CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
  (bytes_entails_memRegion commitFiles_entry_err commitFiles_entry_ok dir_entry_path_ok_len
   entryBorrowRest m5OwnedBytesRest m5ScratchPlaced m5WorkRestPlaced m5Work_exit_to_err_placed
   m5_run_placed m5_seq_placed mPcPlaced_eq_blkPl mkStepPlaced ownedBytes_borrow pathOf_ne_nil
   sep_anyHeap_absorb vecBuf_borrow_eq vecBuf_unborrow writesBefore_entry_done)
open scoped CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   fitsEvents_append rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (WriteFileEnv writeFileEnv_nil)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv IterSeqEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced mainIoBoundedPlaced_iff_mainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced MainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5AfterPlacedBudget.LoopDrop
  (m5_after_entries_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5CallsPlacedBudget
  (m5_call_dealloc_placed m5_call_write_file_of_placed m5_call_write_file_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPathPlacedBudget
  (M5LoopABuildPathEnv m5LoopABuildPathEvents m5LoopAPathCap m5_loop_a_build_path_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopDropPlacedBudget
  (m5ErrEntryDropEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
  (argsBuf_atState_eq_repAlloc m5ErrCellsPlaced_atState_eq_repAlloc
   m5ErrEntryPlaced_heap_atState_eq_repAlloc ownedBytes_atState_eq_repAlloc)

attribute [local irreducible] SepWPp Program.fetch Program.externAt?
attribute [local arm64_norm]
  RustCliAllocBudget.pool_setPC
  RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState
  RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32
  RustCliAllocBudget.pool_writeReg

private theorem bv_mul48_sub48_a (n : Nat) :
    BitVec.ofNat 64 ((n + 1) * 48) - 48#64 = BitVec.ofNat 64 (n * 48) := by
  have heq : (n + 1) * 48 = n * 48 + 48 := by omega
  rw [heq, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel (BitVec.ofNat 64 (n * 48)) 48#64

private theorem bv_mul48_add_neg48_a (n : Nat) :
    BitVec.ofNat 64 ((n + 1) * 48) + (-48#64) = BitVec.ofNat 64 (n * 48) := by
  rw [← BitVec.sub_eq_add_neg]
  exact bv_mul48_sub48_a n

private theorem addr_advance_entry_a {α : Type} (curPtr : BitVec 64) (done : List α) (e : α) :
    (curPtr + BitVec.ofNat 64 (done.length * 48) + 40#64) + 48#64 =
      curPtr + BitVec.ofNat 64 ((done ++ [e]).length * 48) + 0x28#64 := by
  have hlen_add : (done ++ [e]).length * 48 = done.length * 48 + 48 := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [hlen_add, BitVec.ofNat_add]; bv_omega

set_option maxHeartbeats 1600000 in
private theorem entryBorrowRest_pure_a (A : RustAlloc) (curCap curPtr : BitVec 64)
    (done : List (List (BitVec 8) × List (BitVec 8)))
    (e : List (BitVec 8) × List (BitVec 8))
    (rest : List (List (BitVec 8) × List (BitVec 8)))
    (c1 p1 c2 p2 : BitVec 64) :
    entryBorrowRest A curCap curPtr done e rest c1 p1 c2 p2 =
      ⌜e.2.length < 2 ^ 63 ∧
        (done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63⌝ ∗
        entryBorrowRest A curCap curPtr done e rest c1 p1 c2 p2 := by
  apply Entails.antisymm
  · unfold entryBorrowRest
    apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
    exact Entails.pure_right ⟨Nat.lt_of_le_of_lt h2.1 h2.2.1, h3.1, h3.2.1⟩
      (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _))
  · apply Entails.pure_left; intro _; exact Entails.refl _

private theorem vecBuf_dirEntryAt_atState_eq_repAlloc {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (cap ptr : BitVec 64) (es : List (List (BitVec 8) × List (BitVec 8))) :
    vecBuf (A.atState lim st s) 48 8 (dirEntryAt (A.atState lim st s)) cap ptr es =
      vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr es :=
  rfl

/-- Error-exit allocator event envelope up to `M+0xbcc` for one entry `(dir, name)` in Loop A
(`m5_loop_a_build_path_placed` followed by `write_file`). -/
def M5LoopAErrStepEnv (dir name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ConcatEnv (M5LoopABuildPathEnv dir name) (WriteFileEnv (pathOf dir name).length) evs

example : ∃ evs, M5LoopAErrStepEnv [0x61#8] [0x62#8] evs :=
  ⟨m5LoopABuildPathEvents [0x61#8] [0x62#8] ++ [],
    ConcatEnv.append rfl (writeFileEnv_nil (pathOf [0x61#8] [0x62#8]).length)⟩

/-- Complete single-entry allocator event envelope in Loop A (`m5_loop_a_build_path_placed` +
`write_file` + `__rust_dealloc(capFinal, 1)`). -/
def M5LoopAStepEnv (dir name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ConcatEnv (M5LoopAErrStepEnv dir name)
    (· = rustDeallocEvents (m5LoopAPathCap dir name) 1) evs

example : ∃ evs, M5LoopAStepEnv [0x61#8] [0x62#8] evs :=
  ⟨(m5LoopABuildPathEvents [0x61#8] [0x62#8] ++ []) ++
      rustDeallocEvents (m5LoopAPathCap [0x61#8] [0x62#8]) 1,
    ConcatEnv.append
      (ConcatEnv.append rfl (writeFileEnv_nil (pathOf [0x61#8] [0x62#8]).length))
      rfl⟩

/-- Allocator event envelope for committing `entries` in Loop A followed by `m5_after_entries_placed`
deallocations (`FreeOnlyEvs`) into `AtM5LoopPlaced … (k + 1)`. -/
def M5LoopARestOkEnv (dir : List (BitVec 8))
    (entries : List (List (BitVec 8) × List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  SeqEnv (IterSeqEnv (fun e => M5LoopAStepEnv dir e.1) entries) FreeOnlyEvs evs

example : ∃ evs, M5LoopARestOkEnv [0x61#8] [] evs :=
  ⟨[], Or.inl rfl⟩

/-- Error-exit allocator event envelope at `M+0xbcc` across remaining entries `entries` in Loop A,
tying `m5ErrEntryDropEvents errE` to the failing entry's `m5LoopAPathCap` so post-error cleanup
completes `M5LoopAStepEnv`. -/
def M5LoopARestErrEnv (dir : List (BitVec 8)) (errE : M5ErrEntryPlaced) :
    List (List (BitVec 8) × List (BitVec 8)) → List AllocEvent → Prop
  | [], _ => False
  | e :: rest, evs =>
      (M5LoopAErrStepEnv dir e.1 evs ∧
        m5ErrEntryDropEvents errE = rustDeallocEvents (m5LoopAPathCap dir e.1) 1) ∨
      ConcatEnv (M5LoopAStepEnv dir e.1) (M5LoopARestErrEnv dir errE rest) evs

example :
    ∃ evs,
      M5LoopARestErrEnv [0x61#8]
        (.bdc (BitVec.ofNat 64 (m5LoopAPathCap [0x61#8] [0x62#8])) 1#64 [])
        [([0x62#8], [])] evs :=
  ⟨m5LoopABuildPathEvents [0x61#8] [0x62#8] ++ [],
    Or.inl ⟨ConcatEnv.append rfl (writeFileEnv_nil (pathOf [0x61#8] [0x62#8]).length), rfl⟩⟩

set_option maxHeartbeats 1600000 in
/-- `{StdinEnv ReadEnv}`-parametric budget-threaded single iteration of inner loop A (`d.path ≠ []`)
for head entry `e` and tail `rest` on Block `617` under `FitsEnv`. -/
theorem m5_loop_a_one_of_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr dPathPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {e : List (BitVec 8) × List (BitVec 8)}
    {rest done : List (List (BitVec 8) × List (BitVec 8))}
    {s0 s : State} {v48 v58 v458 v460 v468 : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hk : k < 8)
    (hfit : FitsEnv M lim st (M5LoopARestOkEnv ((storesDirs g)[k]'(by simp [hk])).path (e :: rest)))
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_hook : mainFrameSize + hookStack ≤ stk)
    (hstk_res : mainFrameSize + resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hd_ne : ((storesDirs g)[k]'(by simp [hk])).path ≠ [])
    (herr : ∀ (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced),
      M5LoopARestErrEnv ((storesDirs g)[k]'(by simp [hk])).path errE (e :: rest) evsErr →
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k
        ((storesDirs g)[k]'(by simp [hk])).changed errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
          s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          ((storesDirs g)[k]'(by simp [hk])).changed errE)
        Q Qp oom)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      M5LoopARestOkEnv ((storesDirs g)[k]'(by simp [hk])).path (e :: rest) evs →
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
        (m5LoopMemPlaced (A.atState lim (M.stepEvents evs st) sf)
          s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
        Q Qp oom)
    (hsplit : ((storesDirs g)[k]'(by simp [hk])).changed = done ++ e :: rest)
    (hs : InMainPlaced CodeOk s0 s 0x8fc)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 ((e :: rest).length * 48))
    (hx27 : s.readReg64 (.gpr 27#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).path.length)
    (hfiles : commitFiles io.wr F0
      (writesBefore g k ++
        done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
      some s.fs.files)
    (htr0 : tr0 <+: s.trace)
    (hstdout : ProcessOutcome.traceStreamBytes .stdout s.trace =
      ProcessOutcome.traceStreamBytes .stdout tr0)
    (hP : P ⊢ (dPathPtr ↦ᵣ ((storesDirs g)[k]'(by simp [hk])).path) ∗
      vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ e :: rest) ∗
      m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
        curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
        dPathPtr v48 v58 v458 v460 v468 ∗
      m5WorkRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
        outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
      ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      mainSaved s0 ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
      A.pool lim st s ∗ anyHeap)
    (hmore : ∀ (s' : State) (evs1 : List AllocEvent) (v48' v458' v460' v468' : BitVec 64)
        (P' : SepProp),
      rest ≠ [] →
      M5LoopAStepEnv ((storesDirs g)[k]'(by simp [hk])).path e.1 evs1 →
      FitsEnv M lim (M.stepEvents evs1 st)
        (M5LoopARestOkEnv ((storesDirs g)[k]'(by simp [hk])).path rest) →
      ((storesDirs g)[k]'(by simp [hk])).changed = (done ++ [e]) ++ rest →
      InMainPlaced CodeOk s0 s' 0x8fc →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (rest.length * 48) →
      s'.readReg64 (.gpr 27#5) = curPtr + BitVec.ofNat 64 ((done ++ [e]).length * 48) + 0x28#64 →
      s'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).path.length →
      commitFiles io.wr F0
        (writesBefore g k ++
          (done ++ [e]).map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
        some s'.fs.files →
      tr0 <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      (P' ⊢ (dPathPtr ↦ᵣ ((storesDirs g)[k]'(by simp [hk])).path) ∗
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr ((done ++ [e]) ++ rest) ∗
        m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
          curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
          dPathPtr v48' v58 v458' v460' v468' ∗
        m5WorkRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
          outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
        ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim (M.stepEvents evs1 st) s' ∗ anyHeap) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s' P' Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  change k < (storesDirs g).length at hk
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  let base := curPtr + BitVec.ofNat 64 (done.length * 48)
  let dir := ((storesDirs g)[k]'hk).path
  have hne_cur : ((storesDirs g)[k]'hk).changed ≠ [] := by
    intro h0; rw [hsplit] at h0; simp at h0
  have he_mem : e ∈ ((storesDirs g)[k]'hk).changed := by
    rw [hsplit]; exact List.mem_append_right _ (.head _)
  have ⟨he_ok, he_lt⟩ :
      io.pathOk (pathOf ((storesDirs g)[k]'hk).path e.1) ∧
        (pathOf ((storesDirs g)[k]'hk).path e.1).length < 2 ^ 32 :=
    dir_entry_path_ok_len hk hpaths he_mem
  have hp_eq := pathOf_ne_nil hd_ne e.1
  have hp_len :
      (pathOf ((storesDirs g)[k]'hk).path e.1).length =
        ((storesDirs g)[k]'hk).path.length + 1 + e.1.length := by
    rw [hp_eq]; simp; omega
  have hfit_iter :
      FitsEnv M lim st
        (SeqEnv (M5LoopAStepEnv dir e.1)
          (IterSeqEnv (fun x => M5LoopAStepEnv dir x.1) rest)) :=
    hfit.seq_left
  have hfit_step : FitsEnv M lim st (M5LoopAStepEnv dir e.1) :=
    hfit_iter.seq_left
  have hfit_bp : FitsEnv M lim st (M5LoopABuildPathEnv dir e.1) := by
    intro evs_bp hbp
    let evs_d := rustDeallocEvents (m5LoopAPathCap dir e.1) 1
    have hstep_ev : M5LoopAStepEnv dir e.1 ((evs_bp ++ []) ++ evs_d) :=
      ConcatEnv.append (ConcatEnv.append hbp (writeFileEnv_nil (pathOf dir e.1).length)) rfl
    have hf := hfit_step ((evs_bp ++ []) ++ evs_d) hstep_ev
    rw [List.append_nil] at hf
    exact ((fitsEvents_append M lim evs_bp evs_d st).mp hf).1
  refine SepWPp.weaken_pre hP ?_
  rw [vecBuf_borrow_eq A.repAlloc curCap curPtr done e rest]
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun c1 => ?_
  refine SepWPp.exists_elim fun p1 => ?_
  refine SepWPp.exists_elim fun c2 => ?_
  refine SepWPp.exists_elim fun p2 => ?_
  rw [entryBorrowRest_pure_a A.repAlloc curCap curPtr done e rest c1 p1 c2 p2]
  have hpure_front :
      (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
        ((vecHeader base c1 p1 (BitVec.ofNat 64 e.1.length) ∗
          vecHeader (base + 24#64) c2 p2 (BitVec.ofNat 64 e.2.length) ∗
          (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
          (⌜e.2.length < 2 ^ 63 ∧
            (done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63⌝ ∗
            entryBorrowRest A.repAlloc curCap curPtr done e rest c1 p1 c2 p2)) ∗
          m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
            dPathPtr v48 v58 v458 v460 v468 ∗
          m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
          ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ anyHeap) =
      ⌜e.2.length < 2 ^ 63 ∧
        (done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63⌝ ∗
      ((dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
        vecHeader base c1 p1 (BitVec.ofNat 64 e.1.length) ∗
        vecHeader (base + 24#64) c2 p2 (BitVec.ofNat 64 e.2.length) ∗
        (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
        entryBorrowRest A.repAlloc curCap curPtr done e rest c1 p1 c2 p2 ∗
        m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
          dPathPtr v48 v58 v458 v460 v468 ∗
        m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
        ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ anyHeap) := by
    dsimp only [base]; sep_ac_rfl
  rw [hpure_front]
  refine SepWPp.pure_elim fun ⟨he2_lt63, hle_tot, hcap_lt⟩ => ?_
  have he2_toNat : (BitVec.ofNat 64 e.2.length).toNat = e.2.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by m5_omega)]
  let keptScratch : SepProp :=
    ((fsp + 0x20#64) ↦₆₄ curCap) ∗ ((fsp + 0x28#64) ↦₆₄ curPtr) ∗
      ((fsp + 0x30#64) ↦₆₄ (fsp + 0x1c8#64)) ∗ ((fsp + 0x38#64) ↦₆₄ BitVec.ofNat 64 (k + 1))
  let outerInv : SepProp :=
    keptScratch ∗ entryBorrowRest A.repAlloc curCap curPtr done e rest c1 p1 c2 p2 ∗
      m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
      ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗ anyHeap
  refine m5_loop_a_build_path_placed (base := base) (dPathPtr := dPathPtr) (c1 := c1) (p1 := p1)
    (v48 := v48) (v58 := v58) (v458 := v458) (v460 := v460) (v468 := v468)
    hA hc hfit_bp hstk_ext hstk_res hstk64
    hd_ne he_lt
    hs hx27 hx28
    (F := vecHeader (base + 24#64) c2 p2 (BitVec.ofNat 64 e.2.length) ∗ (p2 ↦ₛ e.2) ∗ outerInv)
    (by
      dsimp only [m5ScratchPlaced, keptScratch, outerInv, fsp, base]
      exact Entails.of_eq (by sep_ac_rfl))
    ?_
  intro sm evs_bp capFinal ptrFinal v458' v460' v468'
    hbp hcapF_eq hcapF_pos hpath_le hcapF_lt hptrF_ne hsm hfsm htrm
    m19 m20 m21 m22 m23 m24 m25 m26 m27 m28
  have hfit_wf :
      FitsEnv M lim (M.stepEvents evs_bp st)
        (WriteFileEnv (pathOf ((storesDirs g)[k]'hk).path e.1).length) := by
    intro evs_wf hwf
    let evs_d := rustDeallocEvents (m5LoopAPathCap dir e.1) 1
    have hstep_ev : M5LoopAStepEnv dir e.1 ((evs_bp ++ evs_wf) ++ evs_d) :=
      ConcatEnv.append (ConcatEnv.append hbp hwf) rfl
    have hf := hfit_step ((evs_bp ++ evs_wf) ++ evs_d) hstep_ev
    have hf12 := ((fitsEvents_append M lim (evs_bp ++ evs_wf) evs_d st).mp hf).1
    exact ((fitsEvents_append M lim evs_bp evs_wf st).mp hf12).2
  have off_m8 : (base + 40#64) + (-8#64) = base + 32#64 := by rw [BitVec.add_assoc]; rfl
  have off_hdr2 :
      vecHeader (base + 24#64) c2 p2 (BitVec.ofNat 64 e.2.length) =
        ((base + 24#64) ↦₆₄ c2) ∗ ((base + 32#64) ↦₆₄ p2) ∗
          (((base + 32#64) + 8#64) ↦₆₄ BitVec.ofNat 64 e.2.length) := by
    unfold vecHeader
    have h1 : (base + 24#64) + 8#64 = base + 32#64 := by rw [BitVec.add_assoc]; rfl
    have h2 : (base + 24#64) + 16#64 = (base + 32#64) + 8#64 := by
      simp only [BitVec.add_assoc]; rfl
    rw [h1, h2]
  have hadd_path_toNat :
      (BitVec.ofNat 64 (((storesDirs g)[k]'hk).path.length + 1) +
          BitVec.ofNat 64 e.1.length).toNat =
        (pathOf ((storesDirs g)[k]'hk).path e.1).length := by
    rw [← BitVec.ofNat_add, ← hp_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by m5_omega)]
  have hpack_all : ∀ {st' : M.σ} {sp_st : State},
      vecHeader base c1 p1 (BitVec.ofNat 64 e.1.length) ∗
        vecHeader (base + 24#64) c2 p2 (BitVec.ofNat 64 e.2.length) ∗
        (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗ (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
        ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
        ((fsp + 0x58#64) ↦₆₄ v58) ∗
        ((fsp + 0x458#64) ↦₆₄ v458') ∗ ((fsp + 0x460#64) ↦₆₄ v460') ∗
        ((fsp + 0x468#64) ↦₆₄ v468') ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st' sp_st ∗ outerInv ⊢
      (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ e :: rest) ∗
        m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
          dPathPtr p1 v58 v458' v460' v468' ∗
        m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
        ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st' sp_st ∗ anyHeap := by
    intro st' sp_st
    dsimp only [outerInv, keptScratch, m5ScratchPlaced, base]
    refine Entails.trans (Entails.of_eq (Q :=
      (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
        vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
          (BitVec.ofNat 64 e.2.length) ∗
        (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
        entryBorrowRest A.repAlloc curCap curPtr done e rest c1 p1 c2 p2) ∗
      ((dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
        (((fsp + 0x20#64) ↦₆₄ curCap) ∗ ((fsp + 0x28#64) ↦₆₄ curPtr) ∗
          ((fsp + 0x30#64) ↦₆₄ (fsp + 0x1c8#64)) ∗ ((fsp + 0x38#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
          ((fsp + 0x58#64) ↦₆₄ v58) ∗
          ((fsp + 0x458#64) ↦₆₄ v458') ∗ ((fsp + 0x460#64) ↦₆₄ v460') ∗
          ((fsp + 0x468#64) ↦₆₄ v468')) ∗
        m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
        ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st' sp_st ∗ anyHeap))
      (by sep_ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono_left (vecBuf_unborrow A.repAlloc curCap curPtr done e rest c1 p1 c2 p2))
      (Entails.of_eq (by sep_ac_rfl))
  rw [ownedBytes_borrow A.repAlloc capFinal ptrFinal
    (BitVec.ofNat 64 (pathOf ((storesDirs g)[k]'hk).path e.1).length)
    (pathOf ((storesDirs g)[k]'hk).path e.1)]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun _ => ?_
  have hpcm := hsm.pc; have hrunm := hsm.run
  refine m5_run_placed hsm.inv (mid := lsρ lsWriteFileSym)
    (P0 := ((base + 32#64) ↦₆₄ p2) ∗ (((base + 32#64) + 8#64) ↦₆₄ BitVec.ofNat 64 e.2.length))
    (F := (ptrFinal ↦ₛ pathOf ((storesDirs g)[k]'hk).path e.1) ∗ (p2 ↦ₛ e.2) ∗
      stackAt fsp (stk - mainFrameSize) ∗
      m5OwnedBytesRest A.repAlloc capFinal ptrFinal (pathOf ((storesDirs g)[k]'hk).path e.1) ∗
      vecHeader base c1 p1 (BitVec.ofNat 64 e.1.length) ∗
      ((base + 24#64) ↦₆₄ c2) ∗
      (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗ (p1 ↦ₛ e.1) ∗
      ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
      ((fsp + 0x58#64) ↦₆₄ v58) ∗
      ((fsp + 0x458#64) ↦₆₄ v458') ∗ ((fsp + 0x460#64) ↦₆₄ v460') ∗
      ((fsp + 0x468#64) ↦₆₄ v468') ∗ A.pool lim (M.stepEvents evs_bp st) sm ∗ outerInv)
    (by rw [off_hdr2]; dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, mPcPlaced_eq_blkPl, hpcm, m27, off_m8])
    (by simp only [arm64_norm, hrunm])
  intro hpcm_w hrunm_w hinv_w
  refine m5_call_write_file_of_placed hio hstk_hook hstk64 hpcm_w hrunm_w hinv_w
    (by simp only [arm64_norm, hsm.sp]) (by simp only [arm64_norm, hsm.fp])
    (by simp only [calleeSavedVRegs, arm64_norm, hsm.vregs]) hsm.spAligned
    (retOff := 0x990) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
    (pathA := ptrFinal) (path := pathOf ((storesDirs g)[k]'hk).path e.1) (buf := p2) (bs := e.2)
    (by simp only [arm64_norm, m22])
    (by simp only [arm64_norm, m25, m21]; dsimp only [dir]; exact hadd_path_toNat)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, he2_toNat]) he_lt he_ok hfit_wf
    (F := m5OwnedBytesRest A.repAlloc capFinal ptrFinal (pathOf ((storesDirs g)[k]'hk).path e.1) ∗
      vecHeader base c1 p1 (BitVec.ofNat 64 e.1.length) ∗
      vecHeader (base + 24#64) c2 p2 (BitVec.ofNat 64 e.2.length) ∗
      (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗ (p1 ↦ₛ e.1) ∗
      ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
      ((fsp + 0x58#64) ↦₆₄ v58) ∗
      ((fsp + 0x458#64) ↦₆₄ v458') ∗ ((fsp + 0x460#64) ↦₆₄ v460') ∗
      ((fsp + 0x468#64) ↦₆₄ v468') ∗ outerInv)
    (by
      rw [off_hdr2]; dsimp only [fsp]
      simp only [arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  intro sw evs_wf hsw hwf hwrw htrw houtw hcsmw
  have hsm_files : sm.fs.files = s.fs.files := by rw [hfsm]
  simp only [arm64_norm, hsm_files] at hwrw
  have htr_w : tr0 <+: sw.trace := htr0.trans (htrm ▸ by simpa only [arm64_norm] using htrw)
  have hout_w :
      ProcessOutcome.traceStreamBytes .stdout sw.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 := by
    simpa only [arm64_norm, htrm, hstdout] using houtw
  have w19 : sw.readReg64 (.gpr 19#5) = buf := hcsmw.1.trans (by simp only [arm64_norm, m19, hx19])
  have w20 : sw.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'hk).changed.length :=
    hcsmw.2.1.trans (by simp only [arm64_norm, m20, hx20])
  have w22 : sw.readReg64 (.gpr 22#5) = ptrFinal :=
    hcsmw.2.2.2.1.trans (by simp only [arm64_norm, m22])
  have w23 : sw.readReg64 (.gpr 23#5) = capFinal :=
    hcsmw.2.2.2.2.1.trans (by simp only [arm64_norm, m23])
  have w24 : sw.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n :=
    hcsmw.2.2.2.2.2.1.trans (by simp only [arm64_norm, m24, hx24])
  have w26 : sw.readReg64 (.gpr 26#5) = BitVec.ofNat 64 ((e :: rest).length * 48) :=
    hcsmw.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, m26, hx26])
  have w27 : sw.readReg64 (.gpr 27#5) = base + 40#64 :=
    hcsmw.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, m27])
  have w28 : sw.readReg64 (.gpr 28#5) = BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length :=
    hcsmw.2.2.2.2.2.2.2.2.2.1.trans (by dsimp only [dir] at m28; simp only [arm64_norm, m28])
  have hpcw := hsw.pc; have hrunw := hsw.run
  have hcapF_ne : capFinal ≠ 0#64 := by
    intro h0; subst h0; change 0 < 0 at hcapF_pos; m5_omega
  cases hwr_eq : io.wr s.fs.files (pathOf ((storesDirs g)[k]'hk).path e.1) e.2 with
  | none =>
    rw [hwr_eq] at hwrw; rcases hwrw with ⟨hx0_w, _⟩
    apply m5_seq_placed hsw.inv (mid := mPcPlaced 0xbcc)
    m5_steps
    apply SepWP.done
      (by simp only [arm64_norm, mPcPlaced_eq_blkPl, hpcw, hx0_w])
      (by simp only [arm64_norm, hrunw])
    intro hpcm_e hrunm_e hinv_e
    let errBcc := M5ErrEntryPlaced.bcc capFinal ptrFinal (pathOf ((storesDirs g)[k]'hk).path e.1)
    let evsErr := evs_bp ++ evs_wf
    have herr_env : M5LoopARestErrEnv dir errBcc (e :: rest) evsErr := by
      refine Or.inl ⟨ConcatEnv.append hbp hwf, ?_⟩
      simp only [m5ErrEntryDropEvents, errBcc, hcapF_ne, ↓reduceIte, hcapF_eq]
    have herr_st : M5LoopErrPlaced CodeOk io F0 tr0 g s0 _ n buf k
        ((storesDirs g)[k]'hk).changed errBcc :=
      { hk := hk, hne := hne_cur
        errRegs := ⟨by simp only [arm64_norm, w22], by simp only [arm64_norm, w23]⟩
        base := mkStepPlaced hsw
          (by simpa only [mPcPlaced_eq_blkPl, errBcc, M5ErrEntryPlaced.pcOff] using hpcm_e) hrunm_e
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv_e (by simp only [calleeSavedVRegs, arm64_norm])
        x19 := by simp only [arm64_norm, w19], x24 := by simp only [arm64_norm, w24]
        x20 := by simp only [arm64_norm, w20]
        commitNone := commitFiles_entry_err hk hsplit hfiles hwr_eq
        trace := by simp only [arm64_norm]; exact htr_w
        stdout := by simp only [arm64_norm, hout_w] }
    refine SepWPp.weaken_pre ?_ (herr _ evsErr errBcc herr_env herr_st)
    have hownF :
        (ptrFinal ↦ₛ pathOf ((storesDirs g)[k]'hk).path e.1) ∗
          m5OwnedBytesRest A.repAlloc capFinal ptrFinal (pathOf ((storesDirs g)[k]'hk).path e.1) ⊢
          errBcc.heap A.repAlloc := by
      dsimp only [errBcc, M5ErrEntryPlaced.heap]
      rw [ownedBytes_borrow A.repAlloc capFinal ptrFinal
        (BitVec.ofNat 64 (pathOf ((storesDirs g)[k]'hk).path e.1).length)
        (pathOf ((storesDirs g)[k]'hk).path e.1)]
      exact Entails.pure_right ⟨rfl, hpath_le, hcapF_lt, hptrF_ne⟩ (Entails.refl _)
    have hst_err :
        M.stepEvents evs_wf (M.stepEvents evs_bp st) = M.stepEvents evsErr st :=
      (M.stepEvents_append evs_bp evs_wf st).symm
    rw [hst_err]
    refine Entails.trans (Entails.of_eq (Q :=
      ((ptrFinal ↦ₛ pathOf ((storesDirs g)[k]'hk).path e.1) ∗
        m5OwnedBytesRest A.repAlloc capFinal ptrFinal (pathOf ((storesDirs g)[k]'hk).path e.1)) ∗
      (vecHeader base c1 p1 (BitVec.ofNat 64 e.1.length) ∗
        vecHeader (base + 24#64) c2 p2 (BitVec.ofNat 64 e.2.length) ∗
        (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗ (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
        ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
        ((fsp + 0x58#64) ↦₆₄ v58) ∗
        ((fsp + 0x458#64) ↦₆₄ v458') ∗ ((fsp + 0x460#64) ↦₆₄ v460') ∗
        ((fsp + 0x468#64) ↦₆₄ v468') ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim (M.stepEvents evsErr st) sw ∗ outerInv))
      (by dsimp only [fsp]; sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hownF hpack_all) ?_
    have hexit := m5Work_exit_to_err_placed A.repAlloc fsp outCap outPtr
      (BitVec.ofNat 64 out.length) inCap inPtr curCap curPtr g hk
      dPathPtr p1 v58 v458' v460' v468'
    simp only [m5ErrMemPlaced, m5ErrEntryPlaced_heap_atState_eq_repAlloc,
      vecBuf_dirEntryAt_atState_eq_repAlloc, ownedBytes_atState_eq_repAlloc,
      argsBuf_atState_eq_repAlloc, m5ErrCellsPlaced_atState_eq_repAlloc,
      RustCliAllocBudget.atState_pool, arm64_norm]
    dsimp only [fsp] at hexit ⊢
    rw [← hsplit]
    refine Entails.trans (Entails.of_eq (Q :=
      (m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) curCap curPtr
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
          dPathPtr p1 v58 v458' v460' v468' ∗
        m5WorkRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
          outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k) ∗
      ((dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗ anyHeap) ∗
      (errBcc.heap A.repAlloc ∗
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr ((storesDirs g)[k]'hk).changed ∗
        ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim (M.stepEvents evsErr st) sw))
      (by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hexit (sepConj_mono_left (sep_anyHeap_absorb _)))
      (Entails.of_eq (by sep_ac_rfl))
  | some F' =>
    rw [hwr_eq] at hwrw; rcases hwrw with ⟨hx0_w, hfs_w⟩
    have hcapF_ne0 : capFinal ≠ 0 := hcapF_ne
    have hlayF : LayoutOk capFinal.toNat 1 := ⟨hcapF_pos, ⟨0, rfl⟩, by m5_omega⟩
    apply m5_seq_placed hsw.inv (mid := lsρ lsRustDeallocSymCli)
    m5_steps
    apply SepWP.done
      (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *])
      (by simp only [arm64_norm, hrunw])
    intro hpcm_d hrunm_d hinv_d
    have hfreeF :
        (ptrFinal ↦ₛ pathOf ((storesDirs g)[k]'hk).path e.1) ∗
          m5OwnedBytesRest A.repAlloc capFinal ptrFinal (pathOf ((storesDirs g)[k]'hk).path e.1) ⊢
          A.live ptrFinal capFinal.toNat 1 ∗ memRegion ptrFinal capFinal.toNat := by
      simp only [m5OwnedBytesRest, hcapF_ne0, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
      have hcapF_ge : (pathOf ((storesDirs g)[k]'hk).path e.1).length ≤ capFinal.toNat := hpath_le
      have hmr :
          memRegion ptrFinal capFinal.toNat =
            memRegion ptrFinal (pathOf ((storesDirs g)[k]'hk).path e.1).length ∗
              memRegion (ptrFinal + BitVec.ofNat 64 (pathOf ((storesDirs g)[k]'hk).path e.1).length)
                (capFinal.toNat - (pathOf ((storesDirs g)[k]'hk).path e.1).length) := by
        conv =>
          lhs
          rw [show capFinal.toNat =
            (pathOf ((storesDirs g)[k]'hk).path e.1).length +
              (capFinal.toNat - (pathOf ((storesDirs g)[k]'hk).path e.1).length) from
            (Nat.add_sub_of_le hcapF_ge).symm]
        exact ProofLib.memRegion_split ptrFinal (pathOf ((storesDirs g)[k]'hk).path e.1).length
          (capFinal.toNat - (pathOf ((storesDirs g)[k]'hk).path e.1).length) (by m5_omega)
      rw [hmr]
      refine Entails.trans (Entails.of_eq (Q :=
        (ptrFinal ↦ₛ pathOf ((storesDirs g)[k]'hk).path e.1) ∗
          (A.live ptrFinal capFinal.toNat 1 ∗
            memRegion (ptrFinal + BitVec.ofNat 64 (pathOf ((storesDirs g)[k]'hk).path e.1).length)
              (capFinal.toNat - (pathOf ((storesDirs g)[k]'hk).path e.1).length)))
        (by sep_ac_rfl)) ?_
      exact Entails.trans
        (sepConj_mono_left (bytes_entails_memRegion ptrFinal (pathOf ((storesDirs g)[k]'hk).path e.1)))
        (Entails.of_eq (by sep_ac_rfl))
    refine m5_call_dealloc_placed hA hstk_ext hstk64 hlayF (by decide) hpcm_d hrunm_d hinv_d
      (by simp only [arm64_norm, hsw.sp]) (by simp only [arm64_norm, hsw.fp])
      (by simp only [calleeSavedVRegs, arm64_norm, hsw.vregs]) hsw.spAligned
      (retOff := 0x9a8) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, *]; try m5_bv_omega)
      (ptr := ptrFinal) (by simp only [arm64_norm, w22])
      (by simp only [arm64_norm, w23]) (by simp only [arm64_norm]; try rfl)
      (F := vecHeader base c1 p1 (BitVec.ofNat 64 e.1.length) ∗
        vecHeader (base + 24#64) c2 p2 (BitVec.ofNat 64 e.2.length) ∗
        (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗ (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
        ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
        ((fsp + 0x58#64) ↦₆₄ v58) ∗
        ((fsp + 0x458#64) ↦₆₄ v458') ∗ ((fsp + 0x460#64) ↦₆₄ v460') ∗
        ((fsp + 0x468#64) ↦₆₄ v468') ∗ outerInv)
      (by
        try dsimp only [fsp]
        simp only [arm64_norm]
        refine Entails.trans (Entails.of_eq (Q :=
          ((ptrFinal ↦ₛ pathOf ((storesDirs g)[k]'hk).path e.1) ∗
            m5OwnedBytesRest A.repAlloc capFinal ptrFinal (pathOf ((storesDirs g)[k]'hk).path e.1)) ∗
          (A.pool lim (M.stepEvents evs_wf (M.stepEvents evs_bp st)) sw ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            vecHeader base c1 p1 (BitVec.ofNat 64 e.1.length) ∗
            vecHeader (base + 24#64) c2 p2 (BitVec.ofNat 64 e.2.length) ∗
            (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗ (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
            (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x40#64) ↦₆₄ dPathPtr) ∗
            (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x48#64) ↦₆₄ p1) ∗
            (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x58#64) ↦₆₄ v58) ∗
            (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x458#64) ↦₆₄ v458') ∗
            (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x460#64) ↦₆₄ v460') ∗
            (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x468#64) ↦₆₄ v468') ∗ outerInv))
          (by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hfreeF) (Entails.of_eq (by sep_ac_rfl))) ?_
    intro sd hsd hfsd htrd hcsmd
    let evs1 := (evs_bp ++ evs_wf) ++ rustDeallocEvents (m5LoopAPathCap dir e.1) 1
    have hstep1 : M5LoopAStepEnv dir e.1 evs1 :=
      ConcatEnv.append (ConcatEnv.append hbp hwf) rfl
    have hst1 :
        M.stepEvents (rustDeallocEvents capFinal.toNat 1)
          (M.stepEvents evs_wf (M.stepEvents evs_bp st)) =
          M.stepEvents evs1 st := by
      dsimp only [evs1]
      rw [hcapF_eq, M.stepEvents_append, M.stepEvents_append]
    rw [hst1]
    have hfiles_next :
        commitFiles io.wr F0
          (writesBefore g k ++
            (done ++ [e]).map (fun x => (pathOf ((storesDirs g)[k]'hk).path x.1, x.2))) =
        some F' :=
      commitFiles_entry_ok hk hfiles hwr_eq
    refine SepWPp.weaken_pre
      (Entails.trans (by dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl)) hpack_all) ?_
    have hpcd := hsd.pc; have hrund := hsd.run
    have d19 : sd.readReg64 (.gpr 19#5) = buf := hcsmd.1.trans (by simp only [arm64_norm, w19])
    have d20 : sd.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'hk).changed.length :=
      hcsmd.2.1.trans (by simp only [arm64_norm, w20])
    have d24 : sd.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n :=
      hcsmd.2.2.2.2.2.1.trans (by simp only [arm64_norm, w24])
    have d26 : sd.readReg64 (.gpr 26#5) = BitVec.ofNat 64 ((e :: rest).length * 48) :=
      hcsmd.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, w26])
    have d27 : sd.readReg64 (.gpr 27#5) = base + 40#64 :=
      hcsmd.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, w27])
    have d28 : sd.readReg64 (.gpr 28#5) = BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length :=
      hcsmd.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, w28])
    cases rest with
    | nil =>
      apply m5_seq_placed hsd.inv (mid := mPcPlaced 0xa6c)
      m5_steps
      apply SepWP.done
        (by simp only [arm64_norm, mPcPlaced_eq_blkPl])
        (by simp only [arm64_norm, hrund])
      intro hpcm_z hrunm_z hinv_z
      have hfiles_k1 : commitFiles io.wr F0 (writesBefore g (k + 1)) = some F' := by
        rwa [writesBefore_entry_done hk hsplit] at hfiles_next
      refine m5_after_entries_placed (st := M.stepEvents evs1 st)
        (io := io) (F0 := F0) (tr0 := tr0) (g := g) (n := n)
        (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
        (buf := buf) (curCap := curCap) (curPtr := curPtr)
        (v40 := dPathPtr) (v48 := p1) (v58 := v58)
        (v458 := v458') (v460 := v460') (v468 := v468')
        (out := out) (inp := inp) (ps := ps) hA hstk_ext hstk64 hk hne_cur
        (mkStepPlaced hsd (by simpa only [mPcPlaced_eq_blkPl] using hpcm_z) hrunm_z
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          hinv_z (by simp only [calleeSavedVRegs, arm64_norm]))
        (by simp only [arm64_norm, d19]) (by simp only [arm64_norm, d20])
        (by simp only [arm64_norm, d24])
        (by simp only [arm64_norm, hfsd, hfs_w, hfiles_k1])
        (by simp only [arm64_norm]; exact htrd ▸ htr_w)
        (by simp only [arm64_norm, htrd, hout_w])
        (by
          rw [← hsplit]
          simp only [arm64_norm]
          refine Entails.trans (Entails.of_eq (Q :=
            ((dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗ anyHeap) ∗
              (vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr
                  ((storesDirs g)[k]'hk).changed ∗
                m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
                  dPathPtr p1 v58 v458' v460' v468' ∗
                m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
                  inCap inPtr g k ∗
                ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
                ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
                argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
                stackAt fsp (stk - mainFrameSize) ∗ A.pool lim (M.stepEvents evs1 st) sd))
            (by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left (sep_anyHeap_absorb _))
            (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl)))
        fun sf evs_free hfree hat => by
          rw [← M.stepEvents_append evs1 evs_free st]
          have hok : M5LoopARestOkEnv dir [e] (evs1 ++ evs_free) :=
            Or.inr ⟨evs1, evs_free, rfl, Or.inl hstep1, hfree⟩
          exact hnext sf (evs1 ++ evs_free) hok hat
    | cons e' rest' =>
      have hfit_rest :
          FitsEnv M lim (M.stepEvents evs1 st) (M5LoopARestOkEnv dir (e' :: rest')) := by
        intro evs_r hr
        have hfull : M5LoopARestOkEnv dir (e :: e' :: rest') (evs1 ++ evs_r) := by
          rcases hr with h_iter | ⟨evs_i, evs_f, rfl, h_iter, h_free⟩
          · exact Or.inl (Or.inr ⟨evs1, evs_r, rfl, hstep1, h_iter⟩)
          · exact Or.inr ⟨evs1 ++ evs_i, evs_f, (List.append_assoc evs1 evs_i evs_f).symm,
              Or.inr ⟨evs1, evs_i, rfl, hstep1, h_iter⟩, h_free⟩
        exact ((fitsEvents_append M lim evs1 evs_r st).mp (hfit (evs1 ++ evs_r) hfull)).2
      have hrem_lt : (e' :: rest').length * 48 < 2 ^ 64 := by
        simp only [List.length_append, List.length_cons] at hle_tot ⊢; m5_omega
      have htot_lt64 : (e :: e' :: rest').length * 48 < 2 ^ 64 := by
        simp only [List.length_append, List.length_cons] at hle_tot ⊢; m5_omega
      have hne48 : BitVec.ofNat 64 ((e :: e' :: rest').length * 48) ≠ 48#64 := by
        intro heq
        have h1 : ((e :: e' :: rest').length * 48) % 2 ^ 64 = 48 := congrArg BitVec.toNat heq
        rw [Nat.mod_eq_of_lt htot_lt64] at h1; simp only [List.length_cons] at h1; omega
      have hsub_eq1 :
          BitVec.ofNat 64 ((e :: e' :: rest').length * 48) - 48#64 =
            BitVec.ofNat 64 ((e' :: rest').length * 48) :=
        bv_mul48_sub48_a (e' :: rest').length
      have hsub_eq2 :
          BitVec.ofNat 64 ((e :: e' :: rest').length * 48) + (-48#64) =
            BitVec.ofNat 64 ((e' :: rest').length * 48) :=
        bv_mul48_add_neg48_a (e' :: rest').length
      have hx27_next :
          base + 88#64 = curPtr + BitVec.ofNat 64 ((done ++ [e]).length * 48) + 0x28#64 := by
        have h40 : base + 88#64 = (base + 40#64) + 48#64 := by
          simp only [base, BitVec.add_assoc]; rfl
        rw [h40]; exact addr_advance_entry_a curPtr done e
      apply m5_seq_placed hsd.inv (mid := mPcPlaced 0x8fc)
      m5_steps
      apply SepWP.done
        (by simp only [arm64_norm, mPcPlaced_eq_blkPl])
        (by simp only [arm64_norm, hrund])
      intro hpcm_z hrunm_z hinv_z
      refine hmore _ evs1 p1 v458' v460' v468' _ (List.cons_ne_nil _ _)
        hstep1 hfit_rest
        (by simp only [List.append_assoc, List.singleton_append]; exact hsplit)
        (mkStepPlaced hsd (by simpa only [mPcPlaced_eq_blkPl] using hpcm_z) hrunm_z
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          hinv_z (by simp only [calleeSavedVRegs, arm64_norm]))
        (by simp only [arm64_norm, d19]) (by simp only [arm64_norm, d20])
        (by simp only [arm64_norm, d24])
        (by simp only [arm64_norm, d26, hsub_eq1, hsub_eq2])
        (by simp only [arm64_norm, d27, hx27_next]) (by simp only [arm64_norm, d28])
        (by simp only [arm64_norm, hfsd, hfs_w, hfiles_next])
        (by simp only [arm64_norm]; exact htrd ▸ htr_w)
        (by simp only [arm64_norm, htrd, hout_w])
        (by
          dsimp only [fsp]
          simp only [List.append_assoc, List.singleton_append, arm64_norm]
          exact Entails.refl _)

/-- Budget-threaded single iteration of inner loop A (`d.path ≠ []`) for head entry `e` and tail
`rest` on Block `617` under `FitsEnv`. -/
theorem m5_loop_a_one_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr dPathPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {e : List (BitVec 8) × List (BitVec 8)}
    {rest done : List (List (BitVec 8) × List (BitVec 8))}
    {s0 s : State} {v48 v58 v458 v460 v468 : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hk : k < 8)
    (hfit : FitsEnv M lim st (M5LoopARestOkEnv ((storesDirs g)[k]'(by simp [hk])).path (e :: rest)))
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_hook : mainFrameSize + hookStack ≤ stk)
    (hstk_res : mainFrameSize + resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hd_ne : ((storesDirs g)[k]'(by simp [hk])).path ≠ [])
    (herr : ∀ (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced),
      M5LoopARestErrEnv ((storesDirs g)[k]'(by simp [hk])).path errE (e :: rest) evsErr →
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k
        ((storesDirs g)[k]'(by simp [hk])).changed errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
          s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          ((storesDirs g)[k]'(by simp [hk])).changed errE)
        Q Qp oom)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      M5LoopARestOkEnv ((storesDirs g)[k]'(by simp [hk])).path (e :: rest) evs →
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
        (m5LoopMemPlaced (A.atState lim (M.stepEvents evs st) sf)
          s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
        Q Qp oom)
    (hsplit : ((storesDirs g)[k]'(by simp [hk])).changed = done ++ e :: rest)
    (hs : InMainPlaced CodeOk s0 s 0x8fc)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 ((e :: rest).length * 48))
    (hx27 : s.readReg64 (.gpr 27#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).path.length)
    (hfiles : commitFiles io.wr F0
      (writesBefore g k ++
        done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
      some s.fs.files)
    (htr0 : tr0 <+: s.trace)
    (hstdout : ProcessOutcome.traceStreamBytes .stdout s.trace =
      ProcessOutcome.traceStreamBytes .stdout tr0)
    (hP : P ⊢ (dPathPtr ↦ᵣ ((storesDirs g)[k]'(by simp [hk])).path) ∗
      vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ e :: rest) ∗
      m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
        curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
        dPathPtr v48 v58 v458 v460 v468 ∗
      m5WorkRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
        outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
      ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      mainSaved s0 ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
      A.pool lim st s ∗ anyHeap)
    (hmore : ∀ (s' : State) (evs1 : List AllocEvent) (v48' v458' v460' v468' : BitVec 64)
        (P' : SepProp),
      rest ≠ [] →
      M5LoopAStepEnv ((storesDirs g)[k]'(by simp [hk])).path e.1 evs1 →
      FitsEnv M lim (M.stepEvents evs1 st)
        (M5LoopARestOkEnv ((storesDirs g)[k]'(by simp [hk])).path rest) →
      ((storesDirs g)[k]'(by simp [hk])).changed = (done ++ [e]) ++ rest →
      InMainPlaced CodeOk s0 s' 0x8fc →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (rest.length * 48) →
      s'.readReg64 (.gpr 27#5) = curPtr + BitVec.ofNat 64 ((done ++ [e]).length * 48) + 0x28#64 →
      s'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).path.length →
      commitFiles io.wr F0
        (writesBefore g k ++
          (done ++ [e]).map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
        some s'.fs.files →
      tr0 <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      (P' ⊢ (dPathPtr ↦ᵣ ((storesDirs g)[k]'(by simp [hk])).path) ∗
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr ((done ++ [e]) ++ rest) ∗
        m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
          curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
          dPathPtr v48' v58 v458' v460' v468' ∗
        m5WorkRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
          outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
        ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim (M.stepEvents evs1 st) s' ∗ anyHeap) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s' P' Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom :=
  m5_loop_a_one_of_placed
    (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
    (buf := buf) (curCap := curCap) (curPtr := curPtr) (dPathPtr := dPathPtr)
    (out := out) (inp := inp) (ps := ps)
    (v48 := v48) (v58 := v58) (v458 := v458) (v460 := v460) (v468 := v468)
    hA hc ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio)
    hk hfit hstk_ext hstk_hook hstk_res hstk64 hpaths hd_ne herr hnext hsplit hs
    hx19 hx20 hx24 hx26 hx27 hx28 hfiles htr0 hstdout hP hmore

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPlacedBudget
