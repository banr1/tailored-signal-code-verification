/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBStepPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5AfterPlacedBudget

/-!
# Budget-Threaded M5 Inner Loop B Induction (`M+0x9e8 .. M+0xa68`, Block `617`)

Budget-threaded verification of `m5_loop_b_one_placed` and `m5_loop_b_entries_placed` (`d.path = []`)
on Block `617` under `FitsEnv`, advancing `A.pool` under `M5LoopBRestOkEnv` (or `M5LoopBRestErrEnv`).
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

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.RustHeap (vecBuf)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession.Cli (StoresGhost dirEntryAt pathOf)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtM5LoopPlaced InMainPlaced IoModel LsCodeInv M5ErrEntryPlaced M5LoopErrPlaced argsBuf
   commitFiles m5ErrMemPlaced m5LoopMemPlaced mPcPlaced mainFrameSize mainSaved ownedBytes
   storesDirs writesBefore)
open CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
  (commitFiles_entry_ok m5ScratchPlaced m5WorkRestPlaced m5_seq_placed
   mPcPlaced_eq_blkPl mkStepPlaced pathOf_nil writesBefore_entry_done)
open scoped CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
open CryptoVerification.SignalSession.Cli.Path.Helpers (ofNat_beq_zero_false)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   fitsEvents_append)
open LibsignalBinary.Heap.SpecBudget (writeFileEnv_nil)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv IterSeqEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced mainIoBoundedPlaced_iff_mainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced MainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5AfterPlacedBudget
  (m5_after_entries_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopDropPlacedBudget
  (m5ErrEntryDropEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBStepPlacedBudget
  (M5LoopBErrStepEnv M5LoopBStepEnv m5_loop_b_write_entry_of_placed m5_loop_b_write_entry_placed)

attribute [local arm64_norm]
  RustCliAllocBudget.pool_setPC
  RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState
  RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32
  RustCliAllocBudget.pool_writeReg

attribute [local irreducible] Program.fetch Program.externAt?

/-- Allocator event envelope for committing `entries` in Loop B (`d.path = []`) followed by
`m5_after_entries_placed` deallocations (`FreeOnlyEvs`) into `AtM5LoopPlaced … (k + 1)`. -/
def M5LoopBRestOkEnv (entries : List (List (BitVec 8) × List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (IterSeqEnv (fun e => M5LoopBStepEnv e.1) entries) FreeOnlyEvs evs

example : ∃ evs, M5LoopBRestOkEnv [] evs :=
  ⟨[], Or.inl rfl⟩

/-- Error-exit allocator event envelope at `M+0xbdc` / `M+0xbf4` across remaining entries `entries`
in Loop B, tying `m5ErrEntryDropEvents errE` to the failing entry so post-error cleanup completes
`M5LoopBStepEnv`. -/
def M5LoopBRestErrEnv (errE : M5ErrEntryPlaced) :
    List (List (BitVec 8) × List (BitVec 8)) → List AllocEvent → Prop
  | [], _ => False
  | e :: rest, evs =>
      (M5LoopBErrStepEnv e.1 evs ∧ M5LoopBStepEnv e.1 (evs ++ m5ErrEntryDropEvents errE)) ∨
      ConcatEnv (M5LoopBStepEnv e.1) (M5LoopBRestErrEnv errE rest) evs

example : ∃ evs, M5LoopBRestErrEnv .bf4 [([], [])] evs :=
  ⟨[], Or.inl ⟨writeFileEnv_nil 0, writeFileEnv_nil 0⟩⟩

private theorem m5LoopBRestOkEnv_cons_right {e : List (BitVec 8) × List (BitVec 8)}
    {rest : List (List (BitVec 8) × List (BitVec 8))} {evs1 evs2 : List AllocEvent}
    (h1 : M5LoopBStepEnv e.1 evs1) (h2 : M5LoopBRestOkEnv rest evs2) :
    M5LoopBRestOkEnv (e :: rest) (evs1 ++ evs2) := by
  rcases h2 with hIt | ⟨evsI, evsF, rfl, hIt, hFr⟩
  · exact Or.inl (Or.inr ⟨evs1, evs2, rfl, h1, hIt⟩)
  · exact Or.inr ⟨evs1 ++ evsI, evsF, (List.append_assoc evs1 evsI evsF).symm,
      Or.inr ⟨evs1, evsI, rfl, h1, hIt⟩, hFr⟩

private theorem bv_mul48_sub48 (n : Nat) :
    BitVec.ofNat 64 ((n + 1) * 48) - 48#64 = BitVec.ofNat 64 (n * 48) := by
  have heq : (n + 1) * 48 = n * 48 + 48 := by omega
  rw [heq, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel (BitVec.ofNat 64 (n * 48)) 48#64

private theorem bv_mul48_add_neg48 (n : Nat) :
    BitVec.ofNat 64 ((n + 1) * 48) + (-48#64) = BitVec.ofNat 64 (n * 48) := by
  rw [← BitVec.sub_eq_add_neg]
  exact bv_mul48_sub48 n

private theorem bv_mul48_beq0_false {α : Type} (e' : α) (rest' : List α)
    (hle : (e' :: rest').length * 48 < 2 ^ 64) :
    (BitVec.ofNat 64 ((e' :: rest').length * 48) == 0#64) = false :=
  ofNat_beq_zero_false (by simp only [List.length_cons]; omega) hle

private theorem addr_advance_entry {α : Type} (curPtr : BitVec 64) (done : List α) (e : α) :
    curPtr + BitVec.ofNat 64 (done.length * 48) + 88#64 =
      curPtr + BitVec.ofNat 64 ((done ++ [e]).length * 48) + 0x28#64 := by
  have hlen_add : (done ++ [e]).length * 48 = done.length * 48 + 48 := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [hlen_add, BitVec.ofNat_add]; bv_omega

private theorem addr_advance_entry' {α : Type} (curPtr : BitVec 64) (done : List α) (e : α) :
    (curPtr + BitVec.ofNat 64 (done.length * 48) + 40#64) + 48#64 =
      curPtr + BitVec.ofNat 64 ((done ++ [e]).length * 48) + 0x28#64 := by
  have hlen_add : (done ++ [e]).length * 48 = done.length * 48 + 48 := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [hlen_add, BitVec.ofNat_add]; bv_omega

set_option maxHeartbeats 1600000 in
/-- `{StdinEnv ReadEnv}`-parametric budget-threaded single iteration of inner loop B (`d.path = []`)
for head entry `e` and tail `rest` on Block `617` under `FitsEnv`. -/
theorem m5_loop_b_one_of_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {io : IoModel} {uuidParse : UuidParser}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {e : List (BitVec 8) × List (BitVec 8)}
    {rest done : List (List (BitVec 8) × List (BitVec 8))}
    {s0 s : State} {v40 v48 v58 v458 v460 v468 : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hfit : FitsEnv M lim st (M5LoopBRestOkEnv (e :: rest)))
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_hook : mainFrameSize + hookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk : k < 8)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hdpath : ((storesDirs g)[k]'(by simp [hk])).path = [])
    (herr : ∀ (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced),
      M5LoopBRestErrEnv errE (e :: rest) evsErr →
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k
        ((storesDirs g)[k]'(by simp [hk])).changed errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
          s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          ((storesDirs g)[k]'(by simp [hk])).changed errE)
        Q Qp oom)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      M5LoopBRestOkEnv (e :: rest) evs →
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
        (m5LoopMemPlaced (A.atState lim (M.stepEvents evs st) sf)
          s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
        Q Qp oom)
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
    (hmore : ∀ (s' : State) (evs1 : List AllocEvent) (P' : SepProp),
      rest ≠ [] →
      M5LoopBStepEnv e.1 evs1 →
      FitsEnv M lim (M.stepEvents evs1 st) (M5LoopBRestOkEnv rest) →
      ((storesDirs g)[k]'(by simp [hk])).changed = (done ++ [e]) ++ rest →
      InMainPlaced CodeOk s0 s' 0x9e8 →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 ((done ++ [e]).length * 48) + 0x28#64 →
      s'.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (rest.length * 48) →
      commitFiles io.wr F0
        (writesBefore g k ++
          (done ++ [e]).map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
        some s'.fs.files →
      tr0 <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      (P' ⊢ vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr ((done ++ [e]) ++ rest) ∗
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
        A.pool lim (M.stepEvents evs1 st) s' ∗ anyHeap) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s' P' Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  have hne_cur : ((storesDirs g)[k]'(by simp [hk])).changed ≠ [] := by
    intro h0; rw [hsplit] at h0; simp at h0
  have hfit1 : FitsEnv M lim st (M5LoopBStepEnv e.1) :=
    fun evs1 h1 => hfit evs1 (Or.inl (Or.inl h1))
  refine m5_loop_b_write_entry_of_placed
    (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
    (buf := buf) (curCap := curCap) (curPtr := curPtr)
    (v40 := v40) (v48 := v48) (v58 := v58) (v458 := v458) (v460 := v460) (v468 := v468)
    (out := out) (inp := inp) (ps := ps)
    hA hc hio hfit1 hstk_ext hstk_hook hstk64
    hk hpaths hdpath
    hsplit hs hx19 hx20 hx24 hx25 hx26 hfiles htr0 hstdout hP
    (fun se evsErr errE hErr hStep hErrSt =>
      herr se evsErr errE (Or.inl ⟨hErr, hStep⟩) hErrSt)
    ?_
  intro s_end evs1 F' h1 hle_tot hcap_lt hse hfse hwr_ok htre hstdoute r19 r20 r24 r25 r26
  have hfit_rest : FitsEnv M lim (M.stepEvents evs1 st) (M5LoopBRestOkEnv rest) := by
    intro evs2 h2
    exact ((fitsEvents_append M lim evs1 evs2 st).mp
      (hfit (evs1 ++ evs2) (m5LoopBRestOkEnv_cons_right h1 h2))).2
  have hfiles_next :
      commitFiles io.wr F0
        (writesBefore g k ++
          (done ++ [e]).map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
      some F' :=
    commitFiles_entry_ok hk hfiles (by simpa only [hdpath, pathOf_nil] using hwr_ok)
  have hpce := hse.pc; have hrune := hse.run
  cases rest with
  | nil =>
    apply m5_seq_placed hse.inv (mid := mPcPlaced 0xa6c)
    m5_steps
    apply SepWP.done
      (by simp only [arm64_norm, mPcPlaced_eq_blkPl]; try m5_bv_omega)
      (by simp only [arm64_norm, hrune])
    intro hpcm hrunm hinv_m
    have hfiles_k1 : commitFiles io.wr F0 (writesBefore g (k + 1)) = some F' := by
      rwa [writesBefore_entry_done hk hsplit] at hfiles_next
    apply m5_after_entries_placed (CodeOk := CodeOk) (io := io) (F0 := F0) (tr0 := tr0) (g := g)
      (n := n) (st := M.stepEvents evs1 st)
      (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
      (buf := buf) (curCap := curCap) (curPtr := curPtr)
      (v40 := v40) (v48 := v48) (v58 := v58) (v458 := v458) (v460 := v460) (v468 := v468)
      (out := out) (inp := inp) (ps := ps)
      hA hstk_ext hstk64 hk hne_cur
    · exact mkStepPlaced hse (by simpa only [mPcPlaced_eq_blkPl] using hpcm) hrunm
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        hinv_m (by simp only [calleeSavedVRegs, arm64_norm])
    · simp only [arm64_norm, r19]
    · simp only [arm64_norm, r20]
    · simp only [arm64_norm, r24]
    · simp only [arm64_norm, hfse, hfiles_k1]
    · simp only [arm64_norm]; exact htre
    · simp only [arm64_norm, hstdoute]
    · simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
        RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
        RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
      rw [← hsplit]
      exact Entails.refl _
    · intro sf evsAfter hFree hat
      have hst_eq : M.stepEvents evsAfter (M.stepEvents evs1 st) =
          M.stepEvents (evs1 ++ evsAfter) st :=
        (M.stepEvents_append evs1 evsAfter st).symm
      rw [hst_eq]
      exact hnext sf (evs1 ++ evsAfter) (Or.inr ⟨evs1, evsAfter, rfl, Or.inl h1, hFree⟩) hat
  | cons e' rest' =>
    have hrem_lt : (e' :: rest').length * 48 < 2 ^ 64 := by
      simp only [List.length_append, List.length_cons] at hle_tot ⊢; m5_omega
    have htot_lt64 : (e :: e' :: rest').length * 48 < 2 ^ 64 := by
      simp only [List.length_append, List.length_cons] at hle_tot ⊢; m5_omega
    have hne48 : BitVec.ofNat 64 ((e :: e' :: rest').length * 48) ≠ 48#64 := by
      intro heq
      have h1_mod : ((e :: e' :: rest').length * 48) % 2 ^ 64 = 48 := congrArg BitVec.toNat heq
      rw [Nat.mod_eq_of_lt htot_lt64] at h1_mod
      simp only [List.length_cons] at h1_mod; omega
    have hsub_eq1 :
        BitVec.ofNat 64 ((e :: e' :: rest').length * 48) - 48#64 =
          BitVec.ofNat 64 ((e' :: rest').length * 48) :=
      bv_mul48_sub48 (e' :: rest').length
    have hsub_eq2 :
        BitVec.ofNat 64 ((e :: e' :: rest').length * 48) + (-48#64) =
          BitVec.ofNat 64 ((e' :: rest').length * 48) :=
      bv_mul48_add_neg48 (e' :: rest').length
    have hx25_next := addr_advance_entry curPtr done e
    have hx25_next' := addr_advance_entry' curPtr done e
    apply m5_seq_placed hse.inv (mid := mPcPlaced 0x9e8)
    m5_steps
    apply SepWP.done
      (by simp only [arm64_norm, mPcPlaced_eq_blkPl, hsub_eq1, hsub_eq2,
        bv_mul48_beq0_false e' rest' hrem_lt]; try m5_bv_omega)
      (by simp only [arm64_norm, hrune])
    intro hpcm hrunm hinv_m
    apply hmore _ evs1 _
    · exact List.cons_ne_nil _ _
    · exact h1
    · exact hfit_rest
    · simp only [List.append_assoc, List.singleton_append]; exact hsplit
    · exact mkStepPlaced hse (by simpa only [mPcPlaced_eq_blkPl] using hpcm) hrunm
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        hinv_m (by simp only [calleeSavedVRegs, arm64_norm])
    · simp only [arm64_norm, r19]
    · simp only [arm64_norm, r20]
    · simp only [arm64_norm, r24]
    · simp only [arm64_norm, r25, hx25_next, hx25_next']
    · simp only [arm64_norm, r26, hsub_eq1, hsub_eq2]
    · simp only [arm64_norm, hfse, hfiles_next]
    · simp only [arm64_norm]; exact htre
    · simp only [arm64_norm, hstdoute]
    · simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
        RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
        RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg,
        List.append_assoc, List.singleton_append]
      exact Entails.refl _

/-- Budget-threaded single iteration of inner loop B (`d.path = []`) for head entry `e` and tail
`rest` on Block `617` under `FitsEnv`. -/
theorem m5_loop_b_one_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {io : IoModel} {uuidParse : UuidParser}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {e : List (BitVec 8) × List (BitVec 8)}
    {rest done : List (List (BitVec 8) × List (BitVec 8))}
    {s0 s : State} {v40 v48 v58 v458 v460 v468 : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hfit : FitsEnv M lim st (M5LoopBRestOkEnv (e :: rest)))
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_hook : mainFrameSize + hookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk : k < 8)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hdpath : ((storesDirs g)[k]'(by simp [hk])).path = [])
    (herr : ∀ (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced),
      M5LoopBRestErrEnv errE (e :: rest) evsErr →
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k
        ((storesDirs g)[k]'(by simp [hk])).changed errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
          s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          ((storesDirs g)[k]'(by simp [hk])).changed errE)
        Q Qp oom)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      M5LoopBRestOkEnv (e :: rest) evs →
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
        (m5LoopMemPlaced (A.atState lim (M.stepEvents evs st) sf)
          s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
        Q Qp oom)
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
    (hmore : ∀ (s' : State) (evs1 : List AllocEvent) (P' : SepProp),
      rest ≠ [] →
      M5LoopBStepEnv e.1 evs1 →
      FitsEnv M lim (M.stepEvents evs1 st) (M5LoopBRestOkEnv rest) →
      ((storesDirs g)[k]'(by simp [hk])).changed = (done ++ [e]) ++ rest →
      InMainPlaced CodeOk s0 s' 0x9e8 →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 ((done ++ [e]).length * 48) + 0x28#64 →
      s'.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (rest.length * 48) →
      commitFiles io.wr F0
        (writesBefore g k ++
          (done ++ [e]).map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
        some s'.fs.files →
      tr0 <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      (P' ⊢ vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr ((done ++ [e]) ++ rest) ∗
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
        A.pool lim (M.stepEvents evs1 st) s' ∗ anyHeap) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s' P' Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom :=
  m5_loop_b_one_of_placed
    (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
    (buf := buf) (curCap := curCap) (curPtr := curPtr)
    (out := out) (inp := inp) (ps := ps)
    (v40 := v40) (v48 := v48) (v58 := v58) (v458 := v458) (v460 := v460) (v468 := v468)
    hA hc ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio)
    hfit hstk_ext hstk_hook hstk64 hk hpaths hdpath herr hnext hsplit hs
    hx19 hx20 hx24 hx25 hx26 hfiles htr0 hstdout hP hmore

/-- `{StdinEnv ReadEnv}`-parametric commit of all remaining entries `rest ≠ []` of `Dir k`
(`d.path = []`) starting at `M+0x9e8` with `done` already committed (`curEntries = done ++ rest`)
under `FitsEnv`. -/
theorem m5_loop_b_entries_of_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {uuidParse : UuidParser}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_hook : mainFrameSize + hookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk : k < 8)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hdpath : ((storesDirs g)[k]'(by simp [hk])).path = []) :
    ∀ (rest done : List (List (BitVec 8) × List (BitVec 8)))
      {st : M.σ} (s : State) (v40 v48 v58 v458 v460 v468 : BitVec 64) (P : SepProp),
      rest ≠ [] →
      FitsEnv M lim st (M5LoopBRestOkEnv rest) →
      (∀ (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced),
        M5LoopBRestErrEnv errE rest evsErr →
        M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k
          ((storesDirs g)[k]'(by simp [hk])).changed errE →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
          (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
            s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
            ((storesDirs g)[k]'(by simp [hk])).changed errE)
          Q Qp oom) →
      (∀ (sf : State) (evs : List AllocEvent),
        M5LoopBRestOkEnv rest evs →
        AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
          (m5LoopMemPlaced (A.atState lim (M.stepEvents evs st) sf)
            s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
          Q Qp oom) →
      ((storesDirs g)[k]'(by simp [hk])).changed = done ++ rest →
      InMainPlaced CodeOk s0 s 0x9e8 →
      s.readReg64 (.gpr 19#5) = buf →
      s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 →
      s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (rest.length * 48) →
      commitFiles io.wr F0
        (writesBefore g k ++
          done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
        some s.fs.files →
      tr0 <+: s.trace →
      ProcessOutcome.traceStreamBytes .stdout s.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      (P ⊢ vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ rest) ∗
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
        A.pool lim st s ∗ anyHeap) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  intro rest; induction rest with
  | nil =>
    intro _ _ _ _ _ _ _ _ _ _ hne_r; intros
    exact (hne_r rfl).elim
  | cons e rest ih =>
    intro done st s v40 v48 v58 v458 v460 v468 P _ hfit herr hnext
      hsplit hs hx19 hx20 hx24 hx25 hx26 hfiles htr0 hstdout hP
    exact m5_loop_b_one_of_placed
      (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
      (buf := buf) (curCap := curCap) (curPtr := curPtr)
      (out := out) (inp := inp) (ps := ps)
      (v40 := v40) (v48 := v48) (v58 := v58) (v458 := v458) (v460 := v460) (v468 := v468)
      hA hc hio hfit hstk_ext hstk_hook hstk64
      hk hpaths hdpath herr hnext hsplit hs hx19 hx20 hx24 hx25 hx26 hfiles htr0 hstdout hP
      fun s' evs1 P' hne_rest h1 hfit_rest =>
        ih (done ++ [e]) s' v40 v48 v58 v458 v460 v468 P' hne_rest hfit_rest
          (fun se evsErr2 errE hErr2 hErrSt => by
            rw [← M.stepEvents_append evs1 evsErr2 st]
            exact herr se (evs1 ++ evsErr2) errE (Or.inr (ConcatEnv.append h1 hErr2)) hErrSt)
          (fun sf evs2 hOk2 hat => by
            rw [← M.stepEvents_append evs1 evs2 st]
            exact hnext sf (evs1 ++ evs2) (m5LoopBRestOkEnv_cons_right h1 hOk2) hat)

/-- Commit all remaining entries `rest ≠ []` of `Dir k` (`d.path = []`) starting at `M+0x9e8` with
`done` already committed (`curEntries = done ++ rest`) under `FitsEnv`. -/
theorem m5_loop_b_entries_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {uuidParse : UuidParser}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_hook : mainFrameSize + hookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk : k < 8)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hdpath : ((storesDirs g)[k]'(by simp [hk])).path = []) :
    ∀ (rest done : List (List (BitVec 8) × List (BitVec 8)))
      {st : M.σ} (s : State) (v40 v48 v58 v458 v460 v468 : BitVec 64) (P : SepProp),
      rest ≠ [] →
      FitsEnv M lim st (M5LoopBRestOkEnv rest) →
      (∀ (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced),
        M5LoopBRestErrEnv errE rest evsErr →
        M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k
          ((storesDirs g)[k]'(by simp [hk])).changed errE →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
          (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
            s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
            ((storesDirs g)[k]'(by simp [hk])).changed errE)
          Q Qp oom) →
      (∀ (sf : State) (evs : List AllocEvent),
        M5LoopBRestOkEnv rest evs →
        AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
          (m5LoopMemPlaced (A.atState lim (M.stepEvents evs st) sf)
            s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
          Q Qp oom) →
      ((storesDirs g)[k]'(by simp [hk])).changed = done ++ rest →
      InMainPlaced CodeOk s0 s 0x9e8 →
      s.readReg64 (.gpr 19#5) = buf →
      s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s.readReg64 (.gpr 25#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 →
      s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (rest.length * 48) →
      commitFiles io.wr F0
        (writesBefore g k ++
          done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
        some s.fs.files →
      tr0 <+: s.trace →
      ProcessOutcome.traceStreamBytes .stdout s.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      (P ⊢ vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ rest) ∗
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
        A.pool lim st s ∗ anyHeap) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom :=
  m5_loop_b_entries_of_placed
    (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
    (buf := buf) (curCap := curCap) (curPtr := curPtr)
    (out := out) (inp := inp) (ps := ps)
    hA hc ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio)
    hstk_ext hstk_hook hstk64 hk hpaths hdpath

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBPlacedBudget
