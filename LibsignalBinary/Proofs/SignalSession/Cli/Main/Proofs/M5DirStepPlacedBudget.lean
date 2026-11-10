/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5BufDeallocPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DirStepPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBPlacedBudget
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Single-`Dir` Commit Step for `main` Hop M5 (Block `617`)

Budget-threaded verification of `m5_loop_a_entries_placed` and `m5_dir_step_placed` on Block `617`
under `RustCliAllocBudget M`, advancing `A.pool` under `M5DirOkEnv` (or `M5DirErrEnv` on write
failure).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DirStepPlacedBudget

set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.RustHeap (vecBuf)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession.Cli (DirGhost StoresGhost dirEntryAt pathOf)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtM5LoopPlaced InMainPlaced IoModel LsCodeInv M5ErrEntryPlaced M5LoopErrPlaced argsBuf
   commitFiles m5ErrMemPlaced m5LoopMemPlaced mPcPlaced mainFrameSize mainSaved ownedBytes
   storesDirs writesBefore writesBefore_succ)
open CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
  (dirAt_unpack dirHeader_entails_memRegion dir_entry_path_ok_len locals_m5LoopCellsPlaced_pop
   locals_m5LoopCellsPlaced_push m5DirPopRestPlaced m5DirPopRest_carve_scratch_placed
   m5DirWorkMidPlaced m5DirWorkMid_finish_placed m5ScratchPlaced m5WorkRestPlaced m5_run_placed
   mPcPlaced_eq_blkPl pathOf_ne_nil sep_anyHeap_absorb shl4_lsl1_nat ubfm_lsl1_bv ubfm_lsl1_nat
   vecBuf_nil_dealloc vecBuf_pure_keep)
open scoped CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
open CryptoVerification.SignalSession.Cli.Path.Helpers
  (ofNat_beq_zero_false ofNat_getElem_63_false ofNat_getLsbD_63_false)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (writeFileEnv_nil)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced mainIoBoundedPlaced_iff_mainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced MainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5BufDeallocPlacedBudget
  (m5BufDeallocEnv_freeOnly m5_buf_dealloc_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPlacedBudget
  (M5LoopARestErrEnv M5LoopARestOkEnv m5_loop_a_one_of_placed m5_loop_a_one_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBPlacedBudget
  (M5LoopBRestErrEnv M5LoopBRestOkEnv m5_loop_b_entries_of_placed m5_loop_b_entries_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
  (argsBuf_atState_eq_repAlloc m5LoopCellsPlaced_atState_eq_repAlloc
   ownedBytes_atState_eq_repAlloc)

private theorem m5_run_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {mid ret : BitVec 64}
    {s : State} {P P0 F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (hP : P ⊢ P0 ∗ (F ∗ A.pool lim st s))
    (hstep : SepWP ((blkPC_617).rebase (blkPl_617).base H) mid s P0
      (fun sm Pm => VmPreserved s sm ∧
        (sm.pc = mid → sm.status = .Running → CodeOk sm.mem →
          SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sm
            (Pm ∗ (F ∗ A.pool lim st sm)) Q Qp oom))) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s P Q Qp oom := by
  intro R hm hL
  have hm' : s.mem ⊨ P0 ∗ ((F ∗ A.pool lim st s) ∗ R) := by
    rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hP) hm
  rcases hstep.elim hm' hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hvm, hcont⟩ | ⟨_, hfalse⟩⟩
  · rw [← A.pool_transport lim st s sm hvm] at hmm
    have hmm' : sm.mem ⊨ (Pm ∗ (F ∗ A.pool lim st sm)) ∗ R := by rwa [sepConj_assoc]
    obtain ⟨sf, hsteps', hout⟩ :=
      hcont hpcm hrunm (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · rw [satisfies_pure_sepConj] at hfalse
    exact False.elim hfalse.1

attribute [local irreducible] SepWPp Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm]
  RustCliAllocBudget.pool_setPC
  RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState
  RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32
  RustCliAllocBudget.pool_writeReg

/-- Allocator event envelope for one outer-loop iteration `m5_dir_step_placed` on `d : DirGhost`
reaching `AtM5LoopPlaced … (k + 1)` (covers `d.changed = []` buffer deallocation via `FreeOnlyEvs`,
Loop B when `d.path = []`, and Loop A when `d.path ≠ []`). -/
def M5DirOkEnv (d : DirGhost) (evs : List AllocEvent) : Prop :=
  if d.path = [] then M5LoopBRestOkEnv d.changed evs else M5LoopARestOkEnv d.path d.changed evs

example : ∃ evs, M5DirOkEnv { path := [], changed := [] } evs :=
  ⟨[], Or.inl rfl⟩

/-- Error-exit allocator event envelope for one outer-loop iteration `m5_dir_step_placed` on
`d : DirGhost` exiting to `M5LoopErrPlaced` at `errE`. -/
def M5DirErrEnv (d : DirGhost) (errE : M5ErrEntryPlaced) (evs : List AllocEvent) : Prop :=
  if d.path = [] then M5LoopBRestErrEnv errE d.changed evs
  else M5LoopARestErrEnv d.path errE d.changed evs

example : ∃ evs, M5DirErrEnv { path := [], changed := [([], [])] } .bf4 evs :=
  ⟨[], Or.inl ⟨writeFileEnv_nil 0, writeFileEnv_nil 0⟩⟩

/-- `{StdinEnv ReadEnv}`-parametric commit of all remaining entries `rest ≠ []` of `Dir k`
(`d.path ≠ []`) starting at `M+0x8fc` with `done` already committed (`curEntries = done ++ rest`)
and `(dPathPtr ↦ᵣ d.path)` in frame under `FitsEnv`. -/
theorem m5_loop_a_entries_of_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr dPathPtr v58 : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_hook : mainFrameSize + hookStack ≤ stk)
    (hstk_res : mainFrameSize + resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk : k < 8)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hd_ne : ((storesDirs g)[k]'(by simp [hk])).path ≠ []) :
    ∀ (rest done : List (List (BitVec 8) × List (BitVec 8)))
      {st : M.σ} (s : State) (v48 v458 v460 v468 : BitVec 64) (P : SepProp),
      rest ≠ [] →
      FitsEnv M lim st (M5LoopARestOkEnv ((storesDirs g)[k]'(by simp [hk])).path rest) →
      (∀ (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced),
        M5LoopARestErrEnv ((storesDirs g)[k]'(by simp [hk])).path errE rest evsErr →
        M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k
          ((storesDirs g)[k]'(by simp [hk])).changed errE →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
          (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
            s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
            ((storesDirs g)[k]'(by simp [hk])).changed errE)
          Q Qp oom) →
      (∀ (sf : State) (evs : List AllocEvent),
        M5LoopARestOkEnv ((storesDirs g)[k]'(by simp [hk])).path rest evs →
        AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
          (m5LoopMemPlaced (A.atState lim (M.stepEvents evs st) sf)
            s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
          Q Qp oom) →
      ((storesDirs g)[k]'(by simp [hk])).changed = done ++ rest →
      InMainPlaced CodeOk s0 s 0x8fc →
      s.readReg64 (.gpr 19#5) = buf →
      s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (rest.length * 48) →
      s.readReg64 (.gpr 27#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 →
      s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).path.length →
      commitFiles io.wr F0
        (writesBefore g k ++
          done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
        some s.fs.files →
      tr0 <+: s.trace →
      ProcessOutcome.traceStreamBytes .stdout s.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      (P ⊢ (dPathPtr ↦ᵣ ((storesDirs g)[k]'(by simp [hk])).path) ∗
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ rest) ∗
        m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
          curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
          dPathPtr v48 v58 v458 v460 v468 ∗
        m5WorkRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
          outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
        ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  intro rest
  induction rest with
  | nil =>
    intro _ _ _ _ _ _ _ _ hne_r
    intros
    exact (hne_r rfl).elim
  | cons e rest ih =>
    intro done st s v48 v458 v460 v468 P _ hfit herr hnext hsplit hs hx19 hx20 hx24 hx26 hx27 hx28 hfiles htr0 hstdout hP
    refine m5_loop_a_one_of_placed
      (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
      (buf := buf) (curCap := curCap) (curPtr := curPtr) (dPathPtr := dPathPtr)
      (out := out) (inp := inp) (ps := ps)
      (v48 := v48) (v58 := v58) (v458 := v458) (v460 := v460) (v468 := v468)
      hA hc hio hk hfit hstk_ext hstk_hook hstk_res hstk64
      hpaths hd_ne herr hnext hsplit hs hx19 hx20 hx24 hx26 hx27 hx28 hfiles htr0 hstdout hP ?_
    intro s' evs1 v48' v458' v460' v468' P' hne' hstep1 hfit_rest hsplit' hs'
      hx19' hx20' hx24' hx26' hx27' hx28' hfiles' htr0' hstdout' hP'
    refine ih (done ++ [e]) s' v48' v458' v460' v468' P' hne' hfit_rest ?_ ?_
      hsplit' hs' hx19' hx20' hx24' hx26' hx27' hx28' hfiles' htr0' hstdout' hP'
    · intro se evsErr2 errE herr2 hE
      rw [← M.stepEvents_append evs1 evsErr2 st]
      exact herr se (evs1 ++ evsErr2) errE (Or.inr ⟨evs1, evsErr2, rfl, hstep1, herr2⟩) hE
    · intro sf evs2 hok2 hat
      rw [← M.stepEvents_append evs1 evs2 st]
      refine hnext sf (evs1 ++ evs2) ?_ hat
      rcases hok2 with hiter | ⟨eI, eF, rfl, hiter, hfree⟩
      · exact Or.inl (Or.inr ⟨evs1, evs2, rfl, hstep1, hiter⟩)
      · exact Or.inr ⟨evs1 ++ eI, eF, (List.append_assoc evs1 eI eF).symm,
          Or.inr ⟨evs1, eI, rfl, hstep1, hiter⟩, hfree⟩

/-- Commit all remaining entries `rest ≠ []` of `Dir k` (`d.path ≠ []`) starting at `M+0x8fc` with
`done` already committed (`curEntries = done ++ rest`) and `(dPathPtr ↦ᵣ d.path)` in frame under
`FitsEnv`. -/
theorem m5_loop_a_entries_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr dPathPtr v58 : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_hook : mainFrameSize + hookStack ≤ stk)
    (hstk_res : mainFrameSize + resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk : k < 8)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hd_ne : ((storesDirs g)[k]'(by simp [hk])).path ≠ []) :
    ∀ (rest done : List (List (BitVec 8) × List (BitVec 8)))
      {st : M.σ} (s : State) (v48 v458 v460 v468 : BitVec 64) (P : SepProp),
      rest ≠ [] →
      FitsEnv M lim st (M5LoopARestOkEnv ((storesDirs g)[k]'(by simp [hk])).path rest) →
      (∀ (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced),
        M5LoopARestErrEnv ((storesDirs g)[k]'(by simp [hk])).path errE rest evsErr →
        M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k
          ((storesDirs g)[k]'(by simp [hk])).changed errE →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
          (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
            s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
            ((storesDirs g)[k]'(by simp [hk])).changed errE)
          Q Qp oom) →
      (∀ (sf : State) (evs : List AllocEvent),
        M5LoopARestOkEnv ((storesDirs g)[k]'(by simp [hk])).path rest evs →
        AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
          (m5LoopMemPlaced (A.atState lim (M.stepEvents evs st) sf)
            s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
          Q Qp oom) →
      ((storesDirs g)[k]'(by simp [hk])).changed = done ++ rest →
      InMainPlaced CodeOk s0 s 0x8fc →
      s.readReg64 (.gpr 19#5) = buf →
      s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).changed.length →
      s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (rest.length * 48) →
      s.readReg64 (.gpr 27#5) = curPtr + BitVec.ofNat 64 (done.length * 48) + 0x28#64 →
      s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 ((storesDirs g)[k]'(by simp [hk])).path.length →
      commitFiles io.wr F0
        (writesBefore g k ++
          done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
        some s.fs.files →
      tr0 <+: s.trace →
      ProcessOutcome.traceStreamBytes .stdout s.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      (P ⊢ (dPathPtr ↦ᵣ ((storesDirs g)[k]'(by simp [hk])).path) ∗
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (done ++ rest) ∗
        m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
          curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
          dPathPtr v48 v58 v458 v460 v468 ∗
        m5WorkRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
          outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
        ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom :=
  m5_loop_a_entries_of_placed
    (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
    (buf := buf) (curCap := curCap) (curPtr := curPtr) (dPathPtr := dPathPtr) (v58 := v58)
    (out := out) (inp := inp) (ps := ps)
    hA hc ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio)
    hstk_ext hstk_hook hstk_res hstk64 hk hpaths hd_ne

private theorem add_two_mul_shl4_eq_mul48 {n : Nat} (hn : n < 2 ^ 58) :
    (BitVec.ofNat 64 n + BitVec.ofNat 64 (2 * n)) <<< 4 = BitVec.ofNat 64 (n * 48) := by
  rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- `{StdinEnv ReadEnv}`-parametric budget-threaded execution of one `Dir k` (`k < 8`) iteration of
`main`'s outer M5 loop (`M+0x8b8`) under `FitsEnv`, advancing to `AtM5LoopPlaced … (k + 1)` or
exiting via `herr` on `write_file` failure. -/
theorem m5_dir_step_of_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hk : k < 8)
    (hfit : FitsEnv M lim st (M5DirOkEnv ((storesDirs g)[k]'(by simp [hk]))))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hs : AtM5LoopPlaced CodeOk io F0 tr0 g s0 s n buf k)
    (herr : ∀ (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced)
        (curCap curPtr : BitVec 64)
        (curEntries : List (List (BitVec 8) × List (BitVec 8))),
      M5DirErrEnv ((storesDirs g)[k]'(by simp [hk])) errE evsErr →
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k curEntries errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
          s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          curEntries errE)
        Q Qp oom)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      M5DirOkEnv ((storesDirs g)[k]'(by simp [hk])) evs →
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
        (m5LoopMemPlaced (A.atState lim (M.stepEvents evs st) sf)
          s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (m5LoopMemPlaced (A.atState lim st s) s0 stk n outCap outPtr inCap inPtr buf out inp ps g k)
      Q Qp oom := by
  set_option maxHeartbeats 1600000 in
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  let dAddr := (s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64
  have hstk_ext : mainFrameSize + extHookStack ≤ stk := by m5_omega
  have hstk_hook : mainFrameSize + hookStack ≤ stk := by m5_omega
  have hstk_res : mainFrameSize + resStack ≤ stk := by m5_omega
  have hbase : InMainPlaced CodeOk s0 s 0x8b8 := by simpa [hk] using hs.base
  change k < (storesDirs g).length at hk
  have hpc := hbase.pc; have hrun := hbase.run
  have hx19 := hs.x19; have hx23 := hs.x23; have hx25 := hs.x25
  have hx24 := hs.x24; have hx26 := hs.x26
  have hk_add1 : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hdAddr_eq : dAddr = fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k) := by
    dsimp only [fsp, dAddr, mainFrameSize]; m5_bv_omega
  have hoff16 : (dAddr + 8#64) + 8#64 = dAddr + 16#64 := by rw [BitVec.add_assoc]; rfl
  have hsp40 : (s.sp + 32#64) + 8#64 = s.sp + 40#64 := by rw [BitVec.add_assoc]; rfl
  have hsp56 : (s.sp + 48#64) + 8#64 = s.sp + 56#64 := by rw [BitVec.add_assoc]; rfl
  have hx25_cell : ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x30#64) ↦₆₄ (s0.sp - 792#64)) =
      ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x30#64) ↦₆₄
        (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64)) :=
    congrArg _ (by
      dsimp only [mainFrameSize]
      rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl)
  dsimp only [m5LoopMemPlaced]
  simp only [ownedBytes_atState_eq_repAlloc, argsBuf_atState_eq_repAlloc,
    m5LoopCellsPlaced_atState_eq_repAlloc, RustCliAllocBudget.atState_pool]
  rw [locals_m5LoopCellsPlaced_pop A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
      inCap inPtr g hk,
    ← hdAddr_eq, dirAt_unpack A.repAlloc dAddr ((storesDirs g)[k]'hk)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun dPathPtr => ?_
  refine SepWPp.exists_elim fun curCap => ?_
  refine SepWPp.exists_elim fun curPtr => ?_
  rw [vecBuf_pure_keep A.repAlloc curCap curPtr ((storesDirs g)[k]'hk).changed]
  have hpure_top :
      ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        ((((dAddr ↦₆₄ curCap) ∗ ((dAddr + 0x08#64) ↦₆₄ curPtr) ∗
            ((dAddr + 0x10#64) ↦₆₄ BitVec.ofNat 64 ((storesDirs g)[k]'hk).changed.length) ∗
            ((dAddr + 0x18#64) ↦₆₄ dPathPtr) ∗
            ((dAddr + 0x20#64) ↦₆₄ BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)) ∗
          (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
          (⌜((storesDirs g)[k]'hk).changed.length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63⌝ ∗
            vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr
              ((storesDirs g)[k]'hk).changed)) ∗
          m5DirPopRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
            inCap inPtr g k) ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ anyHeap =
      ⌜((storesDirs g)[k]'hk).changed.length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63⌝ ∗
      (((dAddr ↦₆₄ curCap) ∗ ((dAddr + 0x08#64) ↦₆₄ curPtr) ∗
          ((dAddr + 0x10#64) ↦₆₄ BitVec.ofNat 64 ((storesDirs g)[k]'hk).changed.length) ∗
          ((dAddr + 0x18#64) ↦₆₄ dPathPtr) ∗
          ((dAddr + 0x20#64) ↦₆₄ BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)) ∗
        (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr
          ((storesDirs g)[k]'hk).changed ∗
        m5DirPopRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
          inCap inPtr g k ∗
        ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ anyHeap) := by
    sep_ac_rfl
  rw [hpure_top]
  refine SepWPp.pure_elim fun ⟨hle_chg, hcap_lt⟩ => ?_
  have hcap_add1_ne' : curCap + 1#64 ≠ 0#64 := by
    intro h
    have hlt64 : curCap.toNat + 1 < 2 ^ 64 := by m5_omega
    have hto : (curCap + 1#64).toNat = curCap.toNat + 1 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hlt64
    rw [h] at hto; simp at hto
  have hcap_add1_ne : (curCap + 1#64 == 0#64) = false := beq_false_of_ne hcap_add1_ne'
  cases hchg : ((storesDirs g)[k]'hk).changed with
  | nil =>
    refine m5_run_placed hbase.inv (mid := mPcPlaced 0xabc)
      (P0 := (((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
        ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
        (((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) + 0x08#64) ↦₆₄
          BitVec.ofNat 64 ([] : List (List (BitVec 8) × List (BitVec 8))).length))
      (F := ((dAddr + 0x18#64) ↦₆₄ dPathPtr) ∗
        ((dAddr + 0x20#64) ↦₆₄ BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length) ∗
        (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr [] ∗
        m5DirPopRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
          inCap inPtr g k ∗
        ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ anyHeap)
      (by rw [← hoff16]; dsimp only [dAddr]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    m5_steps
    apply SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl])
      (by simp only [arm64_norm, hrun])
    intro hpcm hrunm hinv_m
    have hfiles_k1 : commitFiles io.wr F0 (writesBefore g (k + 1)) = some s.fs.files := by
      have hw0 : ((storesDirs g)[k]'hk).writes = [] := by
        unfold DirGhost.writes; simp [hchg]
      rw [writesBefore_succ hk, hw0, List.append_nil]; exact hs.files
    refine m5_buf_dealloc_placed (st := st) (io := io) (F0 := F0) (tr0 := tr0) (g := g) (n := n)
      (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
      (buf := buf) (curCap := curCap) (curPtr := curPtr)
      (out := out) (inp := inp) (ps := ps)
      hc.allocFs hstk_ext hstk64 hk hcap_lt
      (hbase.mk_step hpcm hrunm (by simp only [arm64_norm]) (by simp only [arm64_norm])
        hinv_m (by simp only [calleeSavedVRegs, arm64_norm]))
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, hx23, hk_add1]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hfiles_k1])
      (by simp only [arm64_norm]; exact hs.trace) (by simp only [arm64_norm, hs.stdout])
      (by
        dsimp only [dAddr] at hoff16 ⊢
        rw [hoff16]
        have hhdr := dirHeader_entails_memRegion dAddr curCap curPtr
          (BitVec.ofNat 64 ([] : List (List (BitVec 8) × List (BitVec 8))).length)
          dPathPtr (BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)
        dsimp only [dAddr, fsp] at hhdr hdAddr_eq ⊢
        have hord :
            ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x10#64) ↦₆₄
                  BitVec.ofNat 64 ([] : List (List (BitVec 8) × List (BitVec 8))).length)) ∗
              ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
              ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
                BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length) ∗
              (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
              vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr [] ∗
              m5DirPopRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
                (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
              ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
              ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
              argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
              stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
              A.pool lim st s ∗ anyHeap =
            (((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x10#64) ↦₆₄
                  BitVec.ofNat 64 ([] : List (List (BitVec 8) × List (BitVec 8))).length) ∗
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
                  BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)) ∗
              m5DirPopRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
                (BitVec.ofNat 64 out.length) inCap inPtr g k) ∗
            ((dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗ anyHeap) ∗
            vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr [] ∗
            (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
              ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
              argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
              stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
              A.pool lim st s) := by
          sep_ac_rfl
        rw [hord]
        refine Entails.trans
          (sepConj_mono (sepConj_mono_left hhdr)
            (sepConj_mono (sep_anyHeap_absorb _)
              (sepConj_mono_left (vecBuf_nil_dealloc A.repAlloc curCap curPtr)))) ?_
        rw [hdAddr_eq, locals_m5LoopCellsPlaced_push A.repAlloc _ outCap outPtr
          (BitVec.ofNat 64 out.length) inCap inPtr g hk]
        dsimp only [m5LoopMemPlaced]
        simp only [ownedBytes_atState_eq_repAlloc, argsBuf_atState_eq_repAlloc,
          m5LoopCellsPlaced_atState_eq_repAlloc, RustCliAllocBudget.atState_pool, arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl))
      fun sf evs hevs hat =>
        hnext sf evs (by
          unfold M5DirOkEnv
          rw [hchg]
          by_cases hp : ((storesDirs g)[k]'hk).path = [] <;>
            simp only [hp, ↓reduceIte] <;>
            exact Or.inr ⟨[], evs, rfl, rfl, m5BufDeallocEnv_freeOnly curCap hevs⟩) hat
  | cons e0 rest0 =>
    have hpos_chg : 0 < (e0 :: rest0).length := by simp
    have hchg_lt : (e0 :: rest0).length < 2 ^ 58 := by rw [← hchg]; m5_omega
    have hchg_ne0 : (BitVec.ofNat 64 (e0 :: rest0).length == 0#64) = false :=
      ofNat_beq_zero_false hpos_chg (by m5_omega)
    have hchg_ne0' : BitVec.ofNat 64 (e0 :: rest0).length ≠ 0#64 := by
      intro heq; rw [heq] at hchg_ne0; cases hchg_ne0
    have hmul48 : BitVec.ofNat 64 (e0 :: rest0).length * 48#64 =
        BitVec.ofNat 64 ((e0 :: rest0).length * 48) :=
      (BitVec.ofNat_mul (e0 :: rest0).length 48).symm
    have hcarve := m5DirPopRest_carve_scratch_placed A.repAlloc fsp outCap outPtr
      (BitVec.ofNat 64 out.length) inCap inPtr g hk
    refine SepWPp.weaken_pre
      (sepConj_mono_right <| sepConj_mono_right <| sepConj_mono_right <| sepConj_mono_left hcarve) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun v20 => ?_; refine SepWPp.exists_elim fun v28 => ?_
    refine SepWPp.exists_elim fun v30 => ?_; refine SepWPp.exists_elim fun v38 => ?_
    refine SepWPp.exists_elim fun v40 => ?_; refine SepWPp.exists_elim fun v48 => ?_
    refine SepWPp.exists_elim fun v58 => ?_; refine SepWPp.exists_elim fun v458 => ?_
    refine SepWPp.exists_elim fun v460 => ?_; refine SepWPp.exists_elim fun v468 => ?_
    by_cases hdpath : ((storesDirs g)[k]'hk).path = []
    · have hdpath0 : BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length = 0#64 := by simp [hdpath]
      have hfit_b : FitsEnv M lim st (M5LoopBRestOkEnv (e0 :: rest0)) :=
        Eq.mp (congrArg (FitsEnv M lim st)
          (funext fun evs => by simp only [M5DirOkEnv, hdpath, ↓reduceIte, hchg])) hfit
      refine m5_run_pool_placed hbase.inv (mid := mPcPlaced 0x9e8)
        (P0 := (((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
          ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
          (((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) + 0x08#64) ↦₆₄
            BitVec.ofNat 64 (e0 :: rest0).length) ∗
          ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
            BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length) ∗
          ((s.sp + 0x20#64) ↦₆₄ v20) ∗ (((s.sp + 0x20#64) + 0x08#64) ↦₆₄ v28) ∗
          ((s.sp + 0x30#64) ↦₆₄ v30) ∗ (((s.sp + 0x30#64) + 0x08#64) ↦₆₄ v38))
        (F := ((dAddr + 0x18#64) ↦₆₄ dPathPtr) ∗
          ((fsp + 0x40#64) ↦₆₄ v40) ∗ ((fsp + 0x48#64) ↦₆₄ v48) ∗ ((fsp + 0x58#64) ↦₆₄ v58) ∗
          ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗ ((fsp + 0x468#64) ↦₆₄ v468) ∗
          (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
          vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (e0 :: rest0) ∗
          m5DirWorkMidPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
            inCap inPtr g k ∗
          ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ anyHeap)
        (by
          unfold m5ScratchPlaced
          rw [← hoff16]
          dsimp only [dAddr, fsp]
          rw [← hbase.sp, ← hsp40, ← hsp56]
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      by_vm_steps (
        m5_steps
        refine SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl])
          (by simp only [arm64_norm, hrun])
          ⟨by simp only [wp_norm, arm64_norm], fun hpcm hrunm hinv_m => ?_⟩
        exact m5_loop_b_entries_of_placed (io := io) (F0 := F0) (tr0 := tr0) (g := g) (n := n)
          (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
          (buf := buf) (curCap := curCap) (curPtr := curPtr) (out := out) (inp := inp) (ps := ps)
          hc.allocFs hc hio hstk_ext hstk_hook hstk64 hk hpaths hdpath
          (e0 :: rest0) [] _ v40 v48 v58 v458 v460 v468 _ (List.cons_ne_nil _ _) hfit_b
          (fun se evsErr errE herr_b hE =>
            herr se evsErr errE curCap curPtr ((storesDirs g)[k]'hk).changed
              (by simp only [M5DirErrEnv, hdpath, ↓reduceIte, hchg]; exact herr_b) hE)
          (fun sf evs hok_b hsf =>
            hnext sf evs (by simp only [M5DirOkEnv, hdpath, ↓reduceIte, hchg]; exact hok_b) hsf)
          hchg
          (hbase.mk_step hpcm hrunm (by simp only [arm64_norm]) (by simp only [arm64_norm])
            hinv_m (by simp only [calleeSavedVRegs, arm64_norm]))
          (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hchg])
          (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, add_two_mul_shl4_eq_mul48 hchg_lt])
          (by simp only [arm64_norm, List.map_nil, List.append_nil]; exact hs.files)
          (by simp only [arm64_norm]; exact hs.trace) (by simp only [arm64_norm, hs.stdout])
          (by
            generalize A.pool lim st _ = poolTerm
            dsimp only [dAddr] at hoff16 ⊢
            rw [hoff16, hsp40, hsp56, hbase.sp, hx25_cell]
            have hhdr := dirHeader_entails_memRegion dAddr curCap curPtr
              (BitVec.ofNat 64 (e0 :: rest0).length) dPathPtr
              (BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)
            dsimp only [dAddr, fsp] at hhdr hdAddr_eq ⊢
            have hord :
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x10#64) ↦₆₄
                      BitVec.ofNat 64 (e0 :: rest0).length) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
                      BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x20#64) ↦₆₄ curCap) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x28#64) ↦₆₄ curPtr) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x30#64) ↦₆₄
                      (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64)) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x38#64) ↦₆₄
                      BitVec.ofNat 64 (k + 1))) ∗
                  ((((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x40#64) ↦₆₄ v40) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x48#64) ↦₆₄ v48) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x58#64) ↦₆₄ v58) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x458#64) ↦₆₄ v458) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x460#64) ↦₆₄ v460) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x468#64) ↦₆₄ v468) ∗
                    (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
                    vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (e0 :: rest0) ∗
                    m5DirWorkMidPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap
                      outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
                    ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
                    ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
                    argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
                    mainSaved s0 ∗
                    stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
                    anyHeap) ∗
                    poolTerm) =
                (((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x10#64) ↦₆₄
                      BitVec.ofNat 64 (e0 :: rest0).length) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
                      BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)) ∗
                  m5DirWorkMidPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap
                    outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k) ∗
                ((dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗ anyHeap) ∗
                (vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (e0 :: rest0) ∗
                  m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) curCap curPtr
                    (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
                    v40 v48 v58 v458 v460 v468 ∗
                  ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
                  ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
                  argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
                  mainSaved s0 ∗
                  stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
                  poolTerm) := by
              unfold m5ScratchPlaced; sep_ac_rfl
            rw [hord]
            refine Entails.trans
              (sepConj_mono (sepConj_mono_left hhdr) (sepConj_mono_left (sep_anyHeap_absorb _))) ?_
            rw [hdAddr_eq, m5DirWorkMid_finish_placed A.repAlloc _ outCap outPtr
              (BitVec.ofNat 64 out.length) inCap inPtr g hk, List.nil_append]
            exact Entails.of_eq (by sep_ac_rfl)))
    · have hpos_dp : 0 < ((storesDirs g)[k]'hk).path.length := List.length_pos_of_ne_nil hdpath
      have he0_mem : e0 ∈ ((storesDirs g)[k]'hk).changed := by rw [hchg]; exact .head _
      have ⟨_, hp_lt32⟩ := dir_entry_path_ok_len hk hpaths he0_mem
      have hplen := pathOf_ne_nil hdpath e0.1
      have hd_lt32 : ((storesDirs g)[k]'hk).path.length < 2 ^ 32 := by
        have hlen_eq : (pathOf ((storesDirs g)[k]'hk).path e0.1).length =
            ((storesDirs g)[k]'hk).path.length + 1 + e0.1.length := by
          rw [hplen]; simp; omega
        m5_omega
      have hdp_ne0 : (BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length == 0#64) = false :=
        ofNat_beq_zero_false hpos_dp (by m5_omega)
      have hdp_ne0' : BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length ≠ 0#64 := by
        intro heq; rw [heq] at hdp_ne0; cases hdp_ne0
      have hdp_b63a : (BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length).getLsbD 63 = false :=
        ofNat_getLsbD_63_false (by m5_omega)
      have hdp_b63b : (BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)[63] = false :=
        ofNat_getElem_63_false (by m5_omega)
      have hfit_a :
          FitsEnv M lim st
            (M5LoopARestOkEnv ((storesDirs g)[k]'hk).path (e0 :: rest0)) :=
        Eq.mp (congrArg (FitsEnv M lim st)
          (funext fun evs => by simp only [M5DirOkEnv, hdpath, ↓reduceIte, hchg])) hfit
      refine m5_run_pool_placed hbase.inv (mid := mPcPlaced 0x8fc)
        (P0 := (((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
          ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
          (((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) + 0x08#64) ↦₆₄
            BitVec.ofNat 64 (e0 :: rest0).length) ∗
          ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
          ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
            BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length) ∗
          ((s.sp + 0x20#64) ↦₆₄ v20) ∗ (((s.sp + 0x20#64) + 0x08#64) ↦₆₄ v28) ∗
          ((s.sp + 0x30#64) ↦₆₄ v30) ∗ (((s.sp + 0x30#64) + 0x08#64) ↦₆₄ v38) ∗
          ((s.sp + 0x40#64) ↦₆₄ v40))
        (F := ((fsp + 0x48#64) ↦₆₄ v48) ∗ ((fsp + 0x58#64) ↦₆₄ v58) ∗
          ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗
          ((fsp + 0x468#64) ↦₆₄ v468) ∗
          (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
          vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (e0 :: rest0) ∗
          m5DirWorkMidPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
            inCap inPtr g k ∗
          ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ anyHeap)
        (by
          unfold m5ScratchPlaced
          rw [← hoff16]
          dsimp only [dAddr, fsp]
          rw [← hbase.sp, ← hsp40, ← hsp56]
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      by_vm_steps (
        m5_steps
        refine SepWP.done (by simp only [arm64_norm, mPcPlaced_eq_blkPl])
          (by simp only [arm64_norm, hrun])
          ⟨by simp only [wp_norm, arm64_norm], fun hpcm hrunm hinv_m => ?_⟩
        exact m5_loop_a_entries_of_placed (io := io) (F0 := F0) (tr0 := tr0) (g := g) (n := n)
          (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
          (buf := buf) (curCap := curCap) (curPtr := curPtr) (dPathPtr := dPathPtr) (v58 := v58)
          (out := out) (inp := inp) (ps := ps)
          hc.allocFs hc hio hstk_ext hstk_hook hstk_res hstk64 hk hpaths hdpath
          (e0 :: rest0) [] _ v48 v458 v460 v468 _ (List.cons_ne_nil _ _) hfit_a
          (fun se evsErr errE herr_a hE =>
            herr se evsErr errE curCap curPtr ((storesDirs g)[k]'hk).changed
              (by simp only [M5DirErrEnv, hdpath, ↓reduceIte, hchg]; exact herr_a) hE)
          (fun sf evs hok_a hsf =>
            hnext sf evs (by simp only [M5DirOkEnv, hdpath, ↓reduceIte, hchg]; exact hok_a) hsf)
          hchg
          (hbase.mk_step hpcm hrunm (by simp only [arm64_norm]) (by simp only [arm64_norm])
            hinv_m (by simp only [calleeSavedVRegs, arm64_norm]))
          (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hchg])
          (by simp only [arm64_norm, hx24])
          (by simp only [arm64_norm, add_two_mul_shl4_eq_mul48 hchg_lt])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, List.map_nil, List.append_nil]; exact hs.files)
          (by simp only [arm64_norm]; exact hs.trace) (by simp only [arm64_norm, hs.stdout])
          (by
            generalize A.pool lim st _ = poolTerm
            dsimp only [dAddr] at hoff16 ⊢
            rw [hoff16, hsp40, hsp56, hbase.sp, hx25_cell]
            have hhdr := dirHeader_entails_memRegion dAddr curCap curPtr
              (BitVec.ofNat 64 (e0 :: rest0).length) dPathPtr
              (BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)
            dsimp only [dAddr, fsp] at hhdr hdAddr_eq ⊢
            have hord :
                ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x10#64) ↦₆₄
                      BitVec.ofNat 64 (e0 :: rest0).length) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
                      BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x20#64) ↦₆₄ curCap) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x28#64) ↦₆₄ curPtr) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x30#64) ↦₆₄
                      (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64)) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x38#64) ↦₆₄
                      BitVec.ofNat 64 (k + 1)) ∗
                    ((s0.sp - BitVec.ofNat 64 mainFrameSize + 0x40#64) ↦₆₄ dPathPtr)) ∗
                  ((((fsp + 0x48#64) ↦₆₄ v48) ∗
                    ((fsp + 0x58#64) ↦₆₄ v58) ∗
                    ((fsp + 0x458#64) ↦₆₄ v458) ∗
                    ((fsp + 0x460#64) ↦₆₄ v460) ∗
                    ((fsp + 0x468#64) ↦₆₄ v468) ∗
                    (dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
                    vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (e0 :: rest0) ∗
                    m5DirWorkMidPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
                      inCap inPtr g k ∗
                    ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
                    ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
                    argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
                    mainSaved s0 ∗
                    stackAt fsp (stk - mainFrameSize) ∗
                    anyHeap) ∗
                    poolTerm) =
                (((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) ↦₆₄ curCap) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x08#64) ↦₆₄ curPtr) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x10#64) ↦₆₄
                      BitVec.ofNat 64 (e0 :: rest0).length) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x18#64) ↦₆₄ dPathPtr) ∗
                    ((((s0.sp - 792#64) + BitVec.ofNat 64 k * 40#64) + 0x20#64) ↦₆₄
                      BitVec.ofNat 64 ((storesDirs g)[k]'hk).path.length)) ∗
                  m5DirWorkMidPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap
                    outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k) ∗
                ((dPathPtr ↦ᵣ ((storesDirs g)[k]'hk).path) ∗
                  vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr (e0 :: rest0) ∗
                  m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) curCap curPtr
                    (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
                    dPathPtr v48 v58 v458 v460 v468 ∗
                  ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
                  ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
                  argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
                  mainSaved s0 ∗
                  stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
                  poolTerm ∗ anyHeap) := by
              dsimp only [fsp]; unfold m5ScratchPlaced; sep_ac_rfl
            rw [hord]
            refine Entails.trans (sepConj_mono_left (sepConj_mono_left hhdr)) ?_
            rw [hdAddr_eq, m5DirWorkMid_finish_placed A.repAlloc _ outCap outPtr
              (BitVec.ofNat 64 out.length) inCap inPtr g hk, List.nil_append]
            exact Entails.of_eq (by sep_ac_rfl)))

/-- Budget-threaded execution of one `Dir k` (`k < 8`) iteration of `main`'s outer M5 loop
(`M+0x8b8`) under `FitsEnv`, advancing to `AtM5LoopPlaced … (k + 1)` or exiting via `herr` on
`write_file` failure. -/
theorem m5_dir_step_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n k : Nat}
    {outCap outPtr inCap inPtr buf : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hk : k < 8)
    (hfit : FitsEnv M lim st (M5DirOkEnv ((storesDirs g)[k]'(by simp [hk]))))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hs : AtM5LoopPlaced CodeOk io F0 tr0 g s0 s n buf k)
    (herr : ∀ (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced)
        (curCap curPtr : BitVec 64)
        (curEntries : List (List (BitVec 8) × List (BitVec 8))),
      M5DirErrEnv ((storesDirs g)[k]'(by simp [hk])) errE evsErr →
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k curEntries errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
          s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          curEntries errE)
        Q Qp oom)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      M5DirOkEnv ((storesDirs g)[k]'(by simp [hk])) evs →
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
        (m5LoopMemPlaced (A.atState lim (M.stepEvents evs st) sf)
          s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (m5LoopMemPlaced (A.atState lim st s) s0 stk n outCap outPtr inCap inPtr buf out inp ps g k)
      Q Qp oom :=
  m5_dir_step_of_placed hc
    ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio)
    hk hfit hstk hstk64 hpaths hs herr hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DirStepPlacedBudget
