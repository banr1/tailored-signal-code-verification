/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DirStepPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5AfterPlacedBudget

/-!
# Budget-Threaded M5 Outer Commit Loop (`M+0x8b8 .. M+0xae0 → M+0xf70`, Block `617`)

Budget-threaded verification of `Stores::commit`'s 8-`Dir` outer induction (`m5_loop_from_placed`,
`m5_loop_placed`) on Block `617` under `FitsEnv`, advancing `A.pool` by `M5DirsOkEnv` (or
`M5DirsErrEnv` on `write_file` failure).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopPlacedBudget

set_option linter.dupNamespace false

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession.Cli (DirGhost StoresGhost)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtM5LoopPlaced AtM6Placed IoModel LsCodeInv M5ErrEntryPlaced M5LoopErrPlaced argsBuf commitFiles
   locals m5ErrMemPlaced m5LoopMemPlaced m6CellsPlaced mainFrameSize mainSaved ownedBytes
   storesDirs)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (writeFileEnv_nil)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv IterSeqEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced mainIoBoundedPlaced_iff_mainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (MainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5AfterPlacedBudget (m5_done_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DirStepPlacedBudget
  (M5DirErrEnv M5DirOkEnv m5_dir_step_of_placed m5_dir_step_placed)

/-- Sequential allocator event envelope across a slice `dirs : List DirGhost` of `Stores::commit`
reaching `AtM6Placed … true`. -/
def M5DirsOkEnv (dirs : List DirGhost) (evs : List AllocEvent) : Prop :=
  IterSeqEnv M5DirOkEnv dirs evs

example : ∃ evs, M5DirsOkEnv [] evs :=
  ⟨[], rfl⟩

/-- Error-exit allocator event envelope across `dirs : List DirGhost` when a `write_file` call exits
to `M5LoopErrPlaced` at `errE`. -/
def M5DirsErrEnv (errE : M5ErrEntryPlaced) : List DirGhost → List AllocEvent → Prop
  | [], _ => False
  | d :: ds, evs =>
      M5DirErrEnv d errE evs ∨ ConcatEnv (M5DirOkEnv d) (M5DirsErrEnv errE ds) evs

example : ∃ evs, M5DirsErrEnv .bf4 [{ path := [], changed := [([], [])] }] evs :=
  ⟨[], Or.inl (Or.inl ⟨writeFileEnv_nil 0, writeFileEnv_nil 0⟩)⟩

/-- `{StdinEnv ReadEnv}`-parametric run of remaining `8 - k` `Dir`s from `AtM5LoopPlaced … k`
(`k ≤ 8`) through `M+0xadc -> M+0xc5c -> M+0xf70` under `FitsEnv`. -/
theorem m5_loop_from_of_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n : Nat}
    {outCap outPtr inCap inPtr buf : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) :
    ∀ (rem k : Nat) {st : M.σ} (s : State),
      rem + k = 8 →
      FitsEnv M lim st (M5DirsOkEnv ((storesDirs g).drop k)) →
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 s n buf k →
      (∀ (kErr : Nat) (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced)
          (curCap curPtr : BitVec 64)
          (curEntries : List (List (BitVec 8) × List (BitVec 8))),
        k ≤ kErr →
        M5DirsErrEnv errE ((storesDirs g).drop k) evsErr →
        M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf kErr curEntries errE →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
          (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
            s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g kErr
            curEntries errE)
          Q Qp oom) →
      (∀ (s' : State) (evs : List AllocEvent),
        M5DirsOkEnv ((storesDirs g).drop k) evs →
        commitFiles io.wr F0 g.writes = some s'.fs.files →
        tr0 <+: s'.trace →
        ProcessOutcome.traceStreamBytes .stdout s'.trace =
          ProcessOutcome.traceStreamBytes .stdout tr0 →
        AtM6Placed CodeOk s0 s' true n buf →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s'
          (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
            mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
                outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim (M.stepEvents evs st) s' ∗ anyHeap)
          Q Qp oom) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
        (m5LoopMemPlaced (A.atState lim st s) s0 stk n outCap outPtr inCap inPtr buf out inp ps g k)
        Q Qp oom := by
  intro rem
  induction rem with
  | zero =>
    intro k st s hrem _ hs _ hok
    have hk8 : k = 8 := by omega
    subst hk8
    have hdrop8 : (storesDirs g).drop 8 = [] := by
      have hlen : (storesDirs g).length = 8 := rfl
      simp [hlen]
    exact m5_done_placed hs fun s' hfiles htr0 hstdout hat6 => by
      have hm5ok : M5DirsOkEnv ((storesDirs g).drop 8) [] := by
        rw [hdrop8]
        rfl
      simpa only [AllocCostModel.stepEvents_nil] using hok s' [] hm5ok hfiles htr0 hstdout hat6
  | succ rem ih =>
    intro k st s hrem hfit hs herr hok
    have hk : k < 8 := by omega
    have hk_len : k < (storesDirs g).length := by
      change k < 8
      exact hk
    have hdrop_k : (storesDirs g).drop k =
        ((storesDirs g)[k]'hk_len) :: (storesDirs g).drop (k + 1) :=
      List.drop_eq_getElem_cons hk_len
    have hfit_hd : FitsEnv M lim st (M5DirOkEnv ((storesDirs g)[k]'hk_len)) := by
      unfold M5DirsOkEnv at hfit
      rw [hdrop_k] at hfit
      exact hfit.seq_left
    refine m5_dir_step_of_placed hc hio hk hfit_hd hstk hstk64 hpaths hs ?_ ?_
    · intro se evsErr errE curCap curPtr curEntries herr_d hE
      refine herr k se evsErr errE curCap curPtr curEntries (Nat.le_refl k) ?_ hE
      rw [hdrop_k]
      exact Or.inl herr_d
    · intro sf evs1 hok_d hsf
      have hfit_tl : FitsEnv M lim (M.stepEvents evs1 st)
          (M5DirsOkEnv ((storesDirs g).drop (k + 1))) := by
        unfold M5DirsOkEnv at hfit ⊢
        rw [hdrop_k] at hfit
        exact hfit.seq_right hok_d
      refine ih (k + 1) sf (by omega) hfit_tl hsf ?_ ?_
      · intro kErr se evsErr2 errE curCap curPtr curEntries hk1_le herr_tl hE
        rw [← M.stepEvents_append evs1 evsErr2 st]
        refine herr kErr se (evs1 ++ evsErr2) errE curCap curPtr curEntries
          (Nat.le_of_succ_le hk1_le) ?_ hE
        rw [hdrop_k]
        exact Or.inr ⟨evs1, evsErr2, rfl, hok_d, herr_tl⟩
      · intro s' evs2 hok_tl hfiles htr0 hstdout hat6
        rw [← M.stepEvents_append evs1 evs2 st]
        refine hok s' (evs1 ++ evs2) ?_ hfiles htr0 hstdout hat6
        unfold M5DirsOkEnv at hok_tl ⊢
        rw [hdrop_k]
        exact Or.inr ⟨evs1, evs2, rfl, hok_d, hok_tl⟩

/-- Run remaining `8 - k` `Dir`s from `AtM5LoopPlaced … k` (`k ≤ 8`) through
`M+0xadc -> M+0xc5c -> M+0xf70` under `FitsEnv`. -/
theorem m5_loop_from_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n : Nat}
    {outCap outPtr inCap inPtr buf : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) :
    ∀ (rem k : Nat) {st : M.σ} (s : State),
      rem + k = 8 →
      FitsEnv M lim st (M5DirsOkEnv ((storesDirs g).drop k)) →
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 s n buf k →
      (∀ (kErr : Nat) (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced)
          (curCap curPtr : BitVec 64)
          (curEntries : List (List (BitVec 8) × List (BitVec 8))),
        k ≤ kErr →
        M5DirsErrEnv errE ((storesDirs g).drop k) evsErr →
        M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf kErr curEntries errE →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
          (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
            s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g kErr
            curEntries errE)
          Q Qp oom) →
      (∀ (s' : State) (evs : List AllocEvent),
        M5DirsOkEnv ((storesDirs g).drop k) evs →
        commitFiles io.wr F0 g.writes = some s'.fs.files →
        tr0 <+: s'.trace →
        ProcessOutcome.traceStreamBytes .stdout s'.trace =
          ProcessOutcome.traceStreamBytes .stdout tr0 →
        AtM6Placed CodeOk s0 s' true n buf →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s'
          (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
            mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
                outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim (M.stepEvents evs st) s' ∗ anyHeap)
          Q Qp oom) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
        (m5LoopMemPlaced (A.atState lim st s) s0 stk n outCap outPtr inCap inPtr buf out inp ps g k)
        Q Qp oom :=
  m5_loop_from_of_placed
    (F0 := F0) (tr0 := tr0) (g := g) (n := n)
    (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr) (buf := buf)
    (out := out) (inp := inp) (ps := ps) (s0 := s0) (Q := Q) (Qp := Qp) (oom := oom)
    hc ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio) hstk hstk64 hpaths

/-- `{StdinEnv ReadEnv}`-parametric budget-threaded execution of `Stores::commit`'s 8-`Dir` outer
and inner loops (`M+0x8b8 .. M+0xae0`) and completion hop (`M+0xadc -> M+0xc5c -> M+0xf70`) under
`FitsEnv`, handing write errors to `herr` and full commit completion to `hok` at `AtM6Placed … true`. -/
theorem m5_loop_of_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n : Nat}
    {outCap outPtr inCap inPtr buf : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hfit : FitsEnv M lim st (M5DirsOkEnv (storesDirs g)))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hs : AtM5LoopPlaced CodeOk io F0 tr0 g s0 s n buf 0)
    (hP : P ⊢ m5LoopMemPlaced (A.atState lim st s)
      s0 stk n outCap outPtr inCap inPtr buf out inp ps g 0)
    (herr : ∀ (k : Nat) (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced)
        (curCap curPtr : BitVec 64)
        (curEntries : List (List (BitVec 8) × List (BitVec 8))),
      M5DirsErrEnv errE (storesDirs g) evsErr →
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k curEntries errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
          s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          curEntries errE)
        Q Qp oom)
    (hok : ∀ (s' : State) (evs : List AllocEvent),
      M5DirsOkEnv (storesDirs g) evs →
      commitFiles io.wr F0 g.writes = some s'.fs.files →
      tr0 <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      AtM6Placed CodeOk s0 s' true n buf →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
              outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s' ∗ anyHeap)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom :=
  SepWPp.weaken_pre hP
    (m5_loop_from_of_placed hc hio hstk hstk64 hpaths 8 0 s rfl hfit hs
      (fun kErr se evsErr errE curCap curPtr curEntries _ herr0 hE =>
        herr kErr se evsErr errE curCap curPtr curEntries herr0 hE)
      (fun s' evs hok0 hfiles htr0 hstdout hat6 =>
        hok s' evs hok0 hfiles htr0 hstdout hat6))

/-- Budget-threaded execution of `Stores::commit`'s 8-`Dir` outer and inner loops (`M+0x8b8 .. M+0xae0`)
and completion hop (`M+0xadc -> M+0xc5c -> M+0xf70`) under `FitsEnv`, handing write errors to `herr`
and full commit completion to `hok` at `AtM6Placed … true`. -/
theorem m5_loop_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n : Nat}
    {outCap outPtr inCap inPtr buf : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hfit : FitsEnv M lim st (M5DirsOkEnv (storesDirs g)))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hs : AtM5LoopPlaced CodeOk io F0 tr0 g s0 s n buf 0)
    (hP : P ⊢ m5LoopMemPlaced (A.atState lim st s)
      s0 stk n outCap outPtr inCap inPtr buf out inp ps g 0)
    (herr : ∀ (k : Nat) (se : State) (evsErr : List AllocEvent) (errE : M5ErrEntryPlaced)
        (curCap curPtr : BitVec 64)
        (curEntries : List (List (BitVec 8) × List (BitVec 8))),
      M5DirsErrEnv errE (storesDirs g) evsErr →
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k curEntries errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced (A.atState lim (M.stepEvents evsErr st) se)
          s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          curEntries errE)
        Q Qp oom)
    (hok : ∀ (s' : State) (evs : List AllocEvent),
      M5DirsOkEnv (storesDirs g) evs →
      commitFiles io.wr F0 g.writes = some s'.fs.files →
      tr0 <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      AtM6Placed CodeOk s0 s' true n buf →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
              outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s' ∗ anyHeap)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom :=
  m5_loop_of_placed hc
    ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio)
    hfit hstk hstk64 hpaths hs hP herr hok

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopPlacedBudget
