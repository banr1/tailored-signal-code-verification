/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5MovesPlacedBudget

/-!
# Budget-Threaded Relocatable `main` Hop M5 (`M+0x7b0 → M+0xf70`, Block `617`)

Composes `m5_moves_placed`, `m5_loop_placed`, and `m5_drop_for_m5_placed` on Block `617` under
`FitsEnv M lim st (M5Env g)`, and bridges `M5Env g` into `CliMainPeakSpec.M5PhaseEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5PlacedBudget

set_option linter.dupNamespace false

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (DirGhost StoresGhost pathOf)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtM4EndPlaced AtM6Placed CallV IoModel LsCodeInv M5ErrEntryPlaced argsBuf commitFiles inputOf
   locals m5CellsPlaced m5LoopMemPlaced m6CellsPlaced mainFrameSize mainSaved ownedBytes storesDirs)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (WriteFileEnv writeFileEnv_nil)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (CliWriteFileEnv M5DirStepEnv M5LoopAEntryEnv M5PhaseEnv M5WriteStepEnv)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv IterSeqEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced mainIoBoundedPlaced_iff_mainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (MainIoPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DirStepPlacedBudget
  (M5DirErrEnv M5DirOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPlacedBudget
  (M5LoopARestErrEnv M5LoopARestOkEnv M5LoopAStepEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPathPlacedBudget
  (m5LoopABuildPathEvents m5LoopAPathCap)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopATailPlacedBudget
  (m5LoopATailCap m5LoopATailEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBPlacedBudget
  (M5LoopBRestErrEnv M5LoopBRestOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopDropPlacedBudget
  (m5ErrEntryDropEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopPlacedBudget
  (M5DirsErrEnv M5DirsOkEnv m5_loop_of_placed m5_loop_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPlacedBudget
  (m5ErrMem_eq_atState m5_drop_for_m5_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5MovesPlacedBudget
  (m5_moves_placed)

/-- Unified allocator event envelope for `main`'s entire M5 phase (`M+0x7b0 → M+0xf70`), covering
both full 8-`Dir` commit (`ok = true`) and `write_file`-error early exit followed by
`m5_drop_for_m5_placed` cleanup (`ok = false`, via `IterSeqEnv` prefix early-exit +
`m5ErrEntryDropEvents` + `FreeOnlyEvs`). -/
def M5Env (g : StoresGhost) (evs : List AllocEvent) : Prop :=
  SeqEnv (M5DirsOkEnv (storesDirs g)) FreeOnlyEvs evs

example : ∃ evs, M5Env .opened evs :=
  ⟨[], Or.inl (Or.inl (Or.inl rfl))⟩

private theorem writeFileEnv_imp_cliWriteFileEnv {len : Nat} {evs : List AllocEvent}
    (h : WriteFileEnv len evs) : CliWriteFileEnv len evs := by
  rcases h with rfl | ⟨hle, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hle, rfl⟩

private theorem m5LoopAStepEnv_imp_entry (dir name : List (BitVec 8)) {evs : List AllocEvent}
    (h : M5LoopAStepEnv dir name evs) :
    M5LoopAEntryEnv dir name evs := by
  obtain ⟨evsErr, evsFree, rfl, herr, hfree⟩ := h
  obtain ⟨evsBuild, evsWr, rfl, hbuild, hwr⟩ := herr
  rw [hbuild]
  unfold m5LoopAPathCap m5LoopATailCap at hfree
  unfold M5LoopAEntryEnv m5LoopABuildPathEvents m5LoopATailEvents
  dsimp only at hfree ⊢
  by_cases hlt : reserveCap dir.length dir.length 1 - (dir.length + 1) < name.length <;>
    simp only [hlt, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] at hfree ⊢
  · exact ConcatEnv.append
      (ConcatEnv.append (ConcatEnv.append (ConcatEnv.append rfl rfl) rfl)
        (writeFileEnv_imp_cliWriteFileEnv hwr))
      hfree
  · exact ConcatEnv.append
      (ConcatEnv.append (ConcatEnv.append (ConcatEnv.append rfl rfl) rfl)
        (writeFileEnv_imp_cliWriteFileEnv hwr))
      hfree

private theorem seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h₁ : ∀ evs, E₁ evs → E₁' evs) (h₂ : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) : SeqEnv E₁' E₂' evs := by
  rcases h with h | ⟨evs₁, evs₂, rfl, he₁, he₂⟩
  · exact Or.inl (h₁ _ h)
  · exact Or.inr ⟨evs₁, evs₂, rfl, h₁ _ he₁, h₂ _ he₂⟩

private theorem iterSeqEnv_map_imp {α β : Type} (f : α → β)
    {Step₁ : α → List AllocEvent → Prop} {Step₂ : β → List AllocEvent → Prop}
    {xs : List α} (hstep : ∀ x ∈ xs, ∀ evs, Step₁ x evs → Step₂ (f x) evs) :
    ∀ {evs : List AllocEvent},
      IterSeqEnv Step₁ xs evs → IterSeqEnv Step₂ (xs.map f) evs := by
  induction xs with
  | nil =>
    intro evs h
    exact h
  | cons x xs ih =>
    intro evs h
    exact seqEnv_mono
      (hstep x List.mem_cons_self)
      (fun evs' h' => ih (fun y hy => hstep y (List.mem_cons_of_mem x hy)) h')
      h

private theorem m5DirOkEnv_imp_m5DirStepEnv {d : DirGhost}
    (hd_dirty : d.changed ≠ [] → d.path ≠ [])
    {evs : List AllocEvent} (h : M5DirOkEnv d evs) :
    M5DirStepEnv d.path (d.changed.map Prod.fst) evs := by
  unfold M5DirOkEnv at h
  cases hchg : d.changed with
  | nil =>
    rw [hchg] at h
    by_cases hp : d.path = [] <;> simp only [hp, ↓reduceIte] at h
    · exact h
    · exact h
  | cons e rest =>
    have hd_ne : d.path ≠ [] := hd_dirty (by simp [hchg])
    rw [hchg] at h
    simp only [hd_ne, ↓reduceIte] at h
    refine seqEnv_mono ?_ (fun _ hf => hf) h
    intro evs' hiter
    refine iterSeqEnv_map_imp Prod.fst ?_ hiter
    intro x _ evsStep hstep
    unfold M5WriteStepEnv
    simp only [hd_ne, ↓reduceIte]
    exact m5LoopAStepEnv_imp_entry d.path x.1 hstep

/-- Inclusion bridge into `CliMainPeakSpec.M5PhaseEnv` whenever every dirty `Dir` has a non-empty
directory path (satisfied unconditionally by `StoresGhost.opened` and every `signal_session::run`
output, since `identity.own` is read-only and all 7 mutable `Dir`s have non-empty paths). -/
theorem m5Env_imp_m5PhaseEnv {g : StoresGhost}
    (hdirs : ∀ d ∈ storesDirs g, d.changed ≠ [] → d.path ≠ [])
    {evs : List AllocEvent} (h : M5Env g evs) :
    M5PhaseEnv ((storesDirs g).map (fun d => (d.path, d.changed.map Prod.fst))) evs := by
  refine seqEnv_mono ?_ (fun _ hf => hf) h
  intro evs' hiter
  refine iterSeqEnv_map_imp (fun d => (d.path, d.changed.map Prod.fst)) ?_ hiter
  intro d hd evsDir hdir
  exact m5DirOkEnv_imp_m5DirStepEnv (hdirs d hd) hdir

private theorem m5LoopARestErrEnv_complete {dir : List (BitVec 8)} {errE : M5ErrEntryPlaced} :
    ∀ {entries : List (List (BitVec 8) × List (BitVec 8))} {evsErr : List AllocEvent},
      M5LoopARestErrEnv dir errE entries evsErr →
      M5LoopARestOkEnv dir entries (evsErr ++ m5ErrEntryDropEvents errE)
  | [], _, h => False.elim h
  | _ :: _, evsErr, h => by
    rcases h with ⟨herrStep, hdropEq⟩ | ⟨evs1, evs2, rfl, hstep1, herrRest⟩
    · exact Or.inl (Or.inl ⟨evsErr, m5ErrEntryDropEvents errE, rfl, herrStep, hdropEq⟩)
    · rw [List.append_assoc]
      rcases m5LoopARestErrEnv_complete herrRest with hiter | ⟨eM, eF, heq, hiter, hfree⟩
      · exact Or.inl (Or.inr ⟨evs1, evs2 ++ m5ErrEntryDropEvents errE, rfl, hstep1, hiter⟩)
      · exact Or.inr ⟨evs1 ++ eM, eF, by rw [List.append_assoc, heq],
          Or.inr ⟨evs1, eM, rfl, hstep1, hiter⟩, hfree⟩

private theorem m5LoopBRestErrEnv_complete {errE : M5ErrEntryPlaced} :
    ∀ {entries : List (List (BitVec 8) × List (BitVec 8))} {evsErr : List AllocEvent},
      M5LoopBRestErrEnv errE entries evsErr →
      M5LoopBRestOkEnv entries (evsErr ++ m5ErrEntryDropEvents errE)
  | [], _, h => False.elim h
  | _ :: _, _, h => by
    rcases h with ⟨_, hstep⟩ | ⟨evs1, evs2, rfl, hstep1, herrRest⟩
    · exact Or.inl (Or.inl hstep)
    · rw [List.append_assoc]
      rcases m5LoopBRestErrEnv_complete herrRest with hiter | ⟨eM, eF, heq, hiter, hfree⟩
      · exact Or.inl (Or.inr ⟨evs1, evs2 ++ m5ErrEntryDropEvents errE, rfl, hstep1, hiter⟩)
      · exact Or.inr ⟨evs1 ++ eM, eF, by rw [List.append_assoc, heq],
          Or.inr ⟨evs1, eM, rfl, hstep1, hiter⟩, hfree⟩

private theorem m5DirErrEnv_complete {d : DirGhost} {errE : M5ErrEntryPlaced}
    {evsErr : List AllocEvent} (h : M5DirErrEnv d errE evsErr) :
    M5DirOkEnv d (evsErr ++ m5ErrEntryDropEvents errE) := by
  unfold M5DirErrEnv at h
  unfold M5DirOkEnv
  by_cases hp : d.path = [] <;> simp only [hp, ↓reduceIte] at h ⊢
  · exact m5LoopBRestErrEnv_complete h
  · exact m5LoopARestErrEnv_complete h

private theorem m5DirsErrEnv_complete {errE : M5ErrEntryPlaced} :
    ∀ {dirs : List DirGhost} {evsErr : List AllocEvent},
      M5DirsErrEnv errE dirs evsErr →
      M5DirsOkEnv dirs (evsErr ++ m5ErrEntryDropEvents errE)
  | [], _, h => False.elim h
  | _ :: _, _, h => by
    rcases h with hdErr | ⟨evs1, evs2, rfl, hdOk, hdsErr⟩
    · exact Or.inl (m5DirErrEnv_complete hdErr)
    · rw [List.append_assoc]
      exact Or.inr ⟨evs1, evs2 ++ m5ErrEntryDropEvents errE, rfl, hdOk,
        m5DirsErrEnv_complete hdsErr⟩

private theorem m5Env_of_err {g : StoresGhost} {errE : M5ErrEntryPlaced}
    {evsErr evsDrop evsRest : List AllocEvent}
    (herr : M5DirsErrEnv errE (storesDirs g) evsErr)
    (hdrop : evsDrop = m5ErrEntryDropEvents errE ++ evsRest)
    (hfree : FreeOnlyEvs evsRest) :
    M5Env g (evsErr ++ evsDrop) := by
  rw [hdrop, ← List.append_assoc]
  exact Or.inr ⟨evsErr ++ m5ErrEntryDropEvents errE, evsRest, rfl,
    m5DirsErrEnv_complete herr, hfree⟩

-- Non-vacuity witness: path allocation followed by `0xbdc` write-error cleanup
-- emits both `AllocEvent.alloc` and `m5ErrEntryDropEvents errE` inside `M5Env gErr`.
example :
    let dir : List (BitVec 8) := [0x61#8]
    let name : List (BitVec 8) := [0x62#8]
    let errE : M5ErrEntryPlaced :=
      .bdc (BitVec.ofNat 64 (m5LoopAPathCap dir name)) 1#64 []
    let gErr : StoresGhost :=
      { StoresGhost.opened with
        identity := { StoresGhost.opened.identity with
          own := { path := dir, changed := [(name, [])] } } }
    ∃ evsErr evsDrop evsRest,
      (∃ sz, AllocEvent.alloc sz ∈ evsErr ++ evsDrop) ∧
      m5ErrEntryDropEvents errE ≠ [] ∧
      (∀ ev ∈ m5ErrEntryDropEvents errE, ev ∈ evsErr ++ evsDrop) ∧
      (evsDrop = m5ErrEntryDropEvents errE ++ evsRest ∧ FreeOnlyEvs evsRest) ∧
      M5Env gErr (evsErr ++ evsDrop) := by
  refine ⟨m5LoopABuildPathEvents [0x61#8] [0x62#8] ++ [],
    m5ErrEntryDropEvents (.bdc (BitVec.ofNat 64 (m5LoopAPathCap [0x61#8] [0x62#8])) 1#64 []),
    [], ?_, ?_, ?_, ⟨by simp, FreeOnlyEvs.nil⟩, ?_⟩
  · exact ⟨1, by simp [m5LoopABuildPathEvents, rustAllocEvents]⟩
  · simp [m5ErrEntryDropEvents, rustDeallocEvents]
  · intro ev hev
    exact List.mem_append_right _ hev
  · refine m5Env_of_err
      (errE := .bdc (BitVec.ofNat 64 (m5LoopAPathCap [0x61#8] [0x62#8])) 1#64 [])
      ?_ (by simp) FreeOnlyEvs.nil
    refine Or.inl ?_
    change M5LoopARestErrEnv [0x61#8] _ [([0x62#8], [])] _
    exact Or.inl ⟨ConcatEnv.append rfl (writeFileEnv_nil (pathOf [0x61#8] [0x62#8]).length), rfl⟩

/-- `{StdinEnv ReadEnv}`-parametric budget-threaded M5 hop (`M+0x7b0 → M+0xf70`) on Block `617`
under `FitsEnv M lim st (M5Env g)`: composes `m5_moves_placed`, `m5_loop_of_placed`, and
`m5_drop_for_m5_placed` while advancing `A.pool` by `M5Env g`. -/
theorem main_m5_of_proof_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {g : StoresGhost}
    {out : List (BitVec 8)} {s0 s : State} {stk hookStack resStack : Nat}
    {buf inCap inPtr : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hfit : FitsEnv M lim st (M5Env g))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hs : AtM4EndPlaced CodeOk i s0 s c i.argv.length buf inCap)
    (hnext : ∀ (s' : State) (evs : List AllocEvent) (ok : Bool) (outCap outPtr : BitVec 64),
      M5Env g evs →
      (match commitFiles io.wr s.fs.files g.writes with
       | some F => ok = true ∧ s'.fs.files = F
       | none => ok = false) →
      s.trace <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout s.trace →
      AtM6Placed CodeOk s0 s' ok i.argv.length buf →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
              (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s' ∗ anyHeap)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  have hext : mainFrameSize + extHookStack ≤ stk := by omega
  refine m5_moves_placed (inp := inputOf i c) (n := i.argv.length) (io := io) (g := g)
    (out := out) (ps := ps) (st := st) hc.allocFs hext hs ?_
  intro s1 outCap outPtr _hvm1 _hfs1 _htr1 hloop
  refine m5_loop_of_placed (F0 := s.fs.files) (tr0 := s.trace) (st := st)
    hc hio hfit.seq_left hstk hstk64 hpaths hloop (Entails.refl _) ?_ ?_
  · intro k se evsErr errE curCap curPtr curEntries herr_dirs herr_st
    rw [← m5ErrMem_eq_atState]
    refine m5_drop_for_m5_placed (s := s) (i := i) (c := c)
      (st := M.stepEvents evsErr st) hc.allocFs hext herr_st ?_
    intro s' evsDrop evsRest ok outCap' outPtr' hsplit hcommit htr hstdout hat6
    rcases hsplit with ⟨hdrop_eq, hfree_rest⟩
    rw [← M.stepEvents_append evsErr evsDrop st]
    exact hnext s' (evsErr ++ evsDrop) ok outCap' outPtr'
      (m5Env_of_err herr_dirs hdrop_eq hfree_rest) hcommit htr hstdout hat6
  · intro s' evs hok_dirs hcommit hpre hstdout hat6
    exact hnext s' evs true outCap outPtr (Or.inl hok_dirs)
      (by rw [hcommit]; exact ⟨rfl, rfl⟩) hpre hstdout hat6

/-- Budget-threaded M5 hop (`M+0x7b0 → M+0xf70`) on Block `617` under `FitsEnv M lim st (M5Env g)`:
composes `m5_moves_placed`, `m5_loop_placed`, and `m5_drop_for_m5_placed` while advancing `A.pool`
by `M5Env g`. -/
theorem main_m5_proof_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {uuidParse : UuidParser} {io : IoModel} {i : Inputs} {c : CallV} {g : StoresGhost}
    {out : List (BitVec 8)} {s0 s : State} {stk hookStack resStack : Nat}
    {buf inCap inPtr : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoPlaced A lim H io hookStack)
    (hfit : FitsEnv M lim st (M5Env g))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hs : AtM4EndPlaced CodeOk i s0 s c i.argv.length buf inCap)
    (hnext : ∀ (s' : State) (evs : List AllocEvent) (ok : Bool) (outCap outPtr : BitVec 64),
      M5Env g evs →
      (match commitFiles io.wr s.fs.files g.writes with
       | some F => ok = true ∧ s'.fs.files = F
       | none => ok = false) →
      s.trace <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout s.trace →
      AtM6Placed CodeOk s0 s' ok i.argv.length buf →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
              (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s' ∗ anyHeap)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp oom :=
  main_m5_of_proof_placed hc
    ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio)
    hfit hstk hstk64 hpaths hs hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5PlacedBudget
