/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Fs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `AgreesOutsideReadHooks` and Read-Hook Generalization Bridges

Pointwise hook-map agreement outside `{lsReadFileSym, lsReadStdinSym}`, `TraceFsSound` transport
via `ReadHooksFsT`, `RunHooksPlaced` lifts, stack-monotone `readFileSpecPlaced` weakening, and
the `H`-parametric `initiate` slot predicate `CliInitSlotOkPlacedAt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.AgreesOutsideReadHooks

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement LsBlockBound
   libsignalMutatedBlocks lsmpl lsρ)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives bcmpName)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles TraceFsSound subroutine_ok_rocl_of_plain
   subroutine_ok_withLsCodeRoLoaded_of_plain
   withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet
  (HkdfPlacedHooks extHookStack lsMemcpySym lsMemsetSym memcpyName memmoveName memsetName)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced cliPanicSymbolsPlaced lsBlackBoxSym lsCompress256Sym
   lsDiffieHellmanSym lsDurationSinceSym lsFormatInnerSym lsFromUtf8Sym lsMemrchrSym
   lsPubFromSecretSym lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli
   lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsSharedSecretDropSym
   lsStaticSecretDropSym lsStringCloneSym)
open CryptoVerification.SignalSession.Cli (cliBcmpName)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliRunBudgets cliWrOk hookMemmove_fs hookNoop_fs)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunNeeds RunSem)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks CliGhostHooksFs FsTHooks IsFsC cliExternsPlaced_row cliGhostExterns
   cliGhostExterns_alloc cliGhostExterns_dealloc cliGhostExterns_memcpy_some
   cliGhostExterns_memset_some cliGhostExterns_other cliGhostExterns_realloc
   cliGhostExterns_shim fsTHooks_cliExternsPlaced fsTHooks_cliGhostExterns_of_fs fsTHooks_none
   fsT_externAt hookSat_of_eq panicked_fsT traceFsSound_of_fsTHooks)
open CryptoVerification.SignalSession.Cli.RunProofs (InitOk₀ cliInitiateNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (lsKemEncapsSym)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_sat_of_cliExternsPlaced filesOk₀ memmove_row_placed scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (ActiveReadFilePre ActiveReadFileRun hRead_of_hookSat
   hRead_rocl_of_hookSat hRead_withLsCodeRoLoaded_of_hookSat hookSat_withReadFileHook
   isPanicSymbol_lsReadFileSym readFileEntryGhostHook readFileGhostHook readFileGhostHook_ok
   withReadFileHook withReadFileHook_ne withReadFileHook_self)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks allocContractsFsPlaced_of_hookSat allocContractsXCliPlaced_of_hookSat
   cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliExternsPlaced_memcpyRegionRO_budget_sat cliExternsPlaced_memcpyRegion_budget_sat
   cliExternsPlaced_memcpy_budget_sat cliExternsPlaced_memmove_budget_sat
   cliExternsPlaced_memsetRegion_budget_sat cliExternsPlaced_memset_budget_sat
   cliExternsPlaced_realloc_budget_sat cliExternsPlaced_sessionMemcpyRegion_budget_sat
   cliExternsPlaced_sessionMemcpy_budget_sat cliExternsPlaced_sessionMemmove_budget_sat
   cliExternsPlaced_sessionMemsetRegion_budget_sat cliExternsPlaced_sessionMemset_budget_sat
   cliExternsPlaced_shim_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced readFileSpecPlaced)

/-! ## `withReadStdinHook` and `AgreesOutsideReadHooks` -/

export CryptoVerification.SignalSession.Cli.RunGlue (withReadStdinHook)

@[simp]
theorem withReadStdinHook_self (rsh : State → State) (ext : LibsignalHooks) :
    withReadStdinHook rsh ext lsReadStdinSym = some rsh := by
  simp [withReadStdinHook]

theorem withReadStdinHook_ne (rsh : State → State) (ext : LibsignalHooks) {s : String}
    (hne : s ≠ lsReadStdinSym) :
    withReadStdinHook rsh ext s = ext s := by
  simp [withReadStdinHook, beq_eq_false_iff_ne.mpr hne]

theorem hookSat_withReadStdinHook {α : Type} (ext : LibsignalHooks) {rsh : State → State}
    {spec : Spec α} (hok : HookOk rsh spec) :
    HookSat (withReadStdinHook rsh ext) lsReadStdinSym spec :=
  ⟨rsh, withReadStdinHook_self rsh ext, hok⟩

@[simp]
theorem isPanicSymbol_lsReadStdinSym : Rust.isPanicSymbol lsReadStdinSym = false := by
  simp [Rust.isPanicSymbol, lsReadStdinSym]

@[simp]
theorem withPanics_lsReadStdinSym (ext : LibsignalHooks) :
    Rust.withPanics ext lsReadStdinSym = ext lsReadStdinSym := by
  simp [Rust.withPanics, isPanicSymbol_lsReadStdinSym]

@[simp]
theorem withPanics_withReadStdinHook (rsh : State → State) (ext : LibsignalHooks) :
    Rust.withPanics (withReadStdinHook rsh ext) = withReadStdinHook rsh (Rust.withPanics ext) := by
  funext s
  unfold Rust.withPanics withReadStdinHook
  by_cases hs : s = lsReadStdinSym
  · subst hs
    simp [isPanicSymbol_lsReadStdinSym]
  · simp [beq_eq_false_iff_ne.mpr hs]

@[simp]
theorem withReadStdinHook_lsReadFileSym (rsh : State → State) (ext : LibsignalHooks) :
    withReadStdinHook rsh ext lsReadFileSym = ext lsReadFileSym :=
  withReadStdinHook_ne rsh ext (by decide)

theorem hookSat_readFile_withReadStdinHook {α : Type} (rsh : State → State) {ext : LibsignalHooks}
    {spec : Spec α} (hsat : HookSat ext lsReadFileSym spec) :
    HookSat (withReadStdinHook rsh ext) lsReadFileSym spec :=
  hookSat_of_eq (withReadStdinHook_lsReadFileSym rsh ext) hsat

/-- Pointwise hook-map agreement with `cliGhostExterns gh (cliExternsPlaced mmpl W)` outside the
    two read-hook symbols `{lsReadFileSym, lsReadStdinSym}`. -/
def AgreesOutsideReadHooks (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (H : LibsignalHooks) : Prop :=
  ∀ s : String, s ≠ lsReadFileSym → s ≠ lsReadStdinSym →
    H s = cliGhostExterns gh (cliExternsPlaced mmpl W) s

theorem agreesOutsideReadHooks_cliGhost (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) :
    AgreesOutsideReadHooks mmpl gh W (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  fun _ _ _ => rfl

theorem AgreesOutsideReadHooks.eq_of_ne {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    {W : CliHooks} {H : LibsignalHooks} (h : AgreesOutsideReadHooks mmpl gh W H)
    {s : String} (hFile : s ≠ lsReadFileSym := by decide)
    (hStdin : s ≠ lsReadStdinSym := by decide) :
    H s = cliGhostExterns gh (cliExternsPlaced mmpl W) s :=
  h s hFile hStdin

theorem AgreesOutsideReadHooks.withReadFileHook {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    {W : CliHooks} {H : LibsignalHooks} (rfh : State → State)
    (h : AgreesOutsideReadHooks mmpl gh W H) :
    AgreesOutsideReadHooks mmpl gh W (withReadFileHook rfh H) :=
  fun s hFile hStdin => (withReadFileHook_ne rfh H hFile).trans (h s hFile hStdin)

theorem AgreesOutsideReadHooks.withReadStdinHook {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    {W : CliHooks} {H : LibsignalHooks} (rsh : State → State)
    (h : AgreesOutsideReadHooks mmpl gh W H) :
    AgreesOutsideReadHooks mmpl gh W (withReadStdinHook rsh H) :=
  fun s hFile hStdin => (withReadStdinHook_ne rsh H hStdin).trans (h s hFile hStdin)

theorem agreesOutsideReadHooks_withReadStdin_withReadFile (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (rsh rfh : State → State) :
    AgreesOutsideReadHooks mmpl gh W
      (withReadStdinHook rsh
        (withReadFileHook rfh (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :=
  ((agreesOutsideReadHooks_cliGhost mmpl gh W).withReadFileHook rfh).withReadStdinHook rsh

theorem agreesOutsideReadHooks_cliGhost_updateRead (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (rf : Option { f : State → State // HookFsTraced IsFsC f })
    (rs : Option { f : State → State // HookFsTraced IsFsC f }) :
    AgreesOutsideReadHooks mmpl gh W
      (cliGhostExterns { gh with readFile := rf, readStdin := rs } (cliExternsPlaced mmpl W)) := by
  intro s hFile hStdin
  unfold cliGhostExterns
  simp [beq_eq_false_iff_ne.mpr hFile, beq_eq_false_iff_ne.mpr hStdin]

theorem AgreesOutsideReadHooks.hookSat {α : Type} {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    {W : CliHooks} {H : LibsignalHooks} (h : AgreesOutsideReadHooks mmpl gh W H)
    {s : String} {spec : Spec α}
    (hsat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) s spec)
    (hFile : s ≠ lsReadFileSym := by decide)
    (hStdin : s ≠ lsReadStdinSym := by decide) :
    HookSat H s spec :=
  hookSat_of_eq (h s hFile hStdin) hsat

theorem AgreesOutsideReadHooks.withPanics_eq_of_ne {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    {W : CliHooks} {H : LibsignalHooks} (h : AgreesOutsideReadHooks mmpl gh W H)
    {s : String} (hFile : s ≠ lsReadFileSym := by decide)
    (hStdin : s ≠ lsReadStdinSym := by decide) :
    Rust.withPanics H s = Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) s := by
  unfold Rust.withPanics
  by_cases hp : Rust.isPanicSymbol s
  · simp [hp]
  · simp [hp, h s hFile hStdin]

theorem AgreesOutsideReadHooks.hookSat_withPanics {α : Type} {mmpl : Obj.MultiPlacement}
    {gh : CliGhostHooks} {W : CliHooks} {H : LibsignalHooks}
    (h : AgreesOutsideReadHooks mmpl gh W H) {s : String} {spec : Spec α}
    (hsat : HookSat (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) s spec)
    (hFile : s ≠ lsReadFileSym := by decide)
    (hStdin : s ≠ lsReadStdinSym := by decide) :
    HookSat (Rust.withPanics H) s spec :=
  hookSat_of_eq (h.withPanics_eq_of_ne hFile hStdin) hsat

/-! ## `ReadHooksFsT` and `TraceFsSound` -/

/-- `HookFsTraced IsFsC` on the two read-hook slots (`lsReadFileSym` and `lsReadStdinSym`) of `H`. -/
structure ReadHooksFsT (H : LibsignalHooks) : Prop where
  readFile_fsT : ∀ f, H lsReadFileSym = some f → HookFsTraced IsFsC f
  readStdin_fsT : ∀ f, H lsReadStdinSym = some f → HookFsTraced IsFsC f

theorem readHooksFsT_cliGhost (mmpl : Obj.MultiPlacement) {gh : CliGhostHooks} (W : CliHooks)
    (hFs : CliGhostHooksFs gh) :
    ReadHooksFsT (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  let hAll := fsTHooks_cliGhostExterns_of_fs hFs (fsTHooks_cliExternsPlaced mmpl W)
  ⟨fun f hf => hAll lsReadFileSym f hf, fun f hf => hAll lsReadStdinSym f hf⟩

theorem ReadHooksFsT.withReadFileHook {rfh : State → State} {ext : LibsignalHooks}
    (hRfh : HookFsTraced IsFsC rfh) (hExt : ReadHooksFsT ext) :
    ReadHooksFsT (withReadFileHook rfh ext) where
  readFile_fsT f hf := by
    rw [withReadFileHook_self] at hf
    cases hf
    exact hRfh
  readStdin_fsT f hf := by
    rw [withReadFileHook_ne rfh ext (by decide)] at hf
    exact hExt.readStdin_fsT f hf

theorem ReadHooksFsT.withReadStdinHook {rsh : State → State} {ext : LibsignalHooks}
    (hRsh : HookFsTraced IsFsC rsh) (hExt : ReadHooksFsT ext) :
    ReadHooksFsT (withReadStdinHook rsh ext) where
  readFile_fsT f hf := by
    rw [withReadStdinHook_ne rsh ext (by decide)] at hf
    exact hExt.readFile_fsT f hf
  readStdin_fsT f hf := by
    rw [withReadStdinHook_self] at hf
    cases hf
    exact hRsh

/-- `HookFsTraced IsFsC` for `readFileEntryGhostHook` whenever `P_io` has `FsTHooks` externs and
    overrides and `P_io.svc = Syscall.standard`. -/
theorem readFileEntryGhostHook_fsT {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (hExt : FsTHooks P_io.externs)
    (hOvr : FsTHooks P_io.overrides)
    (hSvc : P_io.svc = Syscall.standard := by rfl) :
    HookFsTraced IsFsC (readFileEntryGhostHook P_io entry_io A lim stk) := by
  classical
  intro s0
  unfold readFileEntryGhostHook
  by_cases hPre : ActiveReadFilePre A lim stk s0
  · simp only [hPre, ↓reduceDIte]
    by_cases hRun : ActiveReadFileRun P_io entry_io s0
    · simp only [hRun, ↓reduceDIte]
      have h0 : FsTraced IsFsC s0 (s0.setPC entry_io) := FsTraced.of_eq rfl rfl
      have hsteps : Steps P_io (s0.setPC entry_io) (Classical.choose hRun.2.2.2) :=
        (Classical.choose_spec hRun.2.2.2).1.toSteps
      have htr : FsTraced IsFsC (s0.setPC entry_io) (Classical.choose hRun.2.2.2) :=
        hsteps.fsTraced (isFs := IsFsC) (fun _ he => he)
          (fun _ _ he => fsT_externAt hExt hOvr he) hSvc
      exact h0.trans htr
    · simp only [hRun, ↓reduceDIte]
      exact FsTraced.of_eq rfl rfl
  · simp only [hPre, ↓reduceDIte]
    exact FsTraced.of_eq rfl rfl

/-- `HookFsTraced IsFsC` for `readFileGhostHook` whenever `P_io` has `FsTHooks` externs/overrides,
    `P_io.svc = Syscall.standard`, and `fallback` is `HookFsTraced IsFsC` (e.g. `readFileHook_fsT`). -/
theorem readFileGhostHook_fsT {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hExt : FsTHooks P_io.externs)
    (hFallback : HookFsTraced IsFsC fallback)
    (hOvr : FsTHooks P_io.overrides)
    (hSvc : P_io.svc = Syscall.standard := by rfl) :
    HookFsTraced IsFsC (readFileGhostHook P_io entry_io A lim stk fallback) := by
  classical
  intro s0
  unfold readFileGhostHook
  by_cases hPre : ActiveReadFilePre A lim stk s0
  · simp only [hPre, ↓reduceDIte]
    by_cases hRun : ActiveReadFileRun P_io entry_io s0
    · simp only [hRun, ↓reduceDIte]
      have h0 : FsTraced IsFsC s0 (s0.setPC entry_io) := FsTraced.of_eq rfl rfl
      have hsteps : Steps P_io (s0.setPC entry_io) (Classical.choose hRun.2.2.2) :=
        (Classical.choose_spec hRun.2.2.2).1.toSteps
      have htr : FsTraced IsFsC (s0.setPC entry_io) (Classical.choose hRun.2.2.2) :=
        hsteps.fsTraced (isFs := IsFsC) (fun _ he => he)
          (fun _ _ he => fsT_externAt hExt hOvr he) hSvc
      exact h0.trans htr
    · simp only [hRun, ↓reduceDIte]
      exact hFallback s0
  · simp only [hPre, ↓reduceDIte]
    exact FsTraced.of_eq rfl rfl

theorem fsTHooks_of_agreesOutsideReadHooks {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    {W : CliHooks} {H : LibsignalHooks}
    (hAgree : AgreesOutsideReadHooks mmpl gh W H)
    (hFsGh : CliGhostHooksFs gh)
    (hFsRead : ReadHooksFsT H) :
    FsTHooks H := by
  intro s f hs
  by_cases hFile : s = lsReadFileSym
  · subst hFile
    exact hFsRead.readFile_fsT f hs
  · by_cases hStdin : s = lsReadStdinSym
    · subst hStdin
      exact hFsRead.readStdin_fsT f hs
    · rw [hAgree s hFile hStdin] at hs
      exact fsTHooks_cliGhostExterns_of_fs hFsGh (fsTHooks_cliExternsPlaced mmpl W) s f hs

theorem fsTHooks_withPanics {H : LibsignalHooks} (hFs : FsTHooks H) :
    FsTHooks (Rust.withPanics H) := by
  intro s f hs
  unfold Rust.withPanics at hs
  split at hs
  · cases hs
    exact panicked_fsT
  · exact hFs s f hs

theorem traceFsSound_of_fsTHooks_lsProg [LibsignalPlacement] {H : LibsignalHooks}
    (hFs : FsTHooks H) {prog : Program} {i : Nat} [hprog : IsLsBlockProg prog i H] :
    TraceFsSound prog := by
  rw [hprog.eq_blockProgram]
  unfold Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program
  exact traceFsSound_of_fsTHooks hFs fsTHooks_none rfl

theorem traceFsSound_of_agreesOutsideReadHooks [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {H : LibsignalHooks}
    (hAgree : AgreesOutsideReadHooks mmpl gh W H)
    (hFsGh : CliGhostHooksFs gh)
    (hFsRead : ReadHooksFsT H)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i H] :
    TraceFsSound prog :=
  traceFsSound_of_fsTHooks_lsProg (fsTHooks_of_agreesOutsideReadHooks hAgree hFsGh hFsRead)

theorem traceFsSound_withPanics_of_agreesOutsideReadHooks [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {H : LibsignalHooks}
    (hAgree : AgreesOutsideReadHooks mmpl gh W H)
    (hFsGh : CliGhostHooksFs gh)
    (hFsRead : ReadHooksFsT H)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics H)] :
    TraceFsSound prog :=
  traceFsSound_of_fsTHooks_lsProg
    (fsTHooks_withPanics (fsTHooks_of_agreesOutsideReadHooks hAgree hFsGh hFsRead))

/-! ## Contract and `RunHooksPlaced` Lifts -/

theorem allocContractsXCliPlaced_of_agreesOutsideReadHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {H : LibsignalHooks}
    (hAgree : AgreesOutsideReadHooks mmpl gh W H)
    (hG : CliGhostAllocHooks M A lim gh) :
    AllocContractsXCliPlaced A lim H :=
  allocContractsXCliPlaced_of_hookSat
    (hAgree.hookSat (cliExternsPlaced_alloc_budget_sat mmpl gh W hG))
    (hAgree.hookSat (cliExternsPlaced_dealloc_budget_sat mmpl gh W hG))
    (hAgree.hookSat (cliExternsPlaced_realloc_budget_sat mmpl gh W hG))
    (hAgree.hookSat (cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq))
    (fun stk => hAgree.hookSat
      (cliExternsPlaced_memcpy_budget_sat mmpl gh W hG stk))
    (fun stk => hAgree.hookSat
      (cliExternsPlaced_sessionMemcpy_budget_sat mmpl gh W hG stk))
    (hAgree.hookSat
      (cliExternsPlaced_memcpyRegion_budget_sat mmpl gh W hG))
    (hAgree.hookSat
      (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG))
    (fun stk => hAgree.hookSat
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_memmove_budget_sat mmpl W stk)))
    (fun stk => hAgree.hookSat
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_sessionMemmove_budget_sat mmpl W stk)))
    (fun stk hpos => hAgree.hookSat
      (cliExternsPlaced_memset_budget_sat mmpl gh W hG stk hpos))
    (fun stk hpos => hAgree.hookSat
      (cliExternsPlaced_sessionMemset_budget_sat mmpl gh W hG stk hpos))
    (hAgree.hookSat
      (cliExternsPlaced_memsetRegion_budget_sat mmpl gh W hG))
    (hAgree.hookSat
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl gh W hG))

theorem allocContractsFsPlaced_of_agreesOutsideReadHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {H : LibsignalHooks}
    (hAgree : AgreesOutsideReadHooks mmpl gh W H)
    (hG : CliGhostAllocHooks M A lim gh) :
    AllocContractsFsPlaced A lim H :=
  allocContractsFsPlaced_of_hookSat
    (hAgree.hookSat (cliExternsPlaced_alloc_budget_sat mmpl gh W hG))
    (hAgree.hookSat (cliExternsPlaced_dealloc_budget_sat mmpl gh W hG))
    (hAgree.hookSat (cliExternsPlaced_realloc_budget_sat mmpl gh W hG))
    (hAgree.hookSat (cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq))
    (fun stk => hAgree.hookSat
      (cliExternsPlaced_memcpy_budget_sat mmpl gh W hG stk))
    (fun stk => hAgree.hookSat
      (cliExternsPlaced_sessionMemcpy_budget_sat mmpl gh W hG stk))
    (hAgree.hookSat
      (cliExternsPlaced_memcpyRegion_budget_sat mmpl gh W hG))
    (hAgree.hookSat
      (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG))
    (hAgree.hookSat
      (cliExternsPlaced_memcpyRegionRO_budget_sat mmpl gh W hG))
    (fun stk => hAgree.hookSat
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_memmove_budget_sat mmpl W stk)))
    (fun stk => hAgree.hookSat
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_sessionMemmove_budget_sat mmpl W stk)))
    (fun stk hpos => hAgree.hookSat
      (cliExternsPlaced_memset_budget_sat mmpl gh W hG stk hpos))
    (fun stk hpos => hAgree.hookSat
      (cliExternsPlaced_sessionMemset_budget_sat mmpl gh W hG stk hpos))
    (hAgree.hookSat
      (cliExternsPlaced_memsetRegion_budget_sat mmpl gh W hG))
    (hAgree.hookSat
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl gh W hG))
    (by
      intro sym hmem f hf s
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hAgree _ (by decide) (by decide), cliGhostExterns_alloc] at hf
        cases hf; exact hG.alloc_fs s
      · rw [hAgree _ (by decide) (by decide), cliGhostExterns_dealloc] at hf
        cases hf; exact hG.dealloc_fs s
      · rw [hAgree _ (by decide) (by decide), cliGhostExterns_realloc] at hf
        cases hf; exact hG.realloc_fs s
      · rw [hAgree _ (by decide) (by decide), cliGhostExterns_shim, hG.shim_eq] at hf
        cases hf; exact hookNoop_fs s
      · obtain ⟨f₀, hf₀, _, _, _, _, _, _, _, hfs₀, _⟩ := hG.memcpy
        rw [hAgree _ (by decide) (by decide),
          show memcpyName = lsMemcpySym from rfl,
          cliGhostExterns_memcpy_some gh _ hf₀] at hf
        cases hf; exact hfs₀ s
      · rw [hAgree _ (by decide) (by decide),
          cliGhostExterns_other gh _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide),
          cliExternsPlaced_row mmpl W (memmove_row_placed mmpl W)] at hf
        cases hf; exact hookMemmove_fs s
      · obtain ⟨f₀, hf₀, _, _, _, _, _, hfs₀, _⟩ := hG.memset
        rw [hAgree _ (by decide) (by decide),
          show memsetName = lsMemsetSym from rfl,
          cliGhostExterns_memset_some gh _ hf₀] at hf
        cases hf; exact hfs₀ s)

theorem codecHooksPlaced_of_agreesOutsideReadHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {H : LibsignalHooks}
    (hAgree : AgreesOutsideReadHooks mmpl gh W H)
    (h0 : CodecHooksPlaced M A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    CodecHooksPlaced M A lim H where
  shim := hAgree.hookSat h0.shim
  alloc := hAgree.hookSat h0.alloc
  realloc := hAgree.hookSat h0.realloc
  dealloc := hAgree.hookSat h0.dealloc
  memcpy := hAgree.hookSat h0.memcpy
  panic_alloc := (hAgree _ (by decide) (by decide)).trans h0.panic_alloc
  panic_raw := (hAgree _ (by decide) (by decide)).trans h0.panic_raw

theorem serContractsXPlaced_of_agreesOutsideReadHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {H : LibsignalHooks}
    (hAgree : AgreesOutsideReadHooks mmpl gh W H)
    (hG : CliGhostAllocHooks M A lim gh) :
    SerContractsXPlaced M A lim H :=
  SerContractsXPlaced.of_hooks
    (hAgree.hookSat (cliExternsPlaced_alloc_budget_sat mmpl gh W hG))
    (hAgree.hookSat (cliExternsPlaced_dealloc_budget_sat mmpl gh W hG))
    (hAgree.hookSat (cliExternsPlaced_realloc_budget_sat mmpl gh W hG))
    (hAgree.hookSat (cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq))
    (hAgree.hookSat
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_sessionMemmove_budget_sat mmpl W extHookStack)))
    (hAgree.hookSat
      (cliExternsPlaced_sessionMemcpy_budget_sat mmpl gh W hG extHookStack))

theorem hkdfPlacedHooks_of_agreesOutsideReadHooks
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {H : LibsignalHooks}
    (hAgree : AgreesOutsideReadHooks mmpl gh W H)
    (h0 : HkdfPlacedHooks W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    HkdfPlacedHooks W.C.F H :=
  { memset := (hAgree _ (by decide) (by decide)).trans h0.memset
    memcpy := (hAgree _ (by decide) (by decide)).trans h0.memcpy
    compress256 := (hAgree _ (by decide) (by decide)).trans h0.compress256 }

theorem panic_of_mem_cliPanicSymbolsPlaced
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {H : LibsignalHooks}
    (hAgree : AgreesOutsideReadHooks mmpl gh W H)
    (h0 : ∀ s, s ∈ cliPanicSymbolsPlaced →
      cliGhostExterns gh (cliExternsPlaced mmpl W) s = some Rust.panicked) :
    ∀ s, s ∈ cliPanicSymbolsPlaced → H s = some Rust.panicked := by
  intro s hs
  have hFile : s ≠ lsReadFileSym := by
    intro heq; subst heq; exact nomatch hs
  have hStdin : s ≠ lsReadStdinSym := by
    intro heq; subst heq; exact nomatch hs
  exact (hAgree s hFile hStdin).trans (h0 s hs)

theorem skeletonRunHooksPlaced_of_agreesOutsideReadHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {H : LibsignalHooks}
    (hAgree : AgreesOutsideReadHooks mmpl gh W H)
    (hFs : FsTHooks H)
    (hG : CliGhostAllocHooks M A lim gh)
    (h0 : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim H where
  alloc := allocContractsXCliPlaced_of_agreesOutsideReadHooks hAgree hG
  allocFs := allocContractsFsPlaced_of_agreesOutsideReadHooks hAgree hG
  panics := panic_of_mem_cliPanicSymbolsPlaced hAgree h0.panics
  memcpyRO := hAgree.hookSat h0.memcpyRO
  bcmp := hAgree.hookSat h0.bcmp
  fs prog i hprog := @traceFsSound_of_fsTHooks_lsProg _ H hFs prog i hprog
  utf8 stk := hAgree.hookSat (h0.utf8 stk)
  memrchr stk := hAgree.hookSat (h0.memrchr stk)
  codecHooks := codecHooksPlaced_of_agreesOutsideReadHooks hAgree h0.codecHooks
  allocZeroed := hAgree.hookSat h0.allocZeroed
  stringClone := hAgree.hookSat h0.stringClone
  formatInner := hAgree.hookSat h0.formatInner

theorem w3RunHooksPlaced_of_agreesOutsideReadHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {H : LibsignalHooks}
    (hAgree : AgreesOutsideReadHooks mmpl gh W H)
    (hFs : FsTHooks H)
    (hG : CliGhostAllocHooks M A lim gh)
    (h0 : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget.RunHooksPlaced
      W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget.RunHooksPlaced
      W A lim H where
  alloc := allocContractsXCliPlaced_of_agreesOutsideReadHooks hAgree hG
  allocFs := allocContractsFsPlaced_of_agreesOutsideReadHooks hAgree hG
  codec := codecHooksPlaced_of_agreesOutsideReadHooks hAgree h0.codec
  ser := serContractsXPlaced_of_agreesOutsideReadHooks hAgree hG
  shim := hAgree.hookSat h0.shim
  shimVm := hAgree.hookSat h0.shimVm
  rawAlloc := hAgree.hookSat h0.rawAlloc
  rawDealloc := hAgree.hookSat h0.rawDealloc
  framelessMemcpy := hAgree.hookSat h0.framelessMemcpy
  sessionMemcpyRegion := hAgree.hookSat h0.sessionMemcpyRegion
  memcpyRegionKeepsFs := hAgree.hookSat h0.memcpyRegionKeepsFs
  memsetRegionKeepsFs := hAgree.hookSat h0.memsetRegionKeepsFs
  allocMemcpyVm := hAgree.hookSat h0.allocMemcpyVm
  memcpyRO := hAgree.hookSat h0.memcpyRO
  bcmp := hAgree.hookSat h0.bcmp
  e2eBcmp := hAgree.hookSat h0.e2eBcmp
  allocZeroed := hAgree.hookSat h0.allocZeroed
  stringClone := hAgree.hookSat h0.stringClone
  formatInner := hAgree.hookSat h0.formatInner
  pubFromSecret := hAgree.hookSat h0.pubFromSecret
  dh := hAgree.hookSat h0.dh
  sharedDrop := hAgree.hookSat h0.sharedDrop
  staticDrop := hAgree.hookSat h0.staticDrop
  blackBox := (hAgree _ (by decide) (by decide)).trans h0.blackBox
  hkdf := let ⟨f, hf, hex⟩ := h0.hkdf.memcpy
    { memset := hAgree.hookSat h0.hkdf.memset
      memcpy := ⟨f, (hAgree _ (by decide) (by decide)).trans hf, hex⟩
      compress256 := (hAgree _ (by decide) (by decide)).trans h0.hkdf.compress256 }
  kemEncaps := (hAgree _ (by decide) (by decide)).trans h0.kemEncaps
  durationSince := (hAgree _ (by decide) (by decide)).trans h0.durationSince
  panic_alloc := (hAgree _ (by decide) (by decide)).trans h0.panic_alloc
  panic_raw := (hAgree _ (by decide) (by decide)).trans h0.panic_raw
  panic_sym := panic_of_mem_cliPanicSymbolsPlaced hAgree h0.panic_sym
  fs := @traceFsSound_of_fsTHooks_lsProg _ H hFs

/-! ## Stack-Monotone `readFileSpecPlaced` Lifts and Slot Predicates -/

private theorem stackAt_le_two_pow_64_of_ret {m : Memory} {p sp : BitVec 64} {stk : Nat}
    {R : SepProp} (hstk : 0 < stk)
    (h : m ⊨ memRegion p 24 ∗ (stackAt sp stk ∗ R)) : stk ≤ 2 ^ 64 := by
  have hdisj := (IsBlock.memRegion p 24).disjoint
    (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk) (by omega) hstk h
  have hlt := (p - (sp - BitVec.ofNat 64 stk)).isLt
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hdisj.2 hlt)

/-- Stack-budget weakening for `HookOk f (readFileSpecPlaced …)`: any `HookOk` at positive stack
    budget `stk0` (`0 < stk0`, e.g. `stk0 = extHookStack`) lifts to any larger `stk ≥ stk0`. -/
theorem hookOk_readFileSpecPlaced_mono_stk {M : AllocCostModel}
    {rd : FsFiles → List (BitVec 8) → Except Unit (List (BitVec 8))}
    {wrOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk0 stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {f : State → State}
    (hpos : 0 < stk0) (hle : stk0 ≤ stk)
    (hf : HookOk f (readFileSpecPlaced rd wrOk A lim stk0 ReadEnv)) :
    HookOk f (readFileSpecPlaced rd wrOk A lim stk ReadEnv) := by
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  dsimp only [readFileSpecPlaced] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  have hmem_disj : s0.mem ⊨ memRegion x.ret 24 ∗
      (stackAt s0.sp stk ∗ ((x.pathA ↦ₛ x.path) ∗ A.pool lim st s0 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hstk64 : stk ≤ 2 ^ 64 :=
    stackAt_le_two_pow_64_of_ret (Nat.lt_of_lt_of_le hpos hle) hmem_disj
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - stk0) ∗ stackAt s0.sp stk0 := by
    have hs := stackAt_split_bottom s0.sp stk0 (stk - stk0) (by omega)
    rwa [Nat.add_sub_of_le hle] at hs
  let F : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - stk0)
  have hpre0 : s0.mem ⊨ (readFileSpecPlaced rd wrOk A lim stk0 ReadEnv).pre (x, st) s0 ∗ (F ∗ R) := by
    dsimp only [readFileSpecPlaced, F]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpure, ?_⟩
    rw [hsplit] at hmem
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  obtain ⟨hkf, hsym, hout⟩ := hf (x, st) (F ∗ R) s0 hrun hpre0 hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp, hq⟩ | ⟨c, hc, hq⟩ | ⟨ho, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [readFileSpecPlaced, F] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    obtain ⟨evs, hq⟩ := hq
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨hevs, hq⟩ := hq
    refine ⟨hevs, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists] at hq ⊢
    obtain ⟨r, hq⟩ := hq
    refine ⟨r, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨hr, hqmem⟩ := hq
    refine ⟨hr, ?_⟩
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hqmem
  · dsimp only [readFileSpecPlaced] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [readFileSpecPlaced] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [readFileSpecPlaced] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1

theorem hookSat_readFileSpecPlaced_mono_stk {M : AllocCostModel}
    {rd : FsFiles → List (BitVec 8) → Except Unit (List (BitVec 8))}
    {wrOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk0 stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {sym : String}
    (hpos : 0 < stk0) (hle : stk0 ≤ stk)
    (hsat : HookSat H sym (readFileSpecPlaced rd wrOk A lim stk0 ReadEnv)) :
    HookSat H sym (readFileSpecPlaced rd wrOk A lim stk ReadEnv) := by
  obtain ⟨f, hlookup, hok⟩ := hsat
  exact ⟨f, hlookup, hookOk_readFileSpecPlaced_mono_stk hpos hle hok⟩

theorem hRead_of_hookSat_mono_stk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk0 stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i H] [LsBlockBound bi]
    (hpos : 0 < stk0) (hle : stk0 ≤ stk)
    (hsat : HookSat H lsReadFileSym (readFileSpecPlaced cliIo.rd cliWrOk A lim stk0 ReadEnv))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv) :=
  hRead_of_hookSat (hookSat_readFileSpecPlaced_mono_stk hpos hle hsat) hi hunmut

theorem hRead_withLsCodeRoLoaded_of_hookSat_mono_stk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk0 stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i H] [LsBlockBound bi]
    (hpos : 0 < stk0) (hle : stk0 ≤ stk)
    (hsat : HookSat H lsReadFileSym (readFileSpecPlaced cliIo.rd cliWrOk A lim stk0 ReadEnv))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv)) :=
  hRead_withLsCodeRoLoaded_of_hookSat
    (hookSat_readFileSpecPlaced_mono_stk hpos hle hsat) hi hunmut

theorem hRead_rocl_of_hookSat_mono_stk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk0 stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i H] [LsBlockBound bi]
    (hpos : 0 < stk0) (hle : stk0 ≤ stk)
    (hsat : HookSat H lsReadFileSym (readFileSpecPlaced cliIo.rd cliWrOk A lim stk0 ReadEnv))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (withLsRoCl lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv)) :=
  hRead_rocl_of_hookSat (hookSat_readFileSpecPlaced_mono_stk hpos hle hsat) hi hunmut

/-- Extern-parametric `signal_session_handshake::initiate` slot contract on `lsProg_579 H` at
fixed `(X, W)`. -/
def CliInitSlotOkPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop :=
  ∀ (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds),
    sEnvs.initiate = InitEnv →
    S.filesOk = filesOk₀ scopeIn (fun _ => True) →
    S.initiate = initDef X ⟨W.C, W.Q⟩ →
    S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
    needs.initiate = cliInitiateNeed cliRunBudgets →
    (slotsOfPlaced A lim sEnvs S needs).initiate.OkPlaced
      (lsProg_579 H) (lsmpl.base 521)

end LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.AgreesOutsideReadHooks
