/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.SpecBudgetFine
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.RunCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget
import LibsignalBinary.Proofs.E2E.Run.NoSvcCommon
import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsShadowHooksFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsSpecSwapRFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsStepTransportRFd
public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.RustRuntime
public import Arm64.Trusted.Spec.SepLogic
public import ProofLib.Hoare.LibcHooks
import ProofLib.Invariant
import ProofLib.MallocngBridge
import ProofLib.Process.Core

/-!
# Two-Stage Pure-`fs` Transfer Core for `CodecHooksPlaced` Callees on `lsProg_579`

Sets up the Stage-A precondition-guarded trap hook table (`codecTrapHooks`), `SVC #0`-free
unmutated-code execution properties, and Stage-B shadow-simulation interfaces used to prove
`sf.fs = s0.fs` on normal return for `CodecHooksPlaced` callees on `lsProg_579`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferCoreFd

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPl_111 libsignalMutatedBlocks
   libsignalSessionLib lsHandleErrorSym lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block
   subroutine_ok_withLsCodeRoLoaded_of_rocl withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (blkPl_85 framelessMemcpySpec memcpyName noAllocShimSpec)
open CryptoVerification.LibsignalTripleRatchet.Prost (lsHandleAllocErrorSym)
open CryptoVerification.LibsignalTripleRatchet.Wire (tryFromPlacedProg)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsRustAllocSymCli lsRustDeallocSymCli
   lsRustNoAllocShimSymCli lsRustReallocSymCli)
open CryptoVerification.SignalSession.Cli.MainHops (hookMemcpy_fs hookNoop_fs)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns cliGhostExterns_memcpy_some)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits MallocngCostModelIface
   MallocngCostModelSound OomPreserved RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (CodeBlocksPermRX CodeBlocksPermRXMem codeBlocksPermRX_of_keepsFrozen
   mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
  (pksmSlotSpecPlacedOkFs tryFromPlacedSpecOkFs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsShadowHooksFd
  (framelessMemcpy_stripped_to_stripped hookOk_hookMemcpy_frameless_vm
   hookOk_hookNoop_noAllocShim_vm hookOk_shadowFallback_alloc hookOk_shadowFallback_dealloc
   hookOk_shadowFallback_realloc shadowFallback)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsSpecSwapRFd
  (pksm_outcome_of_stripped_stripped pksm_outcome_of_stripped_unstripped
   pksm_outcome_of_unstripped_stripped pksm_outcome_of_unstripped_unstripped pksm_pre_stripped
   pksm_pre_unstripped tryFrom_outcome_of_stripped_stripped tryFrom_outcome_of_stripped_unstripped
   tryFrom_outcome_of_unstripped_stripped tryFrom_outcome_of_unstripped_unstripped
   tryFrom_pre_stripped tryFrom_pre_unstripped)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsStepTransportRFd
  (alloc_stripped_to_stripped alloc_unstripped_of_hOut dealloc_stripped_to_stripped
   dealloc_unstripped_of_hOut realloc_stripped_to_stripped realloc_unstripped_of_hOut)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
  (tripleRatchetHooksWPlaced_of_codecHooks tryFromDepsPlaced_of_codecHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (SubsetA4PksmTryFromPlaced cliPksmTryFrom_placed_at_block pksmSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_framelessMemcpy_budget_sat
   cliExternsPlaced_noAllocShim_budget_sat codecHooksPlaced_of_hookSat codecHooksPlaced_of_hooks)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget
  (tryFromPlacedSpec tryFrom_placed_ok_of_deps)

/-! ## Section 1: Stage-A Precondition-Guarded Trap Hook Table (`codecTrapHooks`) -/

def ActivePre {α : Type} (spec : Spec α) (s : State) : Prop :=
  s.status = .Running ∧ s.spAligned = true ∧ ∃ (x : α) (R : SepProp), s.mem ⊨ spec.pre x s ∗ R

noncomputable def guardPre {α : Type} (spec : Spec α) (f : State → State) (s : State) :
    State :=
  open Classical in
  if ActivePre spec s then f s else { s with status := .Exception "pre" }

theorem guardPre_ok {α : Type} {spec : Spec α} {f : State → State}
    (hf : HookOk f spec) : HookOk (guardPre spec f) spec := by
  intro x R s0 hrun hpre hsp
  have hact : ActivePre spec s0 := ⟨hrun, hsp, x, R, hpre⟩
  unfold guardPre
  simp only [hact, ↓reduceIte]
  exact hf x R s0 hrun hpre hsp

/-- Ghost-`memcpyFn` / `baseExt`-parametric Stage-A precondition-guarded trap hook table. -/
noncomputable def codecTrapHooksMc [LibsignalPlacement]
    {M : AllocCostModel} (A0 : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (memcpyFn : State → State) : LibsignalHooks :=
  fun sym =>
    if sym = lsRustNoAllocShimSymCli then some ProofLib.hookNoop
    else if sym = lsRustAllocSymCli then
      some (guardPre (rustCliAllocBudgetSpec M A0 lim false) g.alloc)
    else if sym = lsRustDeallocSymCli then
      some (guardPre (rustCliDeallocBudgetSpec M A0 lim) g.dealloc)
    else if sym = lsRustReallocSymCli then
      some (guardPre (rustCliReallocBudgetSpec M A0 lim) g.realloc)
    else if sym = memcpyName then
      some (guardPre (withVmPreserved framelessMemcpySpec) memcpyFn)
    else if sym = lsHandleAllocErrorSym then some Rust.panicked
    else if sym = lsHandleErrorSym then some Rust.panicked
    else match cliGhostExterns g baseExt sym with
      | some _ => some (fun u => { u with status := .Exception "unlinked" })
      | none => none

noncomputable def codecTrapHooks [LibsignalPlacement]
    {M : AllocCostModel} (A0 : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) : LibsignalHooks :=
  codecTrapHooksMc A0 lim g (cliExternsPlaced mmpl W) (g.memcpy.getD ProofLib.hookMemcpy)

theorem codecHooksPlaced_trap_mc [LibsignalPlacement]
    {M : AllocCostModel} {A0 : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (memcpyFn : State → State)
    (hG : CliGhostAllocHooks M A0 lim g)
    (hMcOk : HookOk memcpyFn (withVmPreserved framelessMemcpySpec)) :
    CodecHooksPlaced M A0 lim (codecTrapHooksMc A0 lim g baseExt memcpyFn) := by
  refine codecHooksPlaced_of_hookSat
    ⟨ProofLib.hookNoop, by simp [codecTrapHooksMc], hookOk_hookNoop_noAllocShim_vm⟩
    ⟨_, by simp only [codecTrapHooksMc, (by decide : lsRustAllocSymCli ≠ lsRustNoAllocShimSymCli),
      ↓reduceIte], guardPre_ok hG.alloc⟩
    ⟨_, by simp only [codecTrapHooksMc, (by decide : lsRustReallocSymCli ≠ lsRustNoAllocShimSymCli),
      (by decide : lsRustReallocSymCli ≠ lsRustAllocSymCli),
      (by decide : lsRustReallocSymCli ≠ lsRustDeallocSymCli), ↓reduceIte], guardPre_ok hG.realloc⟩
    ⟨_, by simp only [codecTrapHooksMc, (by decide : lsRustDeallocSymCli ≠ lsRustNoAllocShimSymCli),
      (by decide : lsRustDeallocSymCli ≠ lsRustAllocSymCli), ↓reduceIte], guardPre_ok hG.dealloc⟩
    ⟨_, by simp only [codecTrapHooksMc, (by decide : memcpyName ≠ lsRustNoAllocShimSymCli),
      (by decide : memcpyName ≠ lsRustAllocSymCli), (by decide : memcpyName ≠ lsRustDeallocSymCli),
      (by decide : memcpyName ≠ lsRustReallocSymCli), ↓reduceIte], guardPre_ok hMcOk⟩
    (by simp only [codecTrapHooksMc, (by decide : lsHandleAllocErrorSym ≠ lsRustNoAllocShimSymCli),
      (by decide : lsHandleAllocErrorSym ≠ lsRustAllocSymCli),
      (by decide : lsHandleAllocErrorSym ≠ lsRustDeallocSymCli),
      (by decide : lsHandleAllocErrorSym ≠ lsRustReallocSymCli),
      (by decide : lsHandleAllocErrorSym ≠ memcpyName), ↓reduceIte])
    (by simp only [codecTrapHooksMc, (by decide : lsHandleErrorSym ≠ lsRustNoAllocShimSymCli),
      (by decide : lsHandleErrorSym ≠ lsRustAllocSymCli),
      (by decide : lsHandleErrorSym ≠ lsRustDeallocSymCli),
      (by decide : lsHandleErrorSym ≠ lsRustReallocSymCli),
      (by decide : lsHandleErrorSym ≠ memcpyName),
      (by decide : lsHandleErrorSym ≠ lsHandleAllocErrorSym), ↓reduceIte])

theorem codecHooksPlaced_trap [LibsignalPlacement]
    {M : AllocCostModel} {A0 : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A0 lim g) :
    CodecHooksPlaced M A0 lim (codecTrapHooks A0 lim mmpl g W) := by
  obtain ⟨f_mc, hf_mc, _, _, _, _, hok_fm, _, hvm_mc, _, _⟩ := hG.memcpy
  unfold codecTrapHooks
  rw [hf_mc]; dsimp only [Option.getD]
  exact codecHooksPlaced_trap_mc g (cliExternsPlaced mmpl W) f_mc hG
    (hookOk_withVmPreserved hok_fm hvm_mc)

theorem tryFrom_at_579_of_codecHooks [LibsignalPlacement]
    {M : AllocCostModel} {A' : RustCliAllocBudget M} {lim : BudgetLimits} {H' : LibsignalHooks}
    (hC : CodecHooksPlaced M A' lim H') :
    subroutine_ok (lsProg_579 H') (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A' lim)) := by
  have h85 : subroutine_ok (tryFromPlacedProg H') blkPl_85.base
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A' lim)) :=
    tryFrom_placed_ok_of_deps
      (tripleRatchetHooksWPlaced_of_codecHooks hC)
      (tryFromDepsPlaced_of_codecHooks hC)
  have hcaller : CryptoVerification.IsLsBlockProg (lsProg_579 H') 579 H' := inferInstance
  have hcallee : CryptoVerification.IsLsBlockProg (tryFromPlacedProg H') 85 H' := inferInstance
  exact subroutine_ok_withLsCodeRoLoaded_of_rocl
    (@ls_subroutine_ok_rocl_of_block _ _ (lsProg_579 H') (tryFromPlacedProg H') 579 85 H'
      hcaller hcallee blkPl_85.base _ h85 _ _ _ _ (by decide) (by decide) (by decide))

theorem pksmSlot_at_579_of_codecHooks [LibsignalPlacement]
    {M : AllocCostModel} {A' : RustCliAllocBudget M} {lim : BudgetLimits} {H' : LibsignalHooks}
    {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    (hSub : ∀ {A'' : RustCliAllocBudget M} {H'' : LibsignalHooks},
      CodecHooksPlaced M A'' lim H'' → SubsetA4PksmTryFromPlaced M A'' lim PksmEnv H'')
    (hParse : ∀ b, S.pksmParse b = pksmParse b)
    (hC : CodecHooksPlaced M A' lim H') :
    subroutine_ok (lsProg_579 H') blkPl_111.base
      (pksmSlotSpecPlaced M A' lim PksmEnv S) :=
  cliPksmTryFrom_placed_at_block (callerProg := lsProg_579 H') (i := 579) (hSub hC) hParse

theorem codecTrapHooksMc_isSome_eq [LibsignalPlacement]
    {M : AllocCostModel} (A0 : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (memcpyFn : State → State)
    (hMcRow : cliGhostExterns g baseExt memcpyName = some memcpyFn)
    (hPanAlloc : cliGhostExterns g baseExt lsHandleAllocErrorSym = some Rust.panicked)
    (hPanRaw : cliGhostExterns g baseExt lsHandleErrorSym = some Rust.panicked)
    (sym : String) :
    (codecTrapHooksMc A0 lim g baseExt memcpyFn sym).isSome =
      (cliGhostExterns g baseExt sym).isSome := by
  unfold codecTrapHooksMc
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · subst h1; simp [CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_shim g baseExt]
  · subst h2; simp [CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_alloc g baseExt]
  · subst h3; simp [CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_dealloc g baseExt]
  · subst h4; simp [CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_realloc g baseExt]
  · subst h5; simp [hMcRow]
  · subst h6; simp [hPanAlloc]
  · subst h7; simp [hPanRaw]
  · cases cliGhostExterns g baseExt sym <;> rfl

theorem codecTrapHooks_isSome_eq [LibsignalPlacement]
    {M : AllocCostModel} (A0 : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A0 lim g) (sym : String) :
    (codecTrapHooks A0 lim mmpl g W sym).isSome =
      (cliGhostExterns g (cliExternsPlaced mmpl W) sym).isSome := by
  have hC := codecHooksPlaced_of_hooks mmpl g W hG
  obtain ⟨f_mc, hf_mc, _, _, _, _, _, _, _, _, _⟩ := hG.memcpy
  unfold codecTrapHooks
  rw [hf_mc]; dsimp only [Option.getD]
  exact codecTrapHooksMc_isSome_eq A0 lim g (cliExternsPlaced mmpl W) f_mc
    (cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hf_mc)
    hC.panic_alloc hC.panic_raw sym

/-! ## Section 2: `lsProg_579` Extern Lookup, `inLsUnmutCode` `SVC #0`-Exclusion, & Stage-A Replay -/

theorem findSome_none_const {α β : Type} :
    ∀ (l : List α), (l.findSome? fun _ => (none : Option β)) = none
  | [] => rfl
  | _ :: tl => findSome_none_const tl

theorem findSome_stub_none_iff {H₁ H₂ : LibsignalHooks}
    (hdom : ∀ sym, (H₁ sym).isSome = (H₂ sym).isSome) (off : Nat) :
    ∀ (stubs : List (String × Nat)),
      ((stubs.findSome? fun (n, o) => if o == off then H₁ n else none) = none) ↔
        ((stubs.findSome? fun (n, o) => if o == off then H₂ n else none) = none)
  | [] => Iff.rfl
  | (n, o) :: tl => by
    simp only [List.findSome?_cons]
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte]
      have hd := hdom n
      cases h1 : H₁ n <;> cases h2 : H₂ n
      · exact findSome_stub_none_iff hdom off tl
      · simp [h1, h2] at hd
      · simp [h1, h2] at hd
      · simp
    · have hof : (o == off) = false := Bool.eq_false_iff.mpr ho
      simp only [hof]
      exact findSome_stub_none_iff hdom off tl

theorem findSome_stub_some {H₁ H₂ : LibsignalHooks}
    (hdom : ∀ sym, (H₁ sym).isSome = (H₂ sym).isSome) (off : Nat) {f : State → State} :
    ∀ (stubs : List (String × Nat)),
      (stubs.findSome? fun (n, o) => if o == off then H₁ n else none) = some f →
      ∃ sym, H₁ sym = some f ∧
        (stubs.findSome? fun (n, o) => if o == off then H₂ n else none) = H₂ sym
  | [], h => by simp at h
  | (n, o) :: tl, h => by
    simp only [List.findSome?_cons] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      have hd := hdom n
      cases h1 : H₁ n <;> cases h2 : H₂ n
      · rw [h1] at h
        exact findSome_stub_some hdom off tl h
      · simp [h1, h2] at hd
      · simp [h1, h2] at hd
      · rw [h1] at h
        injection h with hfeq; subst hfeq
        refine ⟨n, h1, ?_⟩
        rw [h2]
    · have hof : (o == off) = false := Bool.eq_false_iff.mpr ho
      simp only [hof] at h ⊢
      exact findSome_stub_some hdom off tl h

theorem lsProg_579_hookAtOff?_eq [LibsignalPlacement] (H : LibsignalHooks) (off : Nat) :
    (lsProg_579 H).hookAtOff? off =
      (CryptoVerification.SignalSession.Cli.Run.Placed.blkPC_579.stubs.findSome?
        fun (n, o) => if o == off then H n else none) := by
  change (CryptoVerification.SignalSession.Cli.Run.Placed.blkPC_579.rebase
    CryptoVerification.SignalSession.Cli.Run.Placed.blkPl_579.base H).hookAtOff? off = _
  unfold Program.hookAtOff?
  have hovr : ((CryptoVerification.SignalSession.Cli.Run.Placed.blkPC_579.rebase
      CryptoVerification.SignalSession.Cli.Run.Placed.blkPl_579.base H).symbols.findSome?
      fun (n, o) => if o == off then
        (CryptoVerification.SignalSession.Cli.Run.Placed.blkPC_579.rebase
          CryptoVerification.SignalSession.Cli.Run.Placed.blkPl_579.base H).overrides n
      else none) = none := by
    have : (fun (x : String × Nat) => if x.2 == off then
        (CryptoVerification.SignalSession.Cli.Run.Placed.blkPC_579.rebase
          CryptoVerification.SignalSession.Cli.Run.Placed.blkPl_579.base H).overrides x.1
      else none) = (fun _ => none) := by
      funext ⟨n, o⟩; split <;> rfl
    rw [this]; exact findSome_none_const _
  rw [hovr]
  change (CryptoVerification.SignalSession.Cli.Run.Placed.blkPC_579.stubs.findSome?
    fun (n, o) => if o == off then H n else none).or none = _
  cases (CryptoVerification.SignalSession.Cli.Run.Placed.blkPC_579.stubs.findSome?
    fun (n, o) => if o == off then H n else none) <;> rfl

theorem lsProg_579_base_indep [LibsignalPlacement] (H₁ H₂ : LibsignalHooks) :
    (lsProg_579 H₁).base = (lsProg_579 H₂).base := rfl

theorem lsProg_579_codeLoaded_iff [LibsignalPlacement] (H₁ H₂ : LibsignalHooks) (m : Memory) :
    (lsProg_579 H₁).CodeLoaded m ↔ (lsProg_579 H₂).CodeLoaded m := by
  rw [Program.codeLoaded_iff, Program.codeLoaded_iff]
  rfl

theorem lsProg_579_externAt?_none_iff [LibsignalPlacement]
    {H₁ H₂ : LibsignalHooks} (hdom : ∀ sym, (H₁ sym).isSome = (H₂ sym).isSome) (pc : BitVec 64) :
    (lsProg_579 H₁).externAt? pc = none ↔ (lsProg_579 H₂).externAt? pc = none := by
  unfold Program.externAt?
  rw [lsProg_579_base_indep H₁ H₂, lsProg_579_hookAtOff?_eq H₁, lsProg_579_hookAtOff?_eq H₂]
  exact findSome_stub_none_iff hdom _ _

theorem lsProg_579_externAt?_some [LibsignalPlacement]
    {H₁ H₂ : LibsignalHooks} (hdom : ∀ sym, (H₁ sym).isSome = (H₂ sym).isSome)
    {pc : BitVec 64} {f : State → State}
    (h : (lsProg_579 H₁).externAt? pc = some f) :
    ∃ sym, H₁ sym = some f ∧ (lsProg_579 H₂).externAt? pc = H₂ sym := by
  unfold Program.externAt? at h ⊢
  rw [lsProg_579_base_indep H₁ H₂, lsProg_579_hookAtOff?_eq H₁] at h
  rw [lsProg_579_hookAtOff?_eq H₂]
  exact findSome_stub_some hdom _ _ h

def inLsUnmutByte [LibsignalPlacement] (a : BitVec 64) : Bool :=
  (List.range 624).any fun i =>
    !(decide (i ∈ libsignalMutatedBlocks)) &&
      decide (InRegion (lsmpl.base i) (libsignalSessionLib.blockLib i).text.code.length a)

def inLsUnmutCode4 [LibsignalPlacement] (pc : BitVec 64) : Bool :=
  inLsUnmutByte pc && inLsUnmutByte (pc + 1#64) &&
    inLsUnmutByte (pc + 2#64) && inLsUnmutByte (pc + 3#64)

theorem isLazyFree_stripCodec (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripCodecMem keep m).isLazyFree a = m.isLazyFree a := by
  dsimp only [stripCodecMem, Memory.isLazyFree]
  rcases m.cells a with _ | ⟨_ | ⟨r, w, x, _, _⟩, _⟩
  · rfl
  · rfl
  · cases keep a <;> cases r <;> cases w <;> cases x <;> rfl

theorem lscl_stripCodec_of_keep_unmut [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {m : Memory}
    (hkeep : ∀ a, inLsUnmutByte a = true → keep a = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl m) :
    LibsignalCodeLoaded lsmpl (stripCodecMem keep m) := by
  intro i hi hunmut X O svc
  have hL := hcrl.1 i hi hunmut X O svc
  rw [Program.codeLoaded_iff] at hL ⊢
  obtain ⟨h1, h2, hcode⟩ := hL
  refine ⟨h1, h2, fun off hoff => ?_⟩
  have hlen_eq : (libsignalSessionLib.blockProgram lsmpl i X O svc).code.length =
      (libsignalSessionLib.blockLib i).text.code.length :=
    CryptoVerification.E2E.Run.libsignalSessionLib_blockProgram_code_length lsmpl hi X O svc
  let addr := (libsignalSessionLib.blockProgram lsmpl i X O svc).base + BitVec.ofNat 64 off
  have hin_byte : inLsUnmutByte addr = true := by
    unfold inLsUnmutByte
    rw [List.any_eq_true]
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    refine ⟨by intro hm; simp [hm] at hunmut, ?_⟩
    unfold InRegion
    have hb : (libsignalSessionLib.blockProgram lsmpl i X O svc).base = lsmpl.base i := rfl
    have hsub : addr - lsmpl.base i = BitVec.ofNat 64 off := by
      dsimp [addr]; rw [hb]; bv_arith
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ← hlen_eq]
    exact hoff
  have hk : keep addr = true := hkeep addr hin_byte
  obtain ⟨hr, hp, hlf⟩ := hcode off hoff
  refine ⟨(stripCodec_read8 keep m addr).trans hr,
    (stripCodec_perm_of_keep hk).trans hp, ?_⟩
  rwa [isLazyFree_stripCodec]

theorem fetchMem_stripCodec_of_keep4 (P : Program) {keep : BitVec 64 → Bool} {m : Memory}
    {pc : BitVec 64}
    (hk0 : keep pc = true) (hk1 : keep (pc + 1#64) = true)
    (hk2 : keep (pc + 2#64) = true) (hk3 : keep (pc + 3#64) = true) :
    P.fetchMem (stripCodecMem keep m) pc = P.fetchMem m pc := by
  have hr32 : (stripCodecMem keep m).read32 pc = m.read32 pc := by
    simp [Memory.read32, stripCodec_read8]
  have hce : (stripCodecMem keep m).canExec pc 4 = m.canExec pc 4 := by
    have hp0 := stripCodec_perm_of_keep (m := m) hk0
    have hp1 := stripCodec_perm_of_keep (m := m) hk1
    have hp2 := stripCodec_perm_of_keep (m := m) hk2
    have hp3 := stripCodec_perm_of_keep (m := m) hk3
    have h1 : pc + 1#64 + 1#64 = pc + 2#64 := by bv_arith
    have h2 : pc + 2#64 + 1#64 = pc + 3#64 := by bv_arith
    simp only [Memory.canExec, Memory.allPerm, h1, h2, hp0, hp1, hp2, hp3]
  unfold Program.fetchMem
  rw [hce, hr32]

theorem fetchMem_not_isSvc0_of_inLsUnmutCode4 [LibsignalPlacement]
    {P : Program} {m : Memory} {pc : BitVec 64} {inst : Instr}
    (hcrl : LibsignalCodeRoLoaded lsmpl m)
    (hin : inLsUnmutCode4 pc = true)
    (hfm : P.fetchMem m pc = some inst) :
    inst.isSvc0 = false := by
  have hin' := hin
  unfold inLsUnmutCode4 at hin'
  simp only [Bool.and_eq_true] at hin'
  obtain ⟨⟨⟨hb0, hb1⟩, hb2⟩, hb3⟩ := hin'
  have hcl' := lscl_stripCodec_of_keep_unmut (keep := inLsUnmutByte) (fun _ h => h) hcrl
  have hbi : CryptoVerification.LsBlockBound 624 := inferInstance
  have hx : ∀ a, ((stripCodecMem inLsUnmutByte m).perm a).x = true →
      ∃ i, i < 624 ∧ (i ∈ libsignalMutatedBlocks) = false ∧
        InRegion (lsmpl.base i) (libsignalSessionLib.blockLib i).text.code.length a := by
    intro a hxa
    have hba : inLsUnmutByte a = true := (stripCodec_perm_x_imp hxa).2
    unfold inLsUnmutByte at hba
    rw [List.any_eq_true] at hba
    obtain ⟨i, hi_mem, hcond⟩ := hba
    rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hcond
    exact ⟨i, List.mem_range.mp hi_mem, by simp [hcond.1], hcond.2⟩
  have hne := @CryptoVerification.E2E.Run.libsignalSessionLib_fetchMem_ne_svc0_of_lscl
    _ P (stripCodecMem inLsUnmutByte m) hcl' 624 hbi hx pc
  rw [fetchMem_stripCodec_of_keep4 P hb0 hb1 hb2 hb3, hfm] at hne
  cases inst <;> simp [Instr.isSvc0, CryptoVerification.E2E.Run.svc0] at hne ⊢
  exact fun h1 h2 => hne h1 h2

theorem trap_extern_step_eq_and_fs_mc [LibsignalPlacement]
    {M : AllocCostModel} {A0 : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (memcpyFn : State → State)
    (hG : CliGhostAllocHooks M A0 lim g)
    (hMcRow : cliGhostExterns g baseExt memcpyName = some memcpyFn)
    (hMcFs : ∀ u, (memcpyFn u).fs = u.fs)
    (hPanAlloc : cliGhostExterns g baseExt lsHandleAllocErrorSym = some Rust.panicked)
    (hPanRaw : cliGhostExterns g baseExt lsHandleErrorSym = some Rust.panicked)
    {sym : String} {f : State → State} {u : State}
    (htrap : codecTrapHooksMc A0 lim g baseExt memcpyFn sym = some f)
    (hnoex_fu : ∀ msg, (f u).status ≠ .Exception msg) :
    ∃ g_fn, cliGhostExterns g baseExt sym = some g_fn ∧
      g_fn u = f u ∧ (f u).fs = u.fs := by
  unfold codecTrapHooksMc at htrap
  split_ifs at htrap with h1 h2 h3 h4 h5 h6 h7
  · subst h1; injection htrap with hf; subst hf
    have hshim : cliGhostExterns g baseExt lsRustNoAllocShimSymCli = some ProofLib.hookNoop :=
      (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_shim g baseExt).trans
        (congrArg some hG.shim_eq)
    exact ⟨ProofLib.hookNoop, hshim, rfl, hookNoop_fs u⟩
  · subst h2; injection htrap with hf; subst hf
    unfold guardPre at hnoex_fu ⊢
    by_cases hact : ActivePre (rustCliAllocBudgetSpec M A0 lim false) u
    · simp only [hact, ↓reduceIte]
      exact ⟨g.alloc, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_alloc g baseExt,
        rfl, hG.alloc_fs u⟩
    · exfalso; simp only [hact, ↓reduceIte] at hnoex_fu; exact hnoex_fu "pre" rfl
  · subst h3; injection htrap with hf; subst hf
    unfold guardPre at hnoex_fu ⊢
    by_cases hact : ActivePre (rustCliDeallocBudgetSpec M A0 lim) u
    · simp only [hact, ↓reduceIte]
      exact ⟨g.dealloc, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_dealloc g baseExt,
        rfl, hG.dealloc_fs u⟩
    · exfalso; simp only [hact, ↓reduceIte] at hnoex_fu; exact hnoex_fu "pre" rfl
  · subst h4; injection htrap with hf; subst hf
    unfold guardPre at hnoex_fu ⊢
    by_cases hact : ActivePre (rustCliReallocBudgetSpec M A0 lim) u
    · simp only [hact, ↓reduceIte]
      exact ⟨g.realloc, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_realloc g baseExt,
        rfl, hG.realloc_fs u⟩
    · exfalso; simp only [hact, ↓reduceIte] at hnoex_fu; exact hnoex_fu "pre" rfl
  · subst h5; injection htrap with hf; subst hf
    unfold guardPre at hnoex_fu ⊢
    by_cases hact : ActivePre (withVmPreserved framelessMemcpySpec) u
    · simp only [hact, ↓reduceIte]
      exact ⟨memcpyFn, hMcRow, rfl, hMcFs u⟩
    · exfalso; simp only [hact, ↓reduceIte] at hnoex_fu; exact hnoex_fu "pre" rfl
  · subst h6; injection htrap with hf; subst hf
    exact ⟨Rust.panicked, hPanAlloc, rfl, rfl⟩
  · subst h7; injection htrap with hf; subst hf
    exact ⟨Rust.panicked, hPanRaw, rfl, rfl⟩
  · generalize hother : cliGhostExterns g baseExt sym = res at htrap
    cases res
    · cases htrap
    · injection htrap with hf; subst hf
      exfalso; exact hnoex_fu "unlinked" rfl

theorem trap_extern_step_eq_and_fs [LibsignalPlacement]
    {M : AllocCostModel} {A0 : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A0 lim g)
    {sym : String} {f : State → State} {u : State}
    (htrap : codecTrapHooks A0 lim mmpl g W sym = some f)
    (hnoex_fu : ∀ msg, (f u).status ≠ .Exception msg) :
    ∃ g_fn, cliGhostExterns g (cliExternsPlaced mmpl W) sym = some g_fn ∧
      g_fn u = f u ∧ (f u).fs = u.fs := by
  have hC := codecHooksPlaced_of_hooks mmpl g W hG
  obtain ⟨f_mc, hf_mc, _, _, _, _, _, _, _, hfs_mc, _⟩ := hG.memcpy
  unfold codecTrapHooks at htrap
  rw [hf_mc] at htrap; dsimp only [Option.getD] at htrap
  exact trap_extern_step_eq_and_fs_mc g (cliExternsPlaced mmpl W) f_mc hG
    (cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hf_mc)
    hfs_mc hC.panic_alloc hC.panic_raw htrap hnoex_fu

theorem evalInst_eq_execInst_local (P : Program) {inst : Instr}
    (h : inst.isSvc0 = false) (s : State) : P.evalInst inst s = execInst inst s := by
  unfold Program.evalInst execInst
  cases inst with
  | system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
      · dsimp only [execInstWithSvc]; simp [himm]
    · rfl
  | _ => rfl

/-! ## Section 3A: Indexed Deterministic Chains, Lasso/Halt Reachability, & `overrideEntries` -/

inductive StepsN (P : Program) : Nat → State → State → Prop
  | zero (s : State) : StepsN P 0 s s
  | succ {n : Nat} {s u t : State} : Step P s u → StepsN P n u t → StepsN P (n + 1) s t

theorem StepsN.toSteps {P : Program} {n : Nat} {s t : State}
    (h : StepsN P n s t) : Steps P s t := by
  induction h with
  | zero s => exact Steps.refl s
  | succ h1 _ ih => exact Steps.step h1 ih

theorem steps_iff_exists_stepsN {P : Program} {s t : State} :
    Steps P s t ↔ ∃ n, StepsN P n s t := by
  constructor
  · intro h
    induction h with
    | refl s => exact ⟨0, StepsN.zero s⟩
    | step h1 _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, StepsN.succ h1 hn⟩
  · rintro ⟨n, hn⟩; exact hn.toSteps

theorem StepsN.deterministic {P : Program} {n : Nat} {s t₁ t₂ : State}
    (h₁ : StepsN P n s t₁) (h₂ : StepsN P n s t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | zero _ => cases h₂; rfl
  | succ hs₁ hr₁ ih =>
    cases h₂ with
    | succ hs₂ hr₂ =>
      have hu := Step.deterministic hs₁ hs₂
      subst hu; exact ih hr₂

theorem StepsN.split_add {P : Program} {m k : Nat} {s t : State}
    (h : StepsN P (m + k) s t) : ∃ u, StepsN P m s u ∧ StepsN P k u t := by
  induction m generalizing s with
  | zero => simp only [Nat.zero_add] at h; exact ⟨s, StepsN.zero s, h⟩
  | succ m ih =>
    rw [Nat.succ_add] at h
    cases h with
    | succ h1 hrest =>
      obtain ⟨u, hm, hk⟩ := ih hrest
      exact ⟨u, StepsN.succ h1 hm, hk⟩

theorem StepsN.keepsFrozen {P : Program} {n : Nat} {s t : State}
    (h : StepsN P n s t) : s.mem.KeepsFrozen t.mem := by
  induction h with
  | zero s => exact Memory.KeepsFrozen.refl s.mem
  | succ h1 _ ih => exact h1.keepsFrozen.trans ih

theorem stepsN_to_traj {P : Program} {N : Nat} {s0 sf : State}
    (h : StepsN P N s0 sf) :
    ∃ traj : Nat → State,
      traj 0 = s0 ∧ traj N = sf ∧
      (∀ j < N, Step P (traj j) (traj (j + 1))) ∧
      (∀ j ≤ N, StepsN P j s0 (traj j) ∧ StepsN P (N - j) (traj j) sf) := by
  induction h with
  | zero s =>
    refine ⟨fun _ => s, rfl, rfl, fun _ hj => by omega, fun j hj => ?_⟩
    have hj0 : j = 0 := by omega
    subst hj0
    exact ⟨StepsN.zero s, StepsN.zero s⟩
  | @succ n a b c h1 hrest ih =>
    obtain ⟨traj', ht0, htn, hst, hsp⟩ := ih
    let traj : Nat → State := fun k => match k with | 0 => a | k' + 1 => traj' k'
    refine ⟨traj, rfl, htn, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero => dsimp [traj]; rwa [ht0]
      | succ k => exact hst k (by omega)
    · intro j hj
      cases j with
      | zero => exact ⟨StepsN.zero a, StepsN.succ h1 hrest⟩
      | succ k =>
        obtain ⟨hpre, hrem⟩ := hsp k (by omega)
        have hsub : n + 1 - (k + 1) = n - k := Nat.succ_sub_succ_eq_sub n k
        rw [hsub]
        exact ⟨StepsN.succ h1 (ht0 ▸ hpre), hrem⟩

theorem steps_on_lasso {P : Program} {traj : Nat → State} {a b : Nat}
    (hab : a < b)
    (hstep : ∀ j < b, Step P (traj j) (traj (j + 1)))
    (hloop : traj a = traj b)
    {uf : State} (hreach : Steps P (traj 0) uf) :
    ∃ m < b, uf = traj m := by
  let z : Nat → State := fun i => if i < a then traj i else traj (a + (i - a) % (b - a))
  have hz0 : traj 0 = z 0 := by
    dsimp [z]
    by_cases h0 : 0 < a
    · simp only [h0, ↓reduceIte]
    · have ha0 : a = 0 := by omega
      subst ha0; simp
  have hz_bound : ∀ i, ∃ m < b, z i = traj m := by
    intro i; dsimp [z]
    by_cases hi : i < a
    · simp only [hi, ↓reduceIte]; exact ⟨i, by omega, rfl⟩
    · simp only [hi, ↓reduceIte]
      have hmod : (i - a) % (b - a) < b - a := Nat.mod_lt _ (by omega)
      exact ⟨a + (i - a) % (b - a), by omega, rfl⟩
  have hz_step : ∀ i, Step P (z i) (z (i + 1)) := by
    intro i; dsimp [z]
    by_cases hi1 : i + 1 < a
    · have hi : i < a := by omega
      simp only [hi, hi1, ↓reduceIte]
      exact hstep i (by omega)
    · by_cases hi : i < a
      · have hia : i + 1 = a := by omega
        simp only [hi, hi1, ↓reduceIte]
        have h0 : (i + 1 - a) % (b - a) = 0 := by rw [hia, Nat.sub_self, Nat.zero_mod]
        rw [h0, Nat.add_zero, ← hia]
        exact hstep i (by omega)
      · simp only [hi, hi1, ↓reduceIte]
        have hr_lt : (i - a) % (b - a) < b - a := Nat.mod_lt _ (by omega)
        have hsub1 : i + 1 - a = (i - a) + 1 := by omega
        rw [hsub1]
        by_cases hr1 : (i - a) % (b - a) + 1 < b - a
        · have hmod1 : ((i - a) + 1) % (b - a) = (i - a) % (b - a) + 1 := by
            have hdiv := Nat.div_add_mod (i - a) (b - a)
            have : (i - a) + 1 = (b - a) * ((i - a) / (b - a)) + ((i - a) % (b - a) + 1) := by omega
            rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hr1]
          rw [hmod1, ← Nat.add_assoc]
          exact hstep (a + (i - a) % (b - a)) (by omega)
        · have hr_eq : (i - a) % (b - a) + 1 = b - a := by omega
          have hmod0 : ((i - a) + 1) % (b - a) = 0 := by
            have hdiv := Nat.div_add_mod (i - a) (b - a)
            have : (i - a) + 1 = (b - a) * ((i - a) / (b - a) + 1) := by
              rw [Nat.mul_add, Nat.mul_one]; omega
            rw [this, Nat.mul_mod_right]
          rw [hmod0, Nat.add_zero]
          have hba : a + (i - a) % (b - a) + 1 = b := by omega
          have hst := hstep (a + (i - a) % (b - a)) (by omega)
          rwa [hba, ← hloop] at hst
  suffices hgen : ∀ {s uf : State}, Steps P s uf → ∀ i, s = z i → ∃ m < b, uf = traj m from
    hgen hreach 0 hz0
  intro s uf hs
  induction hs with
  | refl _ => intro i hsi; subst hsi; exact hz_bound i
  | step h1 _ ih =>
    intro i hsi; subst hsi
    exact ih (i + 1) (Step.deterministic h1 (hz_step i))

theorem steps_on_halt_chain {P : Program} {traj : Nat → State} {K : Nat}
    (hstep : ∀ j < K, Step P (traj j) (traj (j + 1)))
    (hhalt : Step P (traj K) ((traj K).setStatus .Halted))
    {uf : State} (hreach : Steps P (traj 0) uf) :
    (∃ m ≤ K, uf = traj m) ∨ uf = (traj K).setStatus .Halted := by
  let z : Nat → State := fun i => if i ≤ K then traj i else (traj K).setStatus .Halted
  have hz0 : traj 0 = z 0 := by dsimp [z]
  suffices hgen : ∀ {s uf : State}, Steps P s uf → ∀ i ≤ K + 1, s = z i →
      (∃ m ≤ K, uf = traj m) ∨ uf = (traj K).setStatus .Halted from
    hgen hreach 0 (by omega) hz0
  intro s uf hs
  induction hs with
  | refl _ =>
    intro i hi hsi; subst hsi; dsimp [z]
    by_cases hik : i ≤ K
    · simp only [hik, ↓reduceIte]; exact Or.inl ⟨i, hik, rfl⟩
    · simp [hik]
  | step h1 _ ih =>
    intro i hi hsi; subst hsi
    by_cases hik : i < K
    · have hzi : z i = traj i := by
        dsimp [z]; have h1k : i ≤ K := Nat.le_of_lt hik; simp only [h1k, ↓reduceIte]
      have hzi1 : z (i + 1) = traj (i + 1) := by
        dsimp [z]; have h2k : i + 1 ≤ K := hik; simp only [h2k, ↓reduceIte]
      rw [hzi] at h1
      have hv := Step.deterministic h1 (hstep i hik)
      exact ih (i + 1) (by omega) (hv.trans hzi1.symm)
    · by_cases heqk : i = K
      · rw [heqk] at h1
        have hzi : z K = traj K := by dsimp [z]; simp only [Nat.le_refl K, ↓reduceIte]
        have hzi1 : z (K + 1) = (traj K).setStatus .Halted := by
          have hnk : ¬ K + 1 ≤ K := by omega
          dsimp [z]; simp only [hnk, ↓reduceIte]
        rw [hzi] at h1
        have hv := Step.deterministic h1 hhalt
        exact ih (K + 1) (Nat.le_refl _) (hv.trans hzi1.symm)
      · have hik1 : i = K + 1 := by omega
        rw [hik1] at h1
        have hzi : z (K + 1) = (traj K).setStatus .Halted := by
          have hnk : ¬ K + 1 ≤ K := by omega
          dsimp [z]; simp only [hnk, ↓reduceIte]
        rw [hzi] at h1
        cases h1 <;> simp [State.setStatus] at *

def HookOkAt {α : Type} (spec : Spec α) (u v : State) : Prop :=
  ∀ x R, u.status = .Running → (u.mem ⊨ spec.pre x u ∗ R) → u.spAligned = true →
    u.mem.KeepsFrozen v.mem ∧ v.symtab = u.symtab ∧ SubroutineOutcome spec x R u v

noncomputable def lookupEntry : List (State × State) → State → Option State
  | [], _ => none
  | (k, v) :: tl, s =>
    if @decide (k = s) (Classical.propDecidable _) then some v else lookupEntry tl s

noncomputable def overrideEntries (entries : List (State × State))
    (fallback : State → State) (s : State) : State :=
  (lookupEntry entries s).getD (fallback s)

theorem overrideEntries_eq_of_nodup {entries : List (State × State)}
    (hnodup : (entries.map Prod.fst).Nodup) (fallback : State → State)
    {u v : State} (hmem : (u, v) ∈ entries) :
    overrideEntries entries fallback u = v := by
  unfold overrideEntries
  induction entries with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨u', v'⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnot_in, hnodup_tl⟩ := hnodup
    simp only [List.mem_cons, Prod.mk.injEq] at hmem
    unfold lookupEntry
    by_cases heq : u' = u
    · subst heq
      rcases hmem with ⟨_, rfl⟩ | htl
      · have hd : @decide (u' = u') (Classical.propDecidable _) = true :=
          @decide_eq_true (u' = u') (Classical.propDecidable _) rfl
        rw [hd]; rfl
      · exact False.elim (hnot_in (List.mem_map_of_mem (f := Prod.fst) htl))
    · rcases hmem with ⟨h1, _⟩ | htl
      · exact False.elim (heq h1.symm)
      · have hdec : @decide (u' = u) (Classical.propDecidable _) = false :=
          @decide_eq_false (u' = u) (Classical.propDecidable _) heq
        rw [hdec]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih hnodup_tl htl

theorem hookOk_overrideEntries {α : Type} {spec : Spec α}
    {entries : List (State × State)} {fallback : State → State}
    (hentries : ∀ p ∈ entries, HookOkAt spec p.1 p.2)
    (hfb : HookOk fallback spec) :
    HookOk (overrideEntries entries fallback) spec := by
  intro x R s0 hrun hpre hsp
  unfold overrideEntries
  induction entries with
  | nil => exact hfb x R s0 hrun hpre hsp
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    unfold lookupEntry
    by_cases hk : k = s0
    · subst hk
      have hd : @decide (k = k) (Classical.propDecidable _) = true :=
        @decide_eq_true (k = k) (Classical.propDecidable _) rfl
      rw [hd]; simp only [↓reduceIte, Option.getD_some]
      exact hentries (k, v) (List.mem_cons_self ..) x R hrun hpre hsp
    · have hdec : @decide (k = s0) (Classical.propDecidable _) = false :=
        @decide_eq_false (k = s0) (Classical.propDecidable _) hk
      rw [hdec]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih (fun p hp => hentries p (List.mem_cons_of_mem _ hp))

/-! ## Section 3B-1: Stage-B Sub-Lemma Interfaces & Step Helpers -/

def OutMallocng (keep : BitVec 64 → Bool) (mmpl : Obj.MultiPlacement)
    (lim : BudgetLimits) : Prop :=
  lim.enforced = false ∨
    ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true

theorem b1b_alloc_stripped [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (keep : BitVec 64 → Bool)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    {u : State} (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u)
    (hsym : (g.alloc u).symtab = u.symtab)
    (hkf : (stripCodecS keep u).mem.KeepsFrozen (stripCodecS keep (g.alloc u)).mem) :
    HookOkAt
      (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false)
      (stripCodecS keep u) (stripCodecS keep (g.alloc u)) :=
  fun x R hrun hpre hsp => ⟨hkf, hsym, alloc_stripped_to_stripped hG u hrx x R hrun hpre hsp⟩

theorem b1b_dealloc_stripped [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (keep : BitVec 64 → Bool)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    {u : State} (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u)
    (hsym : (g.dealloc u).symtab = u.symtab)
    (hkf : (stripCodecS keep u).mem.KeepsFrozen (stripCodecS keep (g.dealloc u)).mem) :
    HookOkAt
      (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
      (stripCodecS keep u) (stripCodecS keep (g.dealloc u)) :=
  fun x R hrun hpre hsp => ⟨hkf, hsym, dealloc_stripped_to_stripped hG u hrx x R hrun hpre hsp⟩

theorem b1b_realloc_stripped [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (keep : BitVec 64 → Bool)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    {u : State} (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u)
    (hsym : (g.realloc u).symtab = u.symtab)
    (hkf : (stripCodecS keep u).mem.KeepsFrozen (stripCodecS keep (g.realloc u)).mem) :
    HookOkAt
      (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
      (stripCodecS keep u) (stripCodecS keep (g.realloc u)) :=
  fun x R hrun hpre hsp => ⟨hkf, hsym, realloc_stripped_to_stripped hG u hrx x R hrun hpre hsp⟩

theorem b1b_alloc_unstripped [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (keep : BitVec 64 → Bool)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    {u v' : State} (hOut : OutMallocng keep mmpl lim)
    (hv' : v' = g.alloc u ∨ v' = stripCodecS keep (g.alloc u))
    (hsym : v'.symtab = u.symtab) (hkf : u.mem.KeepsFrozen v'.mem) :
    HookOkAt
      (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false)
      u v' :=
  fun x R hrun hpre hsp => ⟨hkf, hsym, alloc_unstripped_of_hOut hG hOut u v' hv' x R hrun hpre hsp⟩

theorem b1b_dealloc_unstripped [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (keep : BitVec 64 → Bool)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    {u v' : State} (hOut : OutMallocng keep mmpl lim)
    (hv' : v' = g.dealloc u ∨ v' = stripCodecS keep (g.dealloc u))
    (hsym : v'.symtab = u.symtab) (hkf : u.mem.KeepsFrozen v'.mem) :
    HookOkAt
      (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
      u v' :=
  fun x R hrun hpre hsp => ⟨hkf, hsym, dealloc_unstripped_of_hOut hG hOut u v' hv' x R hrun hpre hsp⟩

theorem b1b_realloc_unstripped [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (keep : BitVec 64 → Bool)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    {u v' : State} (hOut : OutMallocng keep mmpl lim)
    (hv' : v' = g.realloc u ∨ v' = stripCodecS keep (g.realloc u))
    (hsym : v'.symtab = u.symtab) (hkf : u.mem.KeepsFrozen v'.mem) :
    HookOkAt
      (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
      u v' :=
  fun x R hrun hpre hsp => ⟨hkf, hsym, realloc_unstripped_of_hOut hG hOut u v' hv' x R hrun hpre hsp⟩

theorem b1b_memcpy_stripped (keep : BitVec 64 → Bool)
    {memcpyFn : State → State}
    (hMcOk : HookOk memcpyFn (withVmPreserved framelessMemcpySpec))
    {u : State} (hsym : (memcpyFn u).symtab = u.symtab)
    (hkf : (stripCodecS keep u).mem.KeepsFrozen (stripCodecS keep (memcpyFn u)).mem) :
    HookOkAt (withVmPreserved framelessMemcpySpec)
      (stripCodecS keep u) (stripCodecS keep (memcpyFn u)) :=
  fun x R hrun hpre hsp =>
    ⟨hkf, hsym, framelessMemcpy_stripped_to_stripped keep hMcOk u x R hrun hpre hsp⟩

theorem b1b_memcpy_unstripped
    {memcpyFn : State → State}
    (hMcOk : HookOk memcpyFn (withVmPreserved framelessMemcpySpec))
    (u : State) :
    HookOkAt (withVmPreserved framelessMemcpySpec) u (memcpyFn u) :=
  fun x R hrun hpre hsp => hMcOk x R u hrun hpre hsp

structure SpecPoolSwap [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) {β : Type} (specF : RustCliAllocBudget M → Spec β) : Prop where
  pre_stripped :
    ∀ {keep : BitVec 64 → Bool},
      (∀ i, i < 624 → (i ∈ libsignalMutatedBlocks) = false →
        ∀ a, InRegion (lsmpl.base i) (libsignalSessionLib.blockLib i).text.code.length a →
          keep a = true) →
      ∀ {x : β} {R : SepProp} {s0 : State},
        (s0.mem ⊨ (specF (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart)).pre x s0 ∗ R) →
        ((stripCodecS keep s0).mem ⊨
          (specF (strippedMallocngBudget keep M I hS γ mmpl tp brkStart)).pre x (stripCodecS keep s0) ∗ R)
  pre_unstripped :
    ∀ {keep : BitVec 64 → Bool}, OutMallocng keep mmpl lim →
      ∀ {x : β} {R : SepProp} {s0 : State},
        (s0.mem ⊨ (specF (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart)).pre x s0 ∗ R) →
        (s0.mem ⊨ (specF (strippedMallocngBudget keep M I hS γ mmpl tp brkStart)).pre x s0 ∗ R)
  out_back :
    ∀ {keep : BitVec 64 → Bool} {x : β} {R : SepProp} {s0 uf s0' uf' : State},
      (s0' = s0 ∨ s0' = stripCodecS keep s0) →
      ((uf' = uf ∧ OutMallocng keep mmpl lim) ∨ uf' = stripCodecS keep uf) →
      (lim.enforced = true → CodeBlocksPermRX mmpl uf) →
      s0.mem.KeepsFrozen uf.mem →
      SubroutineOutcome (specF (strippedMallocngBudget keep M I hS γ mmpl tp brkStart)) x R s0' uf' →
      SubroutineOutcome (specF (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart)) x R s0 uf

theorem b2_specPoolSwap_tryFrom [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) :
    SpecPoolSwap I hS γ mmpl tp brkStart lim
      (fun A => withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A lim)) where
  pre_stripped hk _ _ _ hpre := tryFrom_pre_stripped hk hpre
  pre_unstripped hOut _ _ _ hpre := tryFrom_pre_unstripped hOut hpre
  out_back {keep} {_} {_} {_} {_} {_} {_} hs0 huf hrx hkf hout := by
    rcases hs0 with rfl | rfl <;> rcases huf with ⟨rfl, hOut⟩ | rfl
    · exact tryFrom_outcome_of_unstripped_unstripped keep hrx hkf hOut hout
    · exact tryFrom_outcome_of_unstripped_stripped keep hrx hkf hout
    · exact tryFrom_outcome_of_stripped_unstripped keep hrx hkf hOut hout
    · exact tryFrom_outcome_of_stripped_stripped keep hrx hkf hout

theorem b2_specPoolSwap_pksmSlot [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (PksmEnv : PksmGhost → List AllocEvent → Prop) (S : RunSem) :
    SpecPoolSwap I hS γ mmpl tp brkStart lim
      (fun A => pksmSlotSpecPlaced M A lim PksmEnv S) where
  pre_stripped hk _ _ _ hpre := pksm_pre_stripped hk hpre
  pre_unstripped hOut _ _ _ hpre := pksm_pre_unstripped hOut hpre
  out_back {keep} {_} {_} {_} {_} {_} {_} hs0 huf hrx hkf hout := by
    rcases hs0 with rfl | rfl <;> rcases huf with ⟨rfl, hOut⟩ | rfl
    · exact pksm_outcome_of_unstripped_unstripped keep hrx hkf hOut hout
    · exact pksm_outcome_of_unstripped_stripped keep hrx hkf hout
    · exact pksm_outcome_of_stripped_unstripped keep hrx hkf hOut hout
    · exact pksm_outcome_of_stripped_stripped keep hrx hkf hout

/-- Ghost-`memcpyFn` / `memcpyE`-parametric Stage-B shadow hook table. -/
noncomputable def codecShadowHooksMc [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (memcpyFn : State → State)
    (allocE deallocE reallocE memcpyE : List (State × State)) : LibsignalHooks :=
  fun sym =>
    if sym = lsRustNoAllocShimSymCli then some ProofLib.hookNoop
    else if sym = lsRustAllocSymCli then
      some (overrideEntries allocE (shadowFallback keep lim mmpl g.alloc))
    else if sym = lsRustDeallocSymCli then
      some (overrideEntries deallocE (shadowFallback keep lim mmpl g.dealloc))
    else if sym = lsRustReallocSymCli then
      some (overrideEntries reallocE (shadowFallback keep lim mmpl g.realloc))
    else if sym = memcpyName then
      some (overrideEntries memcpyE memcpyFn)
    else if sym = lsHandleAllocErrorSym then some Rust.panicked
    else if sym = lsHandleErrorSym then some Rust.panicked
    else match cliGhostExterns g baseExt sym with
      | some _ => some (fun u => { u with status := .Exception "unlinked" })
      | none => none

theorem codecShadowHooksMc_isSome_eq [LibsignalPlacement]
    {M : AllocCostModel} (A0 : RustCliAllocBudget M)
    (keep : BitVec 64 → Bool) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (memcpyFn : State → State)
    (allocE deallocE reallocE memcpyE : List (State × State)) (sym : String) :
    (codecShadowHooksMc keep lim mmpl g baseExt memcpyFn allocE deallocE reallocE memcpyE sym).isSome =
      (codecTrapHooksMc A0 lim g baseExt memcpyFn sym).isSome := by
  unfold codecShadowHooksMc codecTrapHooksMc
  split_ifs <;> rfl

theorem codecHooksPlaced_shadow_mc [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (memcpyFn : State → State) (keep : BitVec 64 → Bool)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hMcOk : HookOk memcpyFn (withVmPreserved framelessMemcpySpec))
    {allocE deallocE reallocE memcpyE : List (State × State)}
    (hAllocE : ∀ p ∈ allocE, HookOkAt
      (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false)
      p.1 p.2)
    (hDeallocE : ∀ p ∈ deallocE, HookOkAt
      (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
      p.1 p.2)
    (hReallocE : ∀ p ∈ reallocE, HookOkAt
      (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
      p.1 p.2)
    (hMemcpyE : ∀ p ∈ memcpyE, HookOkAt (withVmPreserved framelessMemcpySpec) p.1 p.2) :
    CodecHooksPlaced M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim
      (codecShadowHooksMc keep lim mmpl g baseExt memcpyFn allocE deallocE reallocE memcpyE) := by
  refine codecHooksPlaced_of_hookSat
    ⟨ProofLib.hookNoop, by simp [codecShadowHooksMc], hookOk_hookNoop_noAllocShim_vm⟩
    ⟨_, by simp only [codecShadowHooksMc, (by decide : lsRustAllocSymCli ≠ lsRustNoAllocShimSymCli),
      ↓reduceIte], hookOk_overrideEntries hAllocE (hookOk_shadowFallback_alloc keep hG)⟩
    ⟨_, by simp only [codecShadowHooksMc, (by decide : lsRustReallocSymCli ≠ lsRustNoAllocShimSymCli),
      (by decide : lsRustReallocSymCli ≠ lsRustAllocSymCli),
      (by decide : lsRustReallocSymCli ≠ lsRustDeallocSymCli), ↓reduceIte],
      hookOk_overrideEntries hReallocE (hookOk_shadowFallback_realloc keep hG)⟩
    ⟨_, by simp only [codecShadowHooksMc, (by decide : lsRustDeallocSymCli ≠ lsRustNoAllocShimSymCli),
      (by decide : lsRustDeallocSymCli ≠ lsRustAllocSymCli), ↓reduceIte],
      hookOk_overrideEntries hDeallocE (hookOk_shadowFallback_dealloc keep hG)⟩
    ⟨_, by simp only [codecShadowHooksMc, (by decide : memcpyName ≠ lsRustNoAllocShimSymCli),
      (by decide : memcpyName ≠ lsRustAllocSymCli),
      (by decide : memcpyName ≠ lsRustDeallocSymCli),
      (by decide : memcpyName ≠ lsRustReallocSymCli), ↓reduceIte],
      hookOk_overrideEntries hMemcpyE hMcOk⟩
    (by simp only [codecShadowHooksMc, (by decide : lsHandleAllocErrorSym ≠ lsRustNoAllocShimSymCli),
      (by decide : lsHandleAllocErrorSym ≠ lsRustAllocSymCli),
      (by decide : lsHandleAllocErrorSym ≠ lsRustDeallocSymCli),
      (by decide : lsHandleAllocErrorSym ≠ lsRustReallocSymCli),
      (by decide : lsHandleAllocErrorSym ≠ memcpyName), ↓reduceIte])
    (by simp only [codecShadowHooksMc, (by decide : lsHandleErrorSym ≠ lsRustNoAllocShimSymCli),
      (by decide : lsHandleErrorSym ≠ lsRustAllocSymCli),
      (by decide : lsHandleErrorSym ≠ lsRustDeallocSymCli),
      (by decide : lsHandleErrorSym ≠ lsRustReallocSymCli),
      (by decide : lsHandleErrorSym ≠ memcpyName),
      (by decide : lsHandleErrorSym ≠ lsHandleAllocErrorSym), ↓reduceIte])

noncomputable def codecShadowHooks [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (allocE deallocE reallocE : List (State × State)) : LibsignalHooks :=
  codecShadowHooksMc keep lim mmpl g (cliExternsPlaced mmpl W)
    (g.memcpy.getD ProofLib.hookMemcpy) allocE deallocE reallocE []

theorem codecShadowHooks_isSome_eq [LibsignalPlacement]
    {M : AllocCostModel} (A0 : RustCliAllocBudget M)
    (keep : BitVec 64 → Bool) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (allocE deallocE reallocE : List (State × State)) (sym : String) :
    (codecShadowHooks keep lim mmpl g W allocE deallocE reallocE sym).isSome =
      (codecTrapHooks A0 lim mmpl g W sym).isSome :=
  codecShadowHooksMc_isSome_eq A0 keep lim mmpl g (cliExternsPlaced mmpl W)
    (g.memcpy.getD ProofLib.hookMemcpy) allocE deallocE reallocE [] sym

theorem codecHooksPlaced_shadow [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (W : CliHooks) (keep : BitVec 64 → Bool)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    {allocE deallocE reallocE : List (State × State)}
    (hAllocE : ∀ p ∈ allocE, HookOkAt
      (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false)
      p.1 p.2)
    (hDeallocE : ∀ p ∈ deallocE, HookOkAt
      (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
      p.1 p.2)
    (hReallocE : ∀ p ∈ reallocE, HookOkAt
      (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
      p.1 p.2) :
    CodecHooksPlaced M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim
      (codecShadowHooks keep lim mmpl g W allocE deallocE reallocE) := by
  obtain ⟨f_mc, hf_mc, _, _, _, _, hok_fm, _, hvm_mc, _, _⟩ := hG.memcpy
  unfold codecShadowHooks
  rw [hf_mc]; dsimp only [Option.getD]
  exact codecHooksPlaced_shadow_mc I hS γ mmpl tp brkStart lim g (cliExternsPlaced mmpl W)
    f_mc keep hG (hookOk_withVmPreserved hok_fm hvm_mc)
    hAllocE hDeallocE hReallocE (fun _ hp => nomatch hp)

theorem not_badKf_of_memcpy (keep : BitVec 64 → Bool)
    {u : State} (hact : ActivePre (withVmPreserved framelessMemcpySpec) u) :
    (stripCodecMem keep u.mem).KeepsFrozen (stripCodecMem keep (ProofLib.hookMemcpy u).mem) := by
  obtain ⟨hrun, hsp, x, R, hpre⟩ := hact
  have hrun' : (stripCodecS keep u).status = .Running := by cases u; exact hrun
  have hsp' : (stripCodecS keep u).spAligned = true := by cases u; exact hsp
  have hpre_eq : (withVmPreserved framelessMemcpySpec).pre x (stripCodecS keep u) =
      (withVmPreserved framelessMemcpySpec).pre x u := by cases u; rfl
  have hpre' : (stripCodecS keep u).mem ⊨
      (withVmPreserved framelessMemcpySpec).pre x (stripCodecS keep u) ∗ R := by
    rw [hpre_eq]; exact (satisfies_stripCodec_iff keep u.mem _).mpr hpre
  have hkf := (hookOk_hookMemcpy_frameless_vm x R (stripCodecS keep u) hrun' hpre' hsp').1
  rw [hookMemcpy_stripCodec] at hkf
  simpa [stripCodecS] using hkf

/-- Stripped `KeepsFrozen` preservation across an active `memcpyFn` step. -/
def MemcpyStripKeepsFrozen (memcpyFn : State → State) : Prop :=
  ∀ (keep : BitVec 64 → Bool) (u : State),
    ActivePre (withVmPreserved framelessMemcpySpec) u →
    u.mem.KeepsFrozen (memcpyFn u).mem →
    (stripCodecMem keep u.mem).KeepsFrozen (stripCodecMem keep (memcpyFn u).mem)

theorem memcpyStripKeepsFrozen_hookMemcpy :
    MemcpyStripKeepsFrozen ProofLib.hookMemcpy :=
  fun keep _ hact _ => not_badKf_of_memcpy keep hact

theorem badKf_single_byte_props {a_bad : BitVec 64}
    {mmpl : Obj.MultiPlacement} {lim : BudgetLimits} {u v : State}
    (hkf : u.mem.KeepsFrozen v.mem)
    (hbad : ¬ (stripCodecMem (fun a => decide (a ≠ a_bad)) u.mem).KeepsFrozen
      (stripCodecMem (fun a => decide (a ≠ a_bad)) v.mem)) :
    ¬ u.mem.Frozen a_bad ∧
      u.mem.KeepsFrozen (stripCodecMem (fun a => decide (a ≠ a_bad)) v.mem) ∧
      ((lim.enforced = true → CodeBlocksPermRX mmpl u) →
        OutMallocng (fun a => decide (a ≠ a_bad)) mmpl lim) := by
  let keep1 : BitVec 64 → Bool := fun a => decide (a ≠ a_bad)
  have hnfr : ¬ u.mem.Frozen a_bad := by
    intro hfr_bad
    apply hbad
    intro a hfr'
    by_cases ha : a = a_bad
    · subst ha
      obtain ⟨hr8, hp, hlf, han⟩ := hkf a hfr_bad
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [stripCodec_read8, stripCodec_read8, hr8]
      · have hp_eq : ∀ (m : Memory),
            (stripCodecMem keep1 m).perm a = (m.perm a).map (stripCodecPerm (keep1 a)) := by
          intro m; dsimp only [stripCodecMem, Memory.perm]
          rcases m.cells a with _ | ⟨_ | ⟨r, w, x, _, _⟩, _⟩
          · rfl
          · rfl
          · cases keep1 a <;> cases r <;> cases w <;> cases x <;> rfl
        rw [hp_eq, hp_eq, hp]
      · rw [isLazyFree_stripCodec, isLazyFree_stripCodec, hlf]
      · dsimp only [stripCodecMem, Memory.isAnon] at *
        rcases hcu : u.mem.cells a with _ | ⟨_ | _, _⟩ <;>
          rcases hcv : v.mem.cells a with _ | ⟨_ | _, _⟩ <;>
          simp_all [stripCodecPerm]
        all_goals (repeat' split) <;> simp_all
    · have hk : keep1 a = true := decide_eq_true ha
      have hfr_u : u.mem.Frozen a := by
        unfold Memory.Frozen at hfr' ⊢
        rwa [stripCodec_perm_of_keep (m := u.mem) hk] at hfr'
      obtain ⟨hr8, hp, hlf, han⟩ := hkf a hfr_u
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [stripCodec_read8, stripCodec_read8, hr8]
      · rw [stripCodec_perm_of_keep hk, stripCodec_perm_of_keep hk, hp]
      · rw [isLazyFree_stripCodec, isLazyFree_stripCodec, hlf]
      · have hc_eq : ∀ (m : Memory), (stripCodecMem keep1 m).isAnon a = m.isAnon a := by
          intro m; dsimp only [stripCodecMem, Memory.isAnon]
          rcases m.cells a with _ | ⟨_ | ⟨r, w, x, _, _⟩, _⟩
          · rfl
          · rfl
          · cases keep1 a <;> cases r <;> cases w <;> cases x <;> rfl
        rw [hc_eq, hc_eq, han]
  have hkf_uv' : u.mem.KeepsFrozen (stripCodecMem keep1 v.mem) := by
    intro a hfr_u
    have hne : a ≠ a_bad := fun h => hnfr (h ▸ hfr_u)
    have hk : keep1 a = true := decide_eq_true hne
    obtain ⟨hr8, hp, hlf, han⟩ := hkf a hfr_u
    refine ⟨(stripCodec_read8 keep1 v.mem a).trans hr8,
      (stripCodec_perm_of_keep (m := v.mem) hk).trans hp,
      (isLazyFree_stripCodec keep1 v.mem a).trans hlf, ?_⟩
    have hc_eq : (stripCodecMem keep1 v.mem).isAnon a = v.mem.isAnon a := by
      dsimp only [stripCodecMem, Memory.isAnon]
      rcases v.mem.cells a with _ | ⟨_ | ⟨r, w, x, _, _⟩, _⟩
      · rfl
      · rfl
      · cases keep1 a <;> cases r <;> cases w <;> cases x <;> rfl
    exact hc_eq.trans han
  refine ⟨hnfr, hkf_uv', fun hrx => ?_⟩
  by_cases henf : lim.enforced = true
  · right
    intro a hin
    apply decide_eq_true
    intro heq; subst heq
    have hrx_a : u.mem.perm a = some Perm.rx := hrx henf a hin
    apply hnfr
    unfold Memory.Frozen
    rw [hrx_a]; rfl
  · left; exact Bool.eq_false_iff.mpr henf

theorem canExec_stripCodec_false_of_not_inLsUnmutCode4 [LibsignalPlacement]
    (pc : BitVec 64) (h : inLsUnmutCode4 pc = false) :
    ∃ a_bad : BitVec 64,
      inLsUnmutByte a_bad = false ∧
      ∀ m : Memory, (stripCodecMem (fun a => decide (a ≠ a_bad)) m).canExec pc 4 = false := by
  have perm_x_false : ∀ (a : BitVec 64) (m : Memory),
      ((stripCodecMem (fun x => decide (x ≠ a)) m).perm a).x = false := by
    intro a m
    have hd : decide (a ≠ a) = false := by simp
    dsimp only [stripCodecMem, Memory.perm]
    rcases m.cells a with _ | ⟨_ | ⟨r, w, x, _, _⟩, _⟩
    · rfl
    · rfl
    · simp only [hd]; cases r <;> cases w <;> cases x <;> rfl
  have h1 : pc + 1#64 + 1#64 = pc + 2#64 := by bv_arith
  have h2 : pc + 2#64 + 1#64 = pc + 3#64 := by bv_arith
  unfold inLsUnmutCode4 at h
  cases hb0 : inLsUnmutByte pc
  · refine ⟨pc, hb0, fun m => ?_⟩
    dsimp only [Memory.canExec, Memory.allPerm]
    rw [perm_x_false pc m]; simp
  · cases hb1 : inLsUnmutByte (pc + 1#64)
    · refine ⟨pc + 1#64, hb1, fun m => ?_⟩
      dsimp only [Memory.canExec, Memory.allPerm]
      rw [perm_x_false (pc + 1#64) m]; simp
    · cases hb2 : inLsUnmutByte (pc + 2#64)
      · refine ⟨pc + 2#64, hb2, fun m => ?_⟩
        dsimp only [Memory.canExec, Memory.allPerm]
        rw [h1, perm_x_false (pc + 2#64) m]; simp
      · cases hb3 : inLsUnmutByte (pc + 3#64)
        · refine ⟨pc + 3#64, hb3, fun m => ?_⟩
          dsimp only [Memory.canExec, Memory.allPerm]
          rw [h1, h2, perm_x_false (pc + 3#64) m]; simp
        · simp [hb0, hb1, hb2, hb3] at h

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferCoreFd
