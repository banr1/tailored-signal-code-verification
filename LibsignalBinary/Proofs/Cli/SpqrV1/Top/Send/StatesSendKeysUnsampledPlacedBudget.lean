/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.DoReservePlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable Scaffolding for `.keysUnsampled` Arm (Block `427`)

Provides budget-threaded `[LibsignalPlacement]` callee contracts for `<Authenticator>::mac_hdr`
(Block `342`) and `do_reserve_and_handle [local#7]` (Block `460`) on `spqrSendPlacedProg ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.Cli.SpqrV1.Alloc.Placed (blkPC_460 blkPl_460)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1 (Authenticator Bytes)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded keys_ls_subroutine_ok_of_block_cro
   memsetName sepWP_seq_lscro sepWPp_seq_lscro sessionMemcpyRegionSpec sessionMemcpySpec
   withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_externAt?_of_mem spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Auth (AuthMacHdrPinnedGhost)
open CryptoVerification.SpqrV1.Poly.ComputeAt (spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Top.Send
  (spqrSendCalleeStack stackAt_spqrSendCallee_split)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
   rustCliReallocBudgetSpec rustCliReallocNoOomSpec
   subroutine_ok_allocNoOom_of_budget subroutine_ok_reallocNoOom_of_budget)
open LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.DoReservePlacedBudget
  (do_reserve_2_raw32_placed_ok do_reserve_2_raw32_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
  (doReserve1Raw32Spec doReserve1Raw32SpecX)
open LibsignalBinary.Proofs.SpqrV1.Auth.MacHdrBudget (authMacHdrPinnedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec
   sessionShimBudgetSpec)

variable [LibsignalPlacement]

namespace KeysUnsampledHelpers

export CryptoVerification.Cli.SpqrV1.Top.Send.KeysUnsampledHelpers
  (SpqrSendJoinStatePlaced of_sepWP_lscro finish_sepWP_lscro)

/-- Derive `subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") sessionMemcpyRegionBudgetSpec`
    (carrying `⌜VmPreserved s0 sf⌝` so `A.pool lim st` frames across `memcpy`)
    from `AllocContractsPlaced M A lim ext`. -/
theorem spqrSend_session_memcpy_region_ok_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") sessionMemcpyRegionBudgetSpec := by
  have h0 : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") (sessionMemcpyBudgetSpec 0) :=
    spqr_hook_ok_of_mem (hA.session_memcpy 0)
  refine subroutine_ok_mono h0 ?_ ?_
  · intro ⟨dst, src, srcBytes⟩ R s hm
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
      sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec, stackAt] at hm ⊢
    rw [ProofLib.memRegion_zero]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro ⟨dst, src, srcBytes⟩ R s0 sf hm
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      sessionMemcpyBudgetSpec, sessionMemcpySpec, stackAt] at hm ⊢
    rw [ProofLib.memRegion_zero] at hm
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm

/-- Plain `sessionMemcpyRegionSpec` companion of `spqrSend_session_memcpy_region_ok_placed`. -/
theorem spqrSend_session_memcpy_region_plain_ok_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") sessionMemcpyRegionSpec := by
  refine subroutine_ok_mono (spqrSend_session_memcpy_region_ok_placed hA)
    (fun _ _ _ hm => hm) ?_
  intro _ R s0 sf hm
  dsimp only [sessionMemcpyRegionBudgetSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hm.2

theorem spqrSend_handle_error_extern
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    (spqrSendPlacedProg ext).externAt? (lsρ spqrHandleErrorSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.handle_error

theorem spqrSend_shim_ok_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym) sessionShimBudgetSpec :=
  spqr_hook_ok_of_mem hA.shim

theorem spqrSend_noAllocShim_ok_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym) noAllocShimSpec :=
  spqr_hook_ok_of_mem hA.noAllocShim

theorem spqrSend_alloc_ok_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false) :=
  spqr_hook_ok_of_mem hA.alloc

theorem spqrSend_allocNoOom_ok_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocNoOomSpec M A lim false) :=
  subroutine_ok_allocNoOom_of_budget (spqrSend_alloc_ok_placed hA)

theorem spqrSend_dealloc_ok_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) :=
  spqr_hook_ok_of_mem hA.dealloc

theorem spqrSend_realloc_ok_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustReallocSym)
      (rustCliReallocBudgetSpec M A lim) :=
  spqr_hook_ok_of_mem hA.realloc

theorem spqrSend_reallocNoOom_ok_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustReallocSym)
      (rustCliReallocNoOomSpec M A lim) :=
  subroutine_ok_reallocNoOom_of_budget (spqrSend_realloc_ok_placed hA)

theorem spqrSend_memset_region_ok_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ memsetName) sessionMemsetRegionBudgetSpec :=
  spqr_hook_ok_of_mem hA.session_memset_region

/-- Run a non-panicking `SepWP` segment to `mid`, propagating `LibsignalCodeRoLoaded lsmpl`
    to a non-panicking `SepWP` continuation. -/
theorem of_sepWP_lscro_plain {prog : Program} {tgt mid : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem → SepWP prog tgt sm Pm post)) :
    SepWP prog tgt s P post :=
  sepWP_seq_lscro hcrl h

theorem finish_sepWP_lscro_plain {prog : Program} {mid tgt : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (hnext : LibsignalCodeRoLoaded lsmpl s.mem → SepWP prog tgt s P' post) (hent : P ⊢ P') :
    SepWP prog mid s P (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem → SepWP prog tgt sm Pm post) := by
  refine SepWP.fold hent (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  exact SepWP.done hpc hrun hnext

/-- Extract a leading existential `∃∗ a, P a` from the precondition of `SepWPp`. -/
theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a : α, SepWPp prog ret s (P a) Q Qp) :
    SepWPp prog ret s (∃∗ a : α, P a) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hma⟩ := hm
  exact h a R hma hL

private theorem lift_subroutine_ok_lscro_post {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog entry
      { withLsCodeRoLoaded lsmpl spec with
        post := fun x' s0' sf => ⌜LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗ spec.post x' s0' sf } := by
  refine Arm64.subroutine_ok.of_codeLoaded fun x' R s0' hpc0 hrun0 hpre0 hsp0 hL0 => ?_
  have ⟨hcrl0, _⟩ := extract_withLsCodeRoLoaded hpre0
  obtain ⟨sf, hsteps, hout, -⟩ := hcall.no_fault_before_outcome x' R s0' hpc0 hrun0 hpre0 hsp0 hL0
  refine Arm64.reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcrl0.of_keepsFrozen hsteps.keepsFrozen, hpost⟩
  · exact Or.inr hrest

/-- Call a panic-capable budget subroutine (`withLsCodeRoLoaded lsmpl spec`) that uses
    `n ≤ spqrSendCalleeStack` bytes of stack, generalized over any panic proposition `Pan`. -/
theorem call_lscro_calleeStack {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : State → SepProp} {Q : State → SepProp → Prop} {Fr F : SepProp}
    {Pan φ_pre : Prop} {φ_post : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜Pan ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hspec_post : ∀ sf, spec.post x s sf = (⌜φ_post sf⌝ ∗ T_post sf ∗ stackAt s.sp n))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post sf) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hcall' := lift_subroutine_ok_lscro_post hcall
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  refine SepWPp.call_wpp (x := x)
    (F := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)
    hcall' hpc hrun hsp_al hlr
    (fun R' hm => by
      change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗
        ((memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) ∗ R')
      rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
      rw [hP, stackAt_spqrSendCallee_split sp n hle] at hm
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
    (fun sm code R' _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost; rw [hexit_eq code sm] at hpost
      exact allowPanic_not_exited hpost)
    (fun sm _ _ hmFr => by
      dsimp only [withLsCodeRoLoaded] at hmFr
      have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (hpan sm))) hmFr
      rw [htr] at hm1
      have hassoc :
          ((⌜Pan ∧ s0.trace <+: sm.trace⌝ ∗ anyHeap) ∗
            (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)) =
          (⌜Pan ∧ s0.trace <+: sm.trace⌝ ∗
            (anyHeap ∗
              (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F))) := by
        sep_ac_rfl
      rw [hassoc] at hm1
      exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))) hm1)
    (fun sm hpcm hrunm hspm hcsm => ?_)
    (fun sm R' _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost; rw [hoom_eq sm] at hpost
      exact (allowPanic_not_exited hpost).elim)
  rw [hsp] at hspm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
  have hpeq : (⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ spec.post x s sm) ∗
      (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) =
      ⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗
        (⌜φ_post sm⌝ ∗ ((stackAt sp spqrSendCalleeStack ∗ T_post sm) ∗ F)) := by
    rw [hspec_post sm, hsp, stackAt_spqrSendCallee_split sp n hle]; sep_ac_rfl
  dsimp only
  exact SepWPp.congr_pre hpeq (SepWPp.pure_left fun hcrl_m => SepWPp.pure_left fun hφ_post =>
    hnext sm hpcm hrunm hspm hφ_post hcrl_m hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs)

/-- Companion of `call_lscro_calleeStack` for budget specs whose postcondition carries an outer
    `∃∗ evs : List AllocEvent, ⌜φ_post evs sf⌝ ∗ T_post evs sf ∗ stackAt s.sp n`. -/
theorem call_lscro_calleeStack_evs {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : List AllocEvent → State → SepProp}
    {Q : State → SepProp → Prop} {Fr F : SepProp}
    {Pan φ_pre : Prop} {φ_post : List AllocEvent → State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜Pan ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hspec_post : ∀ sf,
      spec.post x s sf = (∃∗ evs : List AllocEvent, ⌜φ_post evs sf⌝ ∗ T_post evs sf ∗ stackAt s.sp n))
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post evs sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post evs sf) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hcall' := lift_subroutine_ok_lscro_post hcall
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  refine SepWPp.call_wpp (x := x)
    (F := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)
    hcall' hpc hrun hsp_al hlr
    (fun R' hm => by
      change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗
        ((memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) ∗ R')
      rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
      rw [hP, stackAt_spqrSendCallee_split sp n hle] at hm
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
    (fun sm code R' _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost; rw [hexit_eq code sm] at hpost
      exact allowPanic_not_exited hpost)
    (fun sm _ _ hmFr => by
      dsimp only [withLsCodeRoLoaded] at hmFr
      have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (hpan sm))) hmFr
      rw [htr] at hm1
      have hassoc :
          ((⌜Pan ∧ s0.trace <+: sm.trace⌝ ∗ anyHeap) ∗
            (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)) =
          (⌜Pan ∧ s0.trace <+: sm.trace⌝ ∗
            (anyHeap ∗
              (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F))) := by
        sep_ac_rfl
      rw [hassoc] at hm1
      exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))) hm1)
    (fun sm hpcm hrunm hspm hcsm => ?_)
    (fun sm R' _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost; rw [hoom_eq sm] at hpost
      exact (allowPanic_not_exited hpost).elim)
  rw [hsp] at hspm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
  dsimp only
  have hcrl_eq :
      (⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ spec.post x s sm) ∗
        (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) =
      ⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗
        (spec.post x s sm ∗
          (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)) :=
    sepConj_assoc _ _ _
  refine SepWPp.congr_pre hcrl_eq (SepWPp.pure_left fun hcrl_m => ?_)
  have hex_eq :
      spec.post x s sm ∗
        (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) =
      (∃∗ evs : List AllocEvent,
        (⌜φ_post evs sm⌝ ∗ T_post evs sm ∗ stackAt s.sp n) ∗
          (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)) := by
    rw [hspec_post sm, sepExists_sepConj_left]
  refine SepWPp.congr_pre hex_eq (sepWPp_exists_left fun evs => ?_)
  have hpeq :
      (⌜φ_post evs sm⌝ ∗ T_post evs sm ∗ stackAt s.sp n) ∗
        (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) =
      ⌜φ_post evs sm⌝ ∗ ((stackAt sp spqrSendCalleeStack ∗ T_post evs sm) ∗ F) := by
    rw [hsp, stackAt_spqrSendCallee_split sp n hle]; sep_ac_rfl
  exact SepWPp.congr_pre hpeq (SepWPp.pure_left fun hφ_post =>
    hnext sm evs hpcm hrunm hspm hφ_post hcrl_m
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs)

/-- Non-panicking `SepWP` companion of `call_lscro_calleeStack` for budget callees with
    `spec.onPanic x s sf ⊢ ⌜False⌝`. -/
theorem call_lscro_calleeStack_sepWP {α : Type} {prog : Program}
    {entry ret_pc tgt : BitVec 64} {spec : Spec α} {x : α} {s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : State → SepProp} {Q : State → SepProp → Prop} {F : SepProp}
    {φ_pre : Prop} {φ_post : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_false : ∀ sf, spec.onPanic x s sf ⊢ ⌜False⌝)
    (hspec_post : ∀ sf, spec.post x s sf = (⌜φ_post sf⌝ ∗ T_post sf ∗ stackAt s.sp n))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP prog tgt sf ((stackAt sp spqrSendCalleeStack ∗ T_post sf) ∗ F) Q)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWP prog tgt s P Q := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  have hwpp : SepWPp prog tgt s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜False ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) :=
    call_lscro_calleeStack (s0 := s) (Fr := R) (Pan := False) sp n hle
      hcall hcrl hpc hrun hsp hsp_align rfl hlr hspec_pre hφ hP hexit_eq
      (fun sf => Entails.trans (hpan_false sf) (Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm) (Entails.pure_left False.elim)))
      hspec_post
      (fun sf hpcm hrunm hspm hφm hcrlm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs => by
        intro R' hm' hL'
        rcases (SepWP.to_reaches_pc (hnext sf hpcm hrunm hspm hφm hcrlm
          hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs) hm' hL') with
          ⟨sf', hst, ⟨hpc', hrun', P_f, hmf', hq'⟩ | hoom'⟩
        · exact ⟨sf', hst, Or.inl ⟨hpc', hrun', P_f, hmf', hq'⟩⟩
        · exact ⟨sf', hst, Or.inr (Or.inr hoom')⟩)
      hoom_eq
  obtain ⟨sf, hsteps, hout⟩ := hwpp R hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hq⟩ | ⟨_, P_f, hmf, hqp⟩ | hoom
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, hq⟩⟩
  · have hfalse := hqp hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hfalse
    exact hfalse.1.1.elim
  · exact ⟨sf, hsteps, Or.inr hoom⟩

/-- Non-panicking `SepWP` companion of `call_lscro_calleeStack_evs` for budget callees with
    `spec.onPanic x s sf ⊢ ⌜False⌝` and outer `∃∗ evs : List AllocEvent` postcondition. -/
theorem call_lscro_calleeStack_evs_sepWP {α : Type} {prog : Program}
    {entry ret_pc tgt : BitVec 64} {spec : Spec α} {x : α} {s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : List AllocEvent → State → SepProp}
    {Q : State → SepProp → Prop} {F : SepProp}
    {φ_pre : Prop} {φ_post : List AllocEvent → State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_false : ∀ sf, spec.onPanic x s sf ⊢ ⌜False⌝)
    (hspec_post : ∀ sf,
      spec.post x s sf = (∃∗ evs : List AllocEvent, ⌜φ_post evs sf⌝ ∗ T_post evs sf ∗ stackAt s.sp n))
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post evs sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP prog tgt sf ((stackAt sp spqrSendCalleeStack ∗ T_post evs sf) ∗ F) Q)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWP prog tgt s P Q := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  have hwpp : SepWPp prog tgt s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜False ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) :=
    call_lscro_calleeStack_evs (s0 := s) (Fr := R) (Pan := False) sp n hle
      hcall hcrl hpc hrun hsp hsp_align rfl hlr hspec_pre hφ hP hexit_eq
      (fun sf => Entails.trans (hpan_false sf) (Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm) (Entails.pure_left False.elim)))
      hspec_post
      (fun sf evs hpcm hrunm hspm hφm hcrlm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs => by
        intro R' hm' hL'
        rcases (SepWP.to_reaches_pc (hnext sf evs hpcm hrunm hspm hφm hcrlm
          hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs) hm' hL') with
          ⟨sf', hst, ⟨hpc', hrun', P_f, hmf', hq'⟩ | hoom'⟩
        · exact ⟨sf', hst, Or.inl ⟨hpc', hrun', P_f, hmf', hq'⟩⟩
        · exact ⟨sf', hst, Or.inr (Or.inr hoom')⟩)
      hoom_eq
  obtain ⟨sf, hsteps, hout⟩ := hwpp R hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hq⟩ | ⟨_, P_f, hmf, hqp⟩ | hoom
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, hq⟩⟩
  · have hfalse := hqp hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hfalse
    exact hfalse.1.1.elim
  · exact ⟨sf, hsteps, Or.inr hoom⟩

/-- Under `x.auth.macHdr F x.ep x.hdr = .ok mac`, `(authMacHdrPinnedSpec F M A lim).onPanic`
    is vacuous (`⊢ ⌜False⌝`) because `allocFailedIn` is absent in the budget spec and both
    `u32` length bounds hold. -/
theorem authMacHdrPinned_onPanic_false_of_ok
    {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (x : AuthMacHdrPinnedGhost) (st : M.σ) {mac : Bytes}
    (h : x.auth.macHdr F x.ep x.hdr = .ok mac) (s0 sf : State) :
    (authMacHdrPinnedSpec F M A lim).onPanic (x, st) s0 sf ⊢ ⌜False⌝ := by
  unfold Authenticator.macHdr at h
  dsimp only at h
  split at h
  · rename_i hlt
    rcases hlt with ⟨hk, hd⟩
    dsimp only [authMacHdrPinnedSpec]
    have h1 : ¬ (2 ^ 32 ≤ x.auth.macKey.length) := by omega
    have h2 : ¬ (2 ^ 32 ≤ (Authenticator.hdrLabel ++ toBEBytes 8 x.ep ++ x.hdr).length) := by omega
    simp only [h1, h2, or_self, false_and]
    exact Entails.pure_left False.elim
  · cases h

/-- Generalized `onPanic` entailment for `authMacHdrPinnedSpec` when `macHdr` succeeds,
    ready to plug directly into `call_lscro_calleeStack_evs`. -/
theorem authMacHdrPinned_onPanic_of_ok
    {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Pan : Prop}
    (x : AuthMacHdrPinnedGhost) (st : M.σ) {mac : Bytes}
    (h : x.auth.macHdr F x.ep x.hdr = .ok mac) (s0 sf : State) :
    (authMacHdrPinnedSpec F M A lim).onPanic (x, st) s0 sf ⊢
      ⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap :=
  Entails.trans (authMacHdrPinned_onPanic_false_of_ok x st h s0 sf) (Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm) (Entails.pure_left False.elim))

end KeysUnsampledHelpers

export CryptoVerification.Cli.SpqrV1.Top.Send
  (subroutine_ok_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded)

/-- `<spqr::authenticator::Authenticator>::mac_hdr` (Block `342`) meets
    `withLsCodeRoLoaded lsmpl (authMacHdrPinnedSpec F M A lim)` on `spqrSendPlacedProg ext`. -/
def AuthMacHdrPinnedPlacedOkX (F : ShaCompress) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 342)
    (withLsCodeRoLoaded lsmpl (authMacHdrPinnedSpec F M A lim))

/-- `alloc::raw_vec::RawVecInner<A>::do_reserve_and_handle [local#7]` (Block `460`) meets
    `withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec M A lim)` on `spqrSendPlacedProg ext`. -/
def DoReserve2PlacedOkX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 460)
    (withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec M A lim))

/-- `alloc::raw_vec::RawVecInner<A>::do_reserve_and_handle [local#7]` (Block `460`) meets
    `withLsCodeRoLoaded lsmpl (doReserve1Raw32SpecX M A lim)` on `spqrSendPlacedProg ext`. -/
def DoReserve2PlacedOkXX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 460)
    (withLsCodeRoLoaded lsmpl (doReserve1Raw32SpecX M A lim))

theorem doReserve2_placed_ok_ext_x {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    DoReserve2PlacedOkX M A lim ext := by
  have hraw :
      subroutine_ok ((blkPC_460).rebase (blkPl_460).base (Rust.withPanics ext))
        (lsmpl.base 460) (withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec M A lim)) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (do_reserve_2_raw32_placed_ok (M := M) (A := A) (lim := lim) (H := Rust.withPanics ext)
        hA.handle_error hA.noAllocShim hA.alloc hA.realloc)
  exact keys_ls_subroutine_ok_of_block_cro (callerProg := spqrSendPlacedProg ext) hraw

theorem doReserve2_placed_ok_ext_xx {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    DoReserve2PlacedOkXX M A lim ext := by
  have hraw :
      subroutine_ok ((blkPC_460).rebase (blkPl_460).base (Rust.withPanics ext))
        (lsmpl.base 460) (withLsCodeRoLoaded lsmpl (doReserve1Raw32SpecX M A lim)) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (do_reserve_2_raw32_placed_ok_x (M := M) (A := A) (lim := lim) (H := Rust.withPanics ext)
        hA.handle_error hA.noAllocShim hA.alloc hA.realloc)
  exact keys_ls_subroutine_ok_of_block_cro (callerProg := spqrSendPlacedProg ext) hraw

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
