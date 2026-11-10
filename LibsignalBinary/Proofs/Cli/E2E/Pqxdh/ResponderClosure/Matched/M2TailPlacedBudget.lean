/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymA
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymC
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsEPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P2 Remote-Identity Mismatch Tail

Budget-threaded `[LibsignalPlacement]` counterpart of `Matched.M2TailPlaced` across Blocks `509`,
`530`, and `518`, proving `stageP2_matched_mismatch_tail_exists_placed` and
`stageP2_matched_mismatch_tail_placed` (`(blkPl_518).base + 0x12fc → s0.readReg64 .x30`) under
`StageP2MismatchTailEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlacedBudget

noncomputable section

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement lsLogFilterAddr
  ls_subroutine_ok_of_block lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet (rootStack sessionShimSpec)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (dropSessionStructureLocal2Stack)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost apiDecResultAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
)
open CryptoVerification.E2E.Pqxdh.ResponderStore (dropProcessPrekeyImplState1Spec)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved PanicOomProp decryptPrekeySavedRegsAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (
  SepWPp.weaken_frame entails_replace_sub eq_of_sep_emp
)
open CryptoVerification.CliHandshake.Placed (
  blkLib_eq_509 blkLib_eq_530 blkPC_509 blkPC_530 blkPl_509 blkPl_530 lsProg_509 lsProg_530
)
open scoped CryptoVerification.CliHandshake.Placed
open CryptoVerification.CliHandshake.RespClosurePlaced (
  blkLib_eq_518 blkPC_518 blkPl_518 lsProg_518
)
open scoped CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  cond_ne_adds64_of_ne_neg2_std3 cond_ne_adds64_of_ne_neg3_std3 realign_40
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  SepWPp.intro_rodata_mismatchRemoteIk_placed' a90_mismatch_entails_memRegion48
  coro_250_6w_entails_cells6 coro_250_cells6_eq coro_398_add_15a
  invalidMessage_prekey_out_entails_3 invalidMessage_prekey_out_entails_3_placed
  memRegion_370_36_split memRegion_a90_48_split mismatchRemoteIkStrPlaced
  mismatchRemoteIkStrPlaced_length prevSessionsEmptyAt stack_root_to_cells48
  stack_root_to_dropSS stack_root_to_strToOwned vecU8_unpack_3e0_64 w64_3_entails_memRegion24
)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents rustCliAllocBudgetSpec
  rustCliDeallocBudgetSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2PlacedBudget (
  bind_sepWP_lscro_steps_m2_placed call_lscro_nopanic_m2_placed
  closure_err_drop_record_tail_exists_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget (
  StrToOwnedEnv memRegion24_cells3 stackAt_strToOwnedLocal2 strToOwnedEvents
  strToOwnedLocal2Spec strToOwnedLocal2Stack vecU8_of_exact_alloc
)

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  invalidMessage_prekey_out_entails_3_placed
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

local macro "wp_steps_sync_518 " h:term:max mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException $h))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by wp_norm_lhs))
    (hnext := ?_)
))

/-! ## Envelope combinator and budget pre/post predicates -/

/-- Sequential composition of two allocator event-list envelopes. -/
def SeqEnv (E₁ E₂ : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  ∃ e₁ e₂, E₁ e₁ ∧ E₂ e₂ ∧ evs = e₁ ++ e₂

/-- Tight allocator event envelope for `stageP2_matched_mismatch_tail`:
exact `<str as ToOwned>::to_owned` allocation on `mismatchRemoteIkStrPlaced` (`70` bytes, align `1`)
followed by `FreeOnlyEvs` teardown of `SessionStructure` and `previous_sessions`. -/
def StageP2MismatchTailEnv : List AllocEvent → Prop :=
  SeqEnv (StrToOwnedEnv mismatchRemoteIkStrPlaced) FreeOnlyEvs

theorem stageP2MismatchTailEnv_of_freeOnly {evsFree : List AllocEvent}
    (hfree : FreeOnlyEvs evsFree) :
    StageP2MismatchTailEnv (strToOwnedEvents mismatchRemoteIkStrPlaced ++ evsFree) :=
  ⟨strToOwnedEvents mismatchRemoteIkStrPlaced, evsFree, rfl, hfree, rfl⟩

theorem fitsEvents_of_fitsEnv_stageP2MismatchTail {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} (h : FitsEnv M lim st StageP2MismatchTailEnv) :
    FitsEvents M lim st (strToOwnedEvents mismatchRemoteIkStrPlaced) := by
  have hnil := h (strToOwnedEvents mismatchRemoteIkStrPlaced)
    ⟨strToOwnedEvents mismatchRemoteIkStrPlaced, [], rfl, FreeOnlyEvs.nil,
      (List.append_nil _).symm⟩
  exact hnil

def stageP2MismatchTailPrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 s : State) (sp coroPtr outPtr u_a8 u_d0 : BitVec 64)
    (b_4f2 b_390 b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8))) : SepProp :=
  prevSessionsEmptyAt A.repAlloc coroPtr g ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
  cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x390#64) ↦₈ b_390) ∗
  ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
  memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x3e0#64) 24 ∗
  memRegion (sp + 0xa90#64) 48 ∗
  memRegion outPtr 48 ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  A.pool lim st s ∗
  stackAt sp rootStack

def stageP2MismatchTailPostAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st' : M.σ)
    (s0 sf : State) (sp coroPtr outPtr : BitVec 64) : SepProp :=
  memRegion (coroPtr + 0xe0#64) 368 ∗
  cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
  ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ 3#64) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ 70#64) ∗
  memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x3e0#64) 24 ∗
  memRegion (sp + 0xa90#64) 48 ∗
  apiDecResultAt A.repAlloc outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  A.pool lim st' sf ∗
  stackAt sp rootStack

def stageP2MismatchTailPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 sf : State) (sp coroPtr outPtr : BitVec 64) : SepProp :=
  memRegion (coroPtr + 0xe0#64) 368 ∗
  cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
  ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ 3#64) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ 70#64) ∗
  memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x3e0#64) 24 ∗
  memRegion (sp + 0xa90#64) 48 ∗
  apiDecResultAt A.repAlloc outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  (∃∗ evs : List AllocEvent, ⌜StageP2MismatchTailEnv evs⌝ ∗
    A.pool lim (M.stepEvents evs st) sf) ∗
  stackAt sp rootStack

/-! ## Block `509` (`drop_process_prekey_impl_state1`) and Block `530` (`str::to_owned [local#2]`) -/

private theorem sepWP_withVm_init {P : Program} {b : BitVec 64} {Hk : LibsignalHooks}
    {ret : BitVec 64} {s0 : State} {Pre R : SepProp} {Post : State → SepProp}
    {Q : State → Prop}
    (h : SepWP (P.rebase b Hk) ret s0 Pre
      (fun sf P_f => VmPreserved s0 sf ∧
        (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Post sf ∗ R) ∧ Q sf)) :
    SepWP (P.rebase b Hk) ret s0 Pre
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜VmPreserved s0 sf⌝ ∗ Post sf) ∗ R) ∧ Q sf) := by
  apply SepWP.of_reaches_pc
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hvm, hpost, hq⟩ | hoom⟩ :=
    SepWP.to_reaches_pc h hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, fun hmR => ?_, hq⟩⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm, hpost hmR⟩
  · exact ⟨sf, hsteps, Or.inr hoom⟩

/-- Block `509` (`core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>`)
state `1` under `[LibsignalPlacement]`, strengthened with `VmPreserved`. -/
theorem drop_process_prekey_impl_state1_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks) :
    subroutine_ok (lsProg_509 H) (blkPl_509).base
      (withVmPreserved dropProcessPrekeyImplState1Spec) := by
  unfold dropProcessPrekeyImplState1Spec
  cells_unfold
  dsimp only [lsProg_509, withVmPreserved]
  wp_init ptr s0
  apply sepWP_withVm_init
  wp_steps_vm

theorem drop_process_prekey_impl_state1_placed_ok_at [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 509)
      (withLsCodeLoaded lsmpl (withVmPreserved dropProcessPrekeyImplState1Spec)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (entry := lsmpl.base 509)
    (subroutine_ok_withLsCodeLoaded_of_plain (drop_process_prekey_impl_state1_placed_ok H)) hi

private def shimVmSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝

private theorem shimVm_of_withVmPreserved {P : Program} {a : BitVec 64}
    (h : subroutine_ok P a (withVmPreserved sessionShimSpec)) :
    subroutine_ok P a shimVmSpec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withVmPreserved, sessionShimSpec, shimVmSpec] at hq ⊢
  simpa only [← sepConj_assoc, pure_sepConj_pure] using hq

private def memcpyRegionROVmSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length ∧
     bs.length ≤ 2 ^ 64⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ᵣ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
    (dst ↦ₛ bs) ∗
    (src ↦ᵣ bs)

private theorem memcpyRegionROVm_of_withVmPreserved {P : Program} {a : BitVec 64}
    (h : subroutine_ok P a (withVmPreserved sessionMemcpyRegionROSpec)) :
    subroutine_ok P a memcpyRegionROVmSpec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withVmPreserved, sessionMemcpyRegionROSpec, memcpyRegionROVmSpec] at hq ⊢
  simpa only [← sepConj_assoc, pure_sepConj_pure] using hq

private theorem beq_zero_false_of_ne {w : BitVec 64} (h : w ≠ 0#64) :
    (w == 0#64) = false :=
  beq_eq_false_iff_ne.mpr h

/-- Block `530` (`<str as alloc::borrow::ToOwned>::to_owned [local#2]`) under `[LibsignalPlacement]`
against budget-threaded `strToOwnedLocal2Spec A lim` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
theorem str_to_owned_local2_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok (lsProg_530 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withVmPreserved sessionShimSpec))
    (halloc : subroutine_ok (lsProg_530 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_530 H)
      (lsρ "memcpy")
      (withVmPreserved sessionMemcpyRegionROSpec)) :
    subroutine_ok (lsProg_530 H) (blkPl_530).base
      (strToOwnedLocal2Spec A lim) := by
  have hshim' := shimVm_of_withVmPreserved hshim
  have halloc' := subroutine_ok_allocNoOom_of_budget halloc
  have hmemcpy' := memcpyRegionROVm_of_withVmPreserved hmemcpy
  dsimp only [strToOwnedLocal2Spec,
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget.strToOwnedLocal2SpecWithStack]
  rw [← show strToOwnedLocal2Stack =
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.strToOwnedLocal2StackWith allocHookStack from rfl]
  simp only [stackAt_strToOwnedLocal2, memRegion24_cells3,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨outPtr, srcPtr, bs⟩, st⟩
  dsimp only at *
  have hpos : 0 < bs.length := ‹0 < bs.length›
  have hlt : bs.length < 2 ^ 63 := ‹bs.length < 2 ^ 63›
  have hfits : FitsEvents M lim st (rustAllocEvents bs.length 1) := ‹_›
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk bs.length 1 := ⟨⟨hpos, hpow2, by omega⟩, by decide⟩
  have hlen_le64 : bs.length ≤ 2 ^ 64 := by omega
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  have htr_shim : sf.trace = s0.trace :=
    (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm])
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  simp only [State.setMem_setMem]
  wp_call halloc' (bs.length, 1, st)
  have hacp : AllocCallPreserved sf sf_1 := by assumption
  have hp : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_zero_false_of_ne hp
  have htr_alloc : sf_1.trace = s0.trace :=
    hacp.2.1.trans (by simp only [wp_norm, arm64_norm, htr_shim])
  have hsp0 : sf.sp = s0.sp - 48#64 := ‹sf.sp = _›
  rw [hsp0]
  wp_steps_sync_pool (lsρ "memcpy")
  simp only [State.setMem_setMem]
  wp_call hmemcpy' (sf_1.readReg64 (Reg.gpr 0#5), srcPtr, bs)
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  have htr_mc : sf_2.trace = s0.trace :=
    (‹sf_2.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr_alloc])
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply SepWP.replace_pre (by sep_focus)
    (vecU8_of_exact_alloc A outPtr (sf_1.readReg64 (Reg.gpr 0#5)) bs hpos hlt hp)
  wp_done

theorem str_to_owned_local2_placed_ok_at [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hshim : subroutine_ok (lsProg_530 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withVmPreserved sessionShimSpec))
    (halloc : subroutine_ok (lsProg_530 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_530 H)
      (lsρ "memcpy")
      (withVmPreserved sessionMemcpyRegionROSpec))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A lim)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (entry := lsmpl.base 530)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (str_to_owned_local2_placed_ok hshim halloc hmemcpy)) hi

/-! ## Pool-threaded Block-`518` mismatch funnel segments -/

@[local simp, local wp_norm, local arm64_norm]
private theorem bfi_cap_lo32_lsr8_placed (cap : BitVec 64) :
    ((cap.extractLsb' 0 32).zeroExtend 64 &&& 255#64 |||
      (cap >>> 8 &&& 72057594037927935#64) <<< 8) = cap := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem bfi_setWidth32_lsr8_placed (cap : BitVec 64) :
    ((BitVec.setWidth 32 cap).zeroExtend 64 &&& 255#64 |||
      (cap >>> 8 &&& 72057594037927935#64) <<< 8) = cap := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_hi_lo_append_placed (w : BitVec 64) :
    BitVec.setWidth 32 (w >>> 32) ++ BitVec.setWidth 32 w = w := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem bfi_3_zero_placed :
    ((3#64 : BitVec 64) &&& 255#64 |||
      ((0#64 : BitVec 64) &&& 72057594037927935#64) <<< 8) = 3#64 := by
  decide

private theorem sepWP_frame_pool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {prog : Program} {target_pc : BitVec 64} {s : State}
    {Pre Post : SepProp} {Q : State → Prop}
    (hwp : SepWP prog target_pc s Pre
      (fun s1 P_f => (P_f ⊢ Post) ∧ VmPreserved s s1 ∧ Q s1)) :
    SepWP prog target_pc s (Pre ∗ A.pool lim st s)
      (fun s1 P_f => (P_f ⊢ Post ∗ A.pool lim st s1) ∧ Q s1) := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨s1, hsteps, hout⟩ := SepWP.to_reaches_pc hwp hm hL
  rcases hout with ⟨hpc1, hrun1, P_f, hPf, hent, hvm, hQ⟩ | ⟨_, hoom⟩
  · refine ⟨s1, hsteps, Or.inl ⟨hpc1, hrun1, P_f ∗ A.pool lim st s, ?_, ?_, hQ⟩⟩
    · rwa [sepConj_assoc]
    · rw [A.pool_of_vmPreserved hvm]
      exact sepConj_mono_left hent
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem p2_seg_12fc_vm_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + bv% (0x12fc))
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        VmPreserved s s1 ∧
        (s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
         s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
         s1.readReg64 .x1 =
           lsρ "libsignal_cli_handshake:.rodata..Lanon.86" ∧
         s1.readReg64 .x2 = 70#64 ∧
         s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
         s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
         s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
         s1.readReg64 .x30 = (blkPl_518).base + bv% (0x1310))) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, by simp_all [wp_norm, arm64_norm], rfl, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Pool-threaded `(blkPl_518).base + 0x12fc → lsmpl.base 530` under `[LibsignalPlacement]`. -/
theorem p2_seg_12fc_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ)
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + bv% (0x12fc))
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530) s
      (A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 =
          lsρ "libsignal_cli_handshake:.rodata..Lanon.86" ∧
        s1.readReg64 .x2 = 70#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + bv% (0x1310)) := by
  simpa only [emp_sepConj] using
    sepWP_frame_pool A lim st (p2_seg_12fc_vm_placed_wp ext s coroPtr hpc hrun hx19)

/-- Pool-threaded `(blkPl_518).base + 0x1310 → lsmpl.base 509` under `[LibsignalPlacement]`. -/
theorem p2_seg_1310_to_drop_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ)
    (s : State) (coroPtr outPtr cap ptr len u_a8 u_c8 u_d0 : BitVec 64)
    (b_4f2 : BitVec 8)
    (hpc : s.pc = (blkPl_518).base + bv% (0x1310))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 509) s
      (((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ len) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((s.sp + 0xa8#64) ↦₆₄ 3#64) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ len) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ len) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0x8000000000000018#64 ∧
        s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x22 = ptr ∧
        s1.readReg64 .x23 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
        s1.readReg64 .x24 = cap ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + bv% (0x1698)) := by
  have hcond : ConditionHolds CondCode.NE (addsPState64 0x8000000000000018#64 3#64) = true :=
    cond_ne_adds64_of_ne_neg3_std3 (by decide)
  have hsplit_cap :
      ((s.sp + 0x3e0#64) ↦₆₄ cap) =
        ((s.sp + 0x3e0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
        ((s.sp + 0x3e4#64) ↦₃₂ cap.extractLsb' 32 32) := by
    rw [pointsTo64_split32 (s.sp + 0x3e0#64) cap]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  apply SepWP.fold (Entails.of_eq hsplit_cap) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps_sync_518 (Rust.withPanics ext) (lsmpl.base 509)
  simp only [State.setMem_setMem]
  apply SepWP.fold (Entails.of_eq hsplit_cap.symm) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]; clear * -; bv_bits,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]; clear * -; bv_bits,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

private theorem coro_268_split32_m2e_placed (coroPtr w : BitVec 64) :
    (coroPtr + 0x268#64) ↦₆₄ w =
    ((coroPtr + 0x268#64) ↦₃₂ w.extractLsb' 0 32) ∗
    ((coroPtr + 0x26c#64) ↦₃₂ w.extractLsb' 32 32) := by
  rw [pointsTo64_split32, BitVec.add_assoc]; rfl

private theorem coro_268_pair32_m2e_placed (coroPtr : BitVec 64) (lo hi : BitVec 32) :
    ((coroPtr + 0x268#64) ↦₃₂ lo) ∗ ((coroPtr + 0x26c#64) ↦₃₂ hi) =
    (coroPtr + 0x268#64) ↦₆₄ (hi ++ lo) := by
  have hlo : (hi ++ lo).extractLsb' 0 32 = lo := by bv_bits
  have hhi : (hi ++ lo).extractLsb' 32 32 = hi := by bv_bits
  rw [coro_268_split32_m2e_placed coroPtr (hi ++ lo), hlo, hhi]

set_option maxHeartbeats 1200000 in
/-- Pool-threaded `(blkPl_518).base + 0x1698 → +0x3588` under `[LibsignalPlacement]`. -/
theorem p2_seg_1698_mismatch_to_3588_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ)
    (s : State) (coroPtr outPtr cap ptr len
    u_250 u_258 u_260 u_268 u_270 u_278
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8
    u_370 u_378 u_380 u_388 : BitVec 64)
    (u_390 : BitVec 32) (b_390 : BitVec 8)
    (hpc : s.pc = (blkPl_518).base + bv% (0x1698))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0x8000000000000018#64)
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx22 : s.readReg64 .x22 = ptr)
    (hx23 : s.readReg64 .x23 = (cap.extractLsb' 0 32).zeroExtend 64)
    (hx24 : s.readReg64 .x24 = cap)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + bv% (0x3588)) s
      (((s.sp + 0xa8#64) ↦₆₄ 3#64) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ len) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗ ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗ ((coroPtr + 0x268#64) ↦₆₄ u_268) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗ ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗ ((s.sp + 0xa98#64) ↦₆₄ u_a98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ u_aa0) ∗ ((s.sp + 0xaa8#64) ↦₆₄ u_aa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ u_ab0) ∗ ((s.sp + 0xab8#64) ↦₆₄ u_ab8) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗ ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ u_380) ∗ ((s.sp + 0x388#64) ↦₆₄ u_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ u_390) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa8#64) ↦₆₄ 3#64) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ len) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ((coroPtr + 0x250#64) ↦₆₄ 0x8000000000000018#64) ∗
          ((coroPtr + 0x258#64) ↦₆₄ cap) ∗ ((coroPtr + 0x260#64) ↦₆₄ ptr) ∗
          ((coroPtr + 0x268#64) ↦₆₄ len) ∗ ((coroPtr + 0x270#64) ↦₆₄ 3#64) ∗
          ((coroPtr + 0x278#64) ↦₆₄ s.readReg64 .x27) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((s.sp + 0xa90#64) ↦₆₄ 0x8000000000000018#64) ∗
          ((s.sp + 0xa98#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((s.sp + 0xa9c#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
          ((s.sp + 0xaa4#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
          ((s.sp + 0xaac#64) ↦₆₄ ((3#64 : BitVec 64).extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
          ((s.sp + 0xab4#64) ↦₆₄ ((s.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)) ∗
          ((s.sp + 0xabc#64) ↦₃₂ (s.readReg64 .x27).extractLsb' 32 32) ∗
          ((s.sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
          ((s.sp + 0x378#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
          ((s.sp + 0x380#64) ↦₆₄ ((3#64 : BitVec 64).extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
          ((s.sp + 0x388#64) ↦₆₄ ((s.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)) ∗
          ((s.sp + 0x390#64) ↦₃₂ (s.readReg64 .x27).extractLsb' 32 32) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30) := by
  have hcond : ConditionHolds CondCode.NE (addsPState64 0x8000000000000018#64 2#64) = true :=
    cond_ne_adds64_of_ne_neg2_std3 (by decide)
  have hrealign_a98 := realign_40 (s.sp + 0xa98#64) cap ptr len 3#64 (s.readReg64 (Reg.gpr 27#5))
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrealign_a98
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0x8000000000000018#64 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 0#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = ptr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = (cap.extractLsb' 0 32).zeroExtend 64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = cap := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  dsimp only [lsLogFilterAddr]
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException (Rust.withPanics ext)))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := (blkPl_518).base + bv% (0x3588))
  intro _m_strip
  apply SepWP.fold (Entails.of_eq (coro_268_split32_m2e_placed coroPtr u_268)) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq (coro_268_pair32_m2e_placed coroPtr _ _)) (by sep_focus)
  wp_simp_pre [sepConj_assoc, setWidth32_hi_lo_append_placed]
  wp_steps
  apply SepWP.fold (Entails.of_eq hrealign_a98) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by wp_norm_lhs))
    (hnext := ?_)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by dsimp only [Reg.x27]; sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-! ## Budget-threaded Stage P2 remote-identity mismatch tail (`+0x12fc → s0.readReg64 .x30`) -/

private theorem sepWPp_drop_left {prog : Program} {ret : BitVec 64} {s : State}
    {P_all D P_keep : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P_all = D ∗ P_keep)
    (h : SepWPp prog ret s P_keep Q Qp) :
    SepWPp prog ret s P_all Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

private theorem sepWPp_ret_frame_nopanic {prog : Program} {ret : BitVec 64} {s : State}
    {P P_stage F : SepProp} {Q_stage Q : State → SepProp → Prop}
    (hstage : SepWPp prog ret s P_stage Q_stage (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hret : ∀ sf P_f, sf.pc = ret → sf.status = .Running → Q_stage sf P_f → Q sf (P_f ∗ F)) :
    SepWPp prog ret s P Q (fun _ _ => False) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hqf⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f ∗ F, hmf, hret sf P_f hpcf hrunf hqf⟩⟩
  · exact False.elim hpan
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem sepWPp_lift_qp {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (fun _ _ => False)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, hok | ⟨_, _, _, hpan⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact False.elim hpan
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `[LibsignalPlacement]` Stage P2 remote-identity mismatch tail
(`(blkPl_518).base + 0x12fc → s0.readReg64 .x30`) under
`FitsEvents M lim st (strToOwnedEvents mismatchRemoteIkStrPlaced)`. -/
theorem stageP2_matched_mismatch_tail_exists_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A lim)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st : M.σ) (s0 s : State)
    (sp coroPtr outPtr u_a8 u_d0 : BitVec 64)
    (b_4f2 b_390 b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hfits : FitsEvents M lim st (strToOwnedEvents mismatchRemoteIkStrPlaced))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + bv% (0x12fc))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stageP2MismatchTailPrePlaced A lim st s0 s sp coroPtr outPtr u_a8 u_d0
        b_4f2 b_390 b_2c0 g recG recSt)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, StageP2MismatchTailEnv evs ∧
          (P_f ⊢
            stageP2MismatchTailPostAtPlaced A lim (M.stepEvents evs st)
              s0 sf sp coroPtr outPtr)) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  apply sepWPp_lift_qp
  unfold stageP2MismatchTailPrePlaced
  have hroot_le : rootStack ≤ 2 ^ 64 := Nat.le_trans hsp_root (Nat.le_of_lt sp.isLt)
  let roAddr : BitVec 64 := lsρ "libsignal_cli_handshake:.rodata..Lanon.86"
  let st1 : M.σ := M.stepEvents (strToOwnedEvents mismatchRemoteIkStrPlaced) st
  refine SepWPp.intro_rodata_mismatchRemoteIk_placed' hcro ?_
  have h12fc := p2_seg_12fc_placed_wp (A := A) (lim := lim) ext st s coroPtr hpc hrun hx19
  refine bind_sepWP_lscro_steps_m2_placed hcro h12fc (by sep_focus)
    fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx0_1, hx1_1, hx2_1, hx19_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_strToOwned sp hroot_le)) (by sep_focus) ?_
  refine call_lscro_nopanic_m2_placed
    (spec := strToOwnedLocal2Spec A lim)
    (x := ((sp + 0x3e0#64, roAddr, mismatchRemoteIkStrPlaced), st))
    (φ := s1.readReg64 .x0 = sp + 0x3e0#64 ∧
      s1.readReg64 .x1 = roAddr ∧
      s1.readReg64 .x2 = BitVec.ofNat 64 mismatchRemoteIkStrPlaced.length ∧
      0 < mismatchRemoteIkStrPlaced.length ∧
      mismatchRemoteIkStrPlaced.length < 2 ^ 63 ∧
      FitsEvents M lim st (strToOwnedEvents mismatchRemoteIkStrPlaced))
    (T := memRegion (sp + 0x3e0#64) 24 ∗ (roAddr ↦ᵣ mismatchRemoteIkStrPlaced) ∗
      A.pool lim st s1 ∗ stackAt sp strToOwnedLocal2Stack)
    hcro1 (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hto)
    hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [strToOwnedLocal2Spec,
        LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget.strToOwnedLocal2SpecWithStack]
      rw [hsp1])
    ⟨by rwa [← hsp_eq], hx1_1, by rw [mismatchRemoteIkStrPlaced_length]; exact hx2_1,
      by rw [mismatchRemoteIkStrPlaced_length]; decide,
      by rw [mismatchRemoteIkStrPlaced_length]; decide,
      hfits⟩
    (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [strToOwnedLocal2Spec,
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget.strToOwnedLocal2SpecWithStack]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  change SepWPp _ _ s2
    ((vecU8 A.repAlloc (sp + 0x3e0#64) mismatchRemoteIkStrPlaced ∗
      (roAddr ↦ᵣ mismatchRemoteIkStrPlaced) ∗
      A.pool lim st1 s2 ∗
      stackAt sp strToOwnedLocal2Stack) ∗ _) _ _
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_strToOwned sp hroot_le).symm) (by sep_focus) ?_
  refine sepWPp_drop_left (D := roAddr ↦ᵣ mismatchRemoteIkStrPlaced) (by sep_focus) ?_
  refine SepWPp.weaken_frame (vecU8_unpack_3e0_64 A.repAlloc sp mismatchRemoteIkStrPlaced) (by sep_focus) ?_
  rw [mismatchRemoteIkStrPlaced_length]
  sep_norm
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s := hvregs_cs2.trans hvregs1
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx25_2 : s2.readReg64 .x25 = sp + 0x210#64 := hx25_cs2.trans (hx25_1.trans hx25)
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = sp + 0xa90#64 := hx28_cs2.trans (hx28_1.trans hx28)
  have h1310 := p2_seg_1310_to_drop_placed_wp (A := A) (lim := lim) ext st1 s2 coroPtr outPtr
    cap ptr 70#64 u_a8 outPtr u_d0 b_4f2 hpc2 hrun2 hsp2_align hx19_2 hx26_2
  rw [hsp2] at h1310
  refine bind_sepWP_lscro_steps_m2_placed hcro2 h1310 (by sep_focus)
    fun s3 _ hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hvregs3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3,
    hx23_3, hx24_3, hx25_3, hx26_3, _, hx28_3, _, hx30_3⟩
  have hsp3 : s3.sp = sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by rw [State.spAligned, hsp3, ← hsp2]; exact hsp2_align
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_cells48 sp hroot_le)) (by sep_focus) ?_
  refine call_lscro_nopanic_m2_placed
    (spec := withVmPreserved dropProcessPrekeyImplState1Spec)
    (x := coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (sp - 48#64) 6)
    hcro3
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (drop_process_prekey_impl_state1_placed_ok_at (callerProg := lsProg_518 (Rust.withPanics ext))))
    hpc3 hrun3 hsp3_al hx30_3
    (by dsimp only [withVmPreserved, dropProcessPrekeyImplState1Spec]; rw [hsp3, coro_398_add_15a])
    hx0_3 (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  dsimp only [withVmPreserved, dropProcessPrekeyImplState1Spec]
  rw [hsp3, coro_398_add_15a]
  sep_norm
  refine SepWPp.pure_elim fun hvm3_4 => SepWPp.pure_elim fun htr4_3 => ?_
  rw [← A.pool_transport lim st1 s3 s4 hvm3_4]
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_cells48 sp hroot_le).symm) (by sep_focus) ?_
  rcases hcs4 with ⟨hx19_cs4, hx20_cs4, hx21_cs4, hx22_cs4, hx23_cs4, hx24_cs4,
    hx25_cs4, hx26_cs4, _, hx28_cs4, _, hvregs_cs4⟩
  have hvregs4_s : calleeSavedVRegs s4 = calleeSavedVRegs s :=
    hvregs_cs4.trans (hvregs3.trans hvregs2_s)
  have hsp4 : s4.sp = sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4, ← hsp_eq]; exact hsp_align
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx20_4 : s4.readReg64 .x20 = 0x8000000000000018#64 := hx20_cs4.trans hx20_3
  have hx21_4 : s4.readReg64 .x21 = 0#64 := hx21_cs4.trans hx21_3
  have hx22_4 : s4.readReg64 .x22 = ptr := hx22_cs4.trans hx22_3
  have hx23_4 : s4.readReg64 .x23 = (cap.extractLsb' 0 32).zeroExtend 64 := hx23_cs4.trans hx23_3
  have hx24_4 : s4.readReg64 .x24 = cap := hx24_cs4.trans hx24_3
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by
    rw [hsp4]; exact hx25_cs4.trans (hx25_3.trans hx25_2)
  have hx26_4 : s4.readReg64 .x26 = outPtr := hx26_cs4.trans hx26_3
  have hx28_4 : s4.readReg64 .x28 = s4.sp + 0xa90#64 := by
    rw [hsp4]; exact hx28_cs4.trans (hx28_3.trans hx28_2)
  refine SepWPp.weaken_frame (memRegion_370_36_split sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame (memRegion_a90_48_split sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (coro_250_cells6_eq coroPtr)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 =>
    SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 =>
    SepWPp.exists_elim fun u370 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u390 => ?_
  have h1698 := p2_seg_1698_mismatch_to_3588_placed_wp (A := A) (lim := lim) ext st1 s4
    coroPtr outPtr cap ptr 70#64
    u250 u258 u260 u268 u270 u278 ua90 ua98 uaa0 uaa8 uab0 uab8
    u370 u378 u380 u388 u390 b_390 hpc4 hrun4 hsp4_align
    hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx28_4
  rw [hsp4] at h1698
  refine bind_sepWP_lscro_steps_m2_placed hcro4 h1698 (by sep_focus)
    fun s5 _ hpc5 hrun5 hcro5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hvregs5, hx19_5, hx22_5, hx25_5, hx26_5, hx28_5, _, _⟩
  have hvregs5_s : calleeSavedVRegs s5 = calleeSavedVRegs s := hvregs5.trans hvregs4_s
  have hsp5 : s5.sp = sp := hsp5_4
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_dropSS sp hroot_le)) (by sep_focus) ?_
  have hdrop_rec := closure_err_drop_record_tail_exists_placed_ok (A := A) (lim := lim) (ext := ext)
    (Qp := fun _ _ => False)
    hdealloc hdrop_ss st1 s0 s5 sp coroPtr outPtr 0x8000000000000018#64
    (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
    ((70#64 : BitVec 64).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
    ((3#64 : BitVec 64).extractLsb' 0 32 ++ (70#64 : BitVec 64).extractLsb' 32 32)
    ((s4.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)
    (cap.extractLsb' 0 32) ((s4.readReg64 .x27).extractLsb' 32 32) b_2c0
    g recG recSt hcro5 hsp5 (Nat.le_trans (by decide) hsp_root)
    hpc5 hrun5 hsp5_align hx19_5 hx22_5 hx25_5 hx26_5 hx28_5
  refine sepWPp_ret_frame_nopanic hdrop_rec (by sep_focus)
    fun sf P_rec _ _ ⟨⟨evsFree, hfree, hent_rec⟩, hspf, htrf_5, hcsf, hvregsf_5, hcrof⟩ => ?_
  refine ⟨⟨strToOwnedEvents mismatchRemoteIkStrPlaced ++ evsFree,
      stageP2MismatchTailEnv_of_freeOnly hfree, ?_⟩,
    hspf,
    htrf_5.trans (htr5_4.trans (htr4_3.trans (htr3_2.trans (htr2_1.trans htr1_s)))),
    hcsf, hvregsf_5.trans hvregs5_s, hcrof⟩
  unfold stageP2MismatchTailPostAtPlaced
  rw [M.stepEvents_append]
  refine Entails.trans (sepConj_mono_left hent_rec) ?_
  refine Entails.trans (entails_replace_sub (Entails.of_eq (stack_root_to_dropSS sp hroot_le).symm)
    (by sep_focus) rfl) ?_
  have hout := invalidMessage_prekey_out_entails_3 A.repAlloc outPtr cap ptr (s4.readReg64 .x27)
    mismatchRemoteIkStrPlaced
  rw [mismatchRemoteIkStrPlaced_length] at hout
  refine Entails.trans (entails_replace_sub hout (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub
    (coro_250_6w_entails_cells6 coroPtr 0x8000000000000018#64 cap ptr 70#64 3#64 (s4.readReg64 .x27))
    (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub
    (w64_3_entails_memRegion24 (sp + 0x3e0#64) cap ptr 70#64)
    (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) rfl) ?_
  exact entails_replace_sub
    (a90_mismatch_entails_memRegion48 sp cap ptr 70#64 (s4.readReg64 .x27))
    (by sep_focus) (eq_of_sep_emp (by sep_focus))

/-- Spatial `∃∗ evs, ⌜StageP2MismatchTailEnv evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf`
presentation of `stageP2_matched_mismatch_tail_exists_placed` under `FitsEnv M lim st StageP2MismatchTailEnv`. -/
theorem stageP2_matched_mismatch_tail_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A lim)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st : M.σ) (s0 s : State)
    (sp coroPtr outPtr u_a8 u_d0 : BitVec 64)
    (b_4f2 b_390 b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hfits : FitsEnv M lim st StageP2MismatchTailEnv)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + bv% (0x12fc))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stageP2MismatchTailPrePlaced A lim st s0 s sp coroPtr outPtr u_a8 u_d0
        b_4f2 b_390 b_2c0 g recG recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP2MismatchTailPostPlaced A lim st s0 sf sp coroPtr outPtr) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ :=
    stageP2_matched_mismatch_tail_exists_placed (Qp := Qp) hto hdealloc hdrop_ss st s0 s
      sp coroPtr outPtr u_a8 u_d0 b_4f2 b_390 b_2c0 g recG recSt
      (fitsEvents_of_fitsEnv_stageP2MismatchTail hfits)
      hcro hsp_eq hsp_root hpc hrun hsp_align hx19 hx25 hx26 hx28 R hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, ⟨⟨evs, henv, hent⟩, hrest⟩⟩ | hpan_oom
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hrest⟩⟩⟩
    unfold stageP2MismatchTailPostAtPlaced at hent
    unfold stageP2MismatchTailPostPlaced
    refine Entails.trans hent ?_
    have hpack : A.pool lim (M.stepEvents evs st) sf ⊢
        ∃∗ evs' : List AllocEvent, ⌜StageP2MismatchTailEnv evs'⌝ ∗
          A.pool lim (M.stepEvents evs' st) sf :=
      Entails.sepExists_right evs (Entails.pure_right henv (Entails.refl _))
    exact entails_replace_sub hpack (by sep_focus) (by sep_ac_rfl)
  · exact ⟨sf, hsteps, Or.inr hpan_oom⟩

end

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlacedBudget
