/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::init_inner`: VM-Preserving Fixed-Offset Step Lemmas (Slice-Clone & `BL` Steppers)

Proves `VmPreserved`-strengthened `auth_key` slice-clone basic blocks and single-instruction
`bl` steppers for `spqr::init_inner` (`0x532dc`), re-exporting `StepsBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc vecU8)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1 (Bytes Direction)
open CryptoVerification.SpqrV1.States.IntoPb (bv_add_add_lit' bv_sub_sub_lit')
open CryptoVerification.SpqrV1.Top.InitInner
  (initInnerName vecU8_nil_of_cells vecU8_nonempty_of_cells)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsBudgetAux
  (align_pre_tp rebase_fnAddr_eq sepWP_rebase_entails_vmPreserved
   sepWP_rebase_strengthen_vmPreserved withSvc_fetch_eq)

/-! ## 1. Re-Exports from `StepsBudgetAux` -/

export LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsBudgetAux
  (initInnerSavedCells_entails_memRegion sortedSetPtOf_withCapacity_zero
   emptySortedSetPtCells_entails initInner_seq_sepWP_inImage initInner_seq_wp)
export LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsBudgetAux
  (sepWPp_of_sepWP_keepInv initInner_seq_sepWP
   calleeSaved_chain_hi calleeSaved_x29 calleeSaved_x19)
export LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsBudgetAux
  (init_inner_v0 init_inner_epilogue init_inner_prologue_v1
   init_inner_a2b_post_auth init_inner_b2a_post_auth)

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::init_inner")
  (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::new")
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::into_pb")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

local elab "lift_fetches_withSvc" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut hyps : Array Lean.Meta.Hypothesis := #[]
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← Lean.instantiateMVars decl.type
        if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Arm64.Program.fetch 2 then
          let progE := (ty.getArg! 1).getArg! 0
          if !progE.isAppOfArity ``Arm64.Program.withSvc 2 then
            let prf ← Lean.Meta.mkAppM ``withSvc_fetch_eq #[Lean.mkConst ``Arm64.noSyscalls, decl.toExpr]
            let newTy ← Lean.Meta.inferType prf
            hyps := hyps.push { userName := `this, type := newTy, value := prf }
    if !hyps.isEmpty then
      let g ← Lean.Elab.Tactic.getMainGoal
      let (_, g') ← g.assertHypotheses hyps
      Lean.Elab.Tactic.replaceMainGoal [g']

local macro "init_inner_fetches_plain " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic|
    code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.SpqrV1.Top.InitInner.libsignalSessionBin
      $b $H CryptoVerification.SpqrV1.Top.InitInner.initInner_fnOff
      (ls_off% "spqr::init_inner") $k0 $len)

local macro "init_inner_fetches_vm " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| (
      init_inner_fetches_plain $b $H $k0 $len
      lift_fetches_withSvc))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'

/-! ## 2. Slice-Clone Basic Blocks (`authKey` -> `vecU8 A (s0.sp - 1032#64) authKey`) -/

/-- `.a2b` empty-slice path (`+36 -> +120 -> +344 -> +364`), preserving `VmPreserved s s2`. -/
theorem init_inner_a2b_empty_to_364 {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hw2 : s.readReg32 .x2 = Direction.a2b.toI32)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 364#64) s
      (cells (s0.sp - 1032#64) 3 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ vecU8 A (s0.sp - 1032#64) [] ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x0 = s0.sp - 104#64 ∧
        s2.readReg64 .x1 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hvec :
      (((s0.sp - 1032#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 1024#64) ↦₆₄ 1#64) ∗
       ((s0.sp - 1016#64) ↦₆₄ 0#64)) ∗ Rest ⊢
      vecU8 A (s0.sp - 1032#64) [] ∗ Rest := by
    refine sepConj_mono_left ?_
    simpa only [arm64_norm] using vecU8_nil_of_cells A (s0.sp - 1032#64)
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [tripleRatchetProgAtExt, initInnerName, Direction.toI32,
    State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 ⊢
  refine sepWP_rebase_strengthen_vmPreserved hvec ?_
  rw [hfn_eq] at hpc ⊢
  apply sepWP_rebase_vmPreserved
  init_inner_fetches_vm b trapHooks 36 4
  init_inner_fetches_vm b trapHooks 120 4
  init_inner_fetches_vm b trapHooks 344 20
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  wp_steps
  refine align_pre_tp (by sep_ac_rfl) ?_
  wp_done

/-- `.b2a` empty-slice path (`+36 -> +40 -> +172 -> +192`), preserving `VmPreserved s s2`. -/
theorem init_inner_b2a_empty_to_192 {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hw2 : s.readReg32 .x2 = Direction.b2a.toI32)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 192#64) s
      (cells (s0.sp - 1032#64) 3 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ vecU8 A (s0.sp - 1032#64) [] ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x0 = s0.sp - 104#64 ∧
        s2.readReg64 .x1 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hvec :
      (((s0.sp - 1032#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 1024#64) ↦₆₄ 1#64) ∗
       ((s0.sp - 1016#64) ↦₆₄ 0#64)) ∗ Rest ⊢
      vecU8 A (s0.sp - 1032#64) [] ∗ Rest := by
    refine sepConj_mono_left ?_
    simpa only [arm64_norm] using vecU8_nil_of_cells A (s0.sp - 1032#64)
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [tripleRatchetProgAtExt, initInnerName, Direction.toI32,
    State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 ⊢
  refine sepWP_rebase_strengthen_vmPreserved hvec ?_
  rw [hfn_eq] at hpc ⊢
  apply sepWP_rebase_vmPreserved
  init_inner_fetches_vm b trapHooks 36 8
  init_inner_fetches_vm b trapHooks 172 20
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  wp_steps
  refine align_pre_tp (by sep_ac_rfl) ?_
  wp_done

/-- `.a2b` non-empty slice step 1 (`+36 -> +120 -> +128`, 3 instructions), preserving `VmPreserved s s2`. -/
theorem init_inner_a2b_to_128
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hlen_ne : (len == 0#64) = false)
    (hw2 : s.readReg32 .x2 = Direction.a2b.toI32)
    (hx3 : s.readReg64 .x3 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 128#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x21 = akPtr ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_plain b (Rust.withPanics ext) 36 4
  init_inner_fetches_plain b (Rust.withPanics ext) 120 8
  dsimp only [tripleRatchetProgAtExt, initInnerName, Direction.toI32,
    State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `.a2b` non-empty slice step 2 (`+132 -> +140`, 2 instructions), preserving `VmPreserved s s2`. -/
theorem init_inner_a2b_132_to_140
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hx21 : s.readReg64 .x21 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 140#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x21 = akPtr ∧
        s2.readReg64 .x0 = len ∧
        s2.readReg64 .x1 = 1#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_plain b (Rust.withPanics ext) 132 8
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `.a2b` non-empty slice OOM branch (`+144 -> +436 -> +444`, 3 instructions),
    preserving `VmPreserved s s2`. -/
theorem init_inner_a2b_144_oom_to_444
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx20 : s.readReg64 .x20 = len)
    (hx0 : s.readReg64 .x0 = 0#64)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 444#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x0 = 1#64 ∧
        s2.readReg64 .x1 = len ∧
        s2.trace = s0.trace) := by
  init_inner_fetches_plain b (Rust.withPanics ext) 144 4
  init_inner_fetches_plain b (Rust.withPanics ext) 436 8
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `.a2b` non-empty slice step 3 (`+144 -> +160`, 4 instructions), preserving `VmPreserved s s2`. -/
theorem init_inner_a2b_144_ok_to_160
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len ptr : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hx21 : s.readReg64 .x21 = akPtr)
    (hx0 : s.readReg64 .x0 = ptr)
    (hptr_ne : (ptr == 0#64) = false)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 160#64) s
      (cells (s0.sp - 1032#64) 2 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ ((s0.sp - 1032#64) ↦₆₄ len) ∗ ((s0.sp - 1024#64) ↦₆₄ ptr) ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x0 = ptr ∧
        s2.readReg64 .x1 = akPtr ∧
        s2.readReg64 .x2 = len ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine sepWP_rebase_entails_vmPreserved ?_
  rw [hfn_eq] at hpc ⊢
  apply sepWP_rebase_vmPreserved
  init_inner_fetches_vm b trapHooks 144 16
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  wp_steps
  refine align_pre_tp (by sep_ac_rfl) ?_
  wp_done

/-- `.a2b` non-empty slice step 4 (`+164 -> +168 -> +356 -> +364`, 4 instructions),
    preserving `VmPreserved s s2`. -/
theorem init_inner_a2b_164_to_364 {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out ptr : BitVec 64) (authKey : Bytes) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpos : 0 < authKey.length)
    (hlt : authKey.length < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 164#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 364#64) s
      (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
       cells (s0.sp - 1016#64) 1 ∗
       A.live ptr authKey.length 1 ∗
       (ptr ↦ₛ authKey) ∗
       Rest)
      (fun s2 P2 =>
        (P2 ⊢ vecU8 A (s0.sp - 1032#64) authKey ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x0 = s0.sp - 104#64 ∧
        s2.readReg64 .x1 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hvec :
      (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
       ((s0.sp - 1016#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       A.live ptr authKey.length 1 ∗
       (ptr ↦ₛ authKey)) ∗ Rest ⊢
      vecU8 A (s0.sp - 1032#64) authKey ∗ Rest := by
    refine sepConj_mono_left ?_
    simpa only [arm64_norm] using vecU8_nonempty_of_cells A (s0.sp - 1032#64) ptr authKey hpos hlt hptr
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine sepWP_rebase_strengthen_vmPreserved hvec ?_
  rw [hfn_eq] at hpc ⊢
  apply sepWP_rebase_vmPreserved
  init_inner_fetches_vm b trapHooks 164 8
  init_inner_fetches_vm b trapHooks 356 8
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  wp_steps
  refine align_pre_tp (by sep_ac_rfl) ?_
  wp_done

/-- `.b2a` non-empty slice step 1 (`+36 -> +48`, 3 instructions), preserving `VmPreserved s s2`. -/
theorem init_inner_b2a_to_48
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hlen_ne : (len == 0#64) = false)
    (hw2 : s.readReg32 .x2 = Direction.b2a.toI32)
    (hx3 : s.readReg64 .x3 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 48#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x21 = akPtr ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_plain b (Rust.withPanics ext) 36 12
  dsimp only [tripleRatchetProgAtExt, initInnerName, Direction.toI32,
    State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `.b2a` non-empty slice step 2 (`+52 -> +60`, 2 instructions), preserving `VmPreserved s s2`. -/
theorem init_inner_b2a_52_to_60
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 52#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hx21 : s.readReg64 .x21 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 60#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x21 = akPtr ∧
        s2.readReg64 .x0 = len ∧
        s2.readReg64 .x1 = 1#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_plain b (Rust.withPanics ext) 52 8
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `.b2a` non-empty slice OOM branch (`+64 -> +436 -> +444`, 3 instructions),
    preserving `VmPreserved s s2`. -/
theorem init_inner_b2a_64_oom_to_444
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 64#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx20 : s.readReg64 .x20 = len)
    (hx0 : s.readReg64 .x0 = 0#64)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 444#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x0 = 1#64 ∧
        s2.readReg64 .x1 = len ∧
        s2.trace = s0.trace) := by
  init_inner_fetches_plain b (Rust.withPanics ext) 64 4
  init_inner_fetches_plain b (Rust.withPanics ext) 436 8
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `.b2a` non-empty slice step 3 (`+64 -> +80`, 4 instructions), preserving `VmPreserved s s2`. -/
theorem init_inner_b2a_64_ok_to_80
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len ptr : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 64#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hx21 : s.readReg64 .x21 = akPtr)
    (hx0 : s.readReg64 .x0 = ptr)
    (hptr_ne : (ptr == 0#64) = false)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 80#64) s
      (cells (s0.sp - 1032#64) 2 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ ((s0.sp - 1032#64) ↦₆₄ len) ∗ ((s0.sp - 1024#64) ↦₆₄ ptr) ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x0 = ptr ∧
        s2.readReg64 .x1 = akPtr ∧
        s2.readReg64 .x2 = len ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine sepWP_rebase_entails_vmPreserved ?_
  rw [hfn_eq] at hpc ⊢
  apply sepWP_rebase_vmPreserved
  init_inner_fetches_vm b trapHooks 64 16
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  wp_steps
  refine align_pre_tp (by sep_ac_rfl) ?_
  wp_done

/-- `.b2a` non-empty slice step 4 (`+84 -> +88 -> +184 -> +192`, 4 instructions),
    preserving `VmPreserved s s2`. -/
theorem init_inner_b2a_84_to_192 {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out ptr : BitVec 64) (authKey : Bytes) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpos : 0 < authKey.length)
    (hlt : authKey.length < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 192#64) s
      (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
       cells (s0.sp - 1016#64) 1 ∗
       A.live ptr authKey.length 1 ∗
       (ptr ↦ₛ authKey) ∗
       Rest)
      (fun s2 P2 =>
        (P2 ⊢ vecU8 A (s0.sp - 1032#64) authKey ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x0 = s0.sp - 104#64 ∧
        s2.readReg64 .x1 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hvec :
      (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
       ((s0.sp - 1016#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       A.live ptr authKey.length 1 ∗
       (ptr ↦ₛ authKey)) ∗ Rest ⊢
      vecU8 A (s0.sp - 1032#64) authKey ∗ Rest := by
    refine sepConj_mono_left ?_
    simpa only [arm64_norm] using vecU8_nonempty_of_cells A (s0.sp - 1032#64) ptr authKey hpos hlt hptr
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine sepWP_rebase_strengthen_vmPreserved hvec ?_
  rw [hfn_eq] at hpc ⊢
  apply sepWP_rebase_vmPreserved
  init_inner_fetches_vm b trapHooks 84 8
  init_inner_fetches_vm b trapHooks 184 8
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  wp_steps
  refine align_pre_tp (by sep_ac_rfl) ?_
  wp_done

/-! ## 3. Single-Instruction `BL` Steppers (`VmPreserved s s'`) -/

theorem init_inner_bl_364 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 364#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new")) s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 368#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  init_inner_fetches_plain b (Rust.withPanics ext) 364 4
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem init_inner_bl_192 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 192#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new")) s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 196#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  init_inner_fetches_plain b (Rust.withPanics ext) 192 4
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem init_inner_bl_412 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 412#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::v1::chunked::states::States>::into_pb")) s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 416#64 ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧ s'.readReg64 .x0 = s.readReg64 .x0 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  init_inner_fetches_plain b (Rust.withPanics ext) 412 4
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem init_inner_bl_128 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 128#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 132#64 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  init_inner_fetches_plain b (Rust.withPanics ext) 128 4
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem init_inner_bl_140 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 140#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "__rustc::__rust_alloc")) s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 144#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  init_inner_fetches_plain b (Rust.withPanics ext) 140 4
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem init_inner_bl_160 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 160#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "memcpy")) s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 164#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x2 = s.readReg64 .x2 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  init_inner_fetches_plain b (Rust.withPanics ext) 160 4
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem init_inner_bl_48 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 48#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 52#64 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  init_inner_fetches_plain b (Rust.withPanics ext) 48 4
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem init_inner_bl_60 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 60#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "__rustc::__rust_alloc")) s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 64#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  init_inner_fetches_plain b (Rust.withPanics ext) 60 4
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem init_inner_bl_80 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 80#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "memcpy")) s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 84#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x2 = s.readReg64 .x2 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  init_inner_fetches_plain b (Rust.withPanics ext) 80 4
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches; wp_steps; wp_done

end LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsBudget
