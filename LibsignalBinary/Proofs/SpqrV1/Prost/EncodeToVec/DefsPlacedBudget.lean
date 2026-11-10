/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# `PqRatchetState::encode_to_vec` (Block `426`): `StepInvVm` Combinators and Length Helpers

Joint `StepInvVm` (`StepInv ∧ VmPreserved`) invariant, `withStepInvVm` call combinators, and
polymorphic `VersionNegotiation.authKey` length-step helper (`+52..+88`) for Block `426`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification
  (LibsignalPlacement LibsignalCodeLoaded LibsignalRoLoaded withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (VersionNegotiationPB)
open CryptoVerification.SpqrV1.ProtoRepr (VersionNegotiationPBGhost bytesFieldEncodedLen)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (StepInv VRegsAt withStepInv versionNegotiationRest blkPC_426 blkPl_426
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero)
open LibsignalBinary.Heap (VmPreserved)

/-! ## 1. `StepInvVm` (`StepInv` + `VmPreserved`) & `SepWPp` Combinators -/

/-- Joint invariant across pure/non-allocating machine steps: `StepInv` (`FrozenLoaded`, `symtab`,
`calleeSavedVRegs`) together with `VmPreserved` (`VmFieldsPreserved`, `tpidrEl0`, `mem.perm`). -/
abbrev StepInvVm (s s' : State) : Prop :=
  StepInv s s' ∧ VmPreserved s s'

theorem StepInvVm.refl (s : State) : StepInvVm s s :=
  ⟨StepInv.refl s, VmPreserved.refl s⟩

theorem StepInvVm.trans {s0 s1 s2 : State} (h1 : StepInvVm s0 s1) (h2 : StepInvVm s1 s2) :
    StepInvVm s0 s2 :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem StepInvVm.libsignalCodeLoaded {s0 s : State} (hinv : StepInvVm s0 s) {pl : MultiPlacement}
    (hcl : LibsignalCodeLoaded pl s0.mem) : LibsignalCodeLoaded pl s.mem :=
  hinv.1.libsignalCodeLoaded hcl

theorem StepInvVm.libsignalRoLoaded {s0 s : State} (hinv : StepInvVm s0 s) {pl : MultiPlacement}
    (hro : LibsignalRoLoaded pl s0.mem) : LibsignalRoLoaded pl s.mem :=
  hinv.1.libsignalRoLoaded hro

/-- Wrap `spec : Spec α` with `⌜StepInvVm s0 s⌝` in the precondition. -/
def withStepInvVm {α : Type} (s0 : State) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜StepInvVm s0 s⌝ ∗ spec.pre x s }

theorem subroutine_ok_withStepInvVm {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withStepInvVm s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withStepInvVm, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s hpc hrun hpre.2 hsp fun _ hout => hout

theorem subroutine_ok_withStepInvVm_lscl {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α} {s0 : State}
    (hcl0 : LibsignalCodeLoaded pl s0.mem)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withStepInvVm s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withStepInvVm, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv, hpre⟩ := hpre
  have hpre' : s.mem ⊨ (withLsCodeLoaded pl spec).pre x s ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hinv.libsignalCodeLoaded hcl0, hpre⟩
  exact h.mono_outcome x R s hpc hrun hpre' hsp fun _ hout => hout

theorem subroutine_ok_withStepInv_lscl {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α} {s0 : State}
    (hcl0 : LibsignalCodeLoaded pl s0.mem)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withStepInv s0 spec) :=
  CryptoVerification.SpqrV1.Prost.EncodeToVec.subroutine_ok_withStepInv_lscl hcl0 h

theorem sepWPp_of_sepWP_cs_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ProofLib.SepWP prog mid s Pre (fun sm Pm =>
      VmPreserved s sm ∧ VRegsAt s sm ∧
        (StepInvVm s sm → SepWPp prog ret sm Pm Q Qp oom))) :
    SepWPp prog ret s Pre Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvmp, hv, hnext⟩ | ⟨_, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext ⟨StepInv.of_steps hsteps hv.eq, hvmp⟩ R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem sepWP_done_vm {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    [hv : VRegsAt s0 s]
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (hvm : VmPreserved s0 s)
    (hpost : Q s P) :
    ProofLib.SepWP prog target_pc s P (fun sm Pm => VmPreserved s0 sm ∧ VRegsAt s0 sm ∧ Q sm Pm) :=
  ProofLib.SepWP.done hpc hrun ⟨hvm, hv, hpost⟩

theorem sepWP_done_tpidr {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    [hv : VRegsAt s0 s]
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0)
    (hpost : Q s P) :
    ProofLib.SepWP prog target_pc s P
      (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ VRegsAt s0 sm ∧ Q sm Pm) :=
  ProofLib.SepWP.done hpc hrun ⟨htp, hv, hpost⟩

/-- Polymorphic-outcome (`Q`, `Qp`, `oom`) call combinator for `subroutine_ok` contracts that
neither panic, exit, nor OOM (`onPanic = ⌜False⌝`, `onExit = ⌜False⌝`, `onOom = ⌜False⌝`). -/
theorem sepWPp_call_cs_noPanic {α : Type} {prog : Program} {entry ret ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R, s.mem ⊨ P ∗ R → s.mem ⊨ spec.pre x s ∗ (F ∗ R))
    (hexit : ∀ sf code R, sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R) → False)
    (hpanic : ∀ sf R, sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R) → False)
    (hoom : ∀ sf R, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R) → False)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running → sm.sp = s.sp →
      CalleeSavedPreserved s sm → StepInv s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
    ⟨hpan, hpan_mem⟩ | ⟨code, hex, hex_mem⟩ | ⟨hoom_sm, hoom_mem⟩
  · rw [hlr] at hpcm
    rw [← sepConj_assoc] at hpost
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm
        (StepInv.of_steps hsteps hcsm.2.2.2.2.2.2.2.2.2.2.2) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (hpanic sm (F ∗ R) hpan hpan_mem).elim
  · exact (hexit sm code (F ∗ R) hex hex_mem).elim
  · exact (hoom sm (F ∗ R) hoom_sm hoom_mem).elim

/-! ## 2. Budget-Ready `VersionNegotiation.authKey` Length Step (`+52 .. +88`) -/

open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (ule_self_64 ult_self_64 ule_zero_64 ult_zero_64
   zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
   hwVarintLen_eq_ofNat_varintLen_norm hwVarintLen_bvShift_eq_ofNat_varintLen_norm
   zext64_truncate32 noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_length_beq_zero_of_lt bv_u32VarintField_nonzero bv_bytesField_nonempty
   bv_add_ofNat_comm bv_add_ofNat_eq adds_no_overflow_of_eq cmp_ls_false_of_lt)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

theorem step_encodeToVec_vn_authKey_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (a : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (hlen : vn.authKey.length < 2 ^ 64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 52#64) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInvVm s0 s)
    (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = (blkPl_426).base + 88#64 → s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) →
      s1.readReg64 .x20 = a → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .fp = s.readReg64 .fp →
      StepInvVm s0 s1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  dsimp only [versionNegotiationRest]
  obtain ⟨hbeqz, hbnez⟩ := ofNat_length_beq_zero_of_lt hlen
  cases hemp : vn.authKey.isEmpty
  · have hstep := bv_bytesField_nonempty hemp
    simp only [hemp, Bool.not_false] at hbeqz hbnez
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 88#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv)
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have hzero : bytesFieldEncodedLen vn.authKey = vn.authKey.length := by
      unfold bytesFieldEncodedLen
      cases h : vn.authKey with
      | nil => rfl
      | cons _ _ => rw [h] at hemp; cases hemp
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 88#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hzero, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv)

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
