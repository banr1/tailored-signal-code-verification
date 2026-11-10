/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyPop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Verification of `<spqr::chain::Chain>::send_key`

Proves fixed-image (`chainSendKey_ok_ext_x`) and relocatable `[LibsignalPlacement]` contracts
for `<spqr::chain::Chain>::send_key` (`0x60db0`, Block `367`, 149 instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open ChainAddEpochFacts ChainNewFacts NextKeyInternalFacts ChainSendKeyFacts AgreeStateSimp
open SendKeyTailHelpers

private def nextKeyInternalSpecCore (hkdf : HkdfFn) (A : RustAlloc) (extra : Nat) :
    Spec NextKeyInternalGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.nextA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = x.ctrA ∧
      x.next.length = 32 ∧ x.ctr ≠ 0xffffffff#32⌝ ∗
      memRegion x.out 36 ∗ (x.nextA ↦ₛ x.next) ∗ (x.ctrA ↦₃₂ x.ctr) ∗
      A.pool ∗ memRegion (s.sp - BitVec.ofNat 64 (extra + nextKeyInternalStackX)) extra ∗
      stackAt s.sp nextKeyInternalStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      nextKeyOutAt x.out (x.ctr + 1#32) (nextKeyOut hkdf x.next x.ctr) ∗
      (x.nextA ↦ₛ nextKeyNext hkdf x.next x.ctr) ∗ (x.ctrA ↦₃₂ (x.ctr + 1#32)) ∗
      A.pool ∗ memRegion (s0.sp - BitVec.ofNat 64 (extra + nextKeyInternalStackX)) extra ∗
      stackAt s0.sp nextKeyInternalStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private def chainSendKeySpecCore (hkdf : HkdfFn) (A : RustAlloc) (extra : Nat) :
    Spec ChainSendKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.selfPtr ∧ s.readReg64 .x1 = x.epoch ∧ s.readReg64 .x8 = x.out⌝ ∗
      memRegion x.out 40 ∗ chainAt A x.selfPtr x.G x.self ∗ A.pool ∗
      memRegion (s.sp - BitVec.ofNat 64 (extra + chainSendKeyStackX)) extra ∗
      stackAt s.sp chainSendKeyStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sendKeyPostAt A x.selfPtr x.out x.self (Chain.sendKey hkdf x.self x.epoch) ∗ A.pool ∗
      memRegion (s0.sp - BitVec.ofNat 64 (extra + chainSendKeyStackX)) extra ∗
      stackAt s0.sp chainSendKeyStackX
  onPanic := fun x s0 sf =>
    ⌜((Chain.sendKey hkdf x.self x.epoch).isPanic = true ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap

namespace SendKeyDecodes
gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x5b9b8 → 0x5bc08]
end SendKeyDecodes
open SendKeyDecodes

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  nextKeyInternal_fnOff chainSendKey_fnOff
  shim_fnOff alloc_fnOff dealloc_fnOff handleError_fnOff
  panicAddOverflow_fnOff corePanic_fnOff assertFailedUsize_fnOff
  libsignalSessionCode_fnOff_0x5a99c
  libsignalSessionCode_fnOff_0x5b9b8
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_stub% "core::panicking::assert_failed::<usize, usize>")
  (ls_hook% "core::panicking::assert_failed::<usize, usize>")
  (ls_stub% "core::panicking::panic")
  (ls_hook% "core::panicking::panic")

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

local macro "sep_elim_19 "
    c0:ident c1:ident c2:ident c3:ident c4:ident c5:ident
    c6:ident c7:ident c8:ident c9:ident c10:ident c11:ident
    l0:ident l1:ident l2:ident q0:ident q1:ident q2:ident q3:ident : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro $c0:ident; apply SepWPp.exists_elim; intro $c1:ident
    apply SepWPp.exists_elim; intro $c2:ident; apply SepWPp.exists_elim; intro $c3:ident
    apply SepWPp.exists_elim; intro $c4:ident; apply SepWPp.exists_elim; intro $c5:ident
    apply SepWPp.exists_elim; intro $c6:ident; apply SepWPp.exists_elim; intro $c7:ident
    apply SepWPp.exists_elim; intro $c8:ident; apply SepWPp.exists_elim; intro $c9:ident
    apply SepWPp.exists_elim; intro $c10:ident; apply SepWPp.exists_elim; intro $c11:ident
    apply SepWPp.exists_elim; intro $l0:ident; apply SepWPp.exists_elim; intro $l1:ident
    apply SepWPp.exists_elim; intro $l2:ident; apply SepWPp.exists_elim; intro $q0:ident
    apply SepWPp.exists_elim; intro $q1:ident; apply SepWPp.exists_elim; intro $q2:ident
    apply SepWPp.exists_elim; intro $q3:ident))

local macro "sep_elim_err4 " w0:ident b0:ident w2:ident w3:ident : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro $w0:ident; apply SepWPp.exists_elim; intro $b0:ident
    apply SepWPp.exists_elim; intro $w2:ident; apply SepWPp.exists_elim; intro $w3:ident))

theorem onPanic_entails_of_trace_eq {s0 s sf : State} {P : Prop} {F : SepProp}
    (hP : P) (hs : s.trace = s0.trace) :
    (⌜sf.trace = s.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(P ∧ sf.trace = s0.trace) ∨ (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  exact Entails.pure_left fun htr => Entails.pure_right (Or.inl ⟨hP, htr.trans hs⟩) (entails_anyHeap _)

theorem onPanic_entails_of_oom {s0 s sf : State} {P : Prop} {F : SepProp}
    (hs : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(P ∧ sf.trace = s0.trace) ∨ (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hoom, hpre⟩ => ?_
  have hoom0 : allocFailedIn s0 sf := by unfold allocFailedIn at hoom ⊢; rw [← hs]; exact hoom
  have hpre0 : s0.trace <+: sf.trace := by rw [← hs]; exact hpre
  exact Entails.pure_right (Or.inr ⟨hoom0, hpre0⟩) (entails_anyHeap _)

theorem SepWPp.call_allowPanic_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : ImgCallInv img s) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : (∀ code sf, spec.onExit x code s sf = ⌜False⌝) ∧ (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hF.1 hF.2 hpc hrun hsp_align hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [Spec.inImage]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, hpre R' hm⟩
  · intro sf code R' _ hpost
    dsimp only [Spec.inImage] at hpost; rw [hexit_eq.1] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sf _ _ hm'
    exact Satisfies.mono (sepConj_mono_left (hpan sf)) hm'
  · intro sf hpcm hrunm hspm hcsm hfz hsym
    exact hnext sf hpcm hrunm hspm hcsm ⟨hfz, hsym⟩
  · intro sf R' _ hpost
    dsimp only [Spec.inImage] at hpost; rw [hexit_eq.2] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

open Lean Elab Tactic in
elab "wpp_call_nextKey " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  let htrId ← freshIdent `htr_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_inImage $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_nextKey: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; apply onPanic_entails_of_oom; wp_norm_lhs)
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
    dsimp only [nextKeyInternalSpecX, nextKeyInternalSpecCore]
    simp (config := { decide := true }) only [sepConj_assoc, wp_norm, arm64_norm]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    intro $htrId:ident
    wp_norm_hyp $htrId
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId

open Lean Elab Tactic in
elab "wpp_call_nextKeyPanic " hcall:term:max a:term:max hF:term:max hpan:term:max : tactic => do
  evalTactic (← `(tactic| (
    apply (NextKeyInternalFacts.SepWPp.call_allowPanic_inImage_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_nextKeyPanic: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; apply onPanic_entails_of_trace_eq $hpan; wp_norm_lhs)
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    wp_focus_close (wp_unfold_specs; intro _ _ _ _ _ _; refine NextKeyInternalFacts.SepWP.pure_left_focus _ (by sep_focus) fun h => False.elim h)
  )))

def from436Pre (extra : Nat) (A : RustAlloc) (s0 : State) (x : ChainSendKeyGhost)
    (self' : Chain) (ctr' : BitVec 32) (outKey : Bytes)
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) : SepProp :=
  memRegion x.out 40 ∗
  chainRepr A x.selfPtr self' ∗
  nextKeyOutAt (s0.sp - 132#64) ctr' outKey ∗
  stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
  sendKeyScratchAt s0.sp l0 l1 l2 ∗
  ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
  ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗
  calleeSavedSendKeyAt s0 ∗
  A.pool ∗
  memRegion (s0.sp - BitVec.ofNat 64 (extra + chainSendKeyStackX)) extra

set_option maxHeartbeats 800000 in
private theorem sendKey_from_436 {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} {extra : Nat}
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (s0 : State) (hsp0_align : s0.spAligned = true) (x : ChainSendKeyGhost)
    (self' : Chain) (ctr' : BitVec 32) (outKey : Bytes)
    (hout_len : outKey.length = 32)
    (hsend_ok : Chain.sendKey hkdf x.self x.epoch = .ok (self', (ctr', outKey)))
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64)
    {R : SepProp}
    (s : State)
    (hF : ImgCallInv img s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainSendKeyName + 436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx29 : s.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (from436Pre extra A s0 x self' ctr' outKey l0 l1 l2 q0 q1 q2 q3)
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P' ⊢ (chainSendKeySpecCore hkdf A extra).post x s0 sf))
      (fun sf P' => (sf.mem ⊨ P' ∗ R) → (sf.mem ⊨ (chainSendKeySpecCore hkdf A extra).onPanic x s0 sf ∗ R)) := by
  intro prog
  have hfn : libsignalSessionCode.fnOff chainSendKeyName = 0x5b9b8 := chainSendKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b9b8 596
  have h_shim := sub_ok_at_rebase (name := chainSendKeyName) (callee := shimName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5b9b8))
    (by rw [chainSendKey_fnOff, shim_fnOff]) hshim
  have h_alloc := sub_ok_at_rebase (name := chainSendKeyName) (callee := allocName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - 0x5b9b8))
    (by rw [chainSendKey_fnOff, alloc_fnOff]) halloc
  have h_panic_oom := panic_at_handle_error_ext img.base ext chainSendKeyName
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x5b9b8))
    (by rw [chainSendKey_fnOff, handleError_fnOff])
  dsimp only [tripleRatchetProgAtExt] at h_panic_oom
  clear hshim halloc hfn
  dsimp only [prog] at *
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainSendKeyName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  unfold from436Pre nextKeyOutAt
  refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
  have hsp_align : s.spAligned = true := sp_sub_208_aligned hsp0_align hsp
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_norm_hyp hsp0_align
  wp_norm_hyp hsp
  wp_norm_hyp hsp_align
  wp_norm_hyp hx19
  wp_norm_hyp hx29
  wp_norm_hyp htr
  wp_norm_hyp hv
  obtain ⟨k0, k1, k2, k3, _, hout_pack⟩ :=
    exists_unpack64_of_length_32 hout_len
  have hout_unpack := hout_pack (s0.sp - 128#64)
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hout_unpack
  refine SepWPp.fold (Entails.of_eq hout_unpack) (by sep_focus) ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + 464#64) hF ?_
  apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5b9b8)) hF
  wp_steps
  refine SepWP.fold (pointsTo32_cells4_entails_memRegion_36 s0.sp ctr' k0 k1 k2 k3) (by sep_focus) ?_
  have hstack_s0 : stackAt (s0.sp - 208#64) nextKeyInternalStackX = stackAt s.sp nextKeyInternalStackX := by
    rw [hsp]
  refine SepWP.fold (Entails.of_eq (hstack_s0.trans (stackAt_nextKeyInternalX_top_split s.sp))) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  have ⟨hF2, hsym2⟩ := hinv2
  apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x5b9b8)) hinv2
  wp_call h_shim ()
  wp_steps
  have hstack_sf : stackAt s.sp extHookStack = stackAt sf.sp extHookStack :=
    congrArg (stackAt · extHookStack) (by wp_norm_goal)
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  rintro ⟨hF3, hsym3⟩
  wp_call h_alloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    wp_norm_hyp hoom_64
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    intro htrace_oom
    wp_norm_hyp htrace_oom
    wp_norm_hyp hpost
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5b9b8))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_oom) fun hm => ?_
    exact allowPanic_sendKey_oom (s0 := s0)
      (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace_oom, hpost, htr])) hm
  · have hoom_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hmod1, htrace1⟩
    wp_norm_hyp htrace1
    let p_key := sf_1.readReg64 (Reg.gpr 0#5)
    refine SepWPp.fold (Entails.of_eq (ChainNewFacts.memRegion_32_cells4 p_key)) (by sep_focus) ?_
    refine SepWPp.fold (Entails.of_eq (memRegion_40_ok_split x.out)) (by sep_focus) ?_
    refine SepWPp.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0)) (by sep_focus) ?_
    have hsp_sf1 : sf_1.sp = s0.sp - 208#64 := by
      rw [hsp_sf_1, hsp_sf, hsp]
    wp_norm_hyp hsp_sf1
    sep_elim_exists
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.fold (Entails.of_eq (hout_pack p_key).symm) (by sep_focus) ?_
    refine SepWP.fold (sendKeyOkAt_intro A x.out ctr' p_key outKey hout_len hoom_64) (by sep_focus) ?_
    have hstack_sf1 : stackAt sf.sp extHookStack = stackAt (s0.sp - 208#64) extHookStack := by
      rw [hsp_sf, hsp]
    refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_top_split (s0.sp - 208#64)).symm) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (sendKeyScratchAt_def s0.sp l0 l1 l2)) (by sep_focus) ?_
    refine SepWP.fold (rejoin_stack_chainSendKeyX s0.sp l0 l1 l2 k0 k1 k2 k3
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
      (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
      (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5))
      (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
      (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
      (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
    rw [hsend_ok]; dsimp only [sendKeyPostAt]
    refine Entails.pure_right (by wp_norm_goal) ?_
    sep_frame

def from380Pre (extra : Nat) (A : RustAlloc) (s0 : State) (x : ChainSendKeyGhost)
    (sendEpoch1 head1 : BitVec 64) (epochs2 : List ChainEpochGhost) (links2 : List ChainEpoch)
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) : SepProp :=
  memRegion x.out 40 ∗
  (x.selfPtr ↦₆₄ x.G.linksCap) ∗ ((x.selfPtr + 8#64) ↦₆₄ x.G.linksPtr) ∗
  ((x.selfPtr + 16#64) ↦₆₄ head1) ∗ ((x.selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links2.length) ∗
  vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
    x.G.linksCap x.G.linksPtr head1 (epochs2.zip links2) ∗
  ((x.selfPtr + 56#64) ↦₆₄ x.self.currentEpoch) ∗ ((x.selfPtr + 64#64) ↦₆₄ sendEpoch1) ∗
  chainRestSendKeyAt A x.selfPtr x.G x.self ∗
  stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
  sendKeyScratchAt s0.sp l0 l1 l2 ∗
  ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
  ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗
  memRegion (s0.sp - 132#64) 36 ∗
  calleeSavedSendKeyAt s0 ∗
  A.pool ∗
  memRegion (s0.sp - BitVec.ofNat 64 (extra + chainSendKeyStackX)) extra

set_option maxHeartbeats 800000 in
private theorem sendKey_from_380 {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} {extra : Nat}
    (hsub_extra : ∀ sp : BitVec 64,
      sp - 208#64 - BitVec.ofNat 64 (extra + nextKeyInternalStackX) =
        sp - BitVec.ofNat 64 (extra + chainSendKeyStackX))
    (hnextKey : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecCore hkdf A extra).inImage img))
    (hnextKeyPanic : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      (nextKeyInternalPanicSpecX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (s0 : State) (hsp0_align : s0.spAligned = true) (x : ChainSendKeyGhost)
    (sendEpoch1 head1 : BitVec 64)
    (epochs2 : List ChainEpochGhost) (links2 : List ChainEpoch)
    (i : Nat) (hi : i < links2.length)
    (hlen_le : links2.length ≤ x.G.linksCap.toNat)
    (hlen_eq : epochs2.length = links2.length)
    (hres_eq : Chain.sendKey hkdf x.self x.epoch = sendKeyTail hkdf x.self sendEpoch1 links2 i hi)
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64)
    {R : SepProp}
    (s : State)
    (hF : ImgCallInv img s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainSendKeyName + 380#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx20 : s.readReg64 (.gpr 20#5) = x.selfPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 links2.length)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 i)
    (hx29 : s.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (from380Pre extra A s0 x sendEpoch1 head1 epochs2 links2 l0 l1 l2 q0 q1 q2 q3)
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P' ⊢ (chainSendKeySpecCore hkdf A extra).post x s0 sf))
      (fun sf P' => (sf.mem ⊨ P' ∗ R) → (sf.mem ⊨ (chainSendKeySpecCore hkdf A extra).onPanic x s0 sf ∗ R)) := by
  intro prog
  have hfn : libsignalSessionCode.fnOff chainSendKeyName = 0x5b9b8 := chainSendKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b9b8 596
  have h_nextKey := sub_ok_at_rebase_bv (name := chainSendKeyName) (callee := nextKeyInternalName)
    (k := 0x5a99c#64 - 0x5b9b8#64) (by rw [chainSendKey_fnOff, nextKeyInternal_fnOff]; rfl) hnextKey
  have h_nextKeyPanic := sub_ok_at_rebase_bv (name := chainSendKeyName) (callee := nextKeyInternalName)
    (k := 0x5a99c#64 - 0x5b9b8#64) (by rw [chainSendKey_fnOff, nextKeyInternal_fnOff]; rfl) hnextKeyPanic
  have h_from436 := @sendKey_from_436 img hkdf A ext extra hshim halloc s0 hsp0_align x
  dsimp only at h_from436
  clear hnextKey hnextKeyPanic hshim halloc hfn
  dsimp only [prog] at *
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainSendKeyName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  unfold from380Pre
  have hzip_le : (epochs2.zip links2).length ≤ x.G.linksCap.toNat := by simp [hlen_eq, hlen_le]
  have hzip_i : i < (epochs2.zip links2).length := by simp [hlen_eq, hi]
  refine SepWPp.fold (vecDequeRingBuf_get_physIdx A x.G.linksCap x.G.linksPtr head1 (epochs2.zip links2) hzip_le hzip_i) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hhead, hcap_lt, hptr⟩
  have hzip_geti : (epochs2.zip links2)[i] = (epochs2[i]'(by omega), links2[i]'hi) := by
    simp [List.getElem_zip]
  rw [hzip_geti]
  let gce_i := epochs2[i]'(by omega)
  let ce_i := links2[i]'hi
  let slot_i := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx head1.toNat x.G.linksCap.toNat i * 112)
  refine SepWPp.fold (chainEpochAt_unpack_send_next A gce_i ce_i slot_i) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hle_i, hcap_i, hptr_i⟩
  have ⟨hule_i, hult_i⟩ := ofNat_lt_props hi (by omega : links2.length < 2 ^ 63)
  have hmaddi := physIdx_madd_eq (ptr := x.G.linksPtr) hhead (Nat.lt_of_lt_of_le hi hlen_le) hcap_lt
  wp_norm_hyp hsp0_align
  wp_norm_hyp hsp
  wp_norm_hyp hsp_align
  wp_norm_hyp hx19
  wp_norm_hyp hx20
  wp_norm_hyp hx27
  wp_norm_hyp hx28
  wp_norm_hyp hx29
  wp_norm_hyp htr
  wp_norm_hyp hv
  wp_norm_hyp hule_i
  wp_norm_hyp hult_i
  wp_norm_hyp hmaddi
  refine SepWPp.of_sepWP_inImage
    (mid := entry + (0x5a99c#64 - 0x5b9b8#64))
    hF ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  by_cases hbad : ce_i.send.next.length ≠ 32 ∨ ce_i.send.ctr = 0xffffffff#32
  · have hpan_tail : (sendKeyTail hkdf x.self sendEpoch1 links2 i hi).isPanic = true :=
      sendKeyTail_isPanic_of_bad hkdf x.self sendEpoch1 links2 i hi hbad
    have hpan_eq : (Chain.sendKey hkdf x.self x.epoch).isPanic = true := by
      rw [hres_eq]; exact hpan_tail
    have hlen_lt64 : ce_i.send.next.length < 2 ^ 64 := by omega
    change subroutine_ok prog_val
      (entry + (0x5a99c#64 - 0x5b9b8#64))
      (nextKeyInternalPanicSpecX.inImage img) at h_nextKeyPanic
    wpp_call_nextKeyPanic h_nextKeyPanic
      (⟨s0.sp - 132#64, gce_i.send.next.ptr, ce_i.send.next, slot_i + 48#64, ce_i.send.ctr⟩ : NextKeyInternalGhost)
      hinv1 hpan_eq
  · have hlen32 : ce_i.send.next.length = 32 := by omega
    have hctr_ne : ce_i.send.ctr ≠ 0xffffffff#32 := fun hc => hbad (Or.inr hc)
    have hlen32_bv : BitVec.ofNat 64 ce_i.send.next.length = 32#64 := by rw [hlen32]
    wp_norm_hyp hlen32_bv
    have hextra_in :
        memRegion (s0.sp - BitVec.ofNat 64 (extra + chainSendKeyStackX)) extra =
        memRegion (s0.sp - 208#64 - BitVec.ofNat 64 (extra + nextKeyInternalStackX)) extra := by
      rw [hsub_extra s0.sp]
    refine SepWPp.fold (Entails.of_eq hextra_in) (by sep_focus) ?_
    change subroutine_ok prog_val
      (entry + (0x5a99c#64 - 0x5b9b8#64))
      ((nextKeyInternalSpecCore hkdf A extra).inImage img) at h_nextKey
    wpp_call_nextKey h_nextKey
      (⟨s0.sp - 132#64, gce_i.send.next.ptr, ce_i.send.next, slot_i + 48#64, ce_i.send.ctr⟩ : NextKeyInternalGhost)
      hinv1
    have hextra_s :
        memRegion (s.sp - BitVec.ofNat 64 (extra + nextKeyInternalStackX)) extra =
        memRegion (s0.sp - BitVec.ofNat 64 (extra + chainSendKeyStackX)) extra := by
      rw [hsp, hsub_extra s0.sp]
    refine SepWPp.fold (Entails.of_eq hextra_s) (by sep_focus) ?_
    have hstack_s : stackAt s.sp nextKeyInternalStackX = stackAt (s0.sp - 208#64) nextKeyInternalStackX := by
      rw [hsp]
    refine SepWPp.fold (Entails.of_eq hstack_s) (by sep_focus) ?_
    refine SepWPp.fold (nextKeyOutAt_dup_len (s0.sp - 132#64) (ce_i.send.ctr + 1#32)
      (nextKeyOut hkdf ce_i.send.next ce_i.send.ctr)) (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    intro hout_len
    have hnext'_len : (nextKeyNext hkdf ce_i.send.next ce_i.send.ctr).length = 32 :=
      nextKeyNext_length_of_nextKeyOut_length hout_len
    let send' : ChainEpochDirection :=
      { ce_i.send with next := nextKeyNext hkdf ce_i.send.next ce_i.send.ctr, ctr := ce_i.send.ctr + 1#32 }
    let links' := links2.set i { ce_i with send := send' }
    have hced := chainEpochDirectionAt_pack_nextKey A slot_i gce_i.send ce_i.send
      (nextKeyNext hkdf ce_i.send.next ce_i.send.ctr) (ce_i.send.ctr + 1#32)
      hlen32 hnext'_len hle_i hcap_i hptr_i
    have hce :
        chainEpochDirectionAt A slot_i gce_i.send send' ∗
          chainEpochDirectionAt A (slot_i + 56#64) gce_i.recv ce_i.recv ⊢
          chainEpochAt A (gce_i, { ce_i with send := send' }) slot_i := Entails.refl _
    have hset := vecDequeRingBuf_set_physIdx A x.G.linksCap x.G.linksPtr head1 (epochs2.zip links2)
      (gce_i, { ce_i with send := send' }) hhead hcap_lt hptr hzip_le hzip_i
    dsimp only at hset
    have hzip_set : (epochs2.zip links2).set i (gce_i, { ce_i with send := send' }) =
        epochs2.zip links' :=
      zip_set_snd epochs2 links2 i gce_i _ (List.getElem?_eq_getElem (by omega))
    rw [hzip_set] at hset
    have hlen_links' : links'.length = links2.length := List.length_set
    have hpack := chainRepr_pack_sendKey A x.selfPtr x.G x.self head1 epochs2 links' sendEpoch1 (by omega)
    rw [hlen_links'] at hpack
    refine SepWPp.fold hced (by sep_focus) ?_
    refine SepWPp.fold hce (by sep_focus) ?_
    refine SepWPp.fold hset (by sep_focus) ?_
    refine SepWPp.fold hpack (by sep_focus) ?_
    have h436_pre :
        chainRepr A x.selfPtr { x.self with sendEpoch := sendEpoch1, links := links' } ∗
        nextKeyOutAt (s0.sp - 132#64) (ce_i.send.ctr + 1#32) (nextKeyOut hkdf ce_i.send.next ce_i.send.ctr) ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
        memRegion x.out 40 ∗
        sendKeyScratchAt s0.sp l0 l1 l2 ∗
        ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
        ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗
        calleeSavedSendKeyAt s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 (extra + chainSendKeyStackX)) extra ⊢
        from436Pre extra A s0 x { x.self with sendEpoch := sendEpoch1, links := links' }
          (ce_i.send.ctr + 1#32) (nextKeyOut hkdf ce_i.send.next ce_i.send.ctr)
          l0 l1 l2 q0 q1 q2 q3 := by
      unfold from436Pre; sep_frame
    refine SepWPp.fold h436_pre (by sep_focus) ?_
    have htail_ok := sendKeyTail_eq_ok hkdf x.self sendEpoch1 links2 i hi hlen32 hctr_ne
    dsimp only at htail_ok
    have hsend_ok : Chain.sendKey hkdf x.self x.epoch =
        .ok ({ x.self with sendEpoch := sendEpoch1, links := links' },
             (ce_i.send.ctr + 1#32, nextKeyOut hkdf ce_i.send.next ce_i.send.ctr)) :=
      hres_eq.trans htail_ok
    rw [sepConj_emp]
    have h436_call := h_from436
      { x.self with sendEpoch := sendEpoch1, links := links' }
      (ce_i.send.ctr + 1#32) (nextKeyOut hkdf ce_i.send.next ce_i.send.ctr)
      hout_len hsend_ok l0 l1 l2 q0 q1 q2 q3 (R := R) sf hF_sf hpc_sf hrun_sf
      (hsp_sf.trans hsp) (by wp_norm_goal) (by wp_norm_goal) (htr_sf.trans htr) (by wp_norm_goal)
    simpa only [sepConj_assoc, satisfies_pure_sepConj] using h436_call

/-! ## Framing `sendKey_from_344` and `sendKey_pop_loop` into `SepWPp` -/

private theorem sendKey_from_344_full {extra : Nat} {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hsub_extra : ∀ sp : BitVec 64,
      sp - 208#64 - BitVec.ofNat 64 (extra + nextKeyInternalStackX) =
        sp - BitVec.ofNat 64 (extra + chainSendKeyStackX))
    (hnextKey : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecCore hkdf A extra).inImage img))
    (hnextKeyPanic : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      (nextKeyInternalPanicSpecX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (s0 : State) (hsp0_align : s0.spAligned = true) (x : ChainSendKeyGhost)
    (head1 : BitVec 64)
    (epochs1 : List ChainEpochGhost) (links1 : List ChainEpoch)
    (h1 : 1 < links1.length)
    (hlen_le : links1.length ≤ x.G.linksCap.toNat)
    (hlen_eq : epochs1.length = links1.length)
    (hres_eq :
      let h0 : 0 < links1.length := by omega
      let links2 := links1.set 0 { links1[0] with send := links1[0].send.clearNext }
      have h1' : 1 < links2.length := by simp [links2]; omega
      Chain.sendKey hkdf x.self x.epoch = sendKeyTail hkdf x.self x.epoch links2 1 h1')
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64)
    {R : SepProp}
    (s : State)
    (hF : ImgCallInv img s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainSendKeyName + 344#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx20 : s.readReg64 (.gpr 20#5) = x.selfPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 links1.length)
    (hx29 : s.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (from380Pre extra A s0 x x.epoch head1 epochs1 links1 l0 l1 l2 q0 q1 q2 q3)
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P' ⊢ (chainSendKeySpecCore hkdf A extra).post x s0 sf))
      (fun sf P' => (sf.mem ⊨ P' ∗ R) → (sf.mem ⊨ (chainSendKeySpecCore hkdf A extra).onPanic x s0 sf ∗ R)) := by
  intro prog
  have h0 : 0 < links1.length := by omega
  let links2 := links1.set 0 { links1[0] with send := links1[0].send.clearNext }
  have h1' : 1 < links2.length := by simp [links2]; omega
  have hlen2_eq : links2.length = links1.length := List.length_set
  let F_344 : SepProp :=
    memRegion x.out 40 ∗
    ((x.selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links1.length) ∗
    ((x.selfPtr + 56#64) ↦₆₄ x.self.currentEpoch) ∗ ((x.selfPtr + 64#64) ↦₆₄ x.epoch) ∗
    chainRestSendKeyAt A x.selfPtr x.G x.self ∗
    stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
    sendKeyScratchAt s0.sp l0 l1 l2 ∗
    ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
    ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗
    memRegion (s0.sp - 132#64) 36 ∗
    calleeSavedSendKeyAt s0 ∗
    A.pool ∗
    memRegion (s0.sp - BitVec.ofNat 64 (extra + chainSendKeyStackX)) extra
  have hstep344 := sendKey_from_344 (img := img) (A := A) (ext := ext)
    x.selfPtr x.G.linksCap x.G.linksPtr head1 epochs1 links1 h0 hlen_le hlen_eq
    s hpc hrun hsp_align hx20
  dsimp only at hstep344
  have hpre344 :
      from380Pre extra A s0 x x.epoch head1 epochs1 links1 l0 l1 l2 q0 q1 q2 q3 ⊢
        clearFrontPre A x.selfPtr x.G.linksCap x.G.linksPtr head1 epochs1 links1 ∗ F_344 := by
    unfold from380Pre clearFrontPre F_344
    sep_frame
  have hpost344 :
      clearFrontPre A x.selfPtr x.G.linksCap x.G.linksPtr head1 epochs1 links2 ∗ F_344 ⊢
        from380Pre extra A s0 x x.epoch head1 epochs1 links2 l0 l1 l2 q0 q1 q2 q3 := by
    unfold from380Pre clearFrontPre F_344
    rw [hlen2_eq]
    sep_frame
  refine SepWPp.seq_entails_inImage hF (SendKeyTailHelpers.SepWP.conseq_entails hstep344 hpre344 hpost344) ?_
  rintro sm hpcm hrunm hFm ⟨hsp_m, hsp_align_m, hx19_m, hx20_m, hx27_m, hx28_m, hx29_m, htr_m, hv_m⟩
  exact sendKey_from_380 hsub_extra hnextKey hnextKeyPanic hshim halloc s0 hsp0_align x
    x.epoch head1 epochs1 links2 1 h1' (by rw [hlen2_eq]; exact hlen_le)
    (by rw [hlen2_eq]; exact hlen_eq) hres_eq l0 l1 l2 q0 q1 q2 q3
    sm hFm hpcm hrunm (hsp_m.trans hsp) hsp_align_m (hx19_m.trans hx19) hx20_m
    (by rw [hlen2_eq]; exact hx27_m.trans hx27) hx28_m (hx29_m.trans hx29) (htr_m.trans htr) (hv_m.trans hv)

set_option maxHeartbeats 1600000 in
private theorem chainSendKey_ok_core {extra : Nat} {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hsub_extra : ∀ sp : BitVec 64,
      sp - 208#64 - BitVec.ofNat 64 (extra + nextKeyInternalStackX) =
        sp - BitVec.ofNat 64 (extra + chainSendKeyStackX))
    (_himg : Obj.Loads libsignalSessionImage img)
    (hnextKey : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecCore hkdf A extra).inImage img))
    (hnextKeyPanic : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      (nextKeyInternalPanicSpecX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr chainSendKeyName)
      ((chainSendKeySpecCore hkdf A extra).inImage img) := by
  unfold tripleRatchetProgAtExt
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff chainSendKeyName = 0x5b9b8 :=
    chainSendKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b9b8 596
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainSendKeyName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear _himg hfn
  have hsp0_align : s0.spAligned = true := hsp_align
  rcases x with ⟨out, selfPtr, epoch, G, self⟩
  dsimp only [Spec.inImage, chainSendKeySpecCore] at *
  refine SepWPp.post_of_entails ?_
  have hinv0 : ImgCallInv img s0 := ⟨‹img.FrozenLoaded s0›, ‹s0.symtab = img.symtab›⟩
  subst out selfPtr epoch
  refine SepWPp.rw_pre (by rw [stackAt_chainSendKeyX_split s0.sp]) ?_
  sep_elim_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c_18 c_17 c_16 c_15 c_14 c_13 c_12
  refine SepWPp.fold (chainAt_unpack_sendKey A (s0.readReg64 (.gpr 0#5)) G self) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hlen_eq, hlen_le, hcap_lt, hptr⟩
  have h_from380 := @sendKey_from_380 img hkdf A ext extra hsub_extra hnextKey hnextKeyPanic hshim halloc s0 hsp0_align
    ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩
  have h_from344 := @sendKey_from_344_full extra img hkdf A ext hsub_extra hnextKey hnextKeyPanic hshim halloc s0 hsp0_align
    ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩
  have h_poploop := @sendKey_pop_loop img A ext hdealloc (s0.readReg64 (.gpr 0#5)) G.linksCap G.linksPtr hcap_lt
  dsimp only at h_from380 h_from344 h_poploop
  clear hnextKey hnextKeyPanic hshim halloc hdealloc
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainSendKeyName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWP, SepWPp]
  examples_hide_fetches
  by_cases hlt_send : s0.readReg64 (.gpr 1#5) < self.sendEpoch
  ·
    have ⟨hult_send, hule_send⟩ := lt_props hlt_send
    wp_norm_hyp hult_send
    wp_norm_hyp hule_send
    refine SepWPp.fold (Entails.of_eq (memRegion_40_err_split (s0.readReg64 (.gpr 8#5)))) (by sep_focus) ?_
    sep_elim_err4 w0 b0 w2 c_22
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.fold (sendKeyErrAt_sendKeyEpochDecreased_intro (s0.readReg64 (.gpr 8#5))
      self.sendEpoch (s0.readReg64 (.gpr 1#5))) (by sep_focus) ?_
    refine SepWP.fold (chainRepr_pack_sendKey A (s0.readReg64 (.gpr 0#5)) G self
      G.linksHead G.epochs self.links self.sendEpoch hlen_eq) (by sep_focus) ?_
    refine SepWP.fold (rejoin_stack_chainSendKeyX s0.sp c_18 c_17 c_16 c_15 c_14 c_13 c_12
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
      (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
      (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5))
      (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
      (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
      (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
    rw [sendKey_of_lt hkdf self (s0.readReg64 (.gpr 1#5)) hlt_send]
    dsimp only [sendKeyPostAt]
    refine Entails.pure_right (by wp_norm_goal) ?_
    sep_frame
  · have ⟨hult_send, hule_send⟩ := ge_props hlt_send
    wp_norm_hyp hult_send
    wp_norm_hyp hule_send
    by_cases hgt_curr : s0.readReg64 (.gpr 1#5) > self.currentEpoch
    ·
      have ⟨hult_curr, hule_curr⟩ := lt_props hgt_curr
      wp_norm_hyp hult_curr
      wp_norm_hyp hule_curr
      refine SepWPp.fold (Entails.of_eq (memRegion_40_err_split (s0.readReg64 (.gpr 8#5)))) (by sep_focus) ?_
      sep_elim_err4 w0 b0 w2 c_22
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.fold (sendKeyErrAt_epochOutOfRange_intro (s0.readReg64 (.gpr 8#5))
        (s0.readReg64 (.gpr 1#5)) w0) (by sep_focus) ?_
      refine SepWP.fold (chainRepr_pack_sendKey A (s0.readReg64 (.gpr 0#5)) G self
        G.linksHead G.epochs self.links self.sendEpoch hlen_eq) (by sep_focus) ?_
      refine SepWP.fold (rejoin_stack_chainSendKeyX s0.sp c_18 c_17 c_16 c_15 c_14 c_13 c_12
        (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
        (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
        (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5))
        (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
        (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
        (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
      rw [sendKey_of_epochIdx_err hkdf self (s0.readReg64 (.gpr 1#5)) _ hlt_send
        (epochIdx_of_gt self (s0.readReg64 (.gpr 1#5)) hgt_curr)]
      dsimp only [sendKeyPostAt]
      refine Entails.pure_right (by wp_norm_goal) ?_
      sep_frame
    · have ⟨hult_curr, hule_curr⟩ := ge_props hgt_curr
      wp_norm_hyp hult_curr
      wp_norm_hyp hule_curr
      by_cases hback_ge : (self.currentEpoch - s0.readReg64 (.gpr 1#5)).toNat ≥ self.links.length
      ·
        have ⟨hult_back, hule_back⟩ := back_ge_props hback_ge (by omega : self.links.length < 2 ^ 63)
        wp_norm_hyp hult_back
        wp_norm_hyp hule_back
        refine SepWPp.fold (Entails.of_eq (memRegion_40_err_split (s0.readReg64 (.gpr 8#5)))) (by sep_focus) ?_
        sep_elim_err4 w0 b0 w2 c_22
        apply SepWPp.of_sepWP_ret
        wp_steps
        refine SepWP.fold (sendKeyErrAt_epochOutOfRange_intro (s0.readReg64 (.gpr 8#5))
          (s0.readReg64 (.gpr 1#5)) w0) (by sep_focus) ?_
        refine SepWP.fold (chainRepr_pack_sendKey A (s0.readReg64 (.gpr 0#5)) G self
          G.linksHead G.epochs self.links self.sendEpoch hlen_eq) (by sep_focus) ?_
        refine SepWP.fold (rejoin_stack_chainSendKeyX s0.sp c_18 c_17 c_16 c_15 c_14 c_13 c_12
          (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
          (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
          (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5))
          (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
          (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
          (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
        rw [sendKey_of_epochIdx_err hkdf self (s0.readReg64 (.gpr 1#5)) _ hlt_send
          (epochIdx_of_back_ge self (s0.readReg64 (.gpr 1#5)) hgt_curr hback_ge)]
        dsimp only [sendKeyPostAt]
        refine Entails.pure_right (by wp_norm_goal) ?_
        sep_frame
      ·
        have hback_lt : (self.currentEpoch - s0.readReg64 (.gpr 1#5)).toNat < self.links.length := by omega
        have ⟨hult_back, hule_back⟩ := back_lt_props hback_lt (by omega : self.links.length < 2 ^ 63)
        let idx0 := self.links.length - 1 - (self.currentEpoch - s0.readReg64 (.gpr 1#5)).toNat
        have hidx0_lt : idx0 < self.links.length := by dsimp [idx0]; omega
        have hidx_eq : self.epochIdx (s0.readReg64 (.gpr 1#5)) = .ok idx0 :=
          epochIdx_of_lt self (s0.readReg64 (.gpr 1#5)) hgt_curr hback_lt
        have hadd_not :
            BitVec.ofNat 64 self.links.length + ~~~(self.currentEpoch - s0.readReg64 (.gpr 1#5)) =
              BitVec.ofNat 64 idx0 :=
          add_not_eq_ofNat_sub hback_lt
        wp_norm_hyp hult_back
        wp_norm_hyp hule_back
        wp_norm_hyp hadd_not
        by_cases heq_send : self.sendEpoch = s0.readReg64 (.gpr 1#5)
        ·
          have heq_beq : (self.sendEpoch == s0.readReg64 (.gpr 1#5)) = true := by simp [heq_send]
          have heq_sub : (self.sendEpoch - s0.readReg64 (.gpr 1#5) == 0#64) = true := by simp [heq_send]
          wp_norm_hyp heq_beq
          wp_norm_hyp heq_sub
          have hres_eq := sendKey_eq_tail_of_eq hkdf self (s0.readReg64 (.gpr 1#5)) idx0 hlt_send hidx_eq hidx0_lt heq_send
          refine SepWPp.of_sepWP_inImage (mid := entry + 380#64) hinv0 ?_
          wp_steps
          refine SepWP.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0).symm) (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (sendKeyScratchAt_def s0.sp c_18 c_17 c_16).symm) (by sep_focus) ?_
          have hpre_fold :
              memRegion (s0.readReg64 (.gpr 8#5)) 40 ∗
              (s0.readReg64 (.gpr 0#5) ↦₆₄ G.linksCap) ∗ ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ G.linksPtr) ∗
              ((s0.readReg64 (.gpr 0#5) + 16#64) ↦₆₄ G.linksHead) ∗ ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
              vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
                G.linksCap G.linksPtr G.linksHead (G.epochs.zip self.links) ∗
              ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ self.currentEpoch) ∗ ((s0.readReg64 (.gpr 0#5) + 64#64) ↦₆₄ self.sendEpoch) ∗
              chainRestSendKeyAt A (s0.readReg64 (.gpr 0#5)) G self ∗
              stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
              sendKeyScratchAt s0.sp c_18 c_17 c_16 ∗
              ((s0.sp - 176#64) ↦₆₄ c_15) ∗ ((s0.sp - 168#64) ↦₆₄ c_14) ∗
              ((s0.sp - 160#64) ↦₆₄ c_13) ∗ ((s0.sp - 152#64) ↦₆₄ c_12) ∗
              memRegion (s0.sp - 132#64) 36 ∗
              calleeSavedSendKeyAt s0 ∗
              A.pool ∗
              memRegion (s0.sp - BitVec.ofNat 64 (extra + chainSendKeyStackX)) extra ⊢
              from380Pre extra A s0 ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩
                self.sendEpoch G.linksHead G.epochs self.links c_18 c_17 c_16 c_15 c_14 c_13 c_12 := by
            unfold from380Pre; sep_frame
          refine SepWP.fold hpre_fold (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv1
          rw [sepConj_emp]
          exact h_from380
            self.sendEpoch G.linksHead G.epochs self.links idx0 hidx0_lt hlen_le hlen_eq hres_eq
            c_18 c_17 c_16 c_15 c_14 c_13 c_12 _ hinv1 (by wp_norm_goal) (by wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        ·
          have ⟨hne_beq, hne_sub, hne_add⟩ := ne_branch_props heq_send
          wp_norm_hyp hne_beq
          wp_norm_hyp hne_sub
          wp_norm_hyp hne_add
          rcases hidx0_cases : idx0 with _ | _ | k
          ·
            have h0_lt : 0 < self.links.length := by omega
            have hidx_0 : self.epochIdx (s0.readReg64 (.gpr 1#5)) = .ok 0 := by
              simpa [hidx0_cases] using hidx_eq
            have hres_eq := sendKey_eq_tail_of_ne_zero hkdf self (s0.readReg64 (.gpr 1#5)) hlt_send hidx_0 h0_lt heq_send
            have hadd_not0 :
                BitVec.ofNat 64 self.links.length + ~~~(self.currentEpoch - s0.readReg64 (.gpr 1#5)) = 0#64 := by
              simpa [hidx0_cases] using hadd_not
            wp_norm_hyp hadd_not0
            refine SepWPp.of_sepWP_inImage (mid := entry + 380#64) hinv0 ?_
            wp_steps
            refine SepWP.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0).symm) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (sendKeyScratchAt_def s0.sp c_18 c_17 c_16).symm) (by sep_focus) ?_
            have hpre_fold :
                memRegion (s0.readReg64 (.gpr 8#5)) 40 ∗
                (s0.readReg64 (.gpr 0#5) ↦₆₄ G.linksCap) ∗ ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ G.linksPtr) ∗
                ((s0.readReg64 (.gpr 0#5) + 16#64) ↦₆₄ G.linksHead) ∗ ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
                vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
                  G.linksCap G.linksPtr G.linksHead (G.epochs.zip self.links) ∗
                ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ self.currentEpoch) ∗ ((s0.readReg64 (.gpr 0#5) + 64#64) ↦₆₄ s0.readReg64 (.gpr 1#5)) ∗
                chainRestSendKeyAt A (s0.readReg64 (.gpr 0#5)) G self ∗
                stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
                sendKeyScratchAt s0.sp c_18 c_17 c_16 ∗
                ((s0.sp - 176#64) ↦₆₄ c_15) ∗ ((s0.sp - 168#64) ↦₆₄ c_14) ∗
                ((s0.sp - 160#64) ↦₆₄ c_13) ∗ ((s0.sp - 152#64) ↦₆₄ c_12) ∗
                memRegion (s0.sp - 132#64) 36 ∗
                calleeSavedSendKeyAt s0 ∗
                A.pool ∗
                memRegion (s0.sp - BitVec.ofNat 64 (extra + chainSendKeyStackX)) extra ⊢
                from380Pre extra A s0 ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩
                  (s0.readReg64 (.gpr 1#5)) G.linksHead G.epochs self.links c_18 c_17 c_16 c_15 c_14 c_13 c_12 := by
              unfold from380Pre; sep_frame
            refine SepWP.fold hpre_fold (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv1
            rw [sepConj_emp]
            exact h_from380
              (s0.readReg64 (.gpr 1#5)) G.linksHead G.epochs self.links 0 h0_lt hlen_le hlen_eq hres_eq
              c_18 c_17 c_16 c_15 c_14 c_13 c_12 _ hinv1 (by wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
          ·
            have h1_lt : 1 < self.links.length := by omega
            have hidx_1 : self.epochIdx (s0.readReg64 (.gpr 1#5)) = .ok 1 := by
              simpa [hidx0_cases] using hidx_eq
            have hres_eq := sendKey_eq_tail_of_ne_pos hkdf self (s0.readReg64 (.gpr 1#5)) 1
              hlt_send hidx_1 h1_lt heq_send (by omega)
            dsimp only [Nat.sub_self, List.drop_zero] at hres_eq
            have hadd_not1 :
                BitVec.ofNat 64 self.links.length + ~~~(self.currentEpoch - s0.readReg64 (.gpr 1#5)) = 1#64 := by
              simpa [hidx0_cases] using hadd_not
            wp_norm_hyp hadd_not1
            refine SepWPp.of_sepWP_inImage (mid := entry + 344#64) hinv0 ?_
            wp_steps
            refine SepWP.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0).symm) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (sendKeyScratchAt_def s0.sp c_18 c_17 c_16).symm) (by sep_focus) ?_
            have hpre_fold :
                memRegion (s0.readReg64 (.gpr 8#5)) 40 ∗
                (s0.readReg64 (.gpr 0#5) ↦₆₄ G.linksCap) ∗ ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ G.linksPtr) ∗
                ((s0.readReg64 (.gpr 0#5) + 16#64) ↦₆₄ G.linksHead) ∗ ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
                vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
                  G.linksCap G.linksPtr G.linksHead (G.epochs.zip self.links) ∗
                ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ self.currentEpoch) ∗ ((s0.readReg64 (.gpr 0#5) + 64#64) ↦₆₄ s0.readReg64 (.gpr 1#5)) ∗
                chainRestSendKeyAt A (s0.readReg64 (.gpr 0#5)) G self ∗
                stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
                sendKeyScratchAt s0.sp c_18 c_17 c_16 ∗
                ((s0.sp - 176#64) ↦₆₄ c_15) ∗ ((s0.sp - 168#64) ↦₆₄ c_14) ∗
                ((s0.sp - 160#64) ↦₆₄ c_13) ∗ ((s0.sp - 152#64) ↦₆₄ c_12) ∗
                memRegion (s0.sp - 132#64) 36 ∗
                calleeSavedSendKeyAt s0 ∗
                A.pool ∗
                memRegion (s0.sp - BitVec.ofNat 64 (extra + chainSendKeyStackX)) extra ⊢
                from380Pre extra A s0 ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩
                  (s0.readReg64 (.gpr 1#5)) G.linksHead G.epochs self.links c_18 c_17 c_16 c_15 c_14 c_13 c_12 := by
              unfold from380Pre; sep_frame
            refine SepWP.fold hpre_fold (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv1
            rw [sepConj_emp]
            exact h_from344
              G.linksHead G.epochs self.links h1_lt hlen_le hlen_eq hres_eq
              c_18 c_17 c_16 c_15 c_14 c_13 c_12 _ hinv1 (by wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
          ·
            have hk_lt : k + 2 < self.links.length := by omega
            have hidx_k : self.epochIdx (s0.readReg64 (.gpr 1#5)) = .ok (k + 2) := by
              simpa [hidx0_cases] using hidx_eq
            have hres_eq := sendKey_eq_tail_of_ne_pos hkdf self (s0.readReg64 (.gpr 1#5)) (k + 2)
              hlt_send hidx_k hk_lt heq_send (by omega)
            dsimp only [Nat.add_sub_cancel] at hres_eq
            have hadd_notk :
                BitVec.ofNat 64 self.links.length + ~~~(self.currentEpoch - s0.readReg64 (.gpr 1#5)) =
                  BitVec.ofNat 64 (k + 2) := by
              simpa [hidx0_cases] using hadd_not
            have ⟨hult_k2, hule_k2⟩ := k_plus_2_ge_2_props k (by omega)
            wp_norm_hyp hadd_notk
            wp_norm_hyp hult_k2
            wp_norm_hyp hule_k2
            refine SepWPp.of_sepWP_inImage (mid := entry + 164#64) hinv0 ?_
            wp_steps
            refine SepWP.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0).symm) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_top_split (s0.sp - 208#64))) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv1
            have hloop := h_poploop k G.linksHead c_16 G.epochs self.links (by omega) hlen_le hlen_eq
              _ hinv1 (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
            let F_loop : SepProp :=
              memRegion (s0.readReg64 (.gpr 8#5)) 40 ∗
              (s0.readReg64 (.gpr 0#5) ↦₆₄ G.linksCap) ∗ ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ G.linksPtr) ∗
              ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ self.currentEpoch) ∗
              ((s0.readReg64 (.gpr 0#5) + 64#64) ↦₆₄ s0.readReg64 (.gpr 1#5)) ∗
              chainRestSendKeyAt A (s0.readReg64 (.gpr 0#5)) G self ∗
              memRegion (s0.sp - 208#64 - BitVec.ofNat 64 nextKeyInternalStackX) 176 ∗
              memRegion (s0.sp - 208#64) 8 ∗
              ((s0.sp - 176#64) ↦₆₄ c_15) ∗ ((s0.sp - 168#64) ↦₆₄ c_14) ∗
              ((s0.sp - 160#64) ↦₆₄ c_13) ∗ ((s0.sp - 152#64) ↦₆₄ c_12) ∗
              memRegion (s0.sp - 144#64) 12 ∗
              memRegion (s0.sp - 132#64) 36 ∗
              calleeSavedSendKeyAt s0 ∗
              memRegion (s0.sp - BitVec.ofNat 64 (extra + chainSendKeyStackX)) extra
            have hpost_loop :
                popLoopPre A (s0.sp - 208#64) (s0.readReg64 (.gpr 0#5)) G.linksCap G.linksPtr
                  (iterHead G.linksCap.toNat G.linksHead (k + 1)) (iterL2 c_16 G.epochs (k + 1))
                  (G.epochs.drop (k + 1)) (self.links.drop (k + 1)) ∗ F_loop ⊢
                from380Pre extra A s0 ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩
                  (s0.readReg64 (.gpr 1#5)) (iterHead G.linksCap.toNat G.linksHead (k + 1))
                  (G.epochs.drop (k + 1)) (self.links.drop (k + 1))
                  G.linksPtr G.linksCap (iterL2 c_16 G.epochs (k + 1)) c_15 c_14 c_13 c_12 := by
              unfold popLoopPre F_loop from380Pre sendKeyScratchAt
              rw [stackAt_nextKeyInternalX_top_split (s0.sp - 208#64)]
              simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
              sep_frame
            refine SepWPp.seq_entails_inImage hinv1
              (SendKeyTailHelpers.SepWP.conseq_entails (F := F_loop) hloop
                (by unfold popLoopPre F_loop
                    simp (config := { decide := true }) only [wp_norm, arm64_norm, bv_sub_add_lit, Nat.reduceSub]
                    sep_frame)
                (by simp (config := { decide := true }) only [wp_norm, arm64_norm]
                    exact hpost_loop)) ?_
            rintro sm hpcm hrunm hFm ⟨hsp_m, hsp_align_m, hx19_m, hx20_m, hx22_m, hx27_m, hx28_m, hx29_m, htr_m, hvregs_m⟩
            exact h_from344
              (iterHead G.linksCap.toNat G.linksHead (k + 1))
              (G.epochs.drop (k + 1)) (self.links.drop (k + 1))
              (by simp; omega) (by simp; omega) (by simp [hlen_eq]) hres_eq
              G.linksPtr G.linksCap (iterL2 c_16 G.epochs (k + 1)) c_15 c_14 c_13 c_12
              sm hFm hpcm hrunm (by rw [hsp_m]; wp_norm_goal) hsp_align_m
              (by rw [hx19_m]; wp_norm_goal) hx20_m hx27_m
              (by rw [hx29_m]; wp_norm_goal) (by rw [htr_m]; wp_norm_goal) (by rw [hvregs_m]; wp_norm_goal)

theorem chainSendKey_ok_of_contracts_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hnextKey : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecX hkdf A).inImage img))
    (hnextKeyPanic : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      (nextKeyInternalPanicSpecX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    ChainSendKeyOkX img hkdf A ext := by
  have hnextKey' : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecCore hkdf A 0).inImage img) := by
    refine sub_ok_conseq_entails hnextKey (fun x s => ?_) (fun x s0 sf => ?_)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    · dsimp only [Spec.inImage, nextKeyInternalSpecCore, nextKeyInternalSpecX]
      rw [ProofLib.memRegion_zero, emp_sepConj]; exact Entails.refl _
    · dsimp only [Spec.inImage, nextKeyInternalSpecCore, nextKeyInternalSpecX]
      rw [ProofLib.memRegion_zero, emp_sepConj]; exact Entails.refl _
  unfold ChainSendKeyOkX
  refine sub_ok_conseq_entails
    (chainSendKey_ok_core (fun sp => by dsimp only [nextKeyInternalStackX, chainSendKeyStackX]; bv_kernel)
      himg hnextKey' hnextKeyPanic hshim halloc hdealloc)
    (fun x s => ?_) (fun x s0 sf => ?_) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · dsimp only [Spec.inImage, chainSendKeySpecCore, chainSendKeySpecX]
    rw [ProofLib.memRegion_zero, emp_sepConj]; exact Entails.refl _
  · dsimp only [Spec.inImage, chainSendKeySpecCore, chainSendKeySpecX]
    rw [ProofLib.memRegion_zero, emp_sepConj]; exact Entails.refl _

theorem chainSendKey_ok_ext_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkX img hkdf ext)
    (hA : AllocContractsX img A ext) :
    ChainSendKeyOkX img hkdf A ext :=
  chainSendKey_ok_of_contracts_x himg
    (nextKeyInternal_ok_ext_x himg hconcat hhkdf hA)
    (nextKeyInternal_panic_ok_ext_x himg)
    (hA.shim extHookStack (by decide) (by decide)) hA.alloc hA.dealloc

theorem chainSendKey_ok_of_contracts_ext {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hnextKey : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecExt hkdf A).inImage img))
    (hnextKeyPanic : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      (nextKeyInternalPanicSpecX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    ChainSendKeyOkExt img hkdf A ext := by
  have hnextKey' : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecCore hkdf A 1232).inImage img) := by
    refine sub_ok_conseq_entails hnextKey (fun x s => ?_) (fun x s0 sf => ?_)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    · dsimp only [Spec.inImage, nextKeyInternalSpecCore, nextKeyInternalSpecExt]
      rw [stackAt_nextKeyInternalExt_eq s.sp]; exact Entails.of_eq (by ac_rfl)
    · dsimp only [Spec.inImage, nextKeyInternalSpecCore, nextKeyInternalSpecExt]
      rw [stackAt_nextKeyInternalExt_eq s0.sp]; exact Entails.of_eq (by ac_rfl)
  unfold ChainSendKeyOkExt
  refine sub_ok_conseq_entails
    (chainSendKey_ok_core (fun sp => by dsimp only [nextKeyInternalStackX, chainSendKeyStackX]; bv_kernel)
      himg hnextKey' hnextKeyPanic hshim halloc hdealloc)
    (fun x s => ?_) (fun x s0 sf => ?_) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · dsimp only [Spec.inImage, chainSendKeySpecCore, chainSendKeySpecExt]
    rw [stackAt_chainSendKeyExt_eq s.sp]; exact Entails.of_eq (by ac_rfl)
  · dsimp only [Spec.inImage, chainSendKeySpecCore, chainSendKeySpecExt]
    rw [stackAt_chainSendKeyExt_eq s0.sp]; exact Entails.of_eq (by ac_rfl)

theorem chainSendKey_ok_ext_ext {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkExt img hkdf ext)
    (hA : AllocContractsX img A ext) :
    ChainSendKeyOkExt img hkdf A ext :=
  chainSendKey_ok_of_contracts_ext himg
    (nextKeyInternal_ok_ext_ext himg hconcat hhkdf hA)
    (nextKeyInternal_panic_ok_ext_x himg)
    (hA.shim extHookStack (by decide) (by decide)) hA.alloc hA.dealloc

abbrev chainSendKey_ok_ext := @chainSendKey_ok_ext_ext

/-! ## Relocatable `[LibsignalPlacement]` Proof (`blkPC_367`) -/

def from436Pre0 (A : RustAlloc) (s0 : State) (x : ChainSendKeyGhost)
    (self' : Chain) (ctr' : BitVec 32) (outKey : Bytes)
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) : SepProp :=
  memRegion x.out 40 ∗
  chainRepr A x.selfPtr self' ∗
  nextKeyOutAt (s0.sp - 132#64) ctr' outKey ∗
  stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
  sendKeyScratchAt s0.sp l0 l1 l2 ∗
  ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
  ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗
  calleeSavedSendKeyAt s0 ∗
  A.pool

def from380Pre0 (A : RustAlloc) (s0 : State) (x : ChainSendKeyGhost)
    (sendEpoch1 head1 : BitVec 64) (epochs2 : List ChainEpochGhost) (links2 : List ChainEpoch)
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) : SepProp :=
  memRegion x.out 40 ∗
  (x.selfPtr ↦₆₄ x.G.linksCap) ∗ ((x.selfPtr + 8#64) ↦₆₄ x.G.linksPtr) ∗
  ((x.selfPtr + 16#64) ↦₆₄ head1) ∗ ((x.selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links2.length) ∗
  vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
    x.G.linksCap x.G.linksPtr head1 (epochs2.zip links2) ∗
  ((x.selfPtr + 56#64) ↦₆₄ x.self.currentEpoch) ∗ ((x.selfPtr + 64#64) ↦₆₄ sendEpoch1) ∗
  chainRestSendKeyAt A x.selfPtr x.G x.self ∗
  stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
  sendKeyScratchAt s0.sp l0 l1 l2 ∗
  ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
  ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗
  memRegion (s0.sp - 132#64) 36 ∗
  calleeSavedSendKeyAt s0 ∗
  A.pool

theorem from380Pre_intro (A : RustAlloc) (s0 : State) (G : ChainGhost) (self : Chain)
    (sendEpoch1 head1 : BitVec 64) (epochs2 : List ChainEpochGhost) (links2 : List ChainEpoch)
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) :
    memRegion (s0.readReg64 (.gpr 8#5)) 40 ∗
    (s0.readReg64 (.gpr 0#5) ↦₆₄ G.linksCap) ∗ ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ G.linksPtr) ∗
    ((s0.readReg64 (.gpr 0#5) + 16#64) ↦₆₄ head1) ∗ ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 links2.length) ∗
    vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
      G.linksCap G.linksPtr head1 (epochs2.zip links2) ∗
    ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ self.currentEpoch) ∗ ((s0.readReg64 (.gpr 0#5) + 64#64) ↦₆₄ sendEpoch1) ∗
    chainRestSendKeyAt A (s0.readReg64 (.gpr 0#5)) G self ∗
    stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
    sendKeyScratchAt s0.sp l0 l1 l2 ∗
    ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
    ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗
    memRegion (s0.sp - 132#64) 36 ∗ calleeSavedSendKeyAt s0 ∗ A.pool ⊢
    from380Pre0 A s0 ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩
      sendEpoch1 head1 epochs2 links2 l0 l1 l2 q0 q1 q2 q3 := by
  unfold from380Pre0; sep_frame

open Lean Elab Tactic in
elab "wpp_call_nextKey_placed " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf; let hpcId ← freshIdent `hpc_sf; let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf; let hcsId ← freshIdent `hcs_sf; let hFId ← freshIdent `hF_sf
  let htrId ← freshIdent `htr_sf
  evalTactic (← `(tactic| (
    apply (NextKeyInternalFacts.SepWPp.call_allowPanic_lsCallInv_mid $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal))))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_nextKey_placed: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs; try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢)))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; apply onPanic_entails_of_oom; wp_norm_lhs)
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
    dsimp only [nextKeyInternalSpecX]
    simp (config := { decide := true }) only [sepConj_assoc, wp_norm, arm64_norm]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_; intro $htrId:ident; wp_norm_hyp $htrId)))
  foldStructEtaTarget; wpNormAndSplitHyp hspId; wpNormAndSplitHyp hcsId

open Lean Elab Tactic in
elab "wpp_call_nextKeyPanic_placed " hcall:term:max a:term:max hF:term:max hpan:term:max : tactic => do
  evalTactic (← `(tactic| (
    apply (NextKeyInternalFacts.SepWPp.call_allowPanic_lsCallInv_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal))))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_nextKeyPanic_placed: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs; try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢)))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; apply onPanic_entails_of_trace_eq $hpan; wp_norm_lhs)
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    wp_focus_close (wp_unfold_specs; intro _ _ _ _ _ _; refine NextKeyInternalFacts.SepWP.pure_left_focus _ (by sep_focus) fun h => False.elim h))))

set_option maxHeartbeats 800000 in
theorem sendKey_from_436_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hoom_ext : ((blkPC_367).rebase (blkPl_367).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (s0 : State) (hsp0_align : s0.spAligned = true) (x : ChainSendKeyGhost)
    (self' : Chain) (ctr' : BitVec 32) (outKey : Bytes) (hout_len : outKey.length = 32)
    (hsend_ok : Chain.sendKey hkdf x.self x.epoch = .ok (self', (ctr', outKey)))
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) {R : SepProp} (s : State)
    (hpc : s.pc = (blkPl_367).base + 436#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 208#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out) (hx29 : s.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hv : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_367).rebase (blkPl_367).base H) (s0.readReg64 (.gpr 30#5)) s
      (from436Pre0 A s0 x self' ctr' outKey l0 l1 l2 q0 q1 q2 q3)
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P' ⊢ (chainSendKeySpecX hkdf A).post x s0 sf))
      (fun sf P' => (sf.mem ⊨ P' ∗ R) → (sf.mem ⊨ (chainSendKeySpecX hkdf A).onPanic x s0 sf ∗ R)) := by
  unfold from436Pre0 nextKeyOutAt
  refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
  have hsp_align : s.spAligned = true := sp_sub_208_aligned hsp0_align hsp
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_norm_hyp hsp0_align; wp_norm_hyp hsp; wp_norm_hyp hsp_align; wp_norm_hyp hx19
  wp_norm_hyp hx29; wp_norm_hyp htr; wp_norm_hyp hv
  obtain ⟨k0, k1, k2, k3, _, hout_pack⟩ := exists_unpack64_of_length_32 hout_len
  have hout_unpack := hout_pack (s0.sp - 128#64)
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hout_unpack
  refine SepWPp.fold (Entails.of_eq hout_unpack) (by sep_focus) ?_
  apply SepWPp.of_sepWP (mid := (blkPl_367).base + 464#64)
  apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  wp_steps
  refine SepWP.fold (pointsTo32_cells4_entails_memRegion_36 s0.sp ctr' k0 k1 k2 k3) (by sep_focus) ?_
  have hstack_s0 : stackAt (s0.sp - 208#64) nextKeyInternalStackX = stackAt s.sp nextKeyInternalStackX := by rw [hsp]
  refine SepWP.fold (Entails.of_eq (hstack_s0.trans (stackAt_nextKeyInternalX_top_split s.sp))) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  wp_call hshim (); wp_steps
  have hstack_sf : stackAt s.sp extHookStack = stackAt sf.sp extHookStack :=
    congrArg (stackAt · extHookStack) (by wp_norm_goal)
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  wp_call halloc (32, 1); apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    wp_norm_hyp hoom_64; simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_; intro htrace_oom
    wp_norm_hyp htrace_oom; wp_norm_hyp hpost
    apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
    wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hoom_ext) fun hm => ?_
    exact allowPanic_sendKey_oom (s0 := s0)
      (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace_oom, hpost, htr])) hm
  · have hoom_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hmod1, htrace1⟩; wp_norm_hyp htrace1
    let p_key := sf_1.readReg64 (Reg.gpr 0#5)
    refine SepWPp.fold (Entails.of_eq (ChainNewFacts.memRegion_32_cells4 p_key)) (by sep_focus) ?_
    refine SepWPp.fold (Entails.of_eq (memRegion_40_ok_split x.out)) (by sep_focus) ?_
    refine SepWPp.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0)) (by sep_focus) ?_
    have hsp_sf1 : sf_1.sp = s0.sp - 208#64 := by rw [hsp_sf_1, hsp_sf, hsp]
    wp_norm_hyp hsp_sf1; sep_elim_exists; apply SepWPp.of_sepWP_ret; wp_steps
    refine SepWP.fold (Entails.of_eq (hout_pack p_key).symm) (by sep_focus) ?_
    refine SepWP.fold (sendKeyOkAt_intro A x.out ctr' p_key outKey hout_len hoom_64) (by sep_focus) ?_
    have hstack_sf1 : stackAt sf.sp extHookStack = stackAt (s0.sp - 208#64) extHookStack := by rw [hsp_sf, hsp]
    refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_top_split (s0.sp - 208#64)).symm) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (sendKeyScratchAt_def s0.sp l0 l1 l2)) (by sep_focus) ?_
    refine SepWP.fold (rejoin_stack_chainSendKeyX s0.sp l0 l1 l2 k0 k1 k2 k3
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
      (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5)) (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
      (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
      (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
    rw [hsend_ok]; dsimp only [sendKeyPostAt]
    refine Entails.pure_right (by wp_norm_goal) ?_; sep_frame

set_option maxHeartbeats 800000 in
theorem sendKey_from_380_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)))
    (hnextKeyPanic : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hoom_ext : ((blkPC_367).rebase (blkPl_367).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (s0 : State) (hsp0_align : s0.spAligned = true) (x : ChainSendKeyGhost)
    (sendEpoch1 head1 : BitVec 64) (epochs2 : List ChainEpochGhost) (links2 : List ChainEpoch)
    (i : Nat) (hi : i < links2.length) (hlen_le : links2.length ≤ x.G.linksCap.toNat)
    (hlen_eq : epochs2.length = links2.length)
    (hres_eq : Chain.sendKey hkdf x.self x.epoch = sendKeyTail hkdf x.self sendEpoch1 links2 i hi)
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) {R : SepProp} (s : State) (hF : LsCallInv lsmpl s.mem)
    (hpc : s.pc = (blkPl_367).base + 380#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out) (hx20 : s.readReg64 (.gpr 20#5) = x.selfPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 links2.length) (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 i)
    (hx29 : s.readReg64 (.gpr 29#5) = s0.sp - 96#64) (htr : s.trace = s0.trace)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_367).rebase (blkPl_367).base H) (s0.readReg64 (.gpr 30#5)) s
      (from380Pre0 A s0 x sendEpoch1 head1 epochs2 links2 l0 l1 l2 q0 q1 q2 q3)
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P' ⊢ (chainSendKeySpecX hkdf A).post x s0 sf))
      (fun sf P' => (sf.mem ⊨ P' ∗ R) → (sf.mem ⊨ (chainSendKeySpecX hkdf A).onPanic x s0 sf ∗ R)) := by
  have h_from436 := @sendKey_from_436_placed _ hkdf A H hshim halloc hoom_ext s0 hsp0_align x
  clear hshim halloc hoom_ext; unfold from380Pre0
  have hzip_le : (epochs2.zip links2).length ≤ x.G.linksCap.toNat := by simp [hlen_eq, hlen_le]
  have hzip_i : i < (epochs2.zip links2).length := by simp [hlen_eq, hi]
  refine SepWPp.fold (vecDequeRingBuf_get_physIdx A x.G.linksCap x.G.linksPtr head1 (epochs2.zip links2) hzip_le hzip_i) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hhead, hcap_lt, hptr⟩
  have hzip_geti : (epochs2.zip links2)[i] = (epochs2[i]'(by omega), links2[i]'hi) := by simp [List.getElem_zip]
  rw [hzip_geti]
  let gce_i := epochs2[i]'(by omega); let ce_i := links2[i]'hi
  let slot_i := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx head1.toNat x.G.linksCap.toNat i * 112)
  refine SepWPp.fold (chainEpochAt_unpack_send_next A gce_i ce_i slot_i) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hle_i, hcap_i, hptr_i⟩
  have ⟨hule_i, hult_i⟩ := ofNat_lt_props hi (by omega : links2.length < 2 ^ 63)
  have hmaddi := physIdx_madd_eq (ptr := x.G.linksPtr) hhead (Nat.lt_of_lt_of_le hi hlen_le) hcap_lt
  wp_norm_hyp hsp0_align; wp_norm_hyp hsp; wp_norm_hyp hsp_align; wp_norm_hyp hx19
  wp_norm_hyp hx20; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hx29
  wp_norm_hyp htr; wp_norm_hyp hv; wp_norm_hyp hule_i; wp_norm_hyp hult_i; wp_norm_hyp hmaddi
  refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 362) hF ?_
  wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  by_cases hbad : ce_i.send.next.length ≠ 32 ∨ ce_i.send.ctr = 0xffffffff#32
  · have hpan_tail : (sendKeyTail hkdf x.self sendEpoch1 links2 i hi).isPanic = true :=
      sendKeyTail_isPanic_of_bad hkdf x.self sendEpoch1 links2 i hi hbad
    have hpan_eq : (Chain.sendKey hkdf x.self x.epoch).isPanic = true := by rw [hres_eq]; exact hpan_tail
    have hlen_lt64 : ce_i.send.next.length < 2 ^ 64 := by omega
    change subroutine_ok _ _ (withLsCallInv lsmpl nextKeyInternalPanicSpecX) at hnextKeyPanic
    wpp_call_nextKeyPanic_placed hnextKeyPanic
      (⟨s0.sp - 132#64, gce_i.send.next.ptr, ce_i.send.next, slot_i + 48#64, ce_i.send.ctr⟩ : NextKeyInternalGhost)
      hinv1 hpan_eq
  · have hlen32 : ce_i.send.next.length = 32 := by omega
    have hctr_ne : ce_i.send.ctr ≠ 0xffffffff#32 := fun hc => hbad (Or.inr hc)
    have hlen32_bv : BitVec.ofNat 64 ce_i.send.next.length = 32#64 := by rw [hlen32]
    wp_norm_hyp hlen32_bv
    change subroutine_ok _ _ (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)) at hnextKey
    wpp_call_nextKey_placed hnextKey
      (⟨s0.sp - 132#64, gce_i.send.next.ptr, ce_i.send.next, slot_i + 48#64, ce_i.send.ctr⟩ : NextKeyInternalGhost) hinv1
    have hstack_s : stackAt s.sp nextKeyInternalStackX = stackAt (s0.sp - 208#64) nextKeyInternalStackX := by rw [hsp]
    refine SepWPp.fold (Entails.of_eq hstack_s) (by sep_focus) ?_
    refine SepWPp.fold (nextKeyOutAt_dup_len (s0.sp - 132#64) (ce_i.send.ctr + 1#32)
      (nextKeyOut hkdf ce_i.send.next ce_i.send.ctr)) (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_; intro hout_len
    have hnext'_len : (nextKeyNext hkdf ce_i.send.next ce_i.send.ctr).length = 32 :=
      nextKeyNext_length_of_nextKeyOut_length hout_len
    let send' : ChainEpochDirection :=
      { ce_i.send with next := nextKeyNext hkdf ce_i.send.next ce_i.send.ctr, ctr := ce_i.send.ctr + 1#32 }
    let links' := links2.set i { ce_i with send := send' }
    have hced := chainEpochDirectionAt_pack_nextKey A slot_i gce_i.send ce_i.send
      (nextKeyNext hkdf ce_i.send.next ce_i.send.ctr) (ce_i.send.ctr + 1#32) hlen32 hnext'_len hle_i hcap_i hptr_i
    have hce : chainEpochDirectionAt A slot_i gce_i.send send' ∗
        chainEpochDirectionAt A (slot_i + 56#64) gce_i.recv ce_i.recv ⊢
        chainEpochAt A (gce_i, { ce_i with send := send' }) slot_i := Entails.refl _
    have hset := vecDequeRingBuf_set_physIdx A x.G.linksCap x.G.linksPtr head1 (epochs2.zip links2)
      (gce_i, { ce_i with send := send' }) hhead hcap_lt hptr hzip_le hzip_i
    dsimp only at hset
    have hzip_set : (epochs2.zip links2).set i (gce_i, { ce_i with send := send' }) = epochs2.zip links' :=
      zip_set_snd epochs2 links2 i gce_i _ (List.getElem?_eq_getElem (by omega))
    rw [hzip_set] at hset
    have hlen_links' : links'.length = links2.length := List.length_set
    have hpack := chainRepr_pack_sendKey A x.selfPtr x.G x.self head1 epochs2 links' sendEpoch1 (by omega)
    rw [hlen_links'] at hpack
    refine SepWPp.fold hced (by sep_focus) ?_; refine SepWPp.fold hce (by sep_focus) ?_
    refine SepWPp.fold hset (by sep_focus) ?_; refine SepWPp.fold hpack (by sep_focus) ?_
    have h436_pre :
        chainRepr A x.selfPtr { x.self with sendEpoch := sendEpoch1, links := links' } ∗
        nextKeyOutAt (s0.sp - 132#64) (ce_i.send.ctr + 1#32) (nextKeyOut hkdf ce_i.send.next ce_i.send.ctr) ∗
        A.pool ∗ stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗ memRegion x.out 40 ∗
        sendKeyScratchAt s0.sp l0 l1 l2 ∗ ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
        ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗ calleeSavedSendKeyAt s0 ⊢
        from436Pre0 A s0 x { x.self with sendEpoch := sendEpoch1, links := links' }
          (ce_i.send.ctr + 1#32) (nextKeyOut hkdf ce_i.send.next ce_i.send.ctr) l0 l1 l2 q0 q1 q2 q3 := by
      unfold from436Pre0; sep_frame
    refine SepWPp.fold h436_pre (by sep_focus) ?_
    have htail_ok := sendKeyTail_eq_ok hkdf x.self sendEpoch1 links2 i hi hlen32 hctr_ne
    dsimp only at htail_ok
    have hsend_ok : Chain.sendKey hkdf x.self x.epoch =
        .ok ({ x.self with sendEpoch := sendEpoch1, links := links' },
             (ce_i.send.ctr + 1#32, nextKeyOut hkdf ce_i.send.next ce_i.send.ctr)) :=
      hres_eq.trans htail_ok
    rw [sepConj_emp]
    have h436_call := h_from436
      { x.self with sendEpoch := sendEpoch1, links := links' }
      (ce_i.send.ctr + 1#32) (nextKeyOut hkdf ce_i.send.next ce_i.send.ctr)
      hout_len hsend_ok l0 l1 l2 q0 q1 q2 q3 (R := R) sf hpc_sf hrun_sf
      (hsp_sf.trans hsp) (by wp_norm_goal) (by wp_norm_goal) (htr_sf.trans htr) (by wp_norm_goal)
    simpa only [sepConj_assoc, satisfies_pure_sepConj] using h436_call

theorem SepWPp.seq_entails_lsCallInv {prog : Program} {pl : Obj.MultiPlacement}
    {mid target : BitVec 64} {s : State} {P P_mid : SepProp}
    {φ : State → Prop} {post panic_post : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => φ sm ∧ (Pm ⊢ P_mid)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LsCallInv pl sm.mem → φ sm →
      SepWPp prog target sm P_mid post panic_post) :
    SepWPp prog target s P post panic_post := by
  intro R hm hL
  rcases h1.elim hm hL with ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hφ, hent⟩ | ⟨_, hfalse⟩⟩
  · have hmm' : sm.mem ⊨ P_mid ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps2, hout⟩ :=
      h2 sm hpcm hrunm (hF.of_steps hsteps1) hφ R hmm' (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · rw [satisfies_pure_sepConj] at hfalse; exact False.elim hfalse.1

theorem sendKey_from_344_full_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)))
    (hnextKeyPanic : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hoom_ext : ((blkPC_367).rebase (blkPl_367).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (s0 : State) (hsp0_align : s0.spAligned = true) (x : ChainSendKeyGhost)
    (head1 : BitVec 64) (epochs1 : List ChainEpochGhost) (links1 : List ChainEpoch)
    (h1 : 1 < links1.length) (hlen_le : links1.length ≤ x.G.linksCap.toNat) (hlen_eq : epochs1.length = links1.length)
    (hres_eq :
      let h0 : 0 < links1.length := by omega
      let links2 := links1.set 0 { links1[0] with send := links1[0].send.clearNext }
      have h1' : 1 < links2.length := by simp [links2]; omega
      Chain.sendKey hkdf x.self x.epoch = sendKeyTail hkdf x.self x.epoch links2 1 h1')
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) {R : SepProp} (s : State) (hF : LsCallInv lsmpl s.mem)
    (hpc : s.pc = (blkPl_367).base + 344#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64) (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out) (hx20 : s.readReg64 (.gpr 20#5) = x.selfPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 links1.length)
    (hx29 : s.readReg64 (.gpr 29#5) = s0.sp - 96#64) (htr : s.trace = s0.trace)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_367).rebase (blkPl_367).base H) (s0.readReg64 (.gpr 30#5)) s
      (from380Pre0 A s0 x x.epoch head1 epochs1 links1 l0 l1 l2 q0 q1 q2 q3)
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P' ⊢ (chainSendKeySpecX hkdf A).post x s0 sf))
      (fun sf P' => (sf.mem ⊨ P' ∗ R) → (sf.mem ⊨ (chainSendKeySpecX hkdf A).onPanic x s0 sf ∗ R)) := by
  have h0 : 0 < links1.length := by omega
  let links2 := links1.set 0 { links1[0] with send := links1[0].send.clearNext }
  have h1' : 1 < links2.length := by simp [links2]; omega
  have hlen2_eq : links2.length = links1.length := List.length_set
  let F_344 : SepProp :=
    memRegion x.out 40 ∗ ((x.selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links1.length) ∗
    ((x.selfPtr + 56#64) ↦₆₄ x.self.currentEpoch) ∗ ((x.selfPtr + 64#64) ↦₆₄ x.epoch) ∗
    chainRestSendKeyAt A x.selfPtr x.G x.self ∗ stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
    sendKeyScratchAt s0.sp l0 l1 l2 ∗ ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
    ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗ memRegion (s0.sp - 132#64) 36 ∗
    calleeSavedSendKeyAt s0 ∗ A.pool
  have hstep344 := sendKey_from_344_placed (A := A) (H := H)
    x.selfPtr x.G.linksCap x.G.linksPtr head1 epochs1 links1 h0 hlen_le hlen_eq s hpc hrun hsp_align hx20
  dsimp only at hstep344
  have hpre344 : from380Pre0 A s0 x x.epoch head1 epochs1 links1 l0 l1 l2 q0 q1 q2 q3 ⊢
      clearFrontPre A x.selfPtr x.G.linksCap x.G.linksPtr head1 epochs1 links1 ∗ F_344 := by
    unfold from380Pre0 clearFrontPre F_344; sep_frame
  have hpost344 : clearFrontPre A x.selfPtr x.G.linksCap x.G.linksPtr head1 epochs1 links2 ∗ F_344 ⊢
      from380Pre0 A s0 x x.epoch head1 epochs1 links2 l0 l1 l2 q0 q1 q2 q3 := by
    unfold from380Pre0 clearFrontPre F_344; rw [hlen2_eq]; sep_frame
  refine SepWPp.seq_entails_lsCallInv hF (SendKeyTailHelpers.SepWP.conseq_entails hstep344 hpre344 hpost344) ?_
  rintro sm hpcm hrunm hFm ⟨hsp_m, hsp_align_m, hx19_m, hx20_m, hx27_m, hx28_m, hx29_m, htr_m, hv_m⟩
  exact sendKey_from_380_placed hnextKey hnextKeyPanic hshim halloc hoom_ext s0 hsp0_align x
    x.epoch head1 epochs1 links2 1 h1' (by rw [hlen2_eq]; exact hlen_le)
    (by rw [hlen2_eq]; exact hlen_eq) hres_eq l0 l1 l2 q0 q1 q2 q3
    sm hFm hpcm hrunm (hsp_m.trans hsp) hsp_align_m (hx19_m.trans hx19) hx20_m
    (by rw [hlen2_eq]; exact hx27_m.trans hx27) hx28_m (hx29_m.trans hx29) (htr_m.trans htr) (hv_m.trans hv)

set_option maxHeartbeats 1600000 in
theorem chainSendKey_placed_ok_of_contracts [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)))
    (hnextKeyPanic : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hdealloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack A extHookStack))
    (hoom_ext : ((blkPC_367).rebase (blkPl_367).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    ChainSendKeyPlacedOkX hkdf A H := by
  unfold ChainSendKeyPlacedOkX; wpp_init x s0
  have hsp0_align : s0.spAligned = true := hsp_align
  rcases x with ⟨out, selfPtr, epoch, G, self⟩
  dsimp only [withLsCallInv, chainSendKeySpecX] at *
  refine SepWPp.post_of_entails ?_
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨‹LibsignalRoLoaded lsmpl s0.mem›, ‹LibsignalCodeLoaded lsmpl s0.mem›⟩
  subst out selfPtr epoch
  refine SepWPp.rw_pre (by rw [stackAt_chainSendKeyX_split s0.sp]) ?_
  sep_elim_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c_18 c_17 c_16 c_15 c_14 c_13 c_12
  refine SepWPp.fold (chainAt_unpack_sendKey A (s0.readReg64 (.gpr 0#5)) G self) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hlen_eq, hlen_le, hcap_lt, hptr⟩
  have h_from380 := @sendKey_from_380_placed _ hkdf A H hnextKey hnextKeyPanic hshim halloc hoom_ext s0 hsp0_align
    ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩
  have h_from344 := @sendKey_from_344_full_placed _ hkdf A H hnextKey hnextKeyPanic hshim halloc hoom_ext s0 hsp0_align
    ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩
  have h_poploop := @sendKey_pop_loop_placed _ A H hdealloc (s0.readReg64 (.gpr 0#5)) G.linksCap G.linksPtr hcap_lt
  clear hnextKey hnextKeyPanic hshim halloc hdealloc hoom_ext
  by_cases hlt_send : s0.readReg64 (.gpr 1#5) < self.sendEpoch
  · have ⟨hult_send, hule_send⟩ := lt_props hlt_send
    wp_norm_hyp hult_send; wp_norm_hyp hule_send
    refine SepWPp.fold (Entails.of_eq (memRegion_40_err_split (s0.readReg64 (.gpr 8#5)))) (by sep_focus) ?_
    sep_elim_err4 w0 b0 w2 c_22; apply SepWPp.of_sepWP_ret; wp_steps
    refine SepWP.fold (sendKeyErrAt_sendKeyEpochDecreased_intro (s0.readReg64 (.gpr 8#5))
      self.sendEpoch (s0.readReg64 (.gpr 1#5))) (by sep_focus) ?_
    refine SepWP.fold (chainRepr_pack_sendKey A (s0.readReg64 (.gpr 0#5)) G self
      G.linksHead G.epochs self.links self.sendEpoch hlen_eq) (by sep_focus) ?_
    refine SepWP.fold (rejoin_stack_chainSendKeyX s0.sp c_18 c_17 c_16 c_15 c_14 c_13 c_12
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
      (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5)) (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
      (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
      (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
    rw [sendKey_of_lt hkdf self (s0.readReg64 (.gpr 1#5)) hlt_send]; dsimp only [sendKeyPostAt]
    refine Entails.pure_right (by wp_norm_goal) ?_; sep_frame
  · have ⟨hult_send, hule_send⟩ := ge_props hlt_send
    wp_norm_hyp hult_send; wp_norm_hyp hule_send
    by_cases hgt_curr : s0.readReg64 (.gpr 1#5) > self.currentEpoch
    · have ⟨hult_curr, hule_curr⟩ := lt_props hgt_curr
      wp_norm_hyp hult_curr; wp_norm_hyp hule_curr
      refine SepWPp.fold (Entails.of_eq (memRegion_40_err_split (s0.readReg64 (.gpr 8#5)))) (by sep_focus) ?_
      sep_elim_err4 w0 b0 w2 c_22; apply SepWPp.of_sepWP_ret; wp_steps
      refine SepWP.fold (sendKeyErrAt_epochOutOfRange_intro (s0.readReg64 (.gpr 8#5))
        (s0.readReg64 (.gpr 1#5)) w0) (by sep_focus) ?_
      refine SepWP.fold (chainRepr_pack_sendKey A (s0.readReg64 (.gpr 0#5)) G self
        G.linksHead G.epochs self.links self.sendEpoch hlen_eq) (by sep_focus) ?_
      refine SepWP.fold (rejoin_stack_chainSendKeyX s0.sp c_18 c_17 c_16 c_15 c_14 c_13 c_12
        (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
        (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5)) (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
        (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
        (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
      rw [sendKey_of_epochIdx_err hkdf self (s0.readReg64 (.gpr 1#5)) _ hlt_send
        (epochIdx_of_gt self (s0.readReg64 (.gpr 1#5)) hgt_curr)]
      dsimp only [sendKeyPostAt]; refine Entails.pure_right (by wp_norm_goal) ?_; sep_frame
    · have ⟨hult_curr, hule_curr⟩ := ge_props hgt_curr
      wp_norm_hyp hult_curr; wp_norm_hyp hule_curr
      by_cases hback_ge : (self.currentEpoch - s0.readReg64 (.gpr 1#5)).toNat ≥ self.links.length
      · have ⟨hult_back, hule_back⟩ := back_ge_props hback_ge (by omega : self.links.length < 2 ^ 63)
        wp_norm_hyp hult_back; wp_norm_hyp hule_back
        refine SepWPp.fold (Entails.of_eq (memRegion_40_err_split (s0.readReg64 (.gpr 8#5)))) (by sep_focus) ?_
        sep_elim_err4 w0 b0 w2 c_22; apply SepWPp.of_sepWP_ret; wp_steps
        refine SepWP.fold (sendKeyErrAt_epochOutOfRange_intro (s0.readReg64 (.gpr 8#5))
          (s0.readReg64 (.gpr 1#5)) w0) (by sep_focus) ?_
        refine SepWP.fold (chainRepr_pack_sendKey A (s0.readReg64 (.gpr 0#5)) G self
          G.linksHead G.epochs self.links self.sendEpoch hlen_eq) (by sep_focus) ?_
        refine SepWP.fold (rejoin_stack_chainSendKeyX s0.sp c_18 c_17 c_16 c_15 c_14 c_13 c_12
          (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
          (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5)) (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
          (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
          (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
        rw [sendKey_of_epochIdx_err hkdf self (s0.readReg64 (.gpr 1#5)) _ hlt_send
          (epochIdx_of_back_ge self (s0.readReg64 (.gpr 1#5)) hgt_curr hback_ge)]
        dsimp only [sendKeyPostAt]; refine Entails.pure_right (by wp_norm_goal) ?_; sep_frame
      · have hback_lt : (self.currentEpoch - s0.readReg64 (.gpr 1#5)).toNat < self.links.length := by omega
        have ⟨hult_back, hule_back⟩ := back_lt_props hback_lt (by omega : self.links.length < 2 ^ 63)
        let idx0 := self.links.length - 1 - (self.currentEpoch - s0.readReg64 (.gpr 1#5)).toNat
        have hidx0_lt : idx0 < self.links.length := by dsimp [idx0]; omega
        have hidx_eq : self.epochIdx (s0.readReg64 (.gpr 1#5)) = .ok idx0 :=
          epochIdx_of_lt self (s0.readReg64 (.gpr 1#5)) hgt_curr hback_lt
        have hadd_not : BitVec.ofNat 64 self.links.length + ~~~(self.currentEpoch - s0.readReg64 (.gpr 1#5)) =
            BitVec.ofNat 64 idx0 := add_not_eq_ofNat_sub hback_lt
        wp_norm_hyp hult_back; wp_norm_hyp hule_back; wp_norm_hyp hadd_not
        by_cases heq_send : self.sendEpoch = s0.readReg64 (.gpr 1#5)
        · have heq_beq : (self.sendEpoch == s0.readReg64 (.gpr 1#5)) = true := by simp [heq_send]
          have heq_sub : (self.sendEpoch - s0.readReg64 (.gpr 1#5) == 0#64) = true := by simp [heq_send]
          wp_norm_hyp heq_beq; wp_norm_hyp heq_sub
          have hres_eq := sendKey_eq_tail_of_eq hkdf self (s0.readReg64 (.gpr 1#5)) idx0 hlt_send hidx_eq hidx0_lt heq_send
          refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_367).base + 380#64) hinv0 ?_; wp_steps
          refine SepWP.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0).symm) (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (sendKeyScratchAt_def s0.sp c_18 c_17 c_16).symm) (by sep_focus) ?_
          refine SepWP.fold (from380Pre_intro A s0 G self self.sendEpoch G.linksHead G.epochs self.links
            c_18 c_17 c_16 c_15 c_14 c_13 c_12) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv1; rw [sepConj_emp]
          exact h_from380 self.sendEpoch G.linksHead G.epochs self.links idx0 hidx0_lt hlen_le hlen_eq hres_eq
            c_18 c_17 c_16 c_15 c_14 c_13 c_12 _ hinv1 (by wp_norm_goal) (by wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        · have ⟨hne_beq, hne_sub, hne_add⟩ := ne_branch_props heq_send
          wp_norm_hyp hne_beq; wp_norm_hyp hne_sub; wp_norm_hyp hne_add
          rcases hidx0_cases : idx0 with _ | _ | k
          · have h0_lt : 0 < self.links.length := by omega
            have hidx_0 : self.epochIdx (s0.readReg64 (.gpr 1#5)) = .ok 0 := by simpa [hidx0_cases] using hidx_eq
            have hres_eq := sendKey_eq_tail_of_ne_zero hkdf self (s0.readReg64 (.gpr 1#5)) hlt_send hidx_0 h0_lt heq_send
            have hadd_not0 : BitVec.ofNat 64 self.links.length + ~~~(self.currentEpoch - s0.readReg64 (.gpr 1#5)) = 0#64 := by
              simpa [hidx0_cases] using hadd_not
            wp_norm_hyp hadd_not0
            refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_367).base + 380#64) hinv0 ?_; wp_steps
            refine SepWP.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0).symm) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (sendKeyScratchAt_def s0.sp c_18 c_17 c_16).symm) (by sep_focus) ?_
            refine SepWP.fold (from380Pre_intro A s0 G self (s0.readReg64 (.gpr 1#5)) G.linksHead G.epochs self.links
              c_18 c_17 c_16 c_15 c_14 c_13 c_12) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv1; rw [sepConj_emp]
            exact h_from380 (s0.readReg64 (.gpr 1#5)) G.linksHead G.epochs self.links 0 h0_lt hlen_le hlen_eq hres_eq
              c_18 c_17 c_16 c_15 c_14 c_13 c_12 _ hinv1 (by wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
          · have h1_lt : 1 < self.links.length := by omega
            have hidx_1 : self.epochIdx (s0.readReg64 (.gpr 1#5)) = .ok 1 := by simpa [hidx0_cases] using hidx_eq
            have hres_eq := sendKey_eq_tail_of_ne_pos hkdf self (s0.readReg64 (.gpr 1#5)) 1
              hlt_send hidx_1 h1_lt heq_send (by omega)
            dsimp only [Nat.sub_self, List.drop_zero] at hres_eq
            have hadd_not1 : BitVec.ofNat 64 self.links.length + ~~~(self.currentEpoch - s0.readReg64 (.gpr 1#5)) = 1#64 := by
              simpa [hidx0_cases] using hadd_not
            wp_norm_hyp hadd_not1
            refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_367).base + 344#64) hinv0 ?_; wp_steps
            refine SepWP.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0).symm) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (sendKeyScratchAt_def s0.sp c_18 c_17 c_16).symm) (by sep_focus) ?_
            refine SepWP.fold (from380Pre_intro A s0 G self (s0.readReg64 (.gpr 1#5)) G.linksHead G.epochs self.links
              c_18 c_17 c_16 c_15 c_14 c_13 c_12) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv1; rw [sepConj_emp]
            exact h_from344 G.linksHead G.epochs self.links h1_lt hlen_le hlen_eq hres_eq
              c_18 c_17 c_16 c_15 c_14 c_13 c_12 _ hinv1 (by wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
          · have hk_lt : k + 2 < self.links.length := by omega
            have hidx_k : self.epochIdx (s0.readReg64 (.gpr 1#5)) = .ok (k + 2) := by simpa [hidx0_cases] using hidx_eq
            have hres_eq := sendKey_eq_tail_of_ne_pos hkdf self (s0.readReg64 (.gpr 1#5)) (k + 2)
              hlt_send hidx_k hk_lt heq_send (by omega)
            dsimp only [Nat.add_sub_cancel] at hres_eq
            have hadd_notk : BitVec.ofNat 64 self.links.length + ~~~(self.currentEpoch - s0.readReg64 (.gpr 1#5)) =
                BitVec.ofNat 64 (k + 2) := by simpa [hidx0_cases] using hadd_not
            have ⟨hult_k2, hule_k2⟩ := k_plus_2_ge_2_props k (by omega)
            wp_norm_hyp hadd_notk; wp_norm_hyp hult_k2; wp_norm_hyp hule_k2
            refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_367).base + 164#64) hinv0 ?_; wp_steps
            refine SepWP.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0).symm) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_top_split (s0.sp - 208#64))) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv1
            let F_loop : SepProp :=
              memRegion (s0.readReg64 (.gpr 8#5)) 40 ∗
              (s0.readReg64 (.gpr 0#5) ↦₆₄ G.linksCap) ∗ ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ G.linksPtr) ∗
              ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ self.currentEpoch) ∗
              ((s0.readReg64 (.gpr 0#5) + 64#64) ↦₆₄ s0.readReg64 (.gpr 1#5)) ∗
              chainRestSendKeyAt A (s0.readReg64 (.gpr 0#5)) G self ∗
              memRegion (s0.sp - 208#64 - BitVec.ofNat 64 nextKeyInternalStackX) 176 ∗
              memRegion (s0.sp - 208#64) 8 ∗ ((s0.sp - 176#64) ↦₆₄ c_15) ∗ ((s0.sp - 168#64) ↦₆₄ c_14) ∗
              ((s0.sp - 160#64) ↦₆₄ c_13) ∗ ((s0.sp - 152#64) ↦₆₄ c_12) ∗ memRegion (s0.sp - 144#64) 12 ∗
              memRegion (s0.sp - 132#64) 36 ∗ calleeSavedSendKeyAt s0
            have hpost_loop :
                popLoopPre A (s0.sp - 208#64) (s0.readReg64 (.gpr 0#5)) G.linksCap G.linksPtr
                  (iterHead G.linksCap.toNat G.linksHead (k + 1)) (iterL2 c_16 G.epochs (k + 1))
                  (G.epochs.drop (k + 1)) (self.links.drop (k + 1)) ∗ F_loop ⊢
                from380Pre0 A s0 ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩
                  (s0.readReg64 (.gpr 1#5)) (iterHead G.linksCap.toNat G.linksHead (k + 1))
                  (G.epochs.drop (k + 1)) (self.links.drop (k + 1))
                  G.linksPtr G.linksCap (iterL2 c_16 G.epochs (k + 1)) c_15 c_14 c_13 c_12 := by
              unfold popLoopPre F_loop from380Pre0 sendKeyScratchAt
              rw [stackAt_nextKeyInternalX_top_split (s0.sp - 208#64)]
              simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]; sep_frame
            refine SepWPp.seq_entails_lsCallInv hinv1
              (SendKeyTailHelpers.SepWP.conseq_entails (F := F_loop)
                (h_poploop k G.linksHead c_16 G.epochs self.links (by omega) hlen_le hlen_eq
                  _ (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
                  (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
                (by unfold popLoopPre F_loop
                    simp (config := { decide := true }) only [wp_norm, arm64_norm, bv_sub_add_lit, Nat.reduceSub]
                    sep_frame)
                (by simp (config := { decide := true }) only [wp_norm, arm64_norm]; exact hpost_loop)) ?_
            rintro sm hpcm hrunm hFm ⟨hsp_m, hsp_align_m, hx19_m, hx20_m, hx22_m, hx27_m, hx28_m, hx29_m, htr_m, hvregs_m⟩
            exact h_from344
              (iterHead G.linksCap.toNat G.linksHead (k + 1))
              (G.epochs.drop (k + 1)) (self.links.drop (k + 1))
              (by simp; omega) (by simp; omega) (by simp [hlen_eq]) hres_eq
              G.linksPtr G.linksCap (iterL2 c_16 G.epochs (k + 1)) c_15 c_14 c_13 c_12
              sm hFm hpcm hrunm (by rw [hsp_m]; wp_norm_goal) hsp_align_m
              (by rw [hx19_m]; wp_norm_goal) hx20_m hx27_m
              (by rw [hx29_m]; wp_norm_goal) (by rw [htr_m]; wp_norm_goal) (by rw [hvregs_m]; wp_norm_goal)

abbrev chainSendKey_placed_ok := @chainSendKey_placed_ok_of_contracts

end CryptoVerification.SpqrV1.ChainProofs
