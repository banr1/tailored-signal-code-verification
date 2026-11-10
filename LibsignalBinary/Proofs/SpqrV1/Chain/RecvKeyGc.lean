/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetLoop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyPop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `KeyHistory::gc` and Post-GC Tail Proofs for `<spqr::chain::Chain>::recv_key`

Proves `KeyHistory::gc` (`+616` and loop at `+932`) and the post-GC `next_key_internal` +
output-key allocation tail (`+660`) for `<spqr::chain::Chain>::recv_key` (Block `366`) in
fixed-image and relocatable `[LibsignalPlacement]` forms.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout
open ChainAddEpochFacts ChainNewFacts NextKeyInternalFacts ChainSendKeyFacts
open RecvKeyDecodes

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  nextKeyInternal_fnOff chainRecvKey_fnOff doReserve7_fnOff shim_fnOff alloc_fnOff dealloc_fnOff handleError_fnOff
  panicAddOverflow_fnOff panicSubOverflow_fnOff corePanic_fnOff assertFailedUsize_fnOff expectFailed_fnOff sliceIndexFail_fnOff
  (ls_lemma% fnOff "<spqr::chain::ChainEpochDirection>::next_key_internal") (ls_lemma% fnOff "<spqr::chain::Chain>::recv_key")
  (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2") (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc") (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow") (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_stub% "core::panicking::panic_const::panic_const_sub_overflow") (ls_hook% "core::panicking::panic_const::panic_const_sub_overflow")
  (ls_stub% "core::panicking::assert_failed::<usize, usize>") (ls_hook% "core::panicking::assert_failed::<usize, usize>")
  (ls_stub% "core::panicking::panic") (ls_hook% "core::panicking::panic")
  (ls_stub% "core::option::expect_failed") (ls_hook% "core::option::expect_failed")
  (ls_stub% "core::slice::index::slice_index_fail") (ls_hook% "core::slice::index::slice_index_fail")

theorem panic_at_core_panic_recvKey (base : BitVec 64) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase base (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase base (Rust.withPanics ext)).fnAddr chainRecvKeyName +
        bv% (ls_off% "core::panicking::panic" - ls_off% "<spqr::chain::Chain>::recv_key")) = some Rust.panicked :=
  panic_at_sym_ext base ext chainRecvKeyName corePanicName
    (num% (ls_off% "core::panicking::panic" - ls_off% "<spqr::chain::Chain>::recv_key"))
    (by rw [chainRecvKey_fnOff, corePanic_fnOff]) (hp := by simp [Rust.isPanicSymbol, corePanicName])

theorem panic_at_slice_recvKey (base : BitVec 64) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase base (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase base (Rust.withPanics ext)).fnAddr chainRecvKeyName +
        bv% (ls_off% "core::slice::index::slice_index_fail" - ls_off% "<spqr::chain::Chain>::recv_key")) = some Rust.panicked :=
  panic_at_sym_ext base ext chainRecvKeyName sliceIndexFailSymName
    (num% (ls_off% "core::slice::index::slice_index_fail" - ls_off% "<spqr::chain::Chain>::recv_key"))
    (by rw [chainRecvKey_fnOff, sliceIndexFail_fnOff]) (hp := by simp [Rust.isPanicSymbol, sliceIndexFailSymName])

local elab "recv_key_fetches " b:term:max H:term:max : tactic => do
  let e ← CodeLookup.lookup `CryptoVerification.libsignalSessionCode .fnOff "<spqr::chain::Chain>::recv_key"
  let off := Lean.Syntax.mkNumLit (toString e.val)
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    code_fetches libsignalSessionCode libsignalSessionBin $b $H $(Lean.mkCIdent e.decl) $off 1248))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  AgreeStateSimp.sp_setPC_pre AgreeStateSimp.sp_setMem_setPC_pre
  AgreeStateSimp.readReg64_setPC_pre AgreeStateSimp.readReg64_setMem_setPC_pre
  AgreeStateSimp.readReg32_setPC_pre AgreeStateSimp.readReg32_setMem_setPC_pre

/-! ## `next_key_internal` Call Helpers for `SepWPp` -/

private theorem onPanic_entails_of_trace_eq {s0 s sf : State} {P : Prop} {F : SepProp}
    (hP : P) (hs : s.trace = s0.trace) :
    (⌜sf.trace = s.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(P ∧ sf.trace = s0.trace) ∨ (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  exact Entails.pure_left fun htr => Entails.pure_right (Or.inl ⟨hP, htr.trans hs⟩) (entails_anyHeap _)

private theorem onPanic_entails_of_oom {s0 s sf : State} {P : Prop} {F : SepProp}
    (hs : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(P ∧ sf.trace = s0.trace) ∨ (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hoom, hpre⟩ => ?_
  have hoom0 : allocFailedIn s0 sf := by unfold allocFailedIn at hoom ⊢; rw [← hs]; exact hoom
  have hpre0 : s0.trace <+: sf.trace := by rw [← hs]; exact hpre
  exact Entails.pure_right (Or.inr ⟨hoom0, hpre0⟩) (entails_anyHeap _)

private theorem SepWPp.call_allowPanic_inImage {α : Type} {prog : Program} {img : Obj.Image}
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
  exact SepWPp.call_wpp_frozen (x := x) (F := F) hcall hF.1 hF.2 hpc hrun hsp_align hlr
    (fun R' hm => by
      dsimp only [Spec.inImage]; rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hF.1, hF.2⟩, hpre R' hm⟩)
    (fun sf code R' _ hpost => by
      dsimp only [Spec.inImage] at hpost; rw [hexit_eq.1] at hpost
      exact not_satisfies_false_sepConj hpost)
    (fun sf _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sf)) hm')
    (fun sf hpcm hrunm hspm hcsm hfz hsym => hnext sf hpcm hrunm hspm hcsm ⟨hfz, hsym⟩)
    (fun sf R' _ hpost => by
      dsimp only [Spec.inImage] at hpost; rw [hexit_eq.2] at hpost
      exact (not_satisfies_false_sepConj hpost).elim)

open Lean Elab Tactic in
elab "wpp_call_nextKey_recv " hcall:term:max a:term:max hF:term:max : tactic => do
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
    | throwError "wpp_call_nextKey_recv: unexpected subgoals"
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
    dsimp only [nextKeyInternalSpecX, nextKeyInternalSpecRecvCore]
    simp (config := { decide := true }) only [sepConj_assoc, wp_norm, arm64_norm]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    intro $htrId:ident
    wp_norm_hyp $htrId
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId

open Lean Elab Tactic in
elab "wpp_call_nextKeyPanic_recv " hcall:term:max a:term:max hF:term:max hpan:term:max : tactic => do
  evalTactic (← `(tactic| (
    apply (NextKeyInternalFacts.SepWPp.call_allowPanic_inImage_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_nextKeyPanic_recv: unexpected subgoals"
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

theorem recvKey_nextKeyOutAt_dup_len (out : BitVec 64) (ctr : BitVec 32) (key : List (BitVec 8)) :
    nextKeyOutAt out ctr key ⊢ ⌜key.length = 32⌝ ∗ nextKeyOutAt out ctr key := by
  unfold nextKeyOutAt
  refine Entails.pure_left fun hlen => ?_
  exact Entails.pure_right hlen (Entails.pure_right hlen (Entails.refl _))

theorem recvKey_nextKeyNext_length_of_nextKeyOut_length {hkdf : HkdfFn} {next : Bytes} {ctr : BitVec 32}
    (h : (nextKeyOut hkdf next ctr).length = 32) :
    (nextKeyNext hkdf next ctr).length = 32 := by
  unfold nextKeyOut at h
  unfold nextKeyNext
  rw [List.length_take, List.length_drop] at h
  rw [List.length_take]
  omega

theorem nextKeyInternal_isError_of_bad (hkdf : HkdfFn) {next : Bytes} {ctr : BitVec 32}
    (hbad : next.length ≠ 32 ∨ ctr = 0xffffffff#32) :
    ∃ p, ChainEpochDirection.nextKeyInternal hkdf next ctr = .error p := by
  unfold ChainEpochDirection.nextKeyInternal
  rcases hbad with hlen | hctr
  · have h1 : (next.length != 32) = true := by simp [hlen]
    exact ⟨.nextKeyBadLen, by simp [h1]⟩
  · by_cases hlen : next.length = 32
    · have h1 : (next.length != 32) = false := by simp [hlen]
      have h2 : (ctr == 0xffffffff#32) = true := by simp [hctr]
      exact ⟨.ctrOverflow, by simp [h1, h2]⟩
    · have h1 : (next.length != 32) = true := by simp [hlen]
      exact ⟨.nextKeyBadLen, by simp [h1]⟩

/-! ## Post-GC `next_key_internal` and Output `Vec<u8>` Tail at `+660` -/

set_option maxHeartbeats 800000 in
set_option maxRecDepth 400000 in
/-- Post-GC tail of `recv_key` at `+660` (`+660 .. +708` -> epilogue). -/
theorem recvKey_from_660 {extra : Nat} {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hsub_extra : ∀ sp : BitVec 64,
      sp - 128#64 - BitVec.ofNat 64 (extra + nextKeyInternalStackX) =
        sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX))
    (hnextKey : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecRecvCore hkdf A extra).inImage img))
    (hnextKeyPanic : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName) (nextKeyInternalPanicSpecX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName) ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName) ((rustAllocSpecWithStack A extHookStack).inImage img))
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (prevPin : VecPin) (recv2 : ChainEpochDirection)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat) (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64) (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_le : recv2.next.length ≤ gce.recv.next.cap.toNat) (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63) (hn_ptr : gce.recv.next.ptr ≠ 0)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let (next', ctr', (_, outKey)) ← ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
      let recv' := { recv2 with next := next', ctr := ctr' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 660#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx21 : s.readReg64 (.gpr 21#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv2.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv2.next) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv2.next.length ∗
        vecU8At A (epPtr + 0x50#64) prevPin.cap prevPin.ptr recv2.prev.data ∗
        ((epPtr + 0x68#64) ↦₃₂ recv2.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗ A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
      (recvKeyPostCore extra hkdf A x s0) (recvKeyPanic hkdf A x s0 R) := by
  intro prog epPtr
  recv_key_fetches img.base (Rust.withPanics ext)
  have h_nextKey := sub_ok_at_rebase_bv (name := chainRecvKeyName) (callee := nextKeyInternalName)
    (k := bv% (2 ^ 64 + ls_off% "<spqr::chain::ChainEpochDirection>::next_key_internal" - ls_off% "<spqr::chain::Chain>::recv_key"))
    (by rw [chainRecvKey_fnOff, nextKeyInternal_fnOff]; rfl) hnextKey
  have h_nextKeyPanic := sub_ok_at_rebase_bv (name := chainRecvKeyName) (callee := nextKeyInternalName)
    (k := bv% (2 ^ 64 + ls_off% "<spqr::chain::ChainEpochDirection>::next_key_internal" - ls_off% "<spqr::chain::Chain>::recv_key"))
    (by rw [chainRecvKey_fnOff, nextKeyInternal_fnOff]; rfl) hnextKeyPanic
  have h_shim := sub_ok_at_rebase (name := chainRecvKeyName) (callee := shimName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::chain::Chain>::recv_key"))
    (by rw [chainRecvKey_fnOff, shim_fnOff]) hshim
  have h_alloc := sub_ok_at_rebase (name := chainRecvKeyName) (callee := allocName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::chain::Chain>::recv_key"))
    (by rw [chainRecvKey_fnOff, alloc_fnOff]) halloc
  have h_panic_oom := panic_at_handle_error_recvKey img.base ext
  have h_ok708 := fun {R : SepProp} => @recvKey_ok_from_708 img hkdf A ext x s0 c3 R
  clear hnextKey hnextKeyPanic hshim halloc
  dsimp only [prog] at *
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName = entry_addr
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  dsimp only [epPtr]; clear epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx19; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp htrace
  refine SepWPp.of_sepWP_inImage (mid := entry_addr + bv% (2 ^ 64 + ls_off% "<spqr::chain::ChainEpochDirection>::next_key_internal" - ls_off% "<spqr::chain::Chain>::recv_key")) hF ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
  by_cases hbad : recv2.next.length ≠ 32 ∨ recv2.ctr = 0xffffffff#32
  · obtain ⟨p, hp_err⟩ := nextKeyInternal_isError_of_bad hkdf hbad
    have hpan_eq : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by rw [hres, hp_err]; rfl
    have hlen_lt64 : recv2.next.length < 2 ^ 64 := by omega
    change subroutine_ok prog_val (entry_addr + bv% (2 ^ 64 + ls_off% "<spqr::chain::ChainEpochDirection>::next_key_internal" - ls_off% "<spqr::chain::Chain>::recv_key"))
      (nextKeyInternalPanicSpecX.inImage img) at h_nextKeyPanic
    wpp_call_nextKeyPanic_recv h_nextKeyPanic
      (⟨s0.sp - 120#64, gce.recv.next.ptr, recv2.next, epPtr + 0x68#64, recv2.ctr⟩ : NextKeyInternalGhost)
      hinv1 hpan_eq
  · have hlen32 : recv2.next.length = 32 := by omega
    have hctr_ne : recv2.ctr ≠ 0xffffffff#32 := fun hc => hbad (Or.inr hc)
    have hlen32_bv : BitVec.ofNat 64 recv2.next.length = 32#64 := by rw [hlen32]
    wp_norm_hyp hlen32_bv
    have hextra_in :
        memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra =
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 (extra + nextKeyInternalStackX)) extra := by
      rw [hsub_extra s0.sp]
    refine SepWPp.fold (Entails.of_eq hextra_in) (by sep_focus) ?_
    change subroutine_ok prog_val (entry_addr + bv% (2 ^ 64 + ls_off% "<spqr::chain::ChainEpochDirection>::next_key_internal" - ls_off% "<spqr::chain::Chain>::recv_key"))
      ((nextKeyInternalSpecRecvCore hkdf A extra).inImage img) at h_nextKey
    wpp_call_nextKey_recv h_nextKey
      (⟨s0.sp - 120#64, gce.recv.next.ptr, recv2.next, epPtr + 0x68#64, recv2.ctr⟩ : NextKeyInternalGhost)
      hinv1
    dsimp only [epPtr]
    have hextra_s :
        memRegion (s.sp - BitVec.ofNat 64 (extra + nextKeyInternalStackX)) extra =
        memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra := by
      rw [hsp, hsub_extra s0.sp]
    refine SepWPp.fold (Entails.of_eq hextra_s) (by sep_focus) ?_
    have hstack_s : stackAt s.sp nextKeyInternalStackX =
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 nextKeyInternalStackX) 176 ∗
        stackAt (s0.sp - 128#64) extHookStack := by
      rw [hsp]; exact stackAt_nextKeyInternalX_top_split (s0.sp - 128#64)
    refine SepWPp.fold (Entails.of_eq hstack_s) (by sep_focus) ?_
    refine SepWPp.fold (recvKey_nextKeyOutAt_dup_len (s0.sp - 120#64) (recv2.ctr + 1#32)
      (nextKeyOut hkdf recv2.next recv2.ctr)) (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    intro hout_len
    have hnext'_len : (nextKeyNext hkdf recv2.next recv2.ctr).length = 32 :=
      recvKey_nextKeyNext_length_of_nextKeyOut_length hout_len
    let next' := nextKeyNext hkdf recv2.next recv2.ctr
    let ctr' := recv2.ctr + 1#32
    let outKey := nextKeyOut hkdf recv2.next recv2.ctr
    let recv' : ChainEpochDirection := { recv2 with next := next', ctr := ctr' }
    let self' : Chain :=
      { x.self with links := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' } }
    have hlen_eq_next' : next'.length = recv2.next.length := by rw [hnext'_len, hlen32]
    have ha40 : epPtr + 0x38#64 + 8#64 = epPtr + 0x40#64 := by bv_kernel
    have ha48 : epPtr + 0x38#64 + 16#64 = epPtr + 0x48#64 := by bv_kernel
    have hpack_next := vecU8At_pack_prev A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr next'
      (by rw [hlen_eq_next']; exact hn_le) hn_cap hn_ptr
    rw [ha40, ha48, hlen_eq_next'] at hpack_next
    clear ha40 ha48
    dsimp only [epPtr] at hpack_next
    refine SepWPp.fold hpack_next (by sep_focus) ?_
    have hpack_chain := chainOuterRecvAt_pack A x epochIndex hi_ep gce prevPin recv'
      hhead hcap_lt hptr hlen_le hlen_eq
    dsimp only at hpack_chain
    refine SepWPp.fold hpack_chain (by sep_focus) ?_
    unfold nextKeyOutAt
    refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
    obtain ⟨k0, k1, k2, k3, hout_pack⟩ := exists_cells4_of_length_32 hout_len
    have hout_unpack := hout_pack (s0.sp - 116#64)
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hout_unpack
    refine SepWPp.fold (Entails.of_eq hout_unpack) (by sep_focus) ?_
    have hsp_sf : sf.sp = s0.sp - 128#64 := hsp_sf.trans hsp
    have hsp_sf_align : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf] at hsp0_align ⊢; revert hsp0_align; bv_kernel
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_norm_hyp hsp_sf; wp_norm_hyp hsp_sf_align
    refine SepWPp.of_sepWP_inImage (mid := entry_addr + 692#64) hF_sf ?_
    apply SepWP.seq_inImage (mid := entry_addr + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::chain::Chain>::recv_key")) hF_sf
    wp_steps
    have hstack_sf0 : stackAt (s0.sp - 128#64) extHookStack = stackAt sf.sp extHookStack :=
      congrArg (stackAt · extHookStack) hsp_sf.symm
    refine SepWP.fold (Entails.of_eq hstack_sf0) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    have ⟨hF2, hsym2⟩ := hinv2
    apply SepWP.seq_inImage (mid := entry_addr + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::chain::Chain>::recv_key")) hinv2
    wp_call h_shim ()
    wp_steps
    have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack :=
      congrArg (stackAt · extHookStack) (by wp_norm_goal)
    refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    rintro ⟨hF3, hsym3⟩
    wp_call h_alloc (32, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF4
    by_cases hoom : sf_2.readReg64 (Reg.gpr 0#5) = 0
    · have hoom_64 : sf_2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      wp_norm_hyp hoom_64; (conv => arg 4; simp only [hoom, ite_true, sepConj_assoc])
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htrace_oom => ?_
      wp_norm_hyp htrace_oom; wp_norm_hyp hpost
      apply SepWPp.of_sepWP (mid := entry_addr + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<spqr::chain::Chain>::recv_key"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_oom) fun hm => ?_
      have htr_f : (Rust.panicked ((((sf_2.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 32#64).writeReg64
          (Reg.gpr 30#5) (entry_addr + 1236#64)).setPC
          (entry_addr + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<spqr::chain::Chain>::recv_key")))).trace =
          s0.trace ++ [allocFailedEvent] := by
        simp only [Rust.panicked, arm64_norm, htrace_oom, hpost, htr_sf, htrace]
      exact allowPanic_recvKey_oom (hkdf := hkdf) (A := A) (x := x) (allocFailedIn_of_eq htr_f) hm
    · have hoom_64 : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      (conv => arg 4; simp only [hoom, ite_false, sepConj_assoc])
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hmod1, htrace1⟩
      wp_norm_hyp htrace1; wp_norm_hyp hpost
      let p_key := sf_2.readReg64 (Reg.gpr 0#5)
      refine SepWPp.fold (Entails.of_eq (ChainNewFacts.memRegion_32_cells4 p_key)) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro u0; apply SepWPp.exists_elim; intro u1
      apply SepWPp.exists_elim; intro u2; apply SepWPp.exists_elim; intro u3
      have hsp_sf2 : sf_2.sp = s0.sp - 128#64 := by rw [hsp_sf_2, hsp_sf_1, hsp_sf]
      have hsp_sf2_align : sf_2.spAligned = true := by
        simp only [State.spAligned, hsp_sf2] at hsp0_align ⊢; revert hsp0_align; bv_kernel
      wp_norm_hyp hsp_sf2; wp_norm_hyp hsp_sf2_align
      refine SepWPp.of_sepWP_inImage (mid := entry_addr + 708#64) hF4 ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (hout_pack p_key).symm) (by sep_focus) ?_
      refine SepWP.fold (pointsTo32_cells4_entails_memRegion_36_sp120 s0.sp ctr' k0 k1 k2 k3) (by sep_focus) ?_
      have hstack_sf_back : stackAt sf_1.sp extHookStack = stackAt (s0.sp - 128#64) extHookStack := by
        rw [hsp_sf_1, hsp_sf]
      refine SepWP.fold (Entails.of_eq hstack_sf_back) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_top_split (s0.sp - 128#64)).symm) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF5
      have hinv5 : RecvKeyStateInv img s0 _ :=
        ⟨hF5, by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by wp_norm_goal,
         by wp_norm_goal,
         by wp_norm_goal,
         by simp only [arm64_norm, htrace1, hpost, htr_sf, htrace],
         by wp_norm_goal⟩
      have hx19_5 : sf_2.readReg64 (.gpr 19#5) = x.out := by wp_norm_goal
      have hres_ok : Chain.recvKey hkdf x.self x.epoch x.index = .ok (self', outKey) := by
        rw [hres, nextKeyInternal_eq_ok hkdf hlen32 hctr_ne]; rfl
      exact recvKey_frame_extra (by sep_frame) (fun {R0} =>
        h_ok708 (R := R0) self' outKey p_key hoom_64 hout_len hres_ok _ hinv5
          (by wp_norm_goal) (by dsimp only [p_key]; wp_norm_goal) (by rw [← hx19_5]; wp_norm_goal))

/-- Split any 36-byte entry at offset `i` (`i + 36 ≤ bs.length`) into four 64-bit words and one 32-bit word. -/
theorem exists_entry36_at_cells (bs : Bytes) (i : Nat) (hi36 : i + 36 ≤ bs.length) :
    ∃ (e0 e1 e2 e3 : BitVec 64) (e4 : BitVec 32),
      (∀ p : BitVec 64, (p ↦ₛ bs) =
        (p ↦ₛ bs.take i) ∗ ((p + BitVec.ofNat 64 i) ↦₆₄ e0) ∗
        ((p + BitVec.ofNat 64 i + 8#64) ↦₆₄ e1) ∗ ((p + BitVec.ofNat 64 i + 16#64) ↦₆₄ e2) ∗
        ((p + BitVec.ofNat 64 i + 24#64) ↦₆₄ e3) ∗ ((p + BitVec.ofNat 64 i + 32#64) ↦₃₂ e4) ∗
        ((p + BitVec.ofNat 64 (i + 36)) ↦ₛ bs.drop (i + 36))) ∧
      (∀ q : BitVec 64,
        (q ↦₆₄ e0) ∗ ((q + 8#64) ↦₆₄ e1) ∗ ((q + 16#64) ↦₆₄ e2) ∗
        ((q + 24#64) ↦₆₄ e3) ∗ ((q + 32#64) ↦₃₂ e4) = (q ↦ₛ bs.extract i (i + 36))) := by
  let ent := bs.extract i (i + 36)
  have hent_len : ent.length = 36 := by
    dsimp [ent]; simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
  have hl32 : (ent.take 32).length = 32 := List.length_take_of_le (by omega)
  have hl4 : (ent.drop 32).length = 4 := by rw [List.length_drop, hent_len]
  obtain ⟨e0, e1, e2, e3, he32⟩ := exists_cells4_of_length_32 hl32
  let e4 : BitVec 32 := pack32LE (ent.drop 32)
  have hent_eq : ∀ q : BitVec 64, (q ↦ₛ ent) =
      (q ↦₆₄ e0) ∗ ((q + 8#64) ↦₆₄ e1) ∗ ((q + 16#64) ↦₆₄ e2) ∗
      ((q + 24#64) ↦₆₄ e3) ∗ ((q + 32#64) ↦₃₂ e4) := by
    intro q
    conv_lhs => rw [← List.take_append_drop 32 ent]
    rw [pointsToBytes_append, hl32, he32 q, pointsTo32_eq_pointsToBytes, unpack32_pack32LE hl4]
    have hq32 : q + BitVec.ofNat 64 32 = q + 32#64 := rfl
    rw [hq32]; ac_rfl
  refine ⟨e0, e1, e2, e3, e4, fun p => ?_, fun q => (hent_eq q).symm⟩
  have hdrop : bs.drop (i + 36) = (bs.drop i).drop 36 := by rw [List.drop_drop, Nat.add_comm]
  have hbs : bs = bs.take i ++ (ent ++ bs.drop (i + 36)) := by
    change bs = bs.take i ++ (bs.extract i (i + 36) ++ bs.drop (i + 36))
    rw [List.extract_eq_take_drop, show i + 36 - i = 36 by omega, hdrop,
      List.take_append_drop, List.take_append_drop]
  have hlen_ti : (bs.take i).length = i := List.length_take_of_le (by omega)
  conv_lhs => rw [hbs]
  rw [pointsToBytes_append, pointsToBytes_append, hlen_ti, hent_len, hent_eq (p + BitVec.ofNat 64 i)]
  have ha1 : p + BitVec.ofNat 64 i + BitVec.ofNat 64 36 = p + BitVec.ofNat 64 (i + 36) := by bv_omega
  rw [ha1]; ac_rfl

/-- Split the last 36 bytes (`bs.length - 36 .. bs.length`) of `p ↦ₛ bs` (`36 ≤ bs.length`). -/
theorem exists_entry36_last_cells (bs : Bytes) (hlen36 : 36 ≤ bs.length) :
    ∃ (el0 el1 el2 el3 : BitVec 64) (el4 : BitVec 32),
      (∀ p : BitVec 64, (p ↦ₛ bs) =
        (p ↦ₛ bs.take (bs.length - 36)) ∗
        ((p + BitVec.ofNat 64 (bs.length - 36)) ↦₆₄ el0) ∗
        ((p + BitVec.ofNat 64 (bs.length - 36) + 8#64) ↦₆₄ el1) ∗
        ((p + BitVec.ofNat 64 (bs.length - 36) + 16#64) ↦₆₄ el2) ∗
        ((p + BitVec.ofNat 64 (bs.length - 36) + 24#64) ↦₆₄ el3) ∗
        ((p + BitVec.ofNat 64 (bs.length - 36) + 32#64) ↦₃₂ el4)) ∧
      (∀ q : BitVec 64,
        (q ↦₆₄ el0) ∗ ((q + 8#64) ↦₆₄ el1) ∗ ((q + 16#64) ↦₆₄ el2) ∗
        ((q + 24#64) ↦₆₄ el3) ∗ ((q + 32#64) ↦₃₂ el4) = (q ↦ₛ bs.drop (bs.length - 36))) := by
  obtain ⟨el0, el1, el2, el3, el4, hsplit, hpack⟩ := exists_entry36_at_cells bs (bs.length - 36) (by omega)
  have hadd : bs.length - 36 + 36 = bs.length := by omega
  have hex : bs.extract (bs.length - 36) (bs.length - 36 + 36) = bs.drop (bs.length - 36) := by
    rw [List.extract_eq_take_drop, show bs.length - 36 + 36 - (bs.length - 36) = 36 by omega,
      List.take_of_length_le (by rw [List.length_drop]; omega)]
  refine ⟨el0, el1, el2, el3, el4, fun p => ?_, fun q => ?_⟩
  · have hp := hsplit p
    rw [hadd, List.drop_length, pointsToBytes_nil, sepConj_emp] at hp; exact hp
  · rw [hpack q, hex]

/-- Fold the 5 cells written at `p + BitVec.ofNat 64 i` into `p ↦ₛ (bs.take i ++ bs.drop (bs.length - 36) ++ bs.drop (i + 36))`. -/
theorem pointsToBytes_write_moved36_at (bs : Bytes) (i : Nat)
    (hi36 : i + 36 ≤ bs.length) (hlen36 : 36 ≤ bs.length)
    (el0 el1 el2 el3 : BitVec 64) (el4 : BitVec 32)
    (hel : ∀ q : BitVec 64,
      (q ↦₆₄ el0) ∗ ((q + 8#64) ↦₆₄ el1) ∗ ((q + 16#64) ↦₆₄ el2) ∗
      ((q + 24#64) ↦₆₄ el3) ∗ ((q + 32#64) ↦₃₂ el4) = (q ↦ₛ bs.drop (bs.length - 36)))
    (p : BitVec 64) :
    (p ↦ₛ bs.take i) ∗ ((p + BitVec.ofNat 64 i) ↦₆₄ el0) ∗
      ((p + BitVec.ofNat 64 i + 8#64) ↦₆₄ el1) ∗ ((p + BitVec.ofNat 64 i + 16#64) ↦₆₄ el2) ∗
      ((p + BitVec.ofNat 64 i + 24#64) ↦₆₄ el3) ∗ ((p + BitVec.ofNat 64 i + 32#64) ↦₃₂ el4) ∗
      ((p + BitVec.ofNat 64 (i + 36)) ↦ₛ bs.drop (i + 36)) =
      (p ↦ₛ (bs.take i ++ bs.drop (bs.length - 36) ++ bs.drop (i + 36))) := by
  have hlen_ti : (bs.take i).length = i := List.length_take_of_le (by omega)
  have hlen_el : (bs.drop (bs.length - 36)).length = 36 := by rw [List.length_drop]; omega
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append,
    hlen_ti, hlen_el, ← hel (p + BitVec.ofNat 64 i)]
  have ha1 : p + BitVec.ofNat 64 i + BitVec.ofNat 64 36 = p + BitVec.ofNat 64 (i + 36) := by bv_omega
  rw [ha1]; ac_rfl

/-- Length of `(KeyHistory.remove ⟨bs⟩ i params).data` in the swap-remove case (`i + 36 < bs.length`). -/
theorem remove_length_of_lt (bs : Bytes) (i : Nat) (params : ChainParamsPB)
    (hlt : i + KeyHistory.KEY_SIZE < bs.length) :
    (KeyHistory.remove ⟨bs⟩ i params).data.length = bs.length - KeyHistory.KEY_SIZE := by
  rw [← remove_data_eq_of_lt bs i params hlt]
  have hL_len :
      (bs.take i ++ bs.drop (bs.length - KeyHistory.KEY_SIZE) ++ bs.drop (i + KeyHistory.KEY_SIZE)).length =
        bs.length := by
    dsimp [KeyHistory.KEY_SIZE] at hlt ⊢
    rw [List.length_append, List.length_append, List.length_take, List.length_drop, List.length_drop]; omega
  rw [List.length_take_of_le (by rw [hL_len]; omega)]

/-- Repack `(ptr ↦ₛ L) ∗ vecU8Rest A cap ptr bs.length` into
`(ptr ↦ₛ (KeyHistory.remove ⟨bs⟩ i params).data) ∗ vecU8Rest A cap ptr (bs.length - 36)`. -/
theorem prev_remove_swap_repack (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes)
    (i : Nat) (params : ChainParamsPB)
    (hlt : i + KeyHistory.KEY_SIZE < bs.length) (hle : bs.length ≤ cap.toNat) :
    let newEnd := bs.length - KeyHistory.KEY_SIZE
    let moved := bs.drop newEnd
    (ptr ↦ₛ (bs.take i ++ moved ++ bs.drop (i + KeyHistory.KEY_SIZE))) ∗ vecU8Rest A cap ptr bs.length ⊢
      (ptr ↦ₛ (KeyHistory.remove ⟨bs⟩ i params).data) ∗
        vecU8Rest A cap ptr (KeyHistory.remove ⟨bs⟩ i params).data.length := by
  intro newEnd moved
  rw [remove_length_of_lt bs i params hlt, ← remove_data_eq_of_lt bs i params hlt]
  let L := bs.take i ++ moved ++ bs.drop (i + KeyHistory.KEY_SIZE)
  change (ptr ↦ₛ L) ∗ vecU8Rest A cap ptr bs.length ⊢ (ptr ↦ₛ L.take newEnd) ∗ vecU8Rest A cap ptr newEnd
  have hL_len : L.length = bs.length := by
    dsimp [L, moved, newEnd, KeyHistory.KEY_SIZE] at hlt ⊢
    rw [List.length_append, List.length_append, List.length_take, List.length_drop, List.length_drop]; omega
  have hnew_le : newEnd ≤ L.length := by dsimp [newEnd]; omega
  have htake_len : (L.take newEnd).length = newEnd := List.length_take_of_le hnew_le
  have hcap_pos : 0 < cap.toNat := by dsimp [KeyHistory.KEY_SIZE] at hlt; omega
  have hcap_ne : cap ≠ 0 := by intro h0; subst h0; simp at hcap_pos
  unfold vecU8Rest; simp only [hcap_ne, ↓reduceIte]
  have hL_eq : (ptr ↦ₛ L) =
      (ptr ↦ₛ L.take newEnd) ∗ ((ptr + BitVec.ofNat 64 newEnd) ↦ₛ L.drop newEnd) := by
    conv_lhs => rw [(List.take_append_drop newEnd L).symm]
    rw [pointsToBytes_append, htake_len]
  have hdrop_len : (L.drop newEnd).length = bs.length - newEnd := by rw [List.length_drop, hL_len]
  rw [hL_eq,
    ProofLib.memRegion_split' (b := ptr + BitVec.ofNat 64 newEnd) (n := bs.length - newEnd)
      (k := cap.toNat - bs.length) (b' := ptr + BitVec.ofNat 64 bs.length)
      (by dsimp [newEnd]; omega) (by dsimp [newEnd]; bv_omega) (by dsimp [newEnd]; omega)]
  rw [show ((ptr ↦ₛ L.take newEnd) ∗ ((ptr + BitVec.ofNat 64 newEnd) ↦ₛ L.drop newEnd)) ∗
        (A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (ptr ↦ₛ L.take newEnd) ∗ (A.live ptr cap.toNat 1 ∗
        (((ptr + BitVec.ofNat 64 newEnd) ↦ₛ L.drop newEnd) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  rw [← hdrop_len]; exact sepConj_mono_left (pointsToBytes_entails_memRegion _ _)

private theorem gc_iter_arith_props {i len : Nat} (hi_lt : i < len) (hlen : len < 2 ^ 63) :
    BitVec.ofNat 64 i + 4#64 = BitVec.ofNat 64 (i + 4) ∧
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (i + 4)) = decide (len < i + 4) ∧
    BitVec.ule (BitVec.ofNat 64 (i + 4)) (BitVec.ofNat 64 len) = !decide (len < i + 4) ∧
    BitVec.ofNat 64 i + 36#64 = BitVec.ofNat 64 (i + 36) ∧
    BitVec.ult (BitVec.ofNat 64 (i + 36)) (BitVec.ofNat 64 len) = decide (i + 36 < len) ∧
    BitVec.ule (BitVec.ofNat 64 len) (BitVec.ofNat 64 (i + 36)) = !decide (i + 36 < len) ∧
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 i) = false ∧
    BitVec.ule (BitVec.ofNat 64 i) (BitVec.ofNat 64 len) = true ∧
    BitVec.ult (BitVec.ofNat 64 i) (BitVec.ofNat 64 i) = false ∧
    BitVec.ule (BitVec.ofNat 64 i) (BitVec.ofNat 64 i) = true := by
  have hi64 : i < 2 ^ 64 := by omega
  have hi4_64 : i + 4 < 2 ^ 64 := by omega
  have hi36_64 : i + 36 < 2 ^ 64 := by omega
  have hlen64 : len < 2 ^ 64 := by omega
  refine ⟨by bv_omega, ?_, ?_, by bv_omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.ult_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hi4_64]
  · rw [BitVec.ule_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi4_64, Nat.mod_eq_of_lt hlen64]
    by_cases h : len < i + 4 <;> simp [h] <;> omega
  · rw [BitVec.ult_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi36_64, Nat.mod_eq_of_lt hlen64]
  · rw [BitVec.ule_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hi36_64]
    by_cases h : i + 36 < len <;> simp [h] <;> omega
  · rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hi64]; omega
  · rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hlen64]; omega
  · simp [BitVec.ult]
  · simp [BitVec.ule]

private theorem gc_swap_arith_props {i len : Nat} (hlt : i + 36 < len) (hlen : len < 2 ^ 63) :
    BitVec.ofNat 64 len - 36#64 = BitVec.ofNat 64 (len - 36) ∧
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (len - 36)) = false ∧
    BitVec.ule (BitVec.ofNat 64 (len - 36)) (BitVec.ofNat 64 len) = true ∧
    BitVec.ult (BitVec.ofNat 64 i) (BitVec.ofNat 64 (len - 36)) = true ∧
    BitVec.ule (BitVec.ofNat 64 (len - 36)) (BitVec.ofNat 64 i) = false := by
  have hi64 : i < 2 ^ 64 := by omega
  have hsub64 : len - 36 < 2 ^ 64 := by omega
  have hlen64 : len < 2 ^ 64 := by omega
  refine ⟨by bv_omega, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64]; omega
  · rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hsub64, Nat.mod_eq_of_lt hlen64]; omega
  · rw [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hsub64]; omega
  · rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hsub64, Nat.mod_eq_of_lt hi64]; omega

private theorem ule_eq_not_ult_32 (a b : BitVec 32) : BitVec.ule a b = !BitVec.ult b a := by
  rw [BitVec.ule_eq_decide, BitVec.ult_eq_decide]
  by_cases h : a.toNat ≤ b.toNat <;> simp [h] <;> omega

private theorem gc_cmp_props {ek : List (BitVec 8)} (hek : ek.length = 4) (thVal : BitVec 32) :
    let w9 := rev32Trunc (rev32Trunc thVal)
    let w11 := rev32Trunc (pack32LE ek)
    BitVec.ult w11 w9 = bytesLt ek (toBEBytes 4 thVal) ∧
    BitVec.ule w9 w11 = !bytesLt ek (toBEBytes 4 thVal) := by
  intro w9 w11
  have hlt := (bytesLt_4_eq_ult_rev32Trunc hek thVal).symm
  exact ⟨hlt, by rw [ule_eq_not_ult_32, hlt]⟩

set_option maxHeartbeats 1200000 in
/-- Single iteration of `KeyHistory.gcLoop` at `+932`. -/
theorem recvKey_gc_loop_step {extra : Nat} {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hsub_extra : ∀ sp : BitVec 64,
      sp - 128#64 - BitVec.ofNat 64 (extra + nextKeyInternalStackX) =
        sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX))
    (hnextKey : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecRecvCore hkdf A extra).inImage img))
    (hnextKeyPanic : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName) (nextKeyInternalPanicSpecX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName) ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName) ((rustAllocSpecWithStack A extHookStack).inImage img))
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (prevPin : VecPin)
    (recv1 : ChainEpochDirection) (kh : KeyHistory) (thVal : BitVec 32) (i : Nat)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat) (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64) (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_le : recv1.next.length ≤ gce.recv.next.cap.toNat) (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0) (hp_le : kh.data.length ≤ prevPin.cap.toNat)
    (hp_cap : prevPin.cap.toNat < 2 ^ 63) (hp_ptr : prevPin.ptr ≠ 0) (hi_lt : i < kh.data.length)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let prevGc ← ChainResult.ofPanic (KeyHistory.gcLoop kh (toBEBytes 4 thVal) x.self.params i)
      let recv2 := { recv1 with prev := prevGc }
      let (next', ctr', (_, outKey)) ← ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
      let recv' := { recv2 with next := next', ctr := ctr' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (h_next : ∀ (kh' : KeyHistory) (i' : Nat)
      (_hp_le' : kh'.data.length ≤ prevPin.cap.toNat) (_hi_lt' : i' < kh'.data.length)
      (_hdec : kh'.data.length - i' < kh.data.length - i)
      (_hres' : Chain.recvKey hkdf x.self x.epoch x.index = (do
        let prevGc ← ChainResult.ofPanic (KeyHistory.gcLoop kh' (toBEBytes 4 thVal) x.self.params i')
        let recv2 := { recv1 with prev := prevGc }
        let (next', ctr', (_, outKey)) ← ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
        let recv' := { recv2 with next := next', ctr := ctr' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
        return ({ x.self with links := links' }, outKey)))
      (s' : State) (_hinv' : RecvKeyStateInv img s0 s')
      (_hpc' : s'.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 932#64)
      (_hx0' : s'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 i') (_hx2' : s'.readReg64 (.gpr 2#5) = BitVec.ofNat 64 kh'.data.length)
      (_hx8' : s'.readReg64 (.gpr 8#5) = prevPin.ptr) (_hx19' : s'.readReg64 (.gpr 19#5) = x.out)
      (_hx21' : s'.readReg64 (.gpr 21#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
      (_hx22' : s'.readReg64 (.gpr 22#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)),
      let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
      let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
      SepWPp prog (s0.readReg64 (.gpr 30#5)) s'
        (memRegion x.out 32 ∗ chainOuterRecvAt A x epochIndex hi_ep gce ∗
          ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
          ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv1.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv1.next) ∗
          vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv1.next.length ∗
          ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗ ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
          ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 kh'.data.length) ∗ (prevPin.ptr ↦ₛ kh'.data) ∗
          vecU8Rest A prevPin.cap prevPin.ptr kh'.data.length ∗
          ((epPtr + 0x68#64) ↦₃₂ recv1.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
          stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ ((s0.sp - 120#64) ↦₃₂ rev32Trunc thVal) ∗
          memRegion (s0.sp - 116#64) 32 ∗ recvKeyFrameRestAt s0 c3 ∗ A.pool ∗
          memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
        (recvKeyPostCore extra hkdf A x s0) (recvKeyPanic hkdf A x s0 R))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 932#64)
    (hx0 : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 i) (hx2 : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 kh.data.length)
    (hx8 : s.readReg64 (.gpr 8#5) = prevPin.ptr) (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx21 : s.readReg64 (.gpr 21#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv1.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv1.next) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv1.next.length ∗
        ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗ ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 kh.data.length) ∗ (prevPin.ptr ↦ₛ kh.data) ∗
        vecU8Rest A prevPin.cap prevPin.ptr kh.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv1.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ ((s0.sp - 120#64) ↦₃₂ rev32Trunc thVal) ∗
        memRegion (s0.sp - 116#64) 32 ∗ recvKeyFrameRestAt s0 c3 ∗ A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
      (recvKeyPostCore extra hkdf A x s0) (recvKeyPanic hkdf A x s0 R) := by
  intro prog epPtr
  recv_key_fetches img.base (Rust.withPanics ext)
  have h_from660 := @recvKey_from_660 extra img hkdf A ext hsub_extra hnextKey hnextKeyPanic hshim halloc
    x s0 c3 R epochIndex hi_ep gce prevPin
  have h_panic_slice := panic_at_slice_recvKey img.base ext
  clear hnextKey hnextKeyPanic hshim halloc
  dsimp only [prog] at *
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName = entry_addr
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  dsimp only [epPtr]; clear epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  have hbs_lt : kh.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have ⟨hi4_add, hult_i4, hule_i4, hi36_add, hult_i36, hule_i36,
        hult_len_i, hule_i_len, hult_ii, hule_ii⟩ := gc_iter_arith_props hi_lt hbs_lt
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx0
  wp_norm_hyp hx2; wp_norm_hyp hx8; wp_norm_hyp hx19; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp htrace
  wp_norm_hyp hi4_add; wp_norm_hyp hult_i4; wp_norm_hyp hule_i4; wp_norm_hyp hi36_add
  wp_norm_hyp hult_i36; wp_norm_hyp hule_i36; wp_norm_hyp hult_len_i; wp_norm_hyp hule_i_len
  wp_norm_hyp hult_ii; wp_norm_hyp hule_ii
  by_cases hbounds : kh.data.length < i + 4
  · have hb_t : decide (kh.data.length < i + 4) = true := decide_eq_true hbounds
    wp_norm_hyp hb_t
    apply SepWPp.of_sepWP (mid := entry_addr + bv% (ls_off% "core::slice::index::slice_index_fail" - ls_off% "<spqr::chain::Chain>::recv_key"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_slice) fun hm => ?_
    have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
      rw [hres, gcLoop_of_bounds kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds]; rfl
    exact allowPanic_recvKey_panic hpan (by simp only [Rust.panicked, arm64_norm, htrace]) hm
  · have hb_f : decide (kh.data.length < i + 4) = false := decide_eq_false hbounds
    have hi4_le : i + 4 ≤ kh.data.length := by omega
    have hlen_ek : (kh.data.extract i (i + 4)).length = 4 := by
      simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
    have ⟨hcmp_ult, hcmp_ule⟩ := gc_cmp_props hlen_ek thVal
    wp_norm_hyp hb_f; wp_norm_hyp hcmp_ult; wp_norm_hyp hcmp_ule
    have hsplit4 := pointsToBytes_split_u32_at prevPin.ptr kh.data i hi4_le
    refine SepWPp.fold (Entails.of_eq hsplit4) (by sep_focus) ?_
    by_cases hrem : bytesLt (kh.data.extract i (i + 4)) (toBEBytes 4 thVal) = true
    · wp_norm_hyp hrem
      by_cases hlt36 : i + 36 < kh.data.length
      · have hlt36_t : decide (i + 36 < kh.data.length) = true := decide_eq_true hlt36
        have ⟨hsub36, hult_sub1, hule_sub1, hult_sub2, hule_sub2⟩ := gc_swap_arith_props hlt36 hbs_lt
        wp_norm_hyp hlt36_t; wp_norm_hyp hsub36; wp_norm_hyp hult_sub1; wp_norm_hyp hule_sub1
        wp_norm_hyp hult_sub2; wp_norm_hyp hule_sub2
        obtain ⟨el0, el1, el2, el3, el4, hel_split, hel_pack⟩ := exists_entry36_last_cells kh.data (by omega)
        obtain ⟨ei0, ei1, ei2, ei3, ei4, hei_split, _⟩ := exists_entry36_at_cells kh.data i (by omega)
        refine SepWPp.of_sepWP_inImage (mid := entry_addr + 932#64) hF ?_
        apply SepWP.seq_inImage (mid := entry_addr + 996#64) hF
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF_996
        apply SepWP.seq_inImage (mid := entry_addr + 1004#64) hF_996
        refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (hel_split prevPin.ptr)) (by sep_focus) ?_
        wp_steps
        refine SepWP.fold (Entails.of_eq (hel_split prevPin.ptr).symm) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (hei_split prevPin.ptr)) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF_mid
        wp_steps
        have hwrite := pointsToBytes_write_moved36_at kh.data i (by omega) (by omega)
          el0 el1 el2 el3 el4 hel_pack prevPin.ptr
        refine SepWP.fold (Entails.of_eq hwrite) (by sep_focus) ?_
        have hrepack := prev_remove_swap_repack A prevPin.cap prevPin.ptr kh.data i x.self.params hlt36 hp_le
        dsimp only [KeyHistory.KEY_SIZE] at hrepack
        refine SepWP.fold hrepack (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF'
        have hinv' : RecvKeyStateInv img s0 _ :=
          ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
           by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
        have hex_eq : kh.data.extract i (i + 4) = (kh.data.drop i).take 4 := by
          rw [List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
        have hrem_drop : bytesLt ((kh.data.drop i).take 4) (toBEBytes 4 thVal) = true := by rwa [← hex_eq]
        have hres' :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let prevGc ← ChainResult.ofPanic
                (KeyHistory.gcLoop (kh.remove i x.self.params) (toBEBytes 4 thVal) x.self.params i)
              let recv2 := { recv1 with prev := prevGc }
              let (next', ctr', (_, outKey)) ←
                ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
              let recv' := { recv2 with next := next', ctr := ctr' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, gcLoop_of_remove kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds hrem_drop]
        have hrem_len : (kh.remove i x.self.params).data.length = kh.data.length - 36 :=
          remove_length_of_lt kh.data i x.self.params hlt36
        have hp_le' : (kh.remove i x.self.params).data.length ≤ prevPin.cap.toNat := by omega
        have hi_lt' : i < (kh.remove i x.self.params).data.length := by omega
        have hdec : (kh.remove i x.self.params).data.length - i < kh.data.length - i := by omega
        refine SepWPp.mono_pre _ ?_
          (h_next (kh.remove i x.self.params) i hp_le' hi_lt' hdec hres' _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by rw [hrem_len]; wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        rw [hrem_len]; sep_frame
      · have hlt36_f : decide (i + 36 < kh.data.length) = false := decide_eq_false hlt36
        wp_norm_hyp hlt36_f
        refine SepWPp.of_sepWP_inImage (mid := entry_addr + 660#64) hF ?_
        wp_steps
        refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
        have hpack_rem := vecU8At_pack_remove_last A
          (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
          prevPin.cap prevPin.ptr kh.data i x.self.params hi_lt hlt36 hp_le hp_cap hp_ptr
        have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
            x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
        have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
            x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
        rw [ha58, ha60] at hpack_rem; clear ha58 ha60
        refine SepWP.fold hpack_rem (by sep_focus) ?_
        refine SepWP.fold (pointsTo32_memRegion_32_entails_36 s0.sp (rev32Trunc thVal)) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyStateInv img s0 _ :=
          ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
           by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
        have hex_eq : kh.data.extract i (i + 4) = (kh.data.drop i).take 4 := by
          rw [List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
        have hrem_drop : bytesLt ((kh.data.drop i).take 4) (toBEBytes 4 thVal) = true := by rwa [← hex_eq]
        have hrem_len : (kh.remove i x.self.params).data.length = i := by
          rw [← remove_data_eq_of_ge kh.data i x.self.params hlt36, List.length_take_of_le (Nat.le_of_lt hi_lt)]
        have hnot_lt : ¬ (i < (kh.remove i x.self.params).data.length) := by omega
        have hres660 :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let recv2 := { recv1 with prev := kh.remove i x.self.params }
              let (next', ctr', (_, outKey)) ←
                ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
              let recv' := { recv2 with next := next', ctr := ctr' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, gcLoop_of_remove kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds hrem_drop,
            gcLoop_of_ge (kh.remove i x.self.params) (toBEBytes 4 thVal) x.self.params i hnot_lt]; rfl
        refine SepWPp.mono_pre _ ?_
          (h_from660 { recv1 with prev := kh.remove i x.self.params }
            hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hres660 _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame
    · have hskip : bytesLt (kh.data.extract i (i + 4)) (toBEBytes 4 thVal) = false := Bool.eq_false_of_ne_true hrem
      wp_norm_hyp hskip
      by_cases hlt36 : i + 36 < kh.data.length
      · have hlt36_t : decide (i + 36 < kh.data.length) = true := decide_eq_true hlt36
        wp_norm_hyp hlt36_t
        refine SepWPp.of_sepWP_inImage (mid := entry_addr + 932#64) hF ?_
        wp_steps
        refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyStateInv img s0 _ :=
          ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
           by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
        have hex_eq : kh.data.extract i (i + 4) = (kh.data.drop i).take 4 := by
          rw [List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
        have hskip_drop : bytesLt ((kh.data.drop i).take 4) (toBEBytes 4 thVal) = false := by rwa [← hex_eq]
        have hres' :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let prevGc ← ChainResult.ofPanic (KeyHistory.gcLoop kh (toBEBytes 4 thVal) x.self.params (i + 36))
              let recv2 := { recv1 with prev := prevGc }
              let (next', ctr', (_, outKey)) ←
                ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
              let recv' := { recv2 with next := next', ctr := ctr' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, gcLoop_of_skip kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds hskip_drop]; rfl
        have hdec : kh.data.length - (i + 36) < kh.data.length - i := by omega
        refine SepWPp.mono_pre _ ?_
          (h_next kh (i + 36) hp_le hlt36 hdec hres' _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame
      · have hlt36_f : decide (i + 36 < kh.data.length) = false := decide_eq_false hlt36
        wp_norm_hyp hlt36_f
        refine SepWPp.of_sepWP_inImage (mid := entry_addr + 660#64) hF ?_
        wp_steps
        refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
        have hpack_prev := vecU8At_pack_prev A
          (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
          prevPin.cap prevPin.ptr kh.data hp_le hp_cap hp_ptr
        have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
            x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
        have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
            x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
        rw [ha58, ha60] at hpack_prev; clear ha58 ha60
        refine SepWP.fold hpack_prev (by sep_focus) ?_
        refine SepWP.fold (pointsTo32_memRegion_32_entails_36 s0.sp (rev32Trunc thVal)) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyStateInv img s0 _ :=
          ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
           by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
        have hex_eq : kh.data.extract i (i + 4) = (kh.data.drop i).take 4 := by
          rw [List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
        have hskip_drop : bytesLt ((kh.data.drop i).take 4) (toBEBytes 4 thVal) = false := by rwa [← hex_eq]
        have hres660 :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let recv2 := { recv1 with prev := kh }
              let (next', ctr', (_, outKey)) ←
                ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
              let recv' := { recv2 with next := next', ctr := ctr' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, gcLoop_of_skip kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds hskip_drop,
            gcLoop_of_ge kh (toBEBytes 4 thVal) x.self.params (i + KeyHistory.KEY_SIZE) hlt36]; rfl
        refine SepWPp.mono_pre _ ?_
          (h_from660 { recv1 with prev := kh }
            hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hres660 _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame

/-- Full `KeyHistory.gcLoop` loop at `+932` by induction on `fuel`. -/
theorem recvKey_gc_loop {extra : Nat} {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc} {ext : String → Option (State → State)}
    (hsub_extra : ∀ sp : BitVec 64,
      sp - 128#64 - BitVec.ofNat 64 (extra + nextKeyInternalStackX) =
        sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX))
    (hnextKey : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName) ((nextKeyInternalSpecRecvCore hkdf A extra).inImage img))
    (hnextKeyPanic : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName) (nextKeyInternalPanicSpecX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName) ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName) ((rustAllocSpecWithStack A extHookStack).inImage img))
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length) (gce : ChainEpochGhost) (prevPin : VecPin)
    (recv1 : ChainEpochDirection) (thVal : BitVec 32)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat) (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64) (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat) (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_le : recv1.next.length ≤ gce.recv.next.cap.toNat) (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0) (hp_cap : prevPin.cap.toNat < 2 ^ 63) (hp_ptr : prevPin.ptr ≠ 0) (fuel : Nat) :
    ∀ (kh : KeyHistory) (i : Nat) (_hfuel : kh.data.length - i ≤ fuel)
      (_hp_le : kh.data.length ≤ prevPin.cap.toNat) (_hi_lt : i < kh.data.length)
      (_hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
        let prevGc ← ChainResult.ofPanic (KeyHistory.gcLoop kh (toBEBytes 4 thVal) x.self.params i)
        let recv2 := { recv1 with prev := prevGc }
        let (next', ctr', (_, outKey)) ← ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
        let recv' := { recv2 with next := next', ctr := ctr' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
        return ({ x.self with links := links' }, outKey)))
      (s : State) (_hinv : RecvKeyStateInv img s0 s)
      (_hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 932#64)
      (_hx0 : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 i) (_hx2 : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 kh.data.length)
      (_hx8 : s.readReg64 (.gpr 8#5) = prevPin.ptr) (_hx19 : s.readReg64 (.gpr 19#5) = x.out)
      (_hx21 : s.readReg64 (.gpr 21#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
      (_hx22 : s.readReg64 (.gpr 22#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)),
      let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
      let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
      SepWPp prog (s0.readReg64 (.gpr 30#5)) s
        (memRegion x.out 32 ∗ chainOuterRecvAt A x epochIndex hi_ep gce ∗
          ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
          ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv1.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv1.next) ∗
          vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv1.next.length ∗
          ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗ ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
          ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 kh.data.length) ∗ (prevPin.ptr ↦ₛ kh.data) ∗
          vecU8Rest A prevPin.cap prevPin.ptr kh.data.length ∗
          ((epPtr + 0x68#64) ↦₃₂ recv1.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
          stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ ((s0.sp - 120#64) ↦₃₂ rev32Trunc thVal) ∗
          memRegion (s0.sp - 116#64) 32 ∗ recvKeyFrameRestAt s0 c3 ∗ A.pool ∗
          memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
        (recvKeyPostCore extra hkdf A x s0) (recvKeyPanic hkdf A x s0 R) := by
  induction fuel with
  | zero => intro kh i hfuel _ hi_lt; omega
  | succ fuel ih =>
    intro kh i hfuel hp_le hi_lt hres s hinv hpc hx0 hx2 hx8 hx19 hx21 hx22
    exact recvKey_gc_loop_step hsub_extra hnextKey hnextKeyPanic hshim halloc
      x s0 c3 epochIndex hi_ep gce prevPin recv1 kh thVal i
      hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hp_le hp_cap hp_ptr hi_lt hres
      (fun kh' i' hp_le' hi_lt' hdec => ih kh' i' (by omega) hp_le' hi_lt')
      s hinv hpc hx0 hx2 hx8 hx19 hx21 hx22

/-! ## `KeyHistory::gc` Entry at `+616` -/

private theorem gc_entry_arith_props (len : Nat) (ctr : BitVec 32) (params : ChainParamsPB)
    (hlen : len < 2 ^ 63) :
    let trimBytes := params.trimSize * KeyHistory.KEY_SIZE
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 trimBytes) = !decide (len ≥ trimBytes) ∧
    BitVec.ule (BitVec.ofNat 64 trimBytes) (BitVec.ofNat 64 len) = decide (len ≥ trimBytes) ∧
    BitVec.ult ctr params.maxOooKeysOrDefault = decide (ctr < params.maxOooKeysOrDefault) ∧
    BitVec.ule params.maxOooKeysOrDefault ctr = !decide (ctr < params.maxOooKeysOrDefault) := by
  intro trimBytes
  have hlen64 : len < 2 ^ 64 := by omega
  have hm := params.maxOooKeysOrDefault.isLt
  have htrim64 : trimBytes < 2 ^ 64 := by dsimp [trimBytes, ChainParamsPB.trimSize, KeyHistory.KEY_SIZE]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [BitVec.ult_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt htrim64]
    by_cases h : len ≥ trimBytes <;> simp [h] <;> omega
  · rw [BitVec.ule_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt htrim64, Nat.mod_eq_of_lt hlen64]
  · simp only [BitVec.ult_eq_decide, BitVec.lt_def]
  · simp only [BitVec.ule_eq_decide, BitVec.lt_def]
    by_cases h : ctr.toNat < params.maxOooKeysOrDefault.toNat <;> simp [h] <;> omega

set_option maxHeartbeats 800000 in
/-- `KeyHistory::gc` + `next_key_internal` + `Ok(outKey)` return from `+616`. -/
theorem recvKey_gc_from_616 {extra : Nat} {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hsub_extra : ∀ sp : BitVec 64,
      sp - 128#64 - BitVec.ofNat 64 (extra + nextKeyInternalStackX) =
        sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX))
    (hnextKey : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecRecvCore hkdf A extra).inImage img))
    (hnextKeyPanic : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName) (nextKeyInternalPanicSpecX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName) ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName) ((rustAllocSpecWithStack A extHookStack).inImage img))
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (prevPin : VecPin) (recv1 : ChainEpochDirection)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat) (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64) (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_le : recv1.next.length ≤ gce.recv.next.cap.toNat) (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0) (hp_le : recv1.prev.data.length ≤ prevPin.cap.toNat)
    (hp_cap : prevPin.cap.toNat < 2 ^ 63) (hp_ptr : prevPin.ptr ≠ 0)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let prevGc ← ChainResult.ofPanic (recv1.prev.gc recv1.ctr x.self.params)
      let recv2 := { recv1 with prev := prevGc }
      let (next', ctr', (_, outKey)) ← ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
      let recv' := { recv2 with next := next', ctr := ctr' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 616#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = recv1.ctr) (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx21 : s.readReg64 (.gpr 21#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hw23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv1.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv1.next) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv1.next.length ∗
        ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗ ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv1.prev.data.length) ∗ (prevPin.ptr ↦ₛ recv1.prev.data) ∗
        vecU8Rest A prevPin.cap prevPin.ptr recv1.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv1.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗ A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
      (recvKeyPostCore extra hkdf A x s0) (recvKeyPanic hkdf A x s0 R) := by
  intro prog epPtr
  recv_key_fetches img.base (Rust.withPanics ext)
  have h_from660 := @recvKey_from_660 extra img hkdf A ext hsub_extra hnextKey hnextKeyPanic hshim halloc
    x s0 c3 R epochIndex hi_ep gce prevPin
  have h_loop := @recvKey_gc_loop extra img hkdf A ext hsub_extra hnextKey hnextKeyPanic hshim halloc
    x s0 c3 R epochIndex hi_ep gce prevPin recv1
    (recv1.ctr - x.self.params.maxOooKeysOrDefault)
    hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hp_cap hp_ptr
  have h_panic_core := panic_at_core_panic_recvKey img.base ext
  clear hnextKey hnextKeyPanic hshim halloc
  dsimp only [prog] at *
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName = entry_addr
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  dsimp only [epPtr]; clear epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  have hbs_lt : recv1.prev.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have htrim_eq := trimSize_mul36_eq x.self.params
  dsimp only at htrim_eq
  have ⟨hult_trim, hule_trim, hult_uf, hule_uf⟩ :=
    gc_entry_arith_props recv1.prev.data.length recv1.ctr x.self.params hbs_lt
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hw8
  wp_norm_hyp hx19; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hw23; wp_norm_hyp htrace
  wp_norm_hyp htrim_eq; wp_norm_hyp hult_trim; wp_norm_hyp hule_trim; wp_norm_hyp hult_uf; wp_norm_hyp hule_uf
  by_cases hge : recv1.prev.data.length ≥ x.self.params.trimSize * KeyHistory.KEY_SIZE
  · have hge_t : decide (recv1.prev.data.length ≥ x.self.params.trimSize * KeyHistory.KEY_SIZE) = true :=
      decide_eq_true hge
    wp_norm_hyp hge_t
    by_cases huf : recv1.ctr < x.self.params.maxOooKeysOrDefault
    · have huf_t : decide (recv1.ctr < x.self.params.maxOooKeysOrDefault) = true := decide_eq_true huf
      wp_norm_hyp huf_t
      apply SepWPp.of_sepWP (mid := entry_addr + bv% (ls_off% "core::panicking::panic" - ls_off% "<spqr::chain::Chain>::recv_key"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_core) fun hm => ?_
      have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
        rw [hres, keyHistory_gc_of_underflow recv1.prev recv1.ctr x.self.params hge huf]; rfl
      exact allowPanic_recvKey_panic hpan (by simp only [Rust.panicked, arm64_norm, htrace]) hm
    · have huf_f : decide (recv1.ctr < x.self.params.maxOooKeysOrDefault) = false := decide_eq_false huf
      wp_norm_hyp huf_f
      refine SepWPp.fold (Entails.of_eq (memRegion_36_split_u32 s0.sp)) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro d_sp8
      refine SepWPp.of_sepWP_inImage (mid := entry_addr + 932#64) hF ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyStateInv img s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
      have hres_loop :
          Chain.recvKey hkdf x.self x.epoch x.index = (do
            let prevGc ← ChainResult.ofPanic
              (KeyHistory.gcLoop recv1.prev (toBEBytes 4 (recv1.ctr - x.self.params.maxOooKeysOrDefault)) x.self.params 0)
            let recv2 := { recv1 with prev := prevGc }
            let (next', ctr', (_, outKey)) ←
              ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
            let recv' := { recv2 with next := next', ctr := ctr' }
            let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
            return ({ x.self with links := links' }, outKey)) := by
        rw [hres, keyHistory_gc_of_ok recv1.prev recv1.ctr x.self.params hge huf]
      have htrim_pos : 0 < x.self.params.trimSize * KeyHistory.KEY_SIZE := by
        dsimp [ChainParamsPB.trimSize, KeyHistory.KEY_SIZE]; omega
      have hpos : 0 < recv1.prev.data.length := by omega
      refine SepWPp.mono_pre _ ?_
        (h_loop recv1.prev.data.length recv1.prev 0 (Nat.sub_le _ _) hp_le hpos hres_loop _ hinv'
          (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
          (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
      sep_frame
  · have hge_f : decide (recv1.prev.data.length ≥ x.self.params.trimSize * KeyHistory.KEY_SIZE) = false :=
      decide_eq_false hge
    wp_norm_hyp hge_f
    refine SepWPp.of_sepWP_inImage (mid := entry_addr + 660#64) hF ?_
    wp_steps
    have hpack_prev := vecU8At_pack_prev A
      (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
      prevPin.cap prevPin.ptr recv1.prev.data hp_le hp_cap hp_ptr
    have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
    have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
    rw [ha58, ha60] at hpack_prev; clear ha58 ha60
    refine SepWP.fold hpack_prev (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyStateInv img s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
    have hres660 :
        Chain.recvKey hkdf x.self x.epoch x.index = (do
          let (next', ctr', (_, outKey)) ←
            ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv1.next recv1.ctr)
          let recv' := { recv1 with next := next', ctr := ctr' }
          let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
          return ({ x.self with links := links' }, outKey)) := by
      rw [hres, keyHistory_gc_of_lt recv1.prev recv1.ctr x.self.params hge]; rfl
    refine SepWPp.mono_pre _ ?_
      (h_from660 recv1 hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hres660 _ hinv'
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame

/-! ## Relocatable `[LibsignalPlacement]` `KeyHistory::gc` and Post-GC Tail (`blkPC_366`) -/

open Lean Elab Tactic in
elab "wpp_call_nextKey_recv_placed " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  let htrId ← freshIdent `htr_sf
  evalTactic (← `(tactic| (
    apply (NextKeyInternalFacts.SepWPp.call_allowPanic_lsCallInv_mid $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_nextKey_recv_placed: unexpected subgoals"
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
    dsimp only [nextKeyInternalSpecX]
    simp (config := { decide := true }) only [sepConj_assoc, wp_norm, arm64_norm]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    intro $htrId:ident
    wp_norm_hyp $htrId
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId

open Lean Elab Tactic in
elab "wpp_call_nextKeyPanic_recv_placed " hcall:term:max a:term:max hF:term:max hpan:term:max : tactic => do
  evalTactic (← `(tactic| (
    apply (NextKeyInternalFacts.SepWPp.call_allowPanic_lsCallInv_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_nextKeyPanic_recv_placed: unexpected subgoals"
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

set_option maxHeartbeats 800000 in
set_option maxRecDepth 400000 in
theorem recvKey_from_660_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)))
    (hnextKeyPanic : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hoom_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (prevPin : VecPin) (recv2 : ChainEpochDirection)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat) (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64) (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_le : recv2.next.length ≤ gce.recv.next.cap.toNat) (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let (next', ctr', (_, outKey)) ←
        ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
      let recv' := { recv2 with next := next', ctr := ctr' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 660#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv2.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv2.next) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv2.next.length ∗
        vecU8At A (epPtr + 0x50#64) prevPin.cap prevPin.ptr recv2.prev.data ∗
        ((epPtr + 0x68#64) ↦₃₂ recv2.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗ A.pool)
      (recvKeyPost hkdf A x s0) (recvKeyPanic hkdf A x s0 R) := by
  intro prog s_idx epPtr
  have h_ok708 := @recvKey_ok_from_708_placed _ hkdf A H x s0 c3 R
  dsimp only [prog, s_idx, epPtr]; clear prog s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx19; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp htrace
  refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 362) hF ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
  by_cases hbad : recv2.next.length ≠ 32 ∨ recv2.ctr = 0xffffffff#32
  · obtain ⟨p, hp_err⟩ := nextKeyInternal_isError_of_bad hkdf hbad
    have hpan_eq : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by rw [hres, hp_err]; rfl
    have hlen_lt64 : recv2.next.length < 2 ^ 64 := by omega
    change subroutine_ok _ _ (withLsCallInv lsmpl nextKeyInternalPanicSpecX) at hnextKeyPanic
    wpp_call_nextKeyPanic_recv_placed hnextKeyPanic
      (⟨s0.sp - 120#64, gce.recv.next.ptr, recv2.next, epPtr + 0x68#64, recv2.ctr⟩ : NextKeyInternalGhost)
      hinv1 hpan_eq
  · have hlen32 : recv2.next.length = 32 := by omega
    have hctr_ne : recv2.ctr ≠ 0xffffffff#32 := fun hc => hbad (Or.inr hc)
    have hlen32_bv : BitVec.ofNat 64 recv2.next.length = 32#64 := by rw [hlen32]
    wp_norm_hyp hlen32_bv
    change subroutine_ok _ _ (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)) at hnextKey
    wpp_call_nextKey_recv_placed hnextKey
      (⟨s0.sp - 120#64, gce.recv.next.ptr, recv2.next, epPtr + 0x68#64, recv2.ctr⟩ : NextKeyInternalGhost)
      hinv1
    dsimp only [epPtr]
    have hstack_s : stackAt s.sp nextKeyInternalStackX =
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 nextKeyInternalStackX) 176 ∗
        stackAt (s0.sp - 128#64) extHookStack := by
      rw [hsp]; exact stackAt_nextKeyInternalX_top_split (s0.sp - 128#64)
    refine SepWPp.fold (Entails.of_eq hstack_s) (by sep_focus) ?_
    refine SepWPp.fold (recvKey_nextKeyOutAt_dup_len (s0.sp - 120#64) (recv2.ctr + 1#32)
      (nextKeyOut hkdf recv2.next recv2.ctr)) (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    intro hout_len
    have hnext'_len : (nextKeyNext hkdf recv2.next recv2.ctr).length = 32 :=
      recvKey_nextKeyNext_length_of_nextKeyOut_length hout_len
    let next' := nextKeyNext hkdf recv2.next recv2.ctr
    let ctr' := recv2.ctr + 1#32
    let outKey := nextKeyOut hkdf recv2.next recv2.ctr
    let recv' : ChainEpochDirection := { recv2 with next := next', ctr := ctr' }
    let self' : Chain :=
      { x.self with links := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' } }
    have hlen_eq_next' : next'.length = recv2.next.length := by rw [hnext'_len, hlen32]
    have ha40 : epPtr + 0x38#64 + 8#64 = epPtr + 0x40#64 := by bv_kernel
    have ha48 : epPtr + 0x38#64 + 16#64 = epPtr + 0x48#64 := by bv_kernel
    have hpack_next := vecU8At_pack_prev A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr next'
      (by rw [hlen_eq_next']; exact hn_le) hn_cap hn_ptr
    rw [ha40, ha48, hlen_eq_next'] at hpack_next
    clear ha40 ha48
    dsimp only [epPtr] at hpack_next
    refine SepWPp.fold hpack_next (by sep_focus) ?_
    have hpack_chain := chainOuterRecvAt_pack A x epochIndex hi_ep gce prevPin recv'
      hhead hcap_lt hptr hlen_le hlen_eq
    dsimp only at hpack_chain
    refine SepWPp.fold hpack_chain (by sep_focus) ?_
    unfold nextKeyOutAt
    refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
    obtain ⟨k0, k1, k2, k3, hout_pack⟩ := exists_cells4_of_length_32 hout_len
    have hout_unpack := hout_pack (s0.sp - 116#64)
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hout_unpack
    refine SepWPp.fold (Entails.of_eq hout_unpack) (by sep_focus) ?_
    have hsp_sf : sf.sp = s0.sp - 128#64 := hsp_sf.trans hsp
    have hsp_sf_align : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf] at hsp0_align ⊢; revert hsp0_align; bv_kernel
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_norm_hyp hsp_sf; wp_norm_hyp hsp_sf_align
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 692#64) hF_sf ?_
    apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
    wp_steps
    have hstack_sf0 : stackAt (s0.sp - 128#64) extHookStack = stackAt sf.sp extHookStack :=
      congrArg (stackAt · extHookStack) hsp_sf.symm
    refine SepWP.fold (Entails.of_eq hstack_sf0) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
    wp_call hshim ()
    wp_steps
    have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack :=
      congrArg (stackAt · extHookStack) (by wp_norm_goal)
    refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    wp_call halloc (32, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF4
    by_cases hoom : sf_2.readReg64 (Reg.gpr 0#5) = 0
    · have hoom_64 : sf_2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      wp_norm_hyp hoom_64; (conv => arg 4; simp only [hoom, ite_true, sepConj_assoc])
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htrace_oom => ?_
      wp_norm_hyp htrace_oom; wp_norm_hyp hpost
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hoom_ext) fun hm => ?_
      have htr_f : (Rust.panicked ((((sf_2.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 32#64).writeReg64
          (Reg.gpr 30#5) ((blkPl_366).base + 1236#64)).setPC
          (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"))).trace =
          s0.trace ++ [allocFailedEvent] := by
        simp only [Rust.panicked, arm64_norm, htrace_oom, hpost, htr_sf, htrace]
      exact allowPanic_recvKey_oom (hkdf := hkdf) (A := A) (x := x) (allocFailedIn_of_eq htr_f) hm
    · have hoom_64 : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      (conv => arg 4; simp only [hoom, ite_false, sepConj_assoc])
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hmod1, htrace1⟩
      wp_norm_hyp htrace1; wp_norm_hyp hpost
      let p_key := sf_2.readReg64 (Reg.gpr 0#5)
      refine SepWPp.fold (Entails.of_eq (ChainNewFacts.memRegion_32_cells4 p_key)) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro u0; apply SepWPp.exists_elim; intro u1
      apply SepWPp.exists_elim; intro u2; apply SepWPp.exists_elim; intro u3
      have hsp_sf2 : sf_2.sp = s0.sp - 128#64 := by rw [hsp_sf_2, hsp_sf_1, hsp_sf]
      have hsp_sf2_align : sf_2.spAligned = true := by
        simp only [State.spAligned, hsp_sf2] at hsp0_align ⊢; revert hsp0_align; bv_kernel
      wp_norm_hyp hsp_sf2; wp_norm_hyp hsp_sf2_align
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 708#64) hF4 ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (hout_pack p_key).symm) (by sep_focus) ?_
      refine SepWP.fold (pointsTo32_cells4_entails_memRegion_36_sp120 s0.sp ctr' k0 k1 k2 k3) (by sep_focus) ?_
      have hstack_sf_back : stackAt sf_1.sp extHookStack = stackAt (s0.sp - 128#64) extHookStack := by
        rw [hsp_sf_1, hsp_sf]
      refine SepWP.fold (Entails.of_eq hstack_sf_back) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_top_split (s0.sp - 128#64)).symm) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF5
      have hinv5 : RecvKeyPlacedStateInv lsmpl s0 _ :=
        ⟨hF5, (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
         (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal),
         (by simp only [arm64_norm, htrace1, hpost, htr_sf, htrace]),
         (by wp_norm_goal)⟩
      have hx19_5 : sf_2.readReg64 (.gpr 19#5) = x.out := by wp_norm_goal
      have hres_ok : Chain.recvKey hkdf x.self x.epoch x.index = .ok (self', outKey) := by
        rw [hres, nextKeyInternal_eq_ok hkdf hlen32 hctr_ne]; rfl
      refine SepWPp.mono_pre _ ?_
        (h_ok708 self' outKey p_key hoom_64 hout_len hres_ok _ hinv5
          (by wp_norm_goal) (by dsimp only [p_key]; wp_norm_goal) (by rw [← hx19_5]; wp_norm_goal))
      sep_frame

set_option maxHeartbeats 1200000 in
theorem recvKey_gc_loop_step_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)))
    (hnextKeyPanic : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hoom_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (hslice_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (prevPin : VecPin)
    (recv1 : ChainEpochDirection) (kh : KeyHistory) (thVal : BitVec 32) (i : Nat)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat) (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64) (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_le : recv1.next.length ≤ gce.recv.next.cap.toNat) (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0) (hp_le : kh.data.length ≤ prevPin.cap.toNat)
    (hp_cap : prevPin.cap.toNat < 2 ^ 63) (hp_ptr : prevPin.ptr ≠ 0) (hi_lt : i < kh.data.length)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let prevGc ← ChainResult.ofPanic (KeyHistory.gcLoop kh (toBEBytes 4 thVal) x.self.params i)
      let recv2 := { recv1 with prev := prevGc }
      let (next', ctr', (_, outKey)) ←
        ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
      let recv' := { recv2 with next := next', ctr := ctr' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (h_next : ∀ (kh' : KeyHistory) (i' : Nat)
      (_hp_le' : kh'.data.length ≤ prevPin.cap.toNat) (_hi_lt' : i' < kh'.data.length)
      (_hdec : kh'.data.length - i' < kh.data.length - i)
      (_hres' : Chain.recvKey hkdf x.self x.epoch x.index = (do
        let prevGc ← ChainResult.ofPanic (KeyHistory.gcLoop kh' (toBEBytes 4 thVal) x.self.params i')
        let recv2 := { recv1 with prev := prevGc }
        let (next', ctr', (_, outKey)) ←
          ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
        let recv' := { recv2 with next := next', ctr := ctr' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
        return ({ x.self with links := links' }, outKey)))
      (s' : State) (_hinv' : RecvKeyPlacedStateInv lsmpl s0 s')
      (_hpc' : s'.pc = (blkPl_366).base + 932#64)
      (_hx0' : s'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 i')
      (_hx2' : s'.readReg64 (.gpr 2#5) = BitVec.ofNat 64 kh'.data.length)
      (_hx8' : s'.readReg64 (.gpr 8#5) = prevPin.ptr) (_hx19' : s'.readReg64 (.gpr 19#5) = x.out)
      (_hx21' : s'.readReg64 (.gpr 21#5) =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
      (_hx22' : s'.readReg64 (.gpr 22#5) =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)),
      let prog := (blkPC_366).rebase (blkPl_366).base H
      let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
      let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
      SepWPp prog (s0.readReg64 (.gpr 30#5)) s'
        (memRegion x.out 32 ∗ chainOuterRecvAt A x epochIndex hi_ep gce ∗
          ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
          ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv1.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv1.next) ∗
          vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv1.next.length ∗
          ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗ ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
          ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 kh'.data.length) ∗ (prevPin.ptr ↦ₛ kh'.data) ∗
          vecU8Rest A prevPin.cap prevPin.ptr kh'.data.length ∗
          ((epPtr + 0x68#64) ↦₃₂ recv1.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
          stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ ((s0.sp - 120#64) ↦₃₂ rev32Trunc thVal) ∗
          memRegion (s0.sp - 116#64) 32 ∗ recvKeyFrameRestAt s0 c3 ∗ A.pool)
        (recvKeyPost hkdf A x s0) (recvKeyPanic hkdf A x s0 R))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 932#64)
    (hx0 : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 i)
    (hx2 : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 kh.data.length)
    (hx8 : s.readReg64 (.gpr 8#5) = prevPin.ptr) (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv1.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv1.next) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv1.next.length ∗
        ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗ ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 kh.data.length) ∗ (prevPin.ptr ↦ₛ kh.data) ∗
        vecU8Rest A prevPin.cap prevPin.ptr kh.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv1.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ ((s0.sp - 120#64) ↦₃₂ rev32Trunc thVal) ∗
        memRegion (s0.sp - 116#64) 32 ∗ recvKeyFrameRestAt s0 c3 ∗ A.pool)
      (recvKeyPost hkdf A x s0) (recvKeyPanic hkdf A x s0 R) := by
  intro prog s_idx epPtr
  have h_from660 := @recvKey_from_660_placed _ hkdf A H hnextKey hnextKeyPanic hshim halloc hoom_ext
    x s0 c3 R epochIndex hi_ep gce prevPin
  clear hnextKey hnextKeyPanic hshim halloc hoom_ext
  dsimp only [prog, s_idx, epPtr]; clear prog s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  have hbs_lt : kh.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have ⟨hi4_add, hult_i4, hule_i4, hi36_add, hult_i36, hule_i36,
        hult_len_i, hule_i_len, hult_ii, hule_ii⟩ := gc_iter_arith_props hi_lt hbs_lt
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx0
  wp_norm_hyp hx2; wp_norm_hyp hx8; wp_norm_hyp hx19; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp htrace
  wp_norm_hyp hi4_add; wp_norm_hyp hult_i4; wp_norm_hyp hule_i4; wp_norm_hyp hi36_add
  wp_norm_hyp hult_i36; wp_norm_hyp hule_i36; wp_norm_hyp hult_len_i; wp_norm_hyp hule_i_len
  wp_norm_hyp hult_ii; wp_norm_hyp hule_ii
  by_cases hbounds : kh.data.length < i + 4
  · have hb_t : decide (kh.data.length < i + 4) = true := decide_eq_true hbounds
    wp_norm_hyp hb_t
    apply SepWPp.of_sepWP (mid := lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail")
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hslice_ext) fun hm => ?_
    have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
      rw [hres, gcLoop_of_bounds kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds]; rfl
    exact allowPanic_recvKey_panic hpan (by simp only [Rust.panicked, arm64_norm, htrace]) hm
  · have hb_f : decide (kh.data.length < i + 4) = false := decide_eq_false hbounds
    have hi4_le : i + 4 ≤ kh.data.length := by omega
    have hlen_ek : (kh.data.extract i (i + 4)).length = 4 := by
      simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
    have ⟨hcmp_ult, hcmp_ule⟩ := gc_cmp_props hlen_ek thVal
    wp_norm_hyp hb_f; wp_norm_hyp hcmp_ult; wp_norm_hyp hcmp_ule
    have hsplit4 := pointsToBytes_split_u32_at prevPin.ptr kh.data i hi4_le
    refine SepWPp.fold (Entails.of_eq hsplit4) (by sep_focus) ?_
    by_cases hrem : bytesLt (kh.data.extract i (i + 4)) (toBEBytes 4 thVal) = true
    · wp_norm_hyp hrem
      by_cases hlt36 : i + 36 < kh.data.length
      · have hlt36_t : decide (i + 36 < kh.data.length) = true := decide_eq_true hlt36
        have ⟨hsub36, hult_sub1, hule_sub1, hult_sub2, hule_sub2⟩ := gc_swap_arith_props hlt36 hbs_lt
        wp_norm_hyp hlt36_t; wp_norm_hyp hsub36; wp_norm_hyp hult_sub1; wp_norm_hyp hule_sub1
        wp_norm_hyp hult_sub2; wp_norm_hyp hule_sub2
        obtain ⟨el0, el1, el2, el3, el4, hel_split, hel_pack⟩ := exists_entry36_last_cells kh.data (by omega)
        obtain ⟨ei0, ei1, ei2, ei3, ei4, hei_split, _⟩ := exists_entry36_at_cells kh.data i (by omega)
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 932#64) hF ?_
        apply SepWP.seq_cps (mid := (blkPl_366).base + 996#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        apply SepWP.seq_cps (mid := (blkPl_366).base + 1004#64)
        refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (hel_split prevPin.ptr)) (by sep_focus) ?_
        wp_steps
        refine SepWP.fold (Entails.of_eq (hel_split prevPin.ptr).symm) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (hei_split prevPin.ptr)) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        wp_steps
        have hwrite := pointsToBytes_write_moved36_at kh.data i (by omega) (by omega)
          el0 el1 el2 el3 el4 hel_pack prevPin.ptr
        refine SepWP.fold (Entails.of_eq hwrite) (by sep_focus) ?_
        have hrepack := prev_remove_swap_repack A prevPin.cap prevPin.ptr kh.data i x.self.params hlt36 hp_le
        dsimp only [KeyHistory.KEY_SIZE] at hrepack
        refine SepWP.fold hrepack (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
           (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal), htrace, (by wp_norm_goal)⟩
        have hex_eq : kh.data.extract i (i + 4) = (kh.data.drop i).take 4 := by
          rw [List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
        have hrem_drop : bytesLt ((kh.data.drop i).take 4) (toBEBytes 4 thVal) = true := by rwa [← hex_eq]
        have hres' :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let prevGc ← ChainResult.ofPanic
                (KeyHistory.gcLoop (kh.remove i x.self.params) (toBEBytes 4 thVal) x.self.params i)
              let recv2 := { recv1 with prev := prevGc }
              let (next', ctr', (_, outKey)) ←
                ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
              let recv' := { recv2 with next := next', ctr := ctr' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, gcLoop_of_remove kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds hrem_drop]
        have hrem_len : (kh.remove i x.self.params).data.length = kh.data.length - 36 :=
          remove_length_of_lt kh.data i x.self.params hlt36
        have hp_le' : (kh.remove i x.self.params).data.length ≤ prevPin.cap.toNat := by omega
        have hi_lt' : i < (kh.remove i x.self.params).data.length := by omega
        have hdec : (kh.remove i x.self.params).data.length - i < kh.data.length - i := by omega
        refine SepWPp.mono_pre _ ?_
          (h_next (kh.remove i x.self.params) i hp_le' hi_lt' hdec hres' _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by rw [hrem_len]; wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        rw [hrem_len]; sep_frame
      · have hlt36_f : decide (i + 36 < kh.data.length) = false := decide_eq_false hlt36
        wp_norm_hyp hlt36_f
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 660#64) hF ?_
        wp_steps
        refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
        have hpack_rem := vecU8At_pack_remove_last A
          (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
          prevPin.cap prevPin.ptr kh.data i x.self.params hi_lt hlt36 hp_le hp_cap hp_ptr
        have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
            x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
        have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
            x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
        rw [ha58, ha60] at hpack_rem; clear ha58 ha60
        refine SepWP.fold hpack_rem (by sep_focus) ?_
        refine SepWP.fold (pointsTo32_memRegion_32_entails_36 s0.sp (rev32Trunc thVal)) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
           (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal), htrace, (by wp_norm_goal)⟩
        have hex_eq : kh.data.extract i (i + 4) = (kh.data.drop i).take 4 := by
          rw [List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
        have hrem_drop : bytesLt ((kh.data.drop i).take 4) (toBEBytes 4 thVal) = true := by rwa [← hex_eq]
        have hrem_len : (kh.remove i x.self.params).data.length = i := by
          rw [← remove_data_eq_of_ge kh.data i x.self.params hlt36, List.length_take_of_le (Nat.le_of_lt hi_lt)]
        have hnot_lt : ¬ (i < (kh.remove i x.self.params).data.length) := by omega
        have hres660 :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let recv2 := { recv1 with prev := kh.remove i x.self.params }
              let (next', ctr', (_, outKey)) ←
                ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
              let recv' := { recv2 with next := next', ctr := ctr' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, gcLoop_of_remove kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds hrem_drop,
            gcLoop_of_ge (kh.remove i x.self.params) (toBEBytes 4 thVal) x.self.params i hnot_lt]; rfl
        refine SepWPp.mono_pre _ ?_
          (h_from660 { recv1 with prev := kh.remove i x.self.params }
            hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hres660 _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame
    · have hskip : bytesLt (kh.data.extract i (i + 4)) (toBEBytes 4 thVal) = false := Bool.eq_false_of_ne_true hrem
      wp_norm_hyp hskip
      by_cases hlt36 : i + 36 < kh.data.length
      · have hlt36_t : decide (i + 36 < kh.data.length) = true := decide_eq_true hlt36
        wp_norm_hyp hlt36_t
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 932#64) hF ?_
        wp_steps
        refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
           (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal), htrace, (by wp_norm_goal)⟩
        have hex_eq : kh.data.extract i (i + 4) = (kh.data.drop i).take 4 := by
          rw [List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
        have hskip_drop : bytesLt ((kh.data.drop i).take 4) (toBEBytes 4 thVal) = false := by rwa [← hex_eq]
        have hres' :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let prevGc ← ChainResult.ofPanic (KeyHistory.gcLoop kh (toBEBytes 4 thVal) x.self.params (i + 36))
              let recv2 := { recv1 with prev := prevGc }
              let (next', ctr', (_, outKey)) ←
                ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
              let recv' := { recv2 with next := next', ctr := ctr' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, gcLoop_of_skip kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds hskip_drop]; rfl
        have hdec : kh.data.length - (i + 36) < kh.data.length - i := by omega
        refine SepWPp.mono_pre _ ?_
          (h_next kh (i + 36) hp_le hlt36 hdec hres' _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame
      · have hlt36_f : decide (i + 36 < kh.data.length) = false := decide_eq_false hlt36
        wp_norm_hyp hlt36_f
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 660#64) hF ?_
        wp_steps
        refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
        have hpack_prev := vecU8At_pack_prev A
          (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
          prevPin.cap prevPin.ptr kh.data hp_le hp_cap hp_ptr
        have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
            x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
        have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
            x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
        rw [ha58, ha60] at hpack_prev; clear ha58 ha60
        refine SepWP.fold hpack_prev (by sep_focus) ?_
        refine SepWP.fold (pointsTo32_memRegion_32_entails_36 s0.sp (rev32Trunc thVal)) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
           (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal), htrace, (by wp_norm_goal)⟩
        have hex_eq : kh.data.extract i (i + 4) = (kh.data.drop i).take 4 := by
          rw [List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
        have hskip_drop : bytesLt ((kh.data.drop i).take 4) (toBEBytes 4 thVal) = false := by rwa [← hex_eq]
        have hres660 :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let recv2 := { recv1 with prev := kh }
              let (next', ctr', (_, outKey)) ←
                ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
              let recv' := { recv2 with next := next', ctr := ctr' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, gcLoop_of_skip kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds hskip_drop,
            gcLoop_of_ge kh (toBEBytes 4 thVal) x.self.params (i + KeyHistory.KEY_SIZE) hlt36]; rfl
        refine SepWPp.mono_pre _ ?_
          (h_from660 { recv1 with prev := kh }
            hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hres660 _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame

theorem recvKey_gc_loop_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc} {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)))
    (hnextKeyPanic : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpecWithStack A extHookStack))
    (hoom_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (hslice_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length) (gce : ChainEpochGhost) (prevPin : VecPin)
    (recv1 : ChainEpochDirection) (thVal : BitVec 32)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat) (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64) (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat) (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_le : recv1.next.length ≤ gce.recv.next.cap.toNat) (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0) (hp_cap : prevPin.cap.toNat < 2 ^ 63) (hp_ptr : prevPin.ptr ≠ 0) (fuel : Nat) :
    ∀ (kh : KeyHistory) (i : Nat) (_hfuel : kh.data.length - i ≤ fuel)
      (_hp_le : kh.data.length ≤ prevPin.cap.toNat) (_hi_lt : i < kh.data.length)
      (_hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
        let prevGc ← ChainResult.ofPanic (KeyHistory.gcLoop kh (toBEBytes 4 thVal) x.self.params i)
        let recv2 := { recv1 with prev := prevGc }
        let (next', ctr', (_, outKey)) ← ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
        let recv' := { recv2 with next := next', ctr := ctr' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
        return ({ x.self with links := links' }, outKey)))
      (s : State) (_hinv : RecvKeyPlacedStateInv lsmpl s0 s)
      (_hpc : s.pc = (blkPl_366).base + 932#64)
      (_hx0 : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 i) (_hx2 : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 kh.data.length)
      (_hx8 : s.readReg64 (.gpr 8#5) = prevPin.ptr) (_hx19 : s.readReg64 (.gpr 19#5) = x.out)
      (_hx21 : s.readReg64 (.gpr 21#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
      (_hx22 : s.readReg64 (.gpr 22#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)),
      let prog := (blkPC_366).rebase (blkPl_366).base H
      let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
      SepWPp prog (s0.readReg64 (.gpr 30#5)) s
        (memRegion x.out 32 ∗ chainOuterRecvAt A x epochIndex hi_ep gce ∗
          ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
          ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv1.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv1.next) ∗
          vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv1.next.length ∗
          ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗ ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
          ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 kh.data.length) ∗ (prevPin.ptr ↦ₛ kh.data) ∗
          vecU8Rest A prevPin.cap prevPin.ptr kh.data.length ∗
          ((epPtr + 0x68#64) ↦₃₂ recv1.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
          stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ ((s0.sp - 120#64) ↦₃₂ rev32Trunc thVal) ∗
          memRegion (s0.sp - 116#64) 32 ∗ recvKeyFrameRestAt s0 c3 ∗ A.pool)
        (recvKeyPost hkdf A x s0) (recvKeyPanic hkdf A x s0 R) := by
  induction fuel with
  | zero => intro kh i hfuel _ hi_lt; omega
  | succ fuel ih =>
    intro kh i hfuel hp_le hi_lt hres s hinv hpc hx0 hx2 hx8 hx19 hx21 hx22
    exact recvKey_gc_loop_step_placed hnextKey hnextKeyPanic hshim halloc hoom_ext hslice_ext
      x s0 c3 epochIndex hi_ep gce prevPin recv1 kh thVal i
      hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hp_le hp_cap hp_ptr hi_lt hres
      (fun kh' i' hp_le' hi_lt' hdec => ih kh' i' (by omega) hp_le' hi_lt')
      s hinv hpc hx0 hx2 hx8 hx19 hx21 hx22

set_option maxHeartbeats 800000 in
theorem recvKey_gc_from_616_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)))
    (hnextKeyPanic : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hoom_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (hslice_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail") = some Rust.panicked)
    (hpanic_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (prevPin : VecPin) (recv1 : ChainEpochDirection)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat) (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64) (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_le : recv1.next.length ≤ gce.recv.next.cap.toNat) (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0) (hp_le : recv1.prev.data.length ≤ prevPin.cap.toNat)
    (hp_cap : prevPin.cap.toNat < 2 ^ 63) (hp_ptr : prevPin.ptr ≠ 0)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let prevGc ← ChainResult.ofPanic (recv1.prev.gc recv1.ctr x.self.params)
      let recv2 := { recv1 with prev := prevGc }
      let (next', ctr', (_, outKey)) ←
        ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
      let recv' := { recv2 with next := next', ctr := ctr' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 616#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = recv1.ctr)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hw23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv1.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv1.next) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv1.next.length ∗
        ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗ ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv1.prev.data.length) ∗ (prevPin.ptr ↦ₛ recv1.prev.data) ∗
        vecU8Rest A prevPin.cap prevPin.ptr recv1.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv1.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗ A.pool)
      (recvKeyPost hkdf A x s0) (recvKeyPanic hkdf A x s0 R) := by
  intro prog s_idx epPtr
  have h_from660 := @recvKey_from_660_placed _ hkdf A H hnextKey hnextKeyPanic hshim halloc hoom_ext
    x s0 c3 R epochIndex hi_ep gce prevPin
  have h_loop := @recvKey_gc_loop_placed _ hkdf A H hnextKey hnextKeyPanic hshim halloc hoom_ext hslice_ext
    x s0 c3 R epochIndex hi_ep gce prevPin recv1
    (recv1.ctr - x.self.params.maxOooKeysOrDefault)
    hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hp_cap hp_ptr
  clear hnextKey hnextKeyPanic hshim halloc hoom_ext hslice_ext
  dsimp only [prog, s_idx, epPtr]; clear prog s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  have hbs_lt : recv1.prev.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have htrim_eq := trimSize_mul36_eq x.self.params
  dsimp only at htrim_eq
  have ⟨hult_trim, hule_trim, hult_uf, hule_uf⟩ :=
    gc_entry_arith_props recv1.prev.data.length recv1.ctr x.self.params hbs_lt
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hw8
  wp_norm_hyp hx19; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hw23; wp_norm_hyp htrace
  wp_norm_hyp htrim_eq; wp_norm_hyp hult_trim; wp_norm_hyp hule_trim; wp_norm_hyp hult_uf; wp_norm_hyp hule_uf
  by_cases hge : recv1.prev.data.length ≥ x.self.params.trimSize * KeyHistory.KEY_SIZE
  · have hge_t : decide (recv1.prev.data.length ≥ x.self.params.trimSize * KeyHistory.KEY_SIZE) = true :=
      decide_eq_true hge
    wp_norm_hyp hge_t
    by_cases huf : recv1.ctr < x.self.params.maxOooKeysOrDefault
    · have huf_t : decide (recv1.ctr < x.self.params.maxOooKeysOrDefault) = true := decide_eq_true huf
      wp_norm_hyp huf_t
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic_ext) fun hm => ?_
      have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
        rw [hres, keyHistory_gc_of_underflow recv1.prev recv1.ctr x.self.params hge huf]; rfl
      exact allowPanic_recvKey_panic hpan (by simp only [Rust.panicked, arm64_norm, htrace]) hm
    · have huf_f : decide (recv1.ctr < x.self.params.maxOooKeysOrDefault) = false := decide_eq_false huf
      wp_norm_hyp huf_f
      refine SepWPp.fold (Entails.of_eq (memRegion_36_split_u32 s0.sp)) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro d_sp8
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 932#64) hF ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
        ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
         (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal), htrace, (by wp_norm_goal)⟩
      have hres_loop :
          Chain.recvKey hkdf x.self x.epoch x.index = (do
            let prevGc ← ChainResult.ofPanic
              (KeyHistory.gcLoop recv1.prev (toBEBytes 4 (recv1.ctr - x.self.params.maxOooKeysOrDefault)) x.self.params 0)
            let recv2 := { recv1 with prev := prevGc }
            let (next', ctr', (_, outKey)) ←
              ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
            let recv' := { recv2 with next := next', ctr := ctr' }
            let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
            return ({ x.self with links := links' }, outKey)) := by
        rw [hres, keyHistory_gc_of_ok recv1.prev recv1.ctr x.self.params hge huf]
      have htrim_pos : 0 < x.self.params.trimSize * KeyHistory.KEY_SIZE := by
        dsimp [ChainParamsPB.trimSize, KeyHistory.KEY_SIZE]; omega
      have hpos : 0 < recv1.prev.data.length := by omega
      refine SepWPp.mono_pre _ ?_
        (h_loop recv1.prev.data.length recv1.prev 0 (Nat.sub_le _ _) hp_le hpos hres_loop _ hinv'
          (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
          (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
      sep_frame
  · have hge_f : decide (recv1.prev.data.length ≥ x.self.params.trimSize * KeyHistory.KEY_SIZE) = false :=
      decide_eq_false hge
    wp_norm_hyp hge_f
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 660#64) hF ?_
    wp_steps
    have hpack_prev := vecU8At_pack_prev A
      (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
      prevPin.cap prevPin.ptr recv1.prev.data hp_le hp_cap hp_ptr
    have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
    have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
    rw [ha58, ha60] at hpack_prev; clear ha58 ha60
    refine SepWP.fold hpack_prev (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
       (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal), htrace, (by wp_norm_goal)⟩
    have hres660 :
        Chain.recvKey hkdf x.self x.epoch x.index = (do
          let (next', ctr', (_, outKey)) ←
            ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv1.next recv1.ctr)
          let recv' := { recv1 with next := next', ctr := ctr' }
          let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
          return ({ x.self with links := links' }, outKey)) := by
      rw [hres, keyHistory_gc_of_lt recv1.prev recv1.ctr x.self.params hge]; rfl
    refine SepWPp.mono_pre _ ?_
      (h_from660 recv1 hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hres660 _ hinv'
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame

end CryptoVerification.SpqrV1.ChainProofs
