/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 10 (`Ct2Sampled`, `+1632`) — Error & Cleanup Paths

Proves stack/OOM (`+11572`) helpers, shared error epilogues at `+2084` and `+2064` (dropping
`sending_ct2`), error-cleanup deallocation paths at `+5844`, `+7236`, `+7212`, and `+5820` for
cloned `Authenticator` buffers, and `ProtoPolynomialEncoder` capacity-exposure helpers.
-/

namespace CryptoVerification.Swarm.IC10.Variant10a

open Arm64 ProofLib
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Alloc

structure V10Alloc (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop where
  alloc : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A)
  dealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr LibsignalTripleRatchet.deallocName) (rustDeallocSpec A)
  shim : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec
  session_memcpy_region : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
    (withStack sessionMemcpyRegionSpec allocHookStack)

namespace V10Alloc

variable {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}

theorem of_allocContracts (hA : AllocContracts b A ext) : V10Alloc b A ext :=
  ⟨hA.alloc, hA.dealloc, hA.shim,
   subroutine_ok_withStack_of_subroutine_ok hA.session_memcpy_region allocHookStack⟩

theorem of_4k (hA : AllocContracts4K b A ext) : V10Alloc b A ext :=
  ⟨hA.alloc, hA.dealloc, hA.shim,
   hA.session_memcpy_region allocHookStack (Nat.le_refl _) (by decide)⟩

theorem alloc_ok_at (hA : V10Alloc b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  sub_ok_at_of_fnAddr hA.alloc name k hk

theorem shim_ok_at (hA : V10Alloc b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec :=
  sub_ok_at_of_fnAddr hA.shim name k hk

theorem session_memcpy_region_ok_at (hA : V10Alloc b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack sessionMemcpyRegionSpec allocHookStack) :=
  sub_ok_at_of_fnAddr hA.session_memcpy_region name k hk

end V10Alloc

end CryptoVerification.Swarm.IC10.Variant10a

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open CryptoVerification.Swarm.IC10.Variant10a

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## 1. General WPp, Stack, & OOM Helpers -/

theorem v10_fnAddr_eq_sub_of_rel {P : Program} {n1 n2 : String} {k : Nat}
    {b : BitVec 64} {X : String → Option (State → State)}
    (hrel : (P.rebase b X).fnAddr n2 = (P.rebase b X).fnAddr n1 + BitVec.ofNat 64 k) :
    (P.rebase b X).fnAddr n1 = (P.rebase b X).fnAddr n2 - BitVec.ofNat 64 k := by
  rw [hrel, BitVec.add_sub_cancel]

private theorem v10_add_2080_sub_58308_eq (x : BitVec 64) :
    x + 2080#64 + 0xffffffffffff1c3c#64 = x - 56228#64 := by bv_omega

private theorem v10_sub_ok_drop_proto_poly_encoder_v10a
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : V10Alloc b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2080#64 + 0xffffffffffff1c3c#64)
      (dropProtoPolyEncoderSpec A) :=
  sub_ok_of_addr_eq
    (by
      rw [v10_add_2080_sub_58308_eq]
      exact v10_fnAddr_eq_sub_of_rel (Program.fnAddr_rel (k := 56228) (b := b) (X := Rust.withPanics ext)
        fnOff_drop_proto_poly_encoder statesFromPb_fnOff (by decide)))
    (drop_glue_proto_poly_encoder_ok_ext (b := b) (A := A) (ext := ext) hA.dealloc)

theorem Ext4K.v10_sub_ok_drop_proto_poly_encoder
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2080#64 + 0xffffffffffff1c3c#64)
      (dropProtoPolyEncoderSpec A) :=
  v10_sub_ok_drop_proto_poly_encoder_v10a (.of_4k hA)

theorem v10_sub_ok_drop_proto_poly_encoder
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2080#64 + 0xffffffffffff1c3c#64)
      (dropProtoPolyEncoderSpec A) :=
  v10_sub_ok_drop_proto_poly_encoder_v10a (.of_allocContracts hA)

theorem _root_.CryptoVerification.Swarm.IC10.Variant10a.v10_sub_ok_dealloc_125316_v10a
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : V10Alloc b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc"))) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff stubOff_rust_dealloc (by decide))
    hA.dealloc

theorem Ext4K.v10_sub_ok_dealloc_125316
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) :=
  v10_sub_ok_dealloc_125316_v10a (.of_4k hA)

theorem v10_sub_ok_dealloc_125316
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) :=
  v10_sub_ok_dealloc_125316_v10a (.of_allocContracts hA)

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

theorem v10_sepWPp_seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

theorem v10_onPanic_frame_entails {s0 sm sf : State} {F : SepProp}
    (htrace : TraceCalleeSaved sm s0) :
    (⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢
  rw [htrace.1] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

theorem v10_sepWPp_call_ret {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact hpre (F ∗ R') hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ hm => Satisfies.mono (sepConj_mono_left (hpan sf)) hm)
    (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))

theorem v10_pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

theorem v10_stackAt_encoderFromPbStack_to_allocHook (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v10_stackAt_allocHook_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v10_stackAt_encoderFromPbStack_to_dropStack48 (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp dropStack48 ∗ memRegion (fsp - 5152#64) 1008 := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack48 1008 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1008 ∗ stackAt fsp dropStack48 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v10_stackAt_dropStack48_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp dropStack48 ∗ memRegion (fsp - 5152#64) 1008 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack48 1008 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1008 ∗ stackAt fsp dropStack48 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

/-- Shared OOM cold path at `+11572` (`mov w0, #1; mov x1, x28; bl handle_error`). -/
theorem v10_states_from_pb_oom_11572
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (target_pc : BitVec 64) (P R : SepProp)
    (Q : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11572#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff statesFromPbName = 0x54cac := statesFromPb_fnOff
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := statesFromPbName) (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error")))
    (by rw [hfn, stubOff_handle_error])
  states_from_pb_fetches_range b (Rust.withPanics ext) 11572 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpanic hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error")))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
  unfold statesFromPbOnPanic
  simpa only [sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm

/-! ## 2. Shared Error Epilogues at `+2084` and `+2064` -/

/-- Shared `Err(err)` exit at `+2084` (`0x5a8c8 -> s0.x30`):
when `x21` has low byte `spqrErrorByte err` and `x19 = out`, writes `x21` to `[out + 8]`,
`noneCap, x26` to `[out + 16..32]`, and branches to `+60`. -/
theorem v10_states_from_pb_err_2084
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2084#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : (s1.readReg64 .x21).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rw [memRegion_out_928_split_32 out]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v24
  apply ProofLib.SepWP.exists_left; intro v16
  apply ProofLib.SepWP.exists_left; intro v8
  apply ProofLib.SepWP.exists_left; intro v0
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 60#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      (out ↦₆₄ v0) ∗
      ((out + 8#64) ↦₈ spqrErrorByte err) ∗
      memRegion (out + 9#64) 919 ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x8 = noneCap ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 2084 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htail := out_8_32_entails_err_tail out (s1.readReg64 .x21)
        18446744073709551615#64 (s1.readReg64 .x26)
      rw [hx21_1] at htail
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ s1.readReg64 .x21) ∗
           ((out + 16#64) ↦₆₄ 18446744073709551615#64) ∗
           ((out + 24#64) ↦₆₄ s1.readReg64 .x26) ∗
           memRegion (out + 32#64) 896) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ v0) ∗
           Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, htr2⟩
    exact states_from_pb_epilogue_60 s0 s2 out err v0 Rest hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

theorem _root_.CryptoVerification.Swarm.IC10.Variant10a.v10_states_from_pb_err_2064_v10a
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : V10Alloc b A ext)
    (s0 s1 : State) (out encAddr : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2064#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = encAddr)
    (hx22_1 : match optEnc with
      | none => s1.readReg64 .x22 = noneCap
      | some _ => (s1.readReg64 .x22).toNat < 2 ^ 63)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoPolynomialEncoderAt A encAddr optEnc ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion encAddr 56 ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2084#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      (memRegion encAddr 56 ∗ A.pool ∗ Rest))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = 0#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · cases optEnc with
    | none =>
      rw [optProtoPolynomialEncoderAt_none']
      states_from_pb_fetches_range b (Rust.withPanics ext) 2064 12
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx22_1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hm := optProtoPolyEncoder_none_entails_memRegion_56 encAddr
        dsimp only [noneCap] at hm
        refine Entails.trans
          (Entails.of_eq (show _ =
            ((encAddr ↦₆₄ 18446744073709551615#64) ∗ memRegion (encAddr + 8#64) 48) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             memRegion (s0.sp - 2400#64) 2304 ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
      · wp_done
    | some enc =>
      rw [optProtoPolynomialEncoderAt_some']
      have hne_none := cap_add_one_beq_zero_false hx22_1
      have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
        spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
      have hdrop := v10_sub_ok_drop_proto_poly_encoder_v10a hA
      simp only [dropProtoPolyEncoderSpec] at hdrop
      refine SepWP.weaken_pre
        (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_dropStack48 (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 2064 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, protoPolynomialEncoderSize,
        BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_dropStack48_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp1] at hst
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp dropStack48 ∗ memRegion (s0.sp - 7552#64) 1008) ∗
            (memRegion (s0.sp - 2400#64) 2304 ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗
             (memRegion encAddr 56 ∗ A.pool ∗ Rest)) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, htr2⟩
    have hx21_b : (s2.readReg64 .x21).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx21_2]; rfl
    have hep := v10_states_from_pb_err_2084 (A := A) (F := F) s0 s2 out .stateDecode
      (memRegion encAddr 56 ∗ A.pool ∗ Rest)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_b htr2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

theorem Ext4K.v10_states_from_pb_err_2064
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s1 : State) (out encAddr : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2064#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = encAddr)
    (hx22_1 : match optEnc with | none => s1.readReg64 .x22 = noneCap | some _ => (s1.readReg64 .x22).toNat < 2 ^ 63)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        optProtoPolynomialEncoderAt A encAddr optEnc ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion encAddr 56 ∗ A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_states_from_pb_err_2064_v10a (.of_4k hA) s0 s1 out encAddr optEnc Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx22_1 htr1

theorem v10_states_from_pb_err_2064
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s1 : State) (out encAddr : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2064#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = encAddr)
    (hx22_1 : match optEnc with | none => s1.readReg64 .x22 = noneCap | some _ => (s1.readReg64 .x22).toNat < 2 ^ 63)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        optProtoPolynomialEncoderAt A encAddr optEnc ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion encAddr 56 ∗ A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_states_from_pb_err_2064_v10a (.of_allocContracts hA) s0 s1 out encAddr optEnc Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx22_1 htr1

/-! ## 3. Shared Error-Cleanup Deallocation Paths at `+5844`, `+7236`, `+7212`, and `+5820` -/

/-- Shared `+5844` transition (`0x5b778 -> +2084`): `mov x21, xzr; b +2084`. -/
theorem v10_states_from_pb_err_5844
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (P : SepProp)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5844#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2084#64) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 5844 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

theorem _root_.CryptoVerification.Swarm.IC10.Variant10a.v10_states_from_pb_err_7236_v10a
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : V10Alloc b A ext)
    (s0 s1 : State) (out ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hca2_ne : (ca2 == 0#64) = false)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7236#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  dsimp only [vecCapPtrDealloc]
  simp only [hca2_ne, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v10_sub_ok_dealloc_125316_v10a hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  states_from_pb_fetches_range b (Rust.withPanics ext) 7236 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_apply
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
    have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
    have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
    rw [haddr] at hst
    nth_rw 1 [← hsp1] at hst
    rw [h184]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
        (((s0.sp - 2216#64) ↦₆₄ pa2) ∗ A.pool ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_left hst
  · wp_done

theorem Ext4K.v10_states_from_pb_err_7236
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s1 : State) (out ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hca2_ne : (ca2 == 0#64) = false) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7236#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca2 pa2 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_7236_v10a (.of_4k hA)
    s0 s1 out ca2 pa2 Rest hca2_ne hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

/-- Shared `+7236` transition (`0x5bce8 -> +2084`): when `(ca2 == 0#64) = false`,
deallocates `vecCapPtrDealloc A ca2 pa2` using `[sp + 184] = pa2` and `x26 = ca2`,
sets `x21 = 0`, and jumps to `+2084`. -/
theorem v10_states_from_pb_err_7236
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s1 : State) (out ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hca2_ne : (ca2 == 0#64) = false) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7236#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca2 pa2 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_7236_v10a (.of_allocContracts hA)
    s0 s1 out ca2 pa2 Rest hca2_ne hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

theorem _root_.CryptoVerification.Swarm.IC10.Variant10a.v10_states_from_pb_err_7212_v10a
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : V10Alloc b A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7212#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7232#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x26 = ca2 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hca1 : (ca1 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hca1, ↓reduceIte, sepConj_emp, emp_sepConj]
      states_from_pb_fetches_range b (Rust.withPanics ext) 7212 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · have hbeq : (ca1 == 0#64) = false := Bool.eq_false_iff.mpr hca1
      dsimp only [vecCapPtrDealloc]
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
        spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
      have hdealloc := v10_sub_ok_dealloc_125316_v10a hA
      simp only [rustDeallocSpec] at hdealloc
      refine SepWP.weaken_pre
        (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 7212 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
        have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp1] at hst
        rw [h200, h184]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2200#64) ↦₆₄ ca1) ∗
             ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
             (if (ca2 == 0#64) = true then emp else A.live pa2 ca2.toNat 1 ∗ memRegion pa2 ca2.toNat) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  ·
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    by_cases hca2 : (ca2 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hca2, ↓reduceIte, sepConj_emp, emp_sepConj]
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5844#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗
          Rest)
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 7232 4
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, htr3⟩
        exact v10_states_from_pb_err_5844 s0 s3 out _ hpc3 hrun3 hsp3 hx19_3 htr3
    · have hbeq : (ca2 == 0#64) = false := Bool.eq_false_iff.mpr hca2
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7236#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          vecCapPtrDealloc A ca2 pa2 ∗
          A.pool ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x26 = ca2 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 7232 4
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
        have h7236 := v10_states_from_pb_err_7236_v10a hA s0 s3 out ca2 pa2
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest)
          hbeq hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
        refine SepWP.mono h7236 ?_
        intro sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx21_f, htr_f⟩
        refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, hx21_f, htr_f⟩

theorem Ext4K.v10_states_from_pb_err_7212
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7212#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx26_1 : s1.readReg64 .x26 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_7212_v10a (.of_4k hA)
    s0 s1 out ca1 pa1 ca2 pa2 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 htr1

/-- Shared `+7212` error-cleanup path (`0x5bcd0 -> +2084`):
deallocates `vecCapPtrDealloc A ca1 pa1` (`[sp + 200] = ca1`, `x21 = pa1`) and
`vecCapPtrDealloc A ca2 pa2` (`x26 = ca2`, `[sp + 184] = pa2`), sets `x21 = 0`, and reaches `+2084`. -/
theorem v10_states_from_pb_err_7212
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7212#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx26_1 : s1.readReg64 .x26 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_7212_v10a (.of_allocContracts hA)
    s0 s1 out ca1 pa1 ca2 pa2 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 htr1

theorem _root_.CryptoVerification.Swarm.IC10.Variant10a.v10_states_from_pb_err_5820_v10a
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : V10Alloc b A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5820#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5840#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x26 = ca2 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hca1 : (ca1 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hca1, ↓reduceIte, sepConj_emp, emp_sepConj]
      states_from_pb_fetches_range b (Rust.withPanics ext) 5820 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · have hbeq : (ca1 == 0#64) = false := Bool.eq_false_iff.mpr hca1
      dsimp only [vecCapPtrDealloc]
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
        spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
      have hdealloc := v10_sub_ok_dealloc_125316_v10a hA
      simp only [rustDeallocSpec] at hdealloc
      refine SepWP.weaken_pre
        (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 5820 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
        have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp1] at hst
        rw [h200, h184]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2200#64) ↦₆₄ ca1) ∗
             ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
             (if (ca2 == 0#64) = true then emp else A.live pa2 ca2.toNat 1 ∗ memRegion pa2 ca2.toNat) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  ·
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    by_cases hca2 : (ca2 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hca2, ↓reduceIte, sepConj_emp, emp_sepConj]
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5844#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗
          Rest)
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 5840 4
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, htr3⟩
        exact v10_states_from_pb_err_5844 s0 s3 out _ hpc3 hrun3 hsp3 hx19_3 htr3
    · have hbeq : (ca2 == 0#64) = false := Bool.eq_false_iff.mpr hca2
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7236#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          vecCapPtrDealloc A ca2 pa2 ∗
          A.pool ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x26 = ca2 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 5840 4
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
        have h7236 := v10_states_from_pb_err_7236_v10a hA s0 s3 out ca2 pa2
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest)
          hbeq hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
        refine SepWP.mono h7236 ?_
        intro sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx21_f, htr_f⟩
        refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, hx21_f, htr_f⟩

theorem Ext4K.v10_states_from_pb_err_5820
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5820#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx26_1 : s1.readReg64 .x26 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_5820_v10a (.of_4k hA)
    s0 s1 out ca1 pa1 ca2 pa2 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 htr1

/-- Shared `+5820` error-cleanup path (`0x5b760 -> +2084`):
deallocates `vecCapPtrDealloc A ca1 pa1` (`[sp + 200] = ca1`, `x21 = pa1`) and
`vecCapPtrDealloc A ca2 pa2` (`x26 = ca2`, `[sp + 184] = pa2`), sets `x21 = 0`, and reaches `+2084`. -/
theorem v10_states_from_pb_err_5820
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5820#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx26_1 : s1.readReg64 .x26 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_5820_v10a (.of_allocContracts hA)
    s0 s1 out ca1 pa1 ca2 pa2 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 htr1

/-! ## 4. `Ct2Sampled` (`+1632`) Cap Exposure and Early Error Paths -/

/-- Pure condition on the exposed `cap` word at `d` of `optProtoPolynomialEncoderAt A d m`. -/
def v10_optEncoderCapProp (cap : BitVec 64) : Option ProtoPolynomialEncoder → Prop
  | none => cap = noneCap
  | some _ => cap.toNat < 2 ^ 63

/-- Remainder of `optProtoPolynomialEncoderAt A d m` after splitting out `d ↦₆₄ cap`. -/
def v10_optProtoPolyEncoderTail (A : RustAlloc) (d cap : BitVec 64)
    (m : Option ProtoPolynomialEncoder) : SepProp :=
  match m with
  | none => ⌜cap = noneCap⌝ ∗ memRegion (d + 8#64) 48
  | some pb =>
    ∃∗ ptr : BitVec 64,
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      protoPolynomialEncoderRestAt A d cap ptr pb

theorem v10_optProtoPolyEncoder_expose_cap (A : RustAlloc) (d : BitVec 64)
    (m : Option ProtoPolynomialEncoder) :
    optProtoPolynomialEncoderAt A d m ⊢
      ∃∗ cap : BitVec 64,
        ⌜v10_optEncoderCapProp cap m⌝ ∗
        (d ↦₆₄ cap) ∗ v10_optProtoPolyEncoderTail A d cap m := by
  cases m with
  | none =>
    rw [optProtoPolynomialEncoderAt_none']
    refine Entails.sepExists_right noneCap ?_
    unfold v10_optEncoderCapProp v10_optProtoPolyEncoderTail
    refine Entails.pure_right rfl ?_
    exact sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))
  | some pb =>
    rw [optProtoPolynomialEncoderAt_some']
    refine Entails.trans (protoPolynomialEncoderAt_expose_cap A d pb) ?_
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    apply Entails.pure_left; intro hlt
    refine Entails.sepExists_right cap ?_
    unfold v10_optEncoderCapProp v10_optProtoPolyEncoderTail
    refine Entails.pure_right hlt ?_
    refine Entails.trans ?_
      (sepConj_mono_right (Entails.sepExists_right ptr (Entails.pure_right hlt (Entails.refl _))))
    exact Entails.of_eq (by ac_rfl)

theorem v10_optProtoPolyEncoder_unexpose_cap (A : RustAlloc) (d cap : BitVec 64)
    (m : Option ProtoPolynomialEncoder) :
    (d ↦₆₄ cap) ∗ v10_optProtoPolyEncoderTail A d cap m ⊢
      optProtoPolynomialEncoderAt A d m := by
  cases m with
  | none =>
    unfold v10_optProtoPolyEncoderTail
    rw [← sepConj_assoc, sepConj_comm (d ↦₆₄ cap), sepConj_assoc]
    apply Entails.pure_left; intro hcap
    subst hcap
    rw [optProtoPolynomialEncoderAt_none']
    exact Entails.refl _
  | some pb =>
    unfold v10_optProtoPolyEncoderTail
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ptr
    rw [← sepConj_assoc, sepConj_comm (d ↦₆₄ cap), sepConj_assoc]
    apply Entails.pure_left; intro _
    rw [optProtoPolynomialEncoderAt_some']
    exact protoPolynomialEncoderAt_unexpose_cap A d cap ptr pb

theorem v10_fsp_split_192 (fsp : BitVec 64) :
    memRegion (fsp + 8#64) 2296 ⊢
      memRegion (fsp + 8#64) 184 ∗
      (∃∗ v_sp192 : BitVec 64, (fsp + 192#64) ↦₆₄ v_sp192) ∗
      memRegion (fsp + 200#64) 2104 := by
  rw [ProofLib.memRegion_split' (b := fsp + 8#64) (n := 184) (k := 2112)
        (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 8) (k := 2104)
        (b' := fsp + 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 192#64)]
  exact Entails.refl _

theorem v10_fsp_unsplit_192 (fsp v0 v192 : BitVec 64) :
    (fsp ↦₆₄ v0) ∗
      memRegion (fsp + 8#64) 184 ∗
      ((fsp + 192#64) ↦₆₄ v192) ∗
      memRegion (fsp + 200#64) 2104 ⊢
      memRegion fsp 2304 := by
  rw [ProofLib.memRegion_split fsp 8 2296 (by decide),
      ProofLib.memRegion_split' (b := fsp + 8#64) (n := 184) (k := 2112)
        (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 8) (k := 2104)
        (b' := fsp + 200#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion fsp v0)
    (sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 192#64) v192)))

theorem v10_pb_64_none_entails_160 (pbA : BitVec 64) :
    ((pbA + 64#64) ↦₆₄ none2Cap) ∗ memRegion (pbA + 72#64) 48 ∗ memRegion (pbA + 120#64) 104 ⊢
      memRegion (pbA + 64#64) 160 := by
  rw [ProofLib.memRegion_split' (b := pbA + 64#64) (n := 8) (k := 152)
        (b' := pbA + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := pbA + 72#64) (n := 48) (k := 104)
        (b' := pbA + 120#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (pbA + 64#64) none2Cap)

theorem v10_pb_64_auth_none_entails_160 (pbA epoch : BitVec 64) :
    ((pbA + 64#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 72#64) 40 ∗
      ((pbA + 112#64) ↦₆₄ epoch) ∗ memRegion (pbA + 120#64) 104 ⊢
      memRegion (pbA + 64#64) 160 := by
  rw [ProofLib.memRegion_split' (b := pbA + 64#64) (n := 8) (k := 152)
        (b' := pbA + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := pbA + 72#64) (n := 40) (k := 112)
        (b' := pbA + 112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := pbA + 112#64) (n := 8) (k := 104)
        (b' := pbA + 120#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion (pbA + 64#64) noneCap)
    (sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (pbA + 112#64) epoch)))

theorem v10_pb_tag_56_160_entails_224 (pbA tag : BitVec 64) :
    (pbA ↦₆₄ tag) ∗ memRegion (pbA + 8#64) 56 ∗ memRegion (pbA + 64#64) 160 ⊢
      memRegion pbA optProtoInnerStateSize := by
  dsimp only [optProtoInnerStateSize]
  rw [ProofLib.memRegion_split pbA 8 216 (by decide),
      ProofLib.memRegion_split' (b := pbA + 8#64) (n := 56) (k := 160)
        (b' := pbA + 64#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion pbA tag)

end CryptoVerification.SpqrV1.States.FromPb
