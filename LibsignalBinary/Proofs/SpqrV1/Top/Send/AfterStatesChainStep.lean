/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof
public import LibsignalBinary.Proofs.SpqrV1.Drop.States1a
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::send`: `send_key` Error Cleanup & `Chain::into_pb` Steps

Symbolic execution of `<Chain>::send_key` error cleanup (`0x31600 -> 0x31a3c`), `ChainPB` 9-word
relocation bridges, and `<Chain>::into_pb` pre/post steps (`0x316dc..0x317fc`) in
`spqr::send::<HookRng>`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.Prost.EncodeToVec

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::send::<libsignal_session::HookRng>")
  (ls_lemma% fnOff "<spqr::chain::Chain>::from_pb")
  (ls_lemma% fnOff "spqr::chain_from_version_negotiation")
  (ls_lemma% fnOff "<spqr::chain::Chain>::add_epoch")
  (ls_lemma% fnOff "<spqr::chain::Chain>::send_key")
  (ls_lemma% fnOff "<spqr::chain::Chain>::into_pb")
  (ls_lemma% fnOff "<spqr::v1::chunked::states::Message>::serialize")
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::into_pb")
  (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#1]")
  (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")
  (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic")
  (ls_stub% "core::panicking::panic_const::panic_const_sub_overflow")

theorem stackAt_spqrSendCallee_eq_dropStack32 (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - dropStack32) ∗
        stackAt sp dropStack32 :=
  ProofLib.stackAt_split_bottom sp dropStack32
    (spqrSendCalleeStack - dropStack32) (by decide)

theorem stackAt_spqrSendCallee_eq_allocHook (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  ProofLib.stackAt_split_bottom sp allocHookStack
    (spqrSendCalleeStack - allocHookStack) (by decide)

theorem stackAt_spqrSendCallee_eq_dropStackPoly64 (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - dropStackPoly64) ∗
        stackAt sp dropStackPoly64 :=
  ProofLib.stackAt_split_bottom sp dropStackPoly64
    (spqrSendCalleeStack - dropStackPoly64) (by decide)

/-- `0x31a08 -> 0x31a3c` (`+4524 -> +4576`): deallocates the `Chain.links` ring buffer (when
    `G.linksCap ≠ 0`), deallocates `Chain.next_root` (when `G.nextRoot.cap ≠ 0`), and calls
    `drop_glue::<States> [local#1]` (`0x35a6c`) on `s.sp + 0x190#64`. -/
theorem step_drop_chain_tail_31a08 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1Spec A F b))
    (s : State) (x23 : BitVec 64) (G : ChainGhost) (c : Chain)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4524#64)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = G.linksPtr)
    (hx21 : s.readReg64 .x21 = G.linksCap)
    (hx23 : s.readReg64 .x23 = x23)
    (hcap_lt : G.linksCap.toNat * 112 < 2 ^ 63)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4576#64) s
      (vecDequeHeader (s.sp + 0x590#64) G.linksCap G.linksPtr G.linksHead
        (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        (if G.linksCap = 0 then emp
         else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
           memRegion G.linksPtr (G.linksCap.toNat * 112)) ∗
        ((s.sp + 0x5b0#64) ↦₆₄ G.nextRoot.cap) ∗
        ((s.sp + 0x5b8#64) ↦₆₄ G.nextRoot.ptr) ∗
        memRegion (s.sp + 0x5c0#64) 40 ∗
        vecCapPtrDealloc A G.nextRoot.cap G.nextRoot.ptr ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTableAt b ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 0x590#64) 88 ∗
          memRegion (s.sp + 0x190#64) 928 ∗
          chunkedStatesLocal1JumpTableAt b ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hdrop_st : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 21008#64)
      (dropChunkedStatesLocal1Spec A F b) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 21008) (b := b) (X := Rust.withPanics ext)
      spqrSend_fnOff dropChunkedStatesLocal1_fnOff (by decide))
    hdrop_states
  clear hdealloc hdrop_states
  simp only [rustDeallocSpec] at hdealloc_raw
  simp only [dropChunkedStatesLocal1Spec] at hdrop_st
  have h88 :
      vecDequeHeader (s.sp + 1424#64) G.linksCap G.linksPtr G.linksHead
        (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        ((s.sp + 1456#64) ↦₆₄ G.nextRoot.cap) ∗
        ((s.sp + 1464#64) ↦₆₄ G.nextRoot.ptr) ∗
        memRegion (s.sp + 1472#64) 40 ⊢
        memRegion (s.sp + 1424#64) 88 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      chainHeaders_entails_memRegion_88 (s.sp + 1424#64) G.linksCap G.linksPtr G.linksHead
        (BitVec.ofNat 64 (G.epochs.zip c.links).length) G.nextRoot.cap G.nextRoot.ptr
  refine SepWP.seq
    (mid := (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4548#64)
    (Mid := fun s1 P1 =>
      s1.status = .Running ∧
      s1.trace = s.trace ∧
      s1.sp = s.sp ∧
      s1.readReg64 .x23 = x23 ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s ∧
      (P1 ⊢ vecDequeHeader (s.sp + 0x590#64) G.linksCap G.linksPtr G.linksHead
        (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        ((s.sp + 0x5b0#64) ↦₆₄ G.nextRoot.cap) ∗
        ((s.sp + 0x5b8#64) ↦₆₄ G.nextRoot.ptr) ∗
        memRegion (s.sp + 0x5c0#64) 40 ∗
        vecCapPtrDealloc A G.nextRoot.cap G.nextRoot.ptr ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTableAt b ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
    ?_ ?_
  · spqr_send_fetches_range b (Rust.withPanics ext) 4524 24
    dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::send::<libsignal_session::HookRng>" = entry
    examples_hide_fetches
    by_cases hc : G.linksCap = 0#64
    · have hc_beq : (G.linksCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx21 ⊢
      wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩
    · have hc_beq : ¬((G.linksCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_lsl7_sub_lsl4 hcap_lt
      simp only [hc, ↓reduceIte]
      wp_conv_pre => rw [stackAt_spqrSendCallee_eq_allocHook s.sp]
      wp_steps
      wp_call hdealloc_raw (G.linksPtr, G.linksCap.toNat * 112, 8)
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by simp only [wp_norm, arm64_norm, *],
          Entails.of_eq (by simp only [hsp_sf, stackAt_spqrSendCallee_eq_allocHook]; ac_rfl)⟩
  · intro s1 P1 hpc1 _ ⟨hrun1, htr1, hsp1, hx23_1, hvregs1, hP1⟩
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    refine SepWP.weaken_pre hP1 ?_
    refine SepWP.seq
      (mid := (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4568#64)
      (Mid := fun s2 P2 =>
        s2.status = .Running ∧
        s2.trace = s.trace ∧
        s2.sp = s.sp ∧
        s2.readReg64 .x23 = x23 ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s ∧
        (P2 ⊢ memRegion (s.sp + 0x590#64) 88 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
          chunkedStatesLocal1JumpTableAt b ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
      ?_ ?_
    · spqr_send_fetches_range b (Rust.withPanics ext) 4548 20
      dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "spqr::send::<libsignal_session::HookRng>" = entry
      examples_hide_fetches
      rw [← hsp1] at h88
      wp_conv_pre => rw [← hsp1]
      dsimp only [vecCapPtrDealloc]
      by_cases hnr : (G.nextRoot.cap == 0#64) = true <;>
        simp only [hnr, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken h88 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal, (by wp_norm_goal : _ = s1.trace).trans htr1,
            (by wp_norm_goal : _ = s1.sp).trans hsp1, by wp_norm_goal,
            (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1,
            Entails.of_eq (by simp only [hsp1])⟩
      · wp_conv_pre => rw [stackAt_spqrSendCallee_eq_allocHook s1.sp]
        wp_steps
        wp_call hdealloc_raw (G.nextRoot.ptr, G.nextRoot.cap.toNat, 1)
        refine SepWP.focus_weaken h88 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal, (by wp_norm_goal : _ = s1.trace).trans htr1,
            (by wp_norm_goal : _ = s1.sp).trans hsp1, by wp_norm_goal,
            (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s1).trans hvregs1,
            Entails.of_eq (by simp only [hsp_sf, hsp1, stackAt_spqrSendCallee_eq_allocHook]; ac_rfl)⟩
    · intro s2 P2 hpc2 _ ⟨hrun2, htr2, hsp2, hx23_2, hvregs2, hP2⟩
      have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
      refine SepWP.weaken_pre hP2 ?_
      spqr_send_fetches_range b (Rust.withPanics ext) 4568 8
      dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hdrop_st hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "spqr::send::<libsignal_session::HookRng>" = entry
      examples_hide_fetches
      wp_conv_pre => rw [← hsp2, stackAt_spqrSendCallee_eq_dropStackPoly64 s2.sp]
      wp_steps
      wp_call hdrop_st ⟨s2.sp + 400#64, st1⟩
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, (by wp_norm_goal : _ = s2.trace).trans htr2,
          (by wp_norm_goal : _ = s2.sp).trans hsp2, by wp_norm_goal,
          (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s2).trans hvregs2, by
            dsimp only [chunkedStatesSize]
            exact Entails.of_eq (by simp only [hsp_sf, hsp2, stackAt_spqrSendCallee_eq_dropStackPoly64]; ac_rfl)⟩

theorem sendKeyErrAt_entails_words (out : BitVec 64) (err : Error) :
    sendKeyErrAt out err ⊢
      (out ↦₆₄ 1#64) ∗
      (∃∗ d0 : BitVec 32, (out + 0x08#64) ↦₃₂ d0) ∗
      (∃∗ d1 : BitVec 32, (out + 0x0c#64) ↦₃₂ d1) ∗
      (∃∗ w2 : BitVec 64, (out + 0x10#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (out + 0x18#64) ↦₆₄ w3) ∗
      memRegion (out + 0x20#64) 8 := by
  unfold sendKeyErrAt
  have h24 :
      (match err with
       | .sendKeyEpochDecreased s e =>
         ((out + 16#64) ↦₆₄ s) ∗ ((out + 24#64) ↦₆₄ e) ∗ memRegion (out + 32#64) 8
       | .epochOutOfRange e =>
         ((out + 16#64) ↦₆₄ e) ∗ memRegion (out + 24#64) 16
       | _ => memRegion (out + 16#64) 24) ⊢
      (∃∗ w2 : BitVec 64, (out + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (out + 24#64) ↦₆₄ w3) ∗
      memRegion (out + 32#64) 8 := by
    rw [← ProofLib.memRegion_eight (out + 16#64), ← ProofLib.memRegion_eight (out + 24#64),
        ← ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 8)
            (b' := out + 32#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 16)
            (b' := out + 24#64) rfl (by bv_omega) (by decide)]
    cases err <;> try exact Entails.refl _
    · rw [ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 16)
            (b' := out + 24#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)
    · rw [ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 16)
            (b' := out + 24#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 8)
            (b' := out + 32#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  have h8 :
      ((out + 8#64) ↦₈ spqrErrorTag err) ∗ memRegion (out + 9#64) 7 ⊢
        (∃∗ d0 : BitVec 32, (out + 8#64) ↦₃₂ d0) ∗
        (∃∗ d1 : BitVec 32, (out + 12#64) ↦₃₂ d1) := by
    rw [← ProofLib.memRegion_four (out + 8#64), ← ProofLib.memRegion_four (out + 12#64),
        ← ProofLib.memRegion_split' (b := out + 8#64) (n := 4) (k := 4)
            (b' := out + 12#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 7)
            (b' := out + 9#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion _ _)
  rw [← sepConj_assoc ((out + 8#64) ↦₈ spqrErrorTag err),
      ← sepConj_assoc (∃∗ d0 : BitVec 32, (out + 8#64) ↦₃₂ d0)]
  exact sepConj_mono_right (sepConj_mono h8 h24)

theorem sendKeyErrSlot_entails_memRegion_40 (out : BitVec 64)
    (w0 : BitVec 64) (d0 d1 : BitVec 32) (w2 w3 : BitVec 64) :
    (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₃₂ d0) ∗ ((out + 12#64) ↦₃₂ d1) ∗
      ((out + 16#64) ↦₆₄ w2) ∗ ((out + 24#64) ↦₆₄ w3) ∗ memRegion (out + 32#64) 8 ⊢
      memRegion out 40 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 32) (b' := out + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 4) (k := 28) (b' := out + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 12#64) (n := 4) (k := 24) (b' := out + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 16) (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 8) (b' := out + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))))

theorem add_emp_arrayAt_nil (A : RustAlloc) (P : SepProp) (ptr : BitVec 64) :
    P ⊢ arrayAt (chainEpoch A) 112 ptr [] ∗ P := by
  dsimp only [arrayAt]
  exact Entails.of_eq (emp_sepConj P).symm

/-- `0x31600 -> 0x31a3c` (`+3492 -> +4576`): `Chain::send_key` error cleanup. Writes
    `spqrSendResultAt A ret none`, drops `chain1` at `s.sp + 0x590#64` (via `0x35ec4` and
    `__rust_dealloc`), and drops `st1` at `s.sp + 0x190#64` (via `0x35a6c`), reaching `0x31a3c`
    (`entry + 4576#64`). -/
theorem step_err_31600 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (hdrop_slice : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChainEpochSliceLocal1Name)
      (dropChainEpochSliceSpec A))
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1Spec A F b))
    (s : State) (ret x23 w0 : BitVec 64) (d0 d1 : BitVec 32) (w2 w3 : BitVec 64)
    (c : Chain) (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3492#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4576#64) s
      (memRegion ret 72 ∗
        ((s.sp + 0x1260#64) ↦₆₄ w0) ∗
        ((s.sp + 0x1268#64) ↦₃₂ d0) ∗
        ((s.sp + 0x126c#64) ↦₃₂ d1) ∗
        ((s.sp + 0x1270#64) ↦₆₄ w2) ∗
        ((s.sp + 0x1278#64) ↦₆₄ w3) ∗
        memRegion (s.sp + 0x1280#64) 8 ∗
        chainRepr A (s.sp + 0x590#64) c ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTableAt b ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret none ∗
          memRegion (s.sp + 0x1260#64) 40 ∗
          memRegion (s.sp + 0x590#64) 88 ∗
          memRegion (s.sp + 0x190#64) 928 ∗
          chunkedStatesLocal1JumpTableAt b ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hslice_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 22120#64)
      (dropChainEpochSliceSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 22120) (b := b) (X := Rust.withPanics ext)
      spqrSend_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#1]") (by decide))
    hdrop_slice
  clear hdrop_slice
  simp only [dropChainEpochSliceSpec] at hslice_raw
  dsimp only [chainRepr]
  wp_pull_exists; rename_i G
  refine SepWP.focus_weaken (chainAt_entails_dealloc A (s.sp + 0x590#64) G c) (by sep_focus) ?_
  unfold vecDequeAt vecDequeRingBuf vecDequeHeader
  wp_focus_pure
  rintro ⟨hlen_le, hcap_lt, hptr_ne, hhead⟩
  dsimp only [chainEpochSize, chainEpochAlign] at hcap_lt hslice_raw ⊢
  have h40 := sendKeyErrSlot_entails_memRegion_40 (s.sp + 4704#64) w0 d0 d1 w2 w3
  refine SepWP.seq
    (mid := (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4524#64)
    (Mid := fun s1 P1 =>
      s1.status = .Running ∧
      s1.trace = s.trace ∧
      s1.sp = s.sp ∧
      s1.readReg64 .x20 = G.linksPtr ∧
      s1.readReg64 .x21 = G.linksCap ∧
      s1.readReg64 .x23 = x23 ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s ∧
      (P1 ⊢ vecDequeHeader (s.sp + 0x590#64) G.linksCap G.linksPtr G.linksHead
        (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        (if G.linksCap = 0 then emp
         else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
           memRegion G.linksPtr (G.linksCap.toNat * 112)) ∗
        ((s.sp + 0x5b0#64) ↦₆₄ G.nextRoot.cap) ∗
        ((s.sp + 0x5b8#64) ↦₆₄ G.nextRoot.ptr) ∗
        memRegion (s.sp + 0x5c0#64) 40 ∗
        vecCapPtrDealloc A G.nextRoot.cap G.nextRoot.ptr ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTableAt b ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗
        (spqrSendResultAt A ret none ∗ memRegion (s.sp + 0x1260#64) 40 ∗ Frame)))
    ?_ ?_
  · have hdrop_states_keep := hdrop_states
    clear hdrop_states hdrop_states_keep
    spqr_send_fetches_range b (Rust.withPanics ext) 3492 76
    spqr_send_fetches_range b (Rust.withPanics ext) 3948 16
    spqr_send_fetches_range b (Rust.withPanics ext) 4484 40
    dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hslice_raw hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::send::<libsignal_session::HookRng>" = entry
    examples_hide_fetches
    wp_conv_pre => rw [memRegion_72_split_dwords_words ret, stackAt_spqrSendCallee_eq_dropStack32 s.sp]
    wp_pull_exists
    generalize hxs : G.epochs.zip c.links = xs at hlen_le ⊢
    cases xs with
    | nil =>
      have hnil_ent :
          (if G.linksCap = 0#64 then emp
           else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
             vecDequeSlotsAt (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr [] 0 G.linksCap.toNat) ⊢
          (if G.linksCap = 0#64 then emp
           else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
             memRegion G.linksPtr (G.linksCap.toNat * 112)) := by
        by_cases hc : G.linksCap = 0#64
        · simp [hc]; exact Entails.refl _
        · simp only [hc, ↓reduceIte]
          exact sepConj_mono_right (vecDequeSlotsAt_nil_entails_memRegion
            (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr hcap_lt)
      refine SepWP.focus_weaken hnil_ent (by sep_focus) ?_
      simp only [List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat]
      wp_steps
      refine SepWP.focus_weaken (add_emp_arrayAt_nil A ((s.sp + 1424#64) ↦₆₄ G.linksCap) G.linksPtr) (by sep_focus) ?_
      wp_call hslice_raw ⟨G.linksPtr, []⟩
      wp_steps
      refine SepWP.focus_weaken (add_emp_arrayAt_nil A ((s.sp + 1424#64) ↦₆₄ G.linksCap) G.linksPtr) (by sep_focus) ?_
      wp_call hslice_raw ⟨G.linksPtr, []⟩
      refine SepWP.focus_weaken (sendResultAt_none_of_dwords_words A ret
        (BitVec.truncate 32 (s.readReg64 (Reg.gpr 24#5))) d1 w2 w3) (by sep_focus) ?_
      refine SepWP.focus_weaken h40 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by simp only [wp_norm, arm64_norm, *], by
            unfold vecDequeHeader
            simp only [List.length_nil, BitVec.ofNat_eq_ofNat, memRegion_zero, emp_sepConj, sepConj_emp,
              Nat.mul_comm, BitVec.add_assoc, BitVec.reduceAdd,
              hsp_sf, stackAt_spqrSendCallee_eq_dropStack32 s.sp]
            exact Entails.of_eq (by ac_rfl)⟩
    | cons x tl =>
      have hlen_pos : 0 < (x :: tl).length := by simp
      have hlen_lt : (x :: tl).length * 112 < 2 ^ 63 := by
        have : (x :: tl).length * 112 ≤ G.linksCap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le
        omega
      have hcap_lt_pow : G.linksCap.toNat < 2 ^ 63 := by omega
      have hne0 := ofNat_beq_zero_false_112 hlen_pos hlen_lt
      have hcap_ne : G.linksCap ≠ 0#64 := by
        intro hc0; rw [hc0] at hlen_le; simp at hlen_le
      simp only [hcap_ne, BitVec.ofNat_eq_ofNat, ↓reduceIte] at hhead ⊢
      have hult : G.linksHead.ult G.linksCap = true := ult_of_toNat_lt hhead
      have haddr1 : G.linksPtr + BitVec.ofNat 64 (G.linksHead.toNat * 112) =
          G.linksPtr + G.linksHead * 112#64 := by
        rw [← mul_112_add_ptr, BitVec.add_comm]
      by_cases hwrap : (x :: tl).length ≤ G.linksCap.toNat - G.linksHead.toNat
      · have hule := ule_sub_of_le hcap_lt_pow hhead hwrap
        obtain ⟨ys, hys_len, hys_ent⟩ := vecDequeSlotsAt_nonwrap_entails
          (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) hcap_lt hhead hwrap
        let eps := ys.map Prod.snd
        have heps_len : eps.length = (x :: tl).length := by simp [eps, hys_len]
        have heps_lt : eps.length * 112 < 2 ^ 63 := by rw [heps_len]; exact hlen_lt
        have hx1_eq : G.linksHead + BitVec.ofNat 64 (x :: tl).length - G.linksHead =
            BitVec.ofNat 64 eps.length := by
          rw [Drop.add_sub_cancel_left_bv, heps_len]
        have hent_ep :
            vecDequeSlotsAt (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) 0 G.linksCap.toNat ⊢
            arrayAt (chainEpoch A) 112 (G.linksPtr + G.linksHead * 112#64) eps ∗
            memRegion G.linksPtr (G.linksHead.toNat * 112) ∗
            memRegion (G.linksPtr + BitVec.ofNat 64 ((G.linksHead.toNat + (x :: tl).length) * 112))
              ((G.linksCap.toNat - G.linksHead.toNat - (x :: tl).length) * 112) := by
          rw [← haddr1]
          exact Entails.trans hys_ent (sepConj_mono_left (arrayAt_chainEpochAt_entails_chainEpoch A _ ys))
        refine SepWP.focus_weaken hent_ep (by sep_focus) ?_
        wp_steps
        wp_call hslice_raw ⟨G.linksPtr + G.linksHead * 112#64, eps⟩
        wp_steps
        refine SepWP.focus_weaken (add_emp_arrayAt_nil A ((s.sp + 1424#64) ↦₆₄ G.linksCap) G.linksPtr) (by sep_focus) ?_
        wp_call hslice_raw ⟨G.linksPtr, []⟩
        rw [← haddr1, heps_len]
        refine SepWP.focus_weaken
          (vecDequeSlotsAt_nonwrap_rejoin 112 G.linksCap.toNat G.linksHead.toNat (x :: tl).length
            G.linksPtr hcap_lt hhead hwrap) (by sep_focus) ?_
        refine SepWP.focus_weaken (sendResultAt_none_of_dwords_words A ret
          (BitVec.truncate 32 (s.readReg64 (Reg.gpr 24#5))) d1 w2 w3) (by sep_focus) ?_
        refine SepWP.focus_weaken h40 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by simp only [wp_norm, arm64_norm, *], by
              unfold vecDequeHeader
              simp only [memRegion_zero, emp_sepConj, sepConj_emp,
                Nat.mul_comm, BitVec.add_assoc, BitVec.reduceAdd,
                hsp_sf, stackAt_spqrSendCallee_eq_dropStack32 s.sp]
              exact Entails.of_eq (by ac_rfl)⟩
      · have hgt : G.linksCap.toNat - G.linksHead.toNat < (x :: tl).length := by omega
        have hnule := not_ule_sub_of_gt hcap_lt_pow hhead hlen_le hgt
        obtain ⟨ys₁, ys₂, hys₁_len, hys₂_len, hys_ent⟩ := vecDequeSlotsAt_wrap_entails
          (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) hcap_lt hhead hlen_le hgt
        let eps₁ := ys₁.map Prod.snd
        let eps₂ := ys₂.map Prod.snd
        have heps₁_len : eps₁.length = G.linksCap.toNat - G.linksHead.toNat := by simp [eps₁, hys₁_len]
        have heps₂_len : eps₂.length = (x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat) := by
          simp [eps₂, hys₂_len]
        have heps₁_lt : eps₁.length * 112 < 2 ^ 63 := by
          rw [heps₁_len]
          have : (G.linksCap.toNat - G.linksHead.toNat) * 112 ≤ G.linksCap.toNat * 112 :=
            Nat.mul_le_mul_right 112 (by omega)
          omega
        have heps₂_lt : eps₂.length * 112 < 2 ^ 63 := by
          rw [heps₂_len]
          have : ((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat)) * 112 ≤ (x :: tl).length * 112 :=
            Nat.mul_le_mul_right 112 (by omega)
          omega
        have hent_ep :
            vecDequeSlotsAt (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) 0 G.linksCap.toNat ⊢
            arrayAt (chainEpoch A) 112 (G.linksPtr + G.linksHead * 112#64) eps₁ ∗
            arrayAt (chainEpoch A) 112 G.linksPtr eps₂ ∗
            memRegion (G.linksPtr + BitVec.ofNat 64 (((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat)) * 112))
              ((G.linksHead.toNat - ((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat))) * 112) := by
          rw [← haddr1]
          exact Entails.trans hys_ent
            (sepConj_mono (arrayAt_chainEpochAt_entails_chainEpoch A _ ys₁)
              (sepConj_mono_left (arrayAt_chainEpochAt_entails_chainEpoch A _ ys₂)))
        refine SepWP.focus_weaken hent_ep (by sep_focus) ?_
        wp_steps
        have hx1_1 : G.linksCap - G.linksHead = BitVec.ofNat 64 eps₁.length := by
          rw [heps₁_len, sub_eq_ofNat_sub (by omega)]
        wp_call hslice_raw ⟨G.linksPtr + G.linksHead * 112#64, eps₁⟩
        wp_steps
        have hx1_2 : BitVec.ofNat 64 (x :: tl).length - (G.linksCap - G.linksHead) =
            BitVec.ofNat 64 eps₂.length := by
          rw [heps₂_len, ofNat_sub_sub_eq hcap_lt_pow hhead (by omega) hlen_le]
        wp_call hslice_raw ⟨G.linksPtr, eps₂⟩
        rw [← haddr1, heps₁_len, heps₂_len]
        refine SepWP.focus_weaken
          (vecDequeSlotsAt_wrap_rejoin 112 G.linksCap.toNat G.linksHead.toNat (x :: tl).length
            G.linksPtr hcap_lt hhead hlen_le hgt) (by sep_focus) ?_
        refine SepWP.focus_weaken (sendResultAt_none_of_dwords_words A ret
          (BitVec.truncate 32 (s.readReg64 (Reg.gpr 24#5))) d1 w2 w3) (by sep_focus) ?_
        refine SepWP.focus_weaken h40 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by simp only [wp_norm, arm64_norm, *], by
              unfold vecDequeHeader
              simp only [Nat.mul_comm, BitVec.add_assoc, BitVec.reduceAdd,
                hsp_sf, stackAt_spqrSendCallee_eq_dropStack32 s.sp]
              exact Entails.of_eq (by ac_rfl)⟩
  · intro s1 P1 hpc1 _ ⟨hrun1, htr1, hsp1, hx20_1, hx21_1, hx23_1, hvregs1, hP1⟩
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    refine SepWP.weaken_pre hP1 ?_
    have hstep := step_drop_chain_tail_31a08 hb hdealloc hdrop_states s1 x23 G c st1
      (spqrSendResultAt A ret none ∗ memRegion (s.sp + 0x1260#64) 40 ∗ Frame)
      hpc1 hrun1 hx20_1 hx21_1 hx23_1 hcap_lt hsp1_align
    rw [hsp1] at hstep
    refine SepWP.mono hstep ?_
    intro sf Q _ _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩
    exact ⟨hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1, Entails.trans hQ (Entails.of_eq (by ac_rfl))⟩

/-! ## 4. Chain Step (`0x315b8 .. 0x31760`) and Chain Resolution (`0x314d8 .. 0x317fc`) -/

theorem links_len_or_grow_ok {len cap : Nat}
    (hle : len ≤ cap) (hbnd : len ≤ 2 ^ 54) :
    len < cap ∨ max (2 * cap) 4 * chainEpochSize < 2 ^ 63 := by
  by_cases hlt : len < cap
  · exact Or.inl hlt
  · right
    change max (2 * cap) 4 * 112 < 2 ^ 63
    omega

theorem list_length_le_sum_map_add {α : Type} (f : α → Nat) (c : Nat) (hc : 1 ≤ c) :
    ∀ l : List α, l.length ≤ (l.map (fun x => f x + c)).sum
  | [] => by simp
  | x :: xs => by
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := list_length_le_sum_map_add f c hc xs
    omega

theorem chain_links_length_le_rawChain (c : Chain) :
    c.links.length ≤ StateSize.rawChain c.intoPb := by
  have h1 := list_length_le_sum_map_add StateSize.rawChainEpoch 200 (by decide)
    c.intoPb.links
  have hlen : c.intoPb.links.length = c.links.length := by
    unfold Chain.intoPb
    simp
  rw [hlen] at h1
  unfold StateSize.rawChain
  omega

theorem memRegion_80_words10 (a : BitVec 64) :
    memRegion a 80 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (a + 32#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (a + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (a + 48#64) ↦₆₄ w6) ∗
      (∃∗ w7 : BitVec 64, (a + 56#64) ↦₆₄ w7) ∗
      (∃∗ w8 : BitVec 64, (a + 64#64) ↦₆₄ w8) ∗
      (∃∗ w9 : BitVec 64, (a + 72#64) ↦₆₄ w9) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 72) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 64) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 56) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 48) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 40) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 32) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 24) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 16) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 64#64) (n := 8) (k := 8) (b' := a + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64),
      ProofLib.memRegion_eight (a + 48#64), ProofLib.memRegion_eight (a + 56#64),
      ProofLib.memRegion_eight (a + 64#64), ProofLib.memRegion_eight (a + 72#64)]

theorem words10_to_memRegion_80 (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
    ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
    ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
    ((a + 72#64) ↦₆₄ w9) ⊢ memRegion a 80 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 72) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 64) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 56) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 48) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 40) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 32) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 24) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 16) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 64#64) (n := 8) (k := 8) (b' := a + 72#64) rfl (by bv_omega) (by decide)]
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (ProofLib.pointsTo64_entails_memRegion _ _)))))))))

/-- Pure relation characterizing the last two 64-bit words (`+0x40` and `+0x48`) of `ChainPB`:
    `params : Option ChainParamsPB` (`12` bytes at `+0x40..+0x4c`) and `direction : BitVec 32`
    (`4` bytes at `+0x4c..+0x50`). -/
def chainPBParamsDirWords (pb : ChainPB) (w8 w9 : BitVec 64) : Prop :=
  match pb.params with
  | none => ∃ p0 p1 : BitVec 32, w8 = p0 ++ 0#32 ∧ w9 = pb.direction ++ p1
  | some cp => w8 = cp.maxJump ++ 1#32 ∧ w9 = pb.direction ++ cp.maxOooKeys

/-- Address-independent heap part of `Top.ChainFrom.chainPBAt A g a pb`. -/
def chainPBHeapAt (A : RustAlloc) (g : ChainPBGhost) (pb : ChainPB) : SepProp :=
  ⌜g.epochs.length = pb.links.length ∧ g.linksCap ≠ noneCap⌝ ∗
    vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A)
      g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
    DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot

theorem optChainParamsDir_entails_words2 (a : BitVec 64) (pb : ChainPB) :
    optChainParamsPBAt (a + 0x40#64) pb.params ∗ ((a + 0x4c#64) ↦₃₂ pb.direction) ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64,
        ⌜chainPBParamsDirWords pb w8 w9⌝ ∗
        ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) := by
  have ha64 : a + 0x40#64 = a + 64#64 := rfl
  have ha68 : a + 64#64 + 4#64 = a + 68#64 := by bv_omega
  have ha72 : a + 64#64 + 8#64 = a + 72#64 := by bv_omega
  have ha76 : a + 0x4c#64 = a + 72#64 + 4#64 := by bv_omega
  cases hparams : pb.params with
  | none =>
    unfold chainPBParamsDirWords
    rw [hparams]
    dsimp only [optChainParamsPBAt]
    rw [ha64, ha68, ha76,
        ProofLib.memRegion_split' (b := a + 68#64) (n := 4) (k := 4)
          (b' := a + 72#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_four (a + 68#64),
        ProofLib.memRegion_four (a + 72#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro p1
    apply Entails.sepExists_elim; intro p0
    refine Entails.sepExists_right (p0 ++ 0#32) (Entails.sepExists_right (pb.direction ++ p1) ?_)
    refine Entails.pure_right ⟨p0, p1, rfl, rfl⟩ ?_
    have h1 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 64#64) 0#32 p0
    rw [ha68] at h1
    have h2 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 72#64) p1 pb.direction
    rw [← h1, ← h2]
    exact Entails.of_eq (by ac_rfl)
  | some cp =>
    unfold chainPBParamsDirWords
    rw [hparams]
    dsimp only [optChainParamsPBAt]
    rw [ha64, ha68, ha72, ha76]
    refine Entails.sepExists_right (cp.maxJump ++ 1#32)
      (Entails.sepExists_right (pb.direction ++ cp.maxOooKeys) ?_)
    refine Entails.pure_right ⟨rfl, rfl⟩ ?_
    have h1 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 64#64) 1#32 cp.maxJump
    rw [ha68] at h1
    have h2 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 72#64) cp.maxOooKeys pb.direction
    rw [← h1, ← h2]
    exact Entails.of_eq (by ac_rfl)

theorem words2_entails_optChainParamsDir (a : BitVec 64) (pb : ChainPB) (w8 w9 : BitVec 64)
    (hw : chainPBParamsDirWords pb w8 w9) :
    ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ⊢
      optChainParamsPBAt (a + 0x40#64) pb.params ∗ ((a + 0x4c#64) ↦₃₂ pb.direction) := by
  have ha64 : a + 0x40#64 = a + 64#64 := rfl
  have ha68 : a + 64#64 + 4#64 = a + 68#64 := by bv_omega
  have ha72 : a + 64#64 + 8#64 = a + 72#64 := by bv_omega
  have ha76 : a + 0x4c#64 = a + 72#64 + 4#64 := by bv_omega
  unfold chainPBParamsDirWords at hw
  cases hparams : pb.params with
  | none =>
    rw [hparams] at hw
    rcases hw with ⟨p0, p1, rfl, rfl⟩
    dsimp only [optChainParamsPBAt]
    rw [ha64, ha68, ha76,
        ← ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 64#64) 0#32 p0,
        ← ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 72#64) p1 pb.direction,
        ha68,
        ProofLib.memRegion_split' (b := a + 68#64) (n := 4) (k := 4)
          (b' := a + 72#64) rfl (by bv_omega) (by decide)]
    have hp0 := ProofLib.pointsTo32_entails_memRegion (a + 68#64) p0
    have hp1 := ProofLib.pointsTo32_entails_memRegion (a + 72#64) p1
    refine Entails.trans (Entails.of_eq (show
      (((a + 64#64) ↦₃₂ 0#32) ∗ ((a + 68#64) ↦₃₂ p0)) ∗
        (((a + 72#64) ↦₃₂ p1) ∗ ((a + 72#64 + 4#64) ↦₃₂ pb.direction)) =
      (((a + 64#64) ↦₃₂ 0#32) ∗ (((a + 68#64) ↦₃₂ p0) ∗ ((a + 72#64) ↦₃₂ p1))) ∗
        ((a + 72#64 + 4#64) ↦₃₂ pb.direction) by ac_rfl)) ?_
    exact sepConj_mono_left (sepConj_mono_right (sepConj_mono hp0 hp1))
  | some cp =>
    rw [hparams] at hw
    rcases hw with ⟨rfl, rfl⟩
    dsimp only [optChainParamsPBAt]
    rw [ha64, ha68, ha72, ha76,
        ← ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 64#64) 1#32 cp.maxJump,
        ← ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 72#64) cp.maxOooKeys pb.direction,
        ha68]
    exact Entails.of_eq (by ac_rfl)

/-- Unpack `ChainFromNorm.chainPBRestAt A g a pb` into 9 64-bit words at `a + 8..a + 72` plus
    `chainPBHeapAt A g pb`. -/
theorem chainPBRestAt_entails_words9 (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) (pb : ChainPB) :
    ChainFromNorm.chainPBRestAt A g a pb ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64,
        ⌜chainPBParamsDirWords pb w8 w9⌝ ∗
        ((a + 8#64) ↦₆₄ g.linksPtr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
        ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
        ((a + 48#64) ↦₆₄ pb.currentEpoch) ∗
        ((a + 56#64) ↦₆₄ pb.sendEpoch) ∗
        ((a + 64#64) ↦₆₄ w8) ∗
        ((a + 72#64) ↦₆₄ w9) ∗
        chainPBHeapAt A g pb := by
  have hvec : vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr pb.nextRoot =
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
      ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
      DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot := by
    unfold vecU8At vecHeader DecodeState.vecU8Heap
    have ha32 : a + 0x18#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 0x18#64 + 16#64 = a + 40#64 := by bv_omega
    rw [ha32, ha40]
    ac_rfl
  unfold ChainFromNorm.chainPBRestAt chainPBHeapAt
  rw [hvec]
  apply Entails.pure_left; intro hlen
  have h1 := ChainFromNorm.vecBuf_linksCap_ne_noneCap A g.linksCap g.linksPtr (g.epochs.zip pb.links)
  have h2 := optChainParamsDir_entails_words2 a pb
  refine Entails.trans (Entails.of_eq (show
    ((a + 8#64) ↦₆₄ g.linksPtr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
      vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
      (((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
        ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
        DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot) ∗
      ((a + 0x30#64) ↦₆₄ pb.currentEpoch) ∗
      ((a + 0x38#64) ↦₆₄ pb.sendEpoch) ∗
      optChainParamsPBAt (a + 0x40#64) pb.params ∗
      ((a + 0x4c#64) ↦₃₂ pb.direction) =
    vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
      (optChainParamsPBAt (a + 0x40#64) pb.params ∗ ((a + 0x4c#64) ↦₃₂ pb.direction)) ∗
      (((a + 8#64) ↦₆₄ g.linksPtr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
        ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
        ((a + 48#64) ↦₆₄ pb.currentEpoch) ∗
        ((a + 56#64) ↦₆₄ pb.sendEpoch) ∗
        DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w9
  apply Entails.pure_left; intro hcap_ne
  refine Entails.trans (Entails.of_eq (show
    vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
      ⌜chainPBParamsDirWords pb w8 w9⌝ ∗
      ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗
      ((a + 8#64) ↦₆₄ g.linksPtr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
      ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
      ((a + 48#64) ↦₆₄ pb.currentEpoch) ∗
      ((a + 56#64) ↦₆₄ pb.sendEpoch) ∗
      DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot =
    ⌜chainPBParamsDirWords pb w8 w9⌝ ∗
      vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
      (((a + 8#64) ↦₆₄ g.linksPtr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
        ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
        ((a + 48#64) ↦₆₄ pb.currentEpoch) ∗
        ((a + 56#64) ↦₆₄ pb.sendEpoch) ∗
        ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗
        DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot) by ac_rfl)) ?_
  apply Entails.pure_left; intro hw
  refine Entails.sepExists_right w8 (Entails.sepExists_right w9 ?_)
  refine Entails.pure_right hw ?_
  have hpure :
      vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) g.linksCap g.linksPtr (g.epochs.zip pb.links) ⊢
        ⌜g.epochs.length = pb.links.length ∧ g.linksCap ≠ noneCap⌝ ∗
          vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) g.linksCap g.linksPtr (g.epochs.zip pb.links) :=
    Entails.pure_right ⟨hlen, hcap_ne⟩ (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hpure) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Repack 9 64-bit words at `a + 8..a + 72` plus `chainPBHeapAt A g pb` into
    `ChainFromNorm.chainPBRestAt A g a pb`. -/
theorem words9_entails_chainPBRestAt (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) (pb : ChainPB)
    (w8 w9 : BitVec 64) (hw : chainPBParamsDirWords pb w8 w9) :
    ((a + 8#64) ↦₆₄ g.linksPtr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
      ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
      ((a + 48#64) ↦₆₄ pb.currentEpoch) ∗
      ((a + 56#64) ↦₆₄ pb.sendEpoch) ∗
      ((a + 64#64) ↦₆₄ w8) ∗
      ((a + 72#64) ↦₆₄ w9) ∗
      chainPBHeapAt A g pb ⊢
      ChainFromNorm.chainPBRestAt A g a pb := by
  have hvec : vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr pb.nextRoot =
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
      ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
      DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot := by
    unfold vecU8At vecHeader DecodeState.vecU8Heap
    have ha32 : a + 0x18#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 0x18#64 + 16#64 = a + 40#64 := by bv_omega
    rw [ha32, ha40]
    ac_rfl
  unfold ChainFromNorm.chainPBRestAt chainPBHeapAt
  rw [hvec]
  have h2 := words2_entails_optChainParamsDir a pb w8 w9 hw
  refine Entails.trans (Entails.of_eq (show
    ((a + 8#64) ↦₆₄ g.linksPtr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
      ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
      ((a + 48#64) ↦₆₄ pb.currentEpoch) ∗
      ((a + 56#64) ↦₆₄ pb.sendEpoch) ∗
      ((a + 64#64) ↦₆₄ w8) ∗
      ((a + 72#64) ↦₆₄ w9) ∗
      (⌜g.epochs.length = pb.links.length ∧ g.linksCap ≠ noneCap⌝ ∗
        vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A)
          g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
        DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot) =
    ⌜g.epochs.length = pb.links.length ∧ g.linksCap ≠ noneCap⌝ ∗
      (((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9)) ∗
      (((a + 8#64) ↦₆₄ g.linksPtr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
        vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A)
          g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
        (((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
          ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
          DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot) ∗
        ((a + 0x30#64) ↦₆₄ pb.currentEpoch) ∗
        ((a + 0x38#64) ↦₆₄ pb.sendEpoch)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hlen, _⟩
  refine Entails.pure_right hlen ?_
  refine Entails.trans (sepConj_mono_left h2) ?_
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_72_words9 (a : BitVec 64) :
    memRegion a 72 =
      (∃∗ w1 : BitVec 64, a ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 8#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 16#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (a + 24#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (a + 32#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (a + 40#64) ↦₆₄ w6) ∗
      (∃∗ w7 : BitVec 64, (a + 48#64) ↦₆₄ w7) ∗
      (∃∗ w8 : BitVec 64, (a + 56#64) ↦₆₄ w8) ∗
      (∃∗ w9 : BitVec 64, (a + 64#64) ↦₆₄ w9) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 64) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 56) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 48) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 40) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 32) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 24) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 16) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 8) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64),
      ProofLib.memRegion_eight (a + 48#64), ProofLib.memRegion_eight (a + 56#64),
      ProofLib.memRegion_eight (a + 64#64)]

theorem words9_to_memRegion_72 (a w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) :
    (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗
    ((a + 24#64) ↦₆₄ w4) ∗ ((a + 32#64) ↦₆₄ w5) ∗ ((a + 40#64) ↦₆₄ w6) ∗
    ((a + 48#64) ↦₆₄ w7) ∗ ((a + 56#64) ↦₆₄ w8) ∗ ((a + 64#64) ↦₆₄ w9) ⊢ memRegion a 72 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 64) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 56) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 48) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 40) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 32) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 24) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 16) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 8) (b' := a + 64#64) rfl (by bv_omega) (by decide)]
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (ProofLib.pointsTo64_entails_memRegion _ _))))))))

/-- Representation of `chainPb : Option ChainPB` at `0x317fc`, split between register `x25`
    (holding the first 8-byte word `links.cap` / `noneCap`) and the 72-byte stack slot at `a_slot`
    (`sp + 0xd90#64`):
    * `none`: `⌜x25 = noneCap⌝ ∗ memRegion a_slot 72`
    * `some ch`: `∃∗ g : ChainPBGhost, ⌜x25 = g.linksCap ∧ g.linksCap ≠ noneCap⌝ ∗ ChainFromNorm.chainPBRestAt A g (a_slot - 8#64) ch` -/
def optChainPBRegSlotAt (A : RustAlloc) (a_slot : BitVec 64) (x25 : BitVec 64) :
    Option ChainPB → SepProp
  | none => ⌜x25 = noneCap⌝ ∗ memRegion a_slot 72
  | some ch =>
    ∃∗ g : ChainPBGhost,
      ⌜x25 = g.linksCap ∧ g.linksCap ≠ noneCap⌝ ∗
        ChainFromNorm.chainPBRestAt A g (a_slot - 8#64) ch

/-- `0x31734 -> 0x317fc` (`+3800 -> +4000`): After `<spqr::chain::Chain>::into_pb` writes
    `ProtoRepr.chainPBAt A (s.sp + 0x1060#64) ch`, loads `x25 := [s.sp + 0x1060]` and copies the
    remaining 72 bytes (`+8..+80`) to `[s.sp + 0xd90..0xdd8]`, forming `optChainPBRegSlotAt A
    (s.sp + 0xd90#64) x25 (some ch)` and jumping to `0x317fc`. -/
theorem step_post_chain_into_pb_31734 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (ch : ChainPB) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3800#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = s.sp + 0x1060#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4000#64) s
      (CryptoVerification.SpqrV1.ProtoRepr.chainPBAt A (s.sp + 0x1060#64) ch ∗
        memRegion (s.sp + 0xd90#64) 72 ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg32 .x24 = s.readReg32 .x24 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ optChainPBRegSlotAt A (s.sp + 0xd90#64) (sf.readReg64 .x25) (some ch) ∗
          memRegion (s.sp + 0x1060#64) 80 ∗ Frame)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 3800 48
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  rw [ChainFrom.chainPBAt_protoRepr_eq_exists A (s.sp + 4192#64) ch,
      memRegion_72_words9 (s.sp + 3472#64)]
  wp_pull_exists; rename_i d1 d2 d3 d4 d5 d6 d7 d8 d9 g
  refine SepWP.focus_weaken (ChainFromNorm.chainPBAt_expose_cap A g (s.sp + 4192#64) ch) (by sep_focus) ?_
  wp_focus_pure; intro hcap_ne
  refine SepWP.focus_weaken (chainPBRestAt_entails_words9 A g (s.sp + 4192#64) ch) (by sep_focus) ?_
  wp_pull_exists; rename_i w8 w9
  wp_focus_pure; intro hw
  wp_steps
  have hd88 : (s.sp + 3472#64) - 8#64 = s.sp + 3464#64 := by bv_omega
  have hrest := words9_entails_chainPBRestAt A g (s.sp + 3464#64) ch w8 w9 hw
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrest
  have h80 := words10_to_memRegion_80 (s.sp + 4192#64)
    g.linksCap g.linksPtr (BitVec.ofNat 64 (g.epochs.zip ch.links).length)
    g.nextRoot.cap g.nextRoot.ptr (BitVec.ofNat 64 ch.nextRoot.length)
    ch.currentEpoch ch.sendEpoch w8 w9
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h80
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken h80 (by sep_focus) ?_
  refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
  dsimp only [optChainPBRegSlotAt]
  rw [hd88]
  refine Entails.trans (Entails.of_eq (show memRegion (s.sp + 4192#64) 80 ∗
      ChainFromNorm.chainPBRestAt A g (s.sp + 3464#64) ch ∗ Frame =
      ChainFromNorm.chainPBRestAt A g (s.sp + 3464#64) ch ∗
      memRegion (s.sp + 4192#64) 80 ∗ Frame by ac_rfl)) ?_
  refine sepConj_mono_left ?_
  refine Entails.sepExists_right g ?_
  exact Entails.pure_right ⟨by wp_norm_goal, hcap_ne⟩ (Entails.refl _)

theorem sendKeyOkSlot_entails_words11 (A : RustAlloc) (a : BitVec 64) (idx : BitVec 32) (msgKey : Bytes) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₃₂ idx) ∗ memRegion (a + 12#64) 4 ∗
      vecU8 A (a + 16#64) msgKey) ∗ memRegion (a + 40#64) 48 ⊢
      ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
      ∃∗ d1 : BitVec 64, ∃∗ d5 : BitVec 64, ∃∗ d6 : BitVec 64,
      ∃∗ d7 : BitVec 64, ∃∗ d8 : BitVec 64, ∃∗ d9 : BitVec 64, ∃∗ d10 : BitVec 64,
        (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ d1) ∗
        ((a + 16#64) ↦₆₄ mkCap) ∗ ((a + 24#64) ↦₆₄ mkPtr) ∗
        ((a + 32#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
        ((a + 40#64) ↦₆₄ d5) ∗ ((a + 48#64) ↦₆₄ d6) ∗
        ((a + 56#64) ↦₆₄ d7) ∗ ((a + 64#64) ↦₆₄ d8) ∗
        ((a + 72#64) ↦₆₄ d9) ∗ ((a + 80#64) ↦₆₄ d10) ∗
        DecodeState.vecU8Heap A mkCap mkPtr msgKey := by
  have hd1 : ((a + 8#64) ↦₃₂ idx) ∗ memRegion (a + 12#64) 4 ⊢
      ∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1 := by
    rw [← ProofLib.memRegion_eight (a + 8#64),
        ProofLib.memRegion_split' (b := a + 8#64) (n := 4) (k := 4)
          (b' := a + 12#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _)
  have hvec : ∀ c p : BitVec 64,
      vecU8At A (a + 16#64) c p msgKey =
        ((a + 16#64) ↦₆₄ c) ∗ ((a + 24#64) ↦₆₄ p) ∗
        ((a + 32#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
        DecodeState.vecU8Heap A c p msgKey := by
    intro c p
    unfold vecU8At vecHeader DecodeState.vecU8Heap
    have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
    have ha32 : a + 16#64 + 16#64 = a + 32#64 := by bv_omega
    rw [ha24, ha32]
    ac_rfl
  rw [ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 40) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 32) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 24) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 64#64) (n := 8) (k := 16) (b' := a + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 72#64) (n := 8) (k := 8) (b' := a + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 40#64), ProofLib.memRegion_eight (a + 48#64),
      ProofLib.memRegion_eight (a + 56#64), ProofLib.memRegion_eight (a + 64#64),
      ProofLib.memRegion_eight (a + 72#64), ProofLib.memRegion_eight (a + 80#64)]
  unfold vecU8
  simp only [hvec, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro d10
  apply Entails.sepExists_elim; intro d9
  apply Entails.sepExists_elim; intro d8
  apply Entails.sepExists_elim; intro d7
  apply Entails.sepExists_elim; intro d6
  apply Entails.sepExists_elim; intro d5
  apply Entails.sepExists_elim; intro mkCap
  apply Entails.sepExists_elim; intro mkPtr
  refine Entails.trans (Entails.of_eq (show
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₃₂ idx) ∗ memRegion (a + 12#64) 4 ∗
      ((a + 16#64) ↦₆₄ mkCap) ∗ ((a + 24#64) ↦₆₄ mkPtr) ∗
      ((a + 32#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
      DecodeState.vecU8Heap A mkCap mkPtr msgKey ∗
      ((a + 40#64) ↦₆₄ d5) ∗ ((a + 48#64) ↦₆₄ d6) ∗
      ((a + 56#64) ↦₆₄ d7) ∗ ((a + 64#64) ↦₆₄ d8) ∗
      ((a + 72#64) ↦₆₄ d9) ∗ ((a + 80#64) ↦₆₄ d10) =
    (((a + 8#64) ↦₃₂ idx) ∗ memRegion (a + 12#64) 4) ∗
      ((a ↦₆₄ 0#64) ∗
        ((a + 16#64) ↦₆₄ mkCap) ∗ ((a + 24#64) ↦₆₄ mkPtr) ∗
        ((a + 32#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
        ((a + 40#64) ↦₆₄ d5) ∗ ((a + 48#64) ↦₆₄ d6) ∗
        ((a + 56#64) ↦₆₄ d7) ∗ ((a + 64#64) ↦₆₄ d8) ∗
        ((a + 72#64) ↦₆₄ d9) ∗ ((a + 80#64) ↦₆₄ d10) ∗
        DecodeState.vecU8Heap A mkCap mkPtr msgKey) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hd1) ?_
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro d1
  refine Entails.sepExists_right mkCap (Entails.sepExists_right mkPtr
    (Entails.sepExists_right d1 (Entails.sepExists_right d5
    (Entails.sepExists_right d6 (Entails.sepExists_right d7
    (Entails.sepExists_right d8 (Entails.sepExists_right d9
    (Entails.sepExists_right d10 ?_))))))))
  exact Entails.of_eq (by ac_rfl)

/-- `0x316dc -> 0x60514` (`+3712 -> +195768`): Extracts `(mkCap, mkPtr, msgKey.length)` from
    `sendKeyOkAt` at `s.sp + 0x1260#64` into `[s.sp + 0x28]`, `[s.sp + 0x8]`, and `x22`, copies
    `chainRepr A (s.sp + 0x590#64) c2` to `s.sp + 0x1260#64`, and calls
    `<spqr::chain::Chain>::into_pb` (`x8 = s.sp + 0x1060#64`, `x0 = s.sp + 0x1260#64`). -/
theorem step_pre_chain_into_pb_316dc {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (idx : BitVec 32) (msgKey : Bytes) (c2 : Chain) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3712#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 174044#64) s
      (((s.sp + 0x1260#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x1268#64) ↦₃₂ idx) ∗
        memRegion (s.sp + 0x126c#64) 4 ∗ vecU8 A (s.sp + 0x1270#64) msgKey ∗
        memRegion (s.sp + 0x1288#64) 48 ∗
        chainRepr A (s.sp + 0x590#64) c2 ∗
        memRegion (s.sp + 0x28#64) 8 ∗
        memRegion (s.sp + 0x8#64) 8 ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x8 = s.sp + 0x1060#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3800#64 ∧
        sf.readReg64 .x22 = BitVec.ofNat 64 msgKey.length ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg32 .x24 = s.readReg32 .x24 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ ∃∗ G : ChainGhost, ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          chainAt A (s.sp + 0x1260#64) G c2 ∗
          ((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗
          DecodeState.vecU8Heap A mkCap mkPtr msgKey ∗
          memRegion (s.sp + 0x590#64) 88 ∗ Frame)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 3712 88
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  rw [ProofLib.memRegion_eight (s.sp + 40#64), ProofLib.memRegion_eight (s.sp + 8#64)]
  wp_pull_exists; rename_i old28 old8
  have hok_words := sendKeyOkSlot_entails_words11 A (s.sp + 4704#64) idx msgKey
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hok_words
  refine SepWP.focus_weaken hok_words (by sep_focus) ?_
  wp_pull_exists; rename_i mkCap mkPtr d1 d5 d6 d7 d8 d9 d10
  refine SepWP.focus_weaken (ChainFromNorm.chainRepr_entails_words11 A (s.sp + 1424#64) c2) (by sep_focus) ?_
  wp_pull_exists; rename_i G pad
  wp_focus_pure; intro hcap_ne
  wp_steps
  have hpack := ChainFromNorm.words11_entails_chainRepr A (s.sp + 4704#64) G c2 pad
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack
  have h88 := ChainFromNorm.words11_to_memRegion_88 (s.sp + 1424#64)
    G.linksCap G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip c2.links).length)
    G.nextRoot.cap G.nextRoot.ptr (BitVec.ofNat 64 c2.nextRoot.length)
    c2.currentEpoch c2.sendEpoch (c2.params.maxOooKeys ++ c2.params.maxJump) (pad ++ c2.dir.toI32)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h88
  refine SepWP.focus_weaken hpack (by sep_focus) ?_
  refine SepWP.focus_weaken h88 (by sep_focus) ?_
  refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
  dsimp only [chainRepr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro G'
  refine Entails.sepExists_right G' (Entails.sepExists_right mkCap
    (Entails.sepExists_right mkPtr ?_))
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Send
