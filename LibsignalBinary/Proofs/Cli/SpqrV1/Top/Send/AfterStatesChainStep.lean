/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainStep
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.Decodes
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1a
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::send` Phase 3b Chain Step and `send_key` Error Cleanup (`+3492..+4576`)

Proves the `Chain::send_key` error cleanup (`+3492 -> +4576`) and the `Chain::into_pb` call
and result relocation (`+3712 -> +4000`) in `spqr::send::<signal_session_ratchet::Coins>`.
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
  (ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>")
  (ls_lemma% fnOff "<spqr::chain::Chain>::from_pb")
  (ls_lemma% fnOff "spqr::chain_from_version_negotiation")
  (ls_lemma% fnOff "<spqr::chain::Chain>::add_epoch")
  (ls_lemma% fnOff "<spqr::chain::Chain>::send_key")
  (ls_lemma% fnOff "<spqr::chain::Chain>::into_pb")
  (ls_lemma% fnOff "<spqr::v1::chunked::states::Message>::serialize")
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::into_pb")
  (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#3]")
  (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#3]")
  (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic")
  (ls_stub% "core::panicking::panic_const::panic_const_sub_overflow")

/-- `+4524 -> +4576`: deallocates `Chain.links` (when `G.linksCap ≠ 0`) and `Chain.next_root`
(when `G.nextRoot.cap ≠ 0`), and calls `drop_glue::<States>` on `s.sp + 0x190#64`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_drop_chain_tail_31a08 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Name)
      (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec A F b))
    (s : State) (x23 : BitVec 64) (G : ChainGhost) (c : Chain)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4524#64)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = G.linksPtr)
    (hx21 : s.readReg64 .x21 = G.linksCap)
    (hx23 : s.readReg64 .x23 = x23)
    (hcap_lt : G.linksCap.toNat * 112 < 2 ^ 63)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4576#64) s
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
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 0x590#64) 88 ∗
          memRegion (s.sp + 0x190#64) 928 ∗
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hdrop_st : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec A F b) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 21008) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1_fnOff (by decide))
    hdrop_states
  clear hdealloc hdrop_states
  simp only [rustDeallocSpec] at hdealloc_raw
  simp only [CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec] at hdrop_st
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
    (mid := (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4548#64)
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
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
    ?_ ?_
  · spqr_send_fetches_range_cli b (Rust.withPanics ext) 4524 24
    dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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
      (mid := (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4568#64)
      (Mid := fun s2 P2 =>
        s2.status = .Running ∧
        s2.trace = s.trace ∧
        s2.sp = s.sp ∧
        s2.readReg64 .x23 = x23 ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s ∧
        (P2 ⊢ memRegion (s.sp + 0x590#64) 88 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
      ?_ ?_
    · spqr_send_fetches_range_cli b (Rust.withPanics ext) 4548 20
      dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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
      spqr_send_fetches_range_cli b (Rust.withPanics ext) 4568 8
      dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hdrop_st hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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

/-- `+3492 -> +4576`: `Chain::send_key` error cleanup; writes `spqrSendResultAt A ret none`,
drops `chain1` at `s.sp + 0x590#64` and `st1` at `s.sp + 0x190#64`, and reaches `+4576`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_err_31600 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (hdrop_slice : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropChainEpochSliceLocal1Name)
      (dropChainEpochSliceSpec A))
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Name)
      (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec A F b))
    (s : State) (ret x23 w0 : BitVec 64) (d0 d1 : BitVec 32) (w2 w3 : BitVec 64)
    (c : Chain) (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3492#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4576#64) s
      (memRegion ret 72 ∗
        ((s.sp + 0x1260#64) ↦₆₄ w0) ∗
        ((s.sp + 0x1268#64) ↦₃₂ d0) ∗
        ((s.sp + 0x126c#64) ↦₃₂ d1) ∗
        ((s.sp + 0x1270#64) ↦₆₄ w2) ∗
        ((s.sp + 0x1278#64) ↦₆₄ w3) ∗
        memRegion (s.sp + 0x1280#64) 8 ∗
        chainRepr A (s.sp + 0x590#64) c ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗
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
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hslice_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (dropChainEpochSliceSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 22120) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#3]") (by decide))
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
    (mid := (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4524#64)
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
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗
        (spqrSendResultAt A ret none ∗ memRegion (s.sp + 0x1260#64) 40 ∗ Frame)))
    ?_ ?_
  · have hdrop_states_keep := hdrop_states
    clear hdrop_states hdrop_states_keep
    spqr_send_fetches_range_cli b (Rust.withPanics ext) 3492 76
    spqr_send_fetches_range_cli b (Rust.withPanics ext) 3948 16
    spqr_send_fetches_range_cli b (Rust.withPanics ext) 4484 40
    dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hslice_raw hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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
    have hstep := CryptoVerification.Cli.SpqrV1.Top.Send.step_drop_chain_tail_31a08 hb hdealloc hdrop_states s1 x23 G c st1
      (spqrSendResultAt A ret none ∗ memRegion (s.sp + 0x1260#64) 40 ∗ Frame)
      hpc1 hrun1 hx20_1 hx21_1 hx23_1 hcap_lt hsp1_align
    rw [hsp1] at hstep
    refine SepWP.mono hstep ?_
    intro sf Q _ _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩
    exact ⟨hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1, Entails.trans hQ (Entails.of_eq (by ac_rfl))⟩

/-! ## `Chain::into_pb` Call and Result Relocation (`+3712 .. +4000`) -/

/-- `+3800 -> +4000`: relocates `ProtoRepr.chainPBAt A (s.sp + 0x1060#64) ch` into
`optChainPBRegSlotAt A (s.sp + 0xd90#64) x25 (some ch)` and jumps to `+4000`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_post_chain_into_pb_31734 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (ch : ChainPB) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3800#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = s.sp + 0x1060#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4000#64) s
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
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3800 48
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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

/-- `+3712 -> <Chain>::into_pb`: stores `(mkCap, mkPtr, msgKey.length)` from `sendKeyOkAt`,
copies `chainRepr A (s.sp + 0x590#64) c2` to `s.sp + 0x1260#64`, and calls
`<spqr::chain::Chain>::into_pb`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_pre_chain_into_pb_316dc {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (idx : BitVec 32) (msgKey : Bytes) (c2 : Chain) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3712#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "<spqr::chain::Chain>::into_pb" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) s
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
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3800#64 ∧
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
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3712 88
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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
