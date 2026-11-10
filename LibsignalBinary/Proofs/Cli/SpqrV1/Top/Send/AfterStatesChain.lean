/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1a
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::send` Phase 3a Panic Blocks, Epilogue, and Error Cleanup

Proves the panic blocks (`+12004`, `+13552`), shared epilogue (`+4576 -> +4664`), and chain
resolution error cleanup paths (`+3848`, `+3880`, `+3896`, `+3920 -> +4576`) in
`spqr::send::<signal_session_ratchet::Coins>`.
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

open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

open CryptoVerification.SpqrV1.Top.MessageSerialize

open CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.States.IntoPb

open CryptoVerification.SpqrV1.Prost.EncodeToVec hiding SepWP.done

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

set_option allowUnsafeReducibility true in
attribute [local semireducible] Arm64.SepProp SepProp.sepExists

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.corePanic_spqrSend_extern (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "core::panicking::panic")) =
      some Rust.panicked := by
  have hstub : libsignalSessionCode.fnOff "core::panicking::panic" = num% (ls_off% "core::panicking::panic") :=
    Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "core::panicking::panic")
  exact panic_at_sym_ext b ext CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName "core::panicking::panic" (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "core::panicking::panic"))
    (by rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff, hstub]) (hp := by simp [Rust.isPanicSymbol])

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.panicSubOverflow_spqrSend_extern (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "core::panicking::panic_const::panic_const_sub_overflow")) =
      some Rust.panicked := by
  have hstub : libsignalSessionCode.fnOff "core::panicking::panic_const::panic_const_sub_overflow" = num% (ls_off% "core::panicking::panic_const::panic_const_sub_overflow") :=
    Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
      (ls_stub% "core::panicking::panic_const::panic_const_sub_overflow")
  exact panic_at_sym_ext b ext CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName
    "core::panicking::panic_const::panic_const_sub_overflow" (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "core::panicking::panic_const::panic_const_sub_overflow"))
    (by rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff, hstub]) (hp := by simp [Rust.isPanicSymbol])

/-- `+12004`: steps to `core::panicking::panic` for `sendKeySomeWithoutChain`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_panic_33740 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 12004#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "core::panicking::panic")) s P
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.mem = s.mem ∧ (Q ⊢ P)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 12004 24
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, rfl, Entails.refl _⟩

/-- `+13552`: steps to `panic_const_sub_overflow` for `sendEpochUnderflow` (`msg.epoch == 0`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_panic_33d4c {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 13552#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "core::panicking::panic_const::panic_const_sub_overflow")) s P
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.mem = s.mem ∧ (Q ⊢ P)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 13552 12
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, rfl, Entails.refl _⟩

/-! ## Shared Epilogue (`+4576 -> +4600 -> +4632 -> +4664`) -/

/-- `+4632 -> +4664`: restores `sp = s0.sp`, pops callee-saved registers `x19..x30`, and
returns to `s0.readReg64 .x30`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_epilogue_31a74 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt s.sp spqrSendCalleeStack ∗
        memRegion s.sp 0x1f20 ∗
        spqrSendSavedRegs s.sp s0 ∗
        Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s0.sp ∧
        Arm64.CalleeSavedPreserved s0 sf ∧
        (Q ⊢ stackAt s0.sp spqrSendStack ∗ Frame)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4632 36
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, spqrSendSavedRegs, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp]; exact spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hsp_add1 : s.sp + 4096#64 + 3872#64 = s.sp + 0x1f20#64 := by bv_omega
  have hsp_sub60 : s.sp + 0x1f20#64 = s0.sp - 0x60#64 := by rw [hsp]; bv_omega
  have hsp_add2_beq : ((s.sp + 0x1f20#64) &&& 15#64 == 0#64) = true := by
    rw [hsp_sub60]; exact spAligned_sub s0.sp 0x60#64 hsp0_align (by decide)
  have hsp_add2 : (s.sp + 0x1f20#64) &&& 15#64 = 0#64 := by
    rwa [beq_iff_eq] at hsp_add2_beq
  have hsp_end : s.sp + 0x1f20#64 + 96#64 = s0.sp := by rw [hsp]; bv_omega
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, ?_, ?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp_add1, hsp_end]
  · simp only [Arm64.CalleeSavedPreserved, Reg.fp, wp_norm, arm64_norm, hsp_add1, hsp_end, hvregs, and_self]
  · rw [hsp]
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_left (stack_restore_spqrSend s0.sp s0))
    unfold spqrSendSavedRegs
    ac_rfl

/-- `+4600 -> +4632`: checks `x23` and `[sp + 0x60]` against `noneCap`, yielding
`memRegion (s.sp + 0x60#64) 80`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_epilogue_31a54 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4600#64)
    (hrun : s.status = .Running)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4632#64) s
      (chainOrigSlotAt s.sp x23 ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 0x60#64) 80 ∗ Frame)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4600 32
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  by_cases hnone : x23 = noneCap
  · subst hnone
    rw [chainOrigSlotAt_none]
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
    rw [← chainOrigSlotAt_none]
    exact sepConj_mono_left (chainOrigSlotAt_entails_memRegion_80 s.sp noneCap)
  · rw [chainOrigSlotAt_of_ne hnone]
    have hcmn : (x23 + 1#64 != 0#64) = true := by
      rw [bne_iff_ne]
      intro h; apply hnone; revert h; bv_omega
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩

/-- `+4576 -> +4600`: drops `optVersionNegotiationPBAt A (s.sp + 0x30#64) vn`, yielding
`memRegion (s.sp + 0x30#64) 48`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_epilogue_31a3c {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (vn : Option VersionNegotiationPB) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4576#64)
    (hrun : s.status = .Running)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4600#64) s
      (CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 0x30#64) 48 ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4576 24
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  have hstack_dealloc :
      stackAt s.sp spqrSendCalleeStack =
        memRegion (s.sp - 123008#64)
          (spqrSendCalleeStack - allocHookStack) ∗
          stackAt s.sp allocHookStack :=
    ProofLib.stackAt_split_bottom s.sp allocHookStack
      (spqrSendCalleeStack - allocHookStack) (by decide)
  have hadd8 : (s.sp + 48#64) + 8#64 = s.sp + 56#64 := by bv_omega
  have hadd16 : (s.sp + 48#64) + 16#64 = s.sp + 64#64 := by bv_omega
  have hmerge_none :
      ((s.sp + 48#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗ memRegion (s.sp + 56#64) 40 ⊢
        memRegion (s.sp + 48#64) 48 := by
    rw [← hadd8]
    exact optVersionNegotiationPBAt_none_entails_memRegion_48 (s.sp + 48#64)
  have hmerge_vn : ∀ c p : BitVec 64,
      ((s.sp + 48#64) ↦₆₄ c) ∗ ((s.sp + 56#64) ↦₆₄ p) ∗ memRegion (s.sp + 64#64) 32 ⊢
        memRegion (s.sp + 48#64) 48 := by
    intro c p
    have h := vnHeader_entails_memRegion_48 (s.sp + 48#64) c p
    rwa [hadd8, hadd16] at h
  cases vn with
  | none =>
    dsimp only [CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt]
    rw [hadd8]
    wp_steps
    refine SepWP.focus_weaken hmerge_none (by sep_focus) ?_
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩
  | some v =>
    dsimp only [CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt]
    refine SepWP.focus_weaken (versionNegotiationPBAt_entails_dealloc A (s.sp + 48#64) v) (by sep_focus) ?_
    wp_pull_exists; rename_i g; rcases g with ⟨cap, ptr⟩
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc] at hcap_lt ⊢
    by_cases hc0 : (cap == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hc_eq : cap = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hc_eq
      wp_steps
      refine SepWP.focus_weaken (hmerge_vn 0#64 ptr) (by sep_focus) ?_
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩
    · have hslt := cap_ne_zero_slt_one_false hcap_lt hc0
      have hlt_false := cap_ne_zero_lt_one_false hcap_lt hc0
      rw [hstack_dealloc]
      wp_steps; wp_apply
      refine SepWP.focus_weaken (hmerge_vn cap ptr) (by sep_focus) ?_
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by simp only [wp_norm, arm64_norm, *],
          Entails.of_eq (by ac_rfl)⟩

/-! ## Error Cleanup Paths (`+3848`, `+3880`, `+3896`, `+3920 -> +4576`) -/

/-- `+3920 -> +4576`: drops `optEpochSecretRegSlotAt A s.sp x21 x27 key` and reaches `+4576`
with `memRegion (s.sp + 0x1bc0#64) 16`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_drop_key_317ac {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (x21 x27 x23 : BitVec 64) (key : Option EpochSecret) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3920#64)
    (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = x21)
    (hx27 : s.readReg64 .x27 = x27)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4576#64) s
      (optEpochSecretRegSlotAt A s.sp x21 x27 key ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 0x1bc0#64) 16 ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3920 32
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  have hstack_dealloc :
      stackAt s.sp spqrSendCalleeStack =
        memRegion (s.sp - 123008#64)
          (spqrSendCalleeStack - allocHookStack) ∗
          stackAt s.sp allocHookStack :=
    ProofLib.stackAt_split_bottom s.sp allocHookStack
      (spqrSendCalleeStack - allocHookStack) (by decide)
  cases key with
  | none =>
    dsimp only [optEpochSecretRegSlotAt]
    wp_focus_pure; intro hx21_eq
    subst hx21_eq
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩
  | some es =>
    refine SepWP.focus_weaken (optEpochSecretRegSlotAt_some_entails_dealloc A s.sp x21 x27 es) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc] at hcap_lt ⊢
    by_cases hc0 : (x21 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hc_eq : x21 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hc_eq
      wp_steps
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩
    · have hult := ult_sub_one_false_of_pos hcap_lt hc0
      rw [hstack_dealloc]
      wp_steps; wp_apply
      wp_steps
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by ac_rfl)⟩

/-- `+3880 -> +4576`: drops `optEpochSecretRegSlotAt A s.sp x21 x27 key` and reaches `+4576`
with `memRegion (s.sp + 0x1bc0#64) 16`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_drop_key_31784 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (x21 x27 x23 : BitVec 64) (key : Option EpochSecret) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3880#64)
    (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = x21)
    (hx27 : s.readReg64 .x27 = x27)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4576#64) s
      (optEpochSecretRegSlotAt A s.sp x21 x27 key ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 0x1bc0#64) 16 ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3880 16
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3932 20
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  have hstack_dealloc :
      stackAt s.sp spqrSendCalleeStack =
        memRegion (s.sp - 123008#64)
          (spqrSendCalleeStack - allocHookStack) ∗
          stackAt s.sp allocHookStack :=
    ProofLib.stackAt_split_bottom s.sp allocHookStack
      (spqrSendCalleeStack - allocHookStack) (by decide)
  cases key with
  | none =>
    dsimp only [optEpochSecretRegSlotAt]
    wp_focus_pure; intro hx21_eq
    subst hx21_eq
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩
  | some es =>
    refine SepWP.focus_weaken (optEpochSecretRegSlotAt_some_entails_dealloc A s.sp x21 x27 es) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc] at hcap_lt ⊢
    by_cases hc0 : (x21 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hc_eq : x21 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hc_eq
      wp_steps
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩
    · have hule := ule_sub_one_true_of_pos hcap_lt hc0
      rw [hstack_dealloc]
      wp_steps; wp_apply
      wp_steps
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by ac_rfl)⟩

/-- `+3896 -> +4576`: `Error::ChainNotAvailable` cleanup when `state_pb.chain = none` and
`state_pb.version_negotiation = none`; writes `spqrSendResultAt A ret none`, drops `st1` and
`key`, and reaches `+4576`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_err_31794 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Name)
      (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec A F b))
    (s : State) (ret x21 x27 x23 : BitVec 64)
    (st1 : States spqrPolyApi (spqrAuthApi F))
    (key : Option EpochSecret) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3896#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21)
    (hx27 : s.readReg64 .x27 = x27)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4576#64) s
      (memRegion ret 72 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        optEpochSecretRegSlotAt A s.sp x21 x27 key ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret none ∗
          memRegion (s.sp + 0x190#64) 928 ∗
          memRegion (s.sp + 0x1bc0#64) 16 ∗
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdrop_st : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec A F b) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 21008) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1_fnOff (by decide))
    hdrop_states
  clear hdrop_states
  simp only [CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec] at hdrop_st
  have hstack_drop :
      stackAt s.sp spqrSendCalleeStack =
        memRegion (s.sp - 123008#64)
          (spqrSendCalleeStack - dropStackPoly64) ∗
          stackAt s.sp dropStackPoly64 :=
    ProofLib.stackAt_split_bottom s.sp dropStackPoly64
      (spqrSendCalleeStack - dropStackPoly64) (by decide)
  refine SepWP.seq
    (mid := (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3920#64)
    (Mid := fun s1 P1 =>
      s1.status = .Running ∧
      s1.trace = s.trace ∧
      s1.sp = s.sp ∧
      s1.readReg64 .x21 = x21 ∧
      s1.readReg64 .x27 = x27 ∧
      s1.readReg64 .x23 = x23 ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s ∧
      (P1 ⊢ optEpochSecretRegSlotAt A s.sp x21 x27 key ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗
        (spqrSendResultAt A ret none ∗
          memRegion (s.sp + 0x190#64) 928 ∗
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗ Frame)))
    ?_ ?_
  · spqr_send_fetches_range_cli b (Rust.withPanics ext) 3896 24
    dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hdrop_st hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
    examples_hide_fetches
    rw [memRegion_72_split_byte ret, hstack_drop]
    wp_pull_exists
    wp_steps
    wp_call hdrop_st ⟨s.sp + 400#64, st1⟩
    refine SepWP.focus_weaken (sendResultAt_none_of_byte A ret 15#8) (by sep_focus) ?_
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by simp only [wp_norm, arm64_norm, *], by
          dsimp only [chunkedStatesSize]
          exact Entails.of_eq (by ac_rfl)⟩
  · intro s1 P1 hpc1 _ ⟨hrun1, htr1, hsp1, hx21_1, hx27_1, hx23_1, hvregs1, hP1⟩
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    refine SepWP.weaken_pre hP1 ?_
    have hstep := CryptoVerification.Cli.SpqrV1.Top.Send.step_drop_key_317ac hdealloc s1 x21 x27 x23 key
      (spqrSendResultAt A ret none ∗ memRegion (s.sp + 0x190#64) 928 ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗ Frame)
      hpc1 hrun1 hx21_1 hx27_1 hx23_1 hsp1_align
    rw [hsp1] at hstep
    refine SepWP.mono hstep ?_
    intro sf Q _ _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩
    exact ⟨hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1, Entails.trans hQ (Entails.of_eq (by ac_rfl))⟩

/-- `+3848 -> +4576`: `Chain::from_pb` error cleanup; writes `spqrSendResultAt A ret none`
from `[s.sp + 0x1060..0x1078]`, drops `st1` and `key`, and reaches `+4576`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_err_31764 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Name)
      (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec A F b))
    (s : State) (ret x21 x27 x23 w1 w2 w3 : BitVec 64)
    (st1 : States spqrPolyApi (spqrAuthApi F))
    (key : Option EpochSecret) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3848#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21)
    (hx27 : s.readReg64 .x27 = x27)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4576#64) s
      (memRegion ret 72 ∗
        ((s.sp + 0x1060#64) ↦₆₄ w1) ∗
        ((s.sp + 0x1068#64) ↦₆₄ w2) ∗
        ((s.sp + 0x1070#64) ↦₆₄ w3) ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        optEpochSecretRegSlotAt A s.sp x21 x27 key ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret none ∗
          memRegion (s.sp + 0x1060#64) 24 ∗
          memRegion (s.sp + 0x190#64) 928 ∗
          memRegion (s.sp + 0x1bc0#64) 16 ∗
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdrop_st : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec A F b) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 21008) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1_fnOff (by decide))
    hdrop_states
  clear hdrop_states
  simp only [CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec] at hdrop_st
  have hstack_drop :
      stackAt s.sp spqrSendCalleeStack =
        memRegion (s.sp - 123008#64)
          (spqrSendCalleeStack - dropStackPoly64) ∗
          stackAt s.sp dropStackPoly64 :=
    ProofLib.stackAt_split_bottom s.sp dropStackPoly64
      (spqrSendCalleeStack - dropStackPoly64) (by decide)
  have h24 :
      ((s.sp + 4192#64) ↦₆₄ w1) ∗ ((s.sp + 4200#64) ↦₆₄ w2) ∗ ((s.sp + 4208#64) ↦₆₄ w3) ⊢
        memRegion (s.sp + 4192#64) 24 := by
    rw [ProofLib.memRegion_split' (b := s.sp + 4192#64) (n := 8) (k := 16)
          (b' := s.sp + 4200#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s.sp + 4200#64) (n := 8) (k := 8)
          (b' := s.sp + 4208#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (ProofLib.pointsTo64_entails_memRegion _ _))
  refine SepWP.seq
    (mid := (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3880#64)
    (Mid := fun s1 P1 =>
      s1.status = .Running ∧
      s1.trace = s.trace ∧
      s1.sp = s.sp ∧
      s1.readReg64 .x21 = x21 ∧
      s1.readReg64 .x27 = x27 ∧
      s1.readReg64 .x23 = x23 ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s ∧
      (P1 ⊢ optEpochSecretRegSlotAt A s.sp x21 x27 key ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗
        (spqrSendResultAt A ret none ∗
          memRegion (s.sp + 0x1060#64) 24 ∗
          memRegion (s.sp + 0x190#64) 928 ∗
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗ Frame)))
    ?_ ?_
  · spqr_send_fetches_range_cli b (Rust.withPanics ext) 3848 32
    dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hdrop_st hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
    examples_hide_fetches
    rw [memRegion_72_split_words3 ret, hstack_drop]
    wp_pull_exists
    wp_steps
    wp_call hdrop_st ⟨s.sp + 400#64, st1⟩
    refine SepWP.focus_weaken (sendResultAt_none_of_words3 A ret w1 w2 w3) (by sep_focus) ?_
    refine SepWP.focus_weaken h24 (by sep_focus) ?_
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by simp only [wp_norm, arm64_norm, *], by
          dsimp only [chunkedStatesSize]
          exact Entails.of_eq (by ac_rfl)⟩
  · intro s1 P1 hpc1 _ ⟨hrun1, htr1, hsp1, hx21_1, hx27_1, hx23_1, hvregs1, hP1⟩
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    refine SepWP.weaken_pre hP1 ?_
    have hstep := CryptoVerification.Cli.SpqrV1.Top.Send.step_drop_key_31784 hdealloc s1 x21 x27 x23 key
      (spqrSendResultAt A ret none ∗ memRegion (s.sp + 0x1060#64) 24 ∗
        memRegion (s.sp + 0x190#64) 928 ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗ Frame)
      hpc1 hrun1 hx21_1 hx27_1 hx23_1 hsp1_align
    rw [hsp1] at hstep
    refine SepWP.mono hstep ?_
    intro sf Q _ _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩
    exact ⟨hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1, Entails.trans hQ (Entails.of_eq (by ac_rfl))⟩

end CryptoVerification.SpqrV1.Top.Send
