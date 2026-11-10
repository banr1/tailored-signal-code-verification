/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1a
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainStep
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainResolve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::send` Phase 3c Chain Resolution and Step (`+3196..+4000`)

Proves the chain resolution branches (`Chain::from_pb` and `chain_from_version_negotiation`),
`vn.min_version <= 0` handling, `Chain::add_epoch` setup, and `Chain::send_key` call/dispatch
in `spqr::send::<signal_session_ratchet::Coins>`.
-/

@[expose] public section

set_option autoImplicit false

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

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

open CryptoVerification.SpqrV1.States

open CryptoVerification.SpqrV1.States.IntoPb

open CryptoVerification.SpqrV1.Prost.EncodeToVec

open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64
  extractLsb_hi_append64
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

/-! ## 1. `+3456..+3492`: `<spqr::chain::Chain>::send_key` Call and Dispatch -/

/-- `+3456 -> +13552`: when `x22 = 0#64` (`msg.epoch = 0`), branches to the subtraction
overflow panic block. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_key_zero_315dc {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3456#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = 0#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 13552#64) s P
      (fun sf Q => sf = s.setPC ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 13552#64) ∧ Q = P) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3456 4
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  wp_steps
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨rfl, rfl⟩

/-- `+3456 -> <Chain>::send_key`: when `x22 ≠ 0#64`, sets `x8 = s.sp + 0x1260#64`,
`x0 = s.sp + 0x590#64`, `x1 = x22 - 1#64`, and calls `<spqr::chain::Chain>::send_key`
(return `+3480`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_pre_send_key_315dc {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3456#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 ≠ 0#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "<spqr::chain::Chain>::send_key" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) s P
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x8 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x0 = s.sp + 0x590#64 ∧
        sf.readReg64 .x1 = s.readReg64 .x22 - 1#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3480#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        Q = P) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3456 24
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  have hx22_beq : (s.readReg64 (Reg.gpr 22#5) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hx22
  wp_steps
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, rfl⟩

/-- `+3480 -> +3712`: on `Ok((idx, msgKey))` at `s.sp + 0x1260#64`, loads `w8 = 0#32` and
`w24 = idx` and branches to `+3712`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_post_send_key_ok_315f4 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (idx : BitVec 32) (msgKey : Bytes) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3480#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3712#64) s
      (sendKeyOkAt A (s.sp + 0x1260#64) idx msgKey ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg32 .x24 = idx ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ ((s.sp + 0x1260#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x1268#64) ↦₃₂ idx) ∗
          memRegion (s.sp + 0x126c#64) 4 ∗ vecU8 A (s.sp + 0x1270#64) msgKey ∗ Frame)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3480 12
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, sendKeyOkAt, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `+3480 -> +3492`: on `Err(err)` at `s.sp + 0x1260#64`, loads `w8 = 1#32` and `w24 = d0`
and falls through to `+3492`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_post_send_key_err_315f4 {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (err : Error) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3480#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3492#64) s
      (sendKeyErrAt (s.sp + 0x1260#64) err ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ ∃∗ d0 : BitVec 32, ∃∗ d1 : BitVec 32, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
          ((s.sp + 0x1260#64) ↦₆₄ 1#64) ∗
          ((s.sp + 0x1268#64) ↦₃₂ d0) ∗
          ((s.sp + 0x126c#64) ↦₃₂ d1) ∗
          ((s.sp + 0x1270#64) ↦₆₄ w2) ∗
          ((s.sp + 0x1278#64) ↦₆₄ w3) ∗
          memRegion (s.sp + 0x1280#64) 8 ∗ Frame)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3480 12
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  have herr := sendKeyErrAt_entails_words (s.sp + 4704#64) err
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at herr
  refine SepWP.focus_weaken herr (by sep_focus) ?_
  wp_pull_exists; rename_i w3 w2 d1 d0
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
  refine Entails.sepExists_right d0 (Entails.sepExists_right d1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_)))
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. `+3424..+3456`: `<spqr::chain::Chain>::add_epoch` Setup -/

/-- `+3424 -> <Chain>::add_epoch`: when `key = some es`, materializes `epochSecretAt` at
`s.sp + 0x1260#64` and calls `<spqr::chain::Chain>::add_epoch` (return `+3456`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_pre_add_epoch_315bc {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (es : EpochSecret) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3424#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "<spqr::chain::Chain>::add_epoch" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) s
      (optEpochSecretRegSlotAt A s.sp (s.readReg64 .x21) (s.readReg64 .x27) (some es) ∗
        memRegion (s.sp + 0x1260#64) 32 ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x590#64 ∧
        sf.readReg64 .x1 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3456#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ epochSecretAt A (s.sp + 0x1260#64) ⟨s.readReg64 .x21, s.readReg64 .x27⟩ es ∗
          memRegion (s.sp + 0x1bc0#64) 16 ∗ Frame)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3424 32
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, optEpochSecretRegSlotAt, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  rw [ProofLib.memRegion_split' (b := s.sp + 4704#64) (n := 8) (k := 24)
        (b' := s.sp + 4712#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s.sp + 4712#64) (n := 8) (k := 16)
        (b' := s.sp + 4720#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s.sp + 4720#64) (n := 8) (k := 8)
        (b' := s.sp + 4728#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (s.sp + 4704#64),
      ProofLib.memRegion_eight (s.sp + 4712#64),
      ProofLib.memRegion_eight (s.sp + 4720#64),
      ProofLib.memRegion_eight (s.sp + 4728#64)]
  wp_pull_exists; rename_i d0 d1 d2 d3
  wp_focus_pure; intro hx21_ne
  wp_steps
  have h16 :
      ((s.sp + 7104#64) ↦₆₄ BitVec.ofNat 64 es.secret.length) ∗
        ((s.sp + 7112#64) ↦₆₄ es.epoch) ⊢
        memRegion (s.sp + 7104#64) 16 := by
    rw [ProofLib.memRegion_split' (b := s.sp + 7104#64) (n := 8) (k := 8)
          (b' := s.sp + 7112#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono
      (ProofLib.pointsTo64_entails_memRegion _ _)
      (ProofLib.pointsTo64_entails_memRegion _ _)
  refine SepWP.focus_weaken h16 (by sep_focus) ?_
  refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, ?_⟩
  dsimp only [epochSecretAt, vecU8At, vecHeader, DecodeState.vecU8Heap]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

/-! ## 3. `+3964..+4000`: `vn.min_version <= 0` Path -/

/-- `+3964 -> +4000`: when `vn.min_version <= 0` and `key = none` (`x21 = noneCap`),
initializes the empty key/chain registers and slots and reaches `+4000`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_min_version_zero_ok_317d8 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3964#64)
    (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4000#64) s
      (memRegion (s.sp + 0xd90#64) 72 ∗
        memRegion (s.sp + 0x28#64) 8 ∗
        memRegion (s.sp + 0x8#64) 8 ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg32 .x24 = 0#32 ∧
        sf.readReg64 .x22 = 0#64 ∧
        sf.readReg32 .x20 = 1#32 ∧
        sf.readReg64 .x25 = LibsignalTripleRatchetRepr.noneCap ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ optChainPBRegSlotAt A (s.sp + 0xd90#64) (sf.readReg64 .x25) none ∗
          (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
            ((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗
            DecodeState.vecU8Heap A mkCap mkPtr []) ∗ Frame)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3964 36
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  rw [ProofLib.memRegion_eight (s.sp + 40#64), ProofLib.memRegion_eight (s.sp + 8#64)]
  wp_pull_exists; rename_i old28 old8
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, ?_⟩
  have hheap : Frame ⊢
      (⌜([] : List (BitVec 8)).length ≤ (0#64).toNat ∧ (0#64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0⌝ ∗
        if (0#64 : BitVec 64) = 0 then emp
        else A.live 1#64 (0#64).toNat 1 ∗ (1#64 ↦ₛ ([] : List (BitVec 8))) ∗
          memRegion (1#64 + BitVec.ofNat 64 ([] : List (BitVec 8)).length) ((0#64).toNat - ([] : List (BitVec 8)).length)) ∗ Frame := by
    have h1 : ([] : List (BitVec 8)).length ≤ (0#64).toNat ∧ (0#64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 := by decide
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    rw [sepConj_assoc]
    exact Entails.pure_right h1 (Entails.of_eq (by simp only [h0, ↓reduceIte, emp_sepConj]))
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  exact sepConj_mono (Entails.pure_right (by wp_norm_goal) (Entails.refl _))
    (sepConj_mono_right (sepConj_mono_right hheap))

/-- `+3964 -> +12004`: when `vn.min_version <= 0` and `key = some es` (`x21 ≠ noneCap`),
branches to the assertion failure panic block (`+12004`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_min_version_zero_panic_317d8 {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3964#64)
    (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 ≠ LibsignalTripleRatchetRepr.noneCap) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 12004#64) s P
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ Q = P) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3964 8
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  have hadd_ne : (s.readReg64 (Reg.gpr 21#5) + 1#64 != 0#64) = true := by
    rw [bne_iff_ne]
    intro h
    apply hx21
    change s.readReg64 (Reg.gpr 21#5) = 18446744073709551615#64
    bv_omega
  wp_steps
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, rfl⟩

/-! ## 4. `+3196..+3424`: `<spqr::chain::Chain>::from_pb` Setup and Branch -/

/-- `+3196 -> +3568`: when `s.pstate.z = true` (`state_pb.chain = none`), branches to the
version negotiation path (`+3568`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_branch_chain_none_314d8 {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3196#64)
    (hrun : s.status = .Running)
    (hz : s.pstate.z = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3568#64) s P
      (fun sf Q => sf = s.setPC ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3568#64) ∧ Q = P) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3196 4
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  have hcond : ConditionHolds CondCode.EQ s.pstate = true := hz
  wp_steps
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨rfl, rfl⟩

/-- `+3196 -> <Chain>::from_pb`: when `s.pstate.z = false` (`state_pb.chain = some pb`),
copies the 80-byte `ChainPB` from `s.sp + 0x60#64` to `s.sp + 0x590#64` and calls
`<spqr::chain::Chain>::from_pb` (return `+3252`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_pre_from_pb_314d8 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (pb : ChainPB) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3196#64)
    (hrun : s.status = .Running)
    (hz : s.pstate.z = false)
    (hx23 : s.readReg64 .x23 ≠ LibsignalTripleRatchetRepr.noneCap)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "<spqr::chain::Chain>::from_pb" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) s
      (CryptoVerification.SpqrV1.ProtoRepr.chainPBAt A (s.sp + 0x60#64) pb ∗
        memRegion (s.sp + 0x590#64) 80 ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x590#64 ∧
        sf.readReg64 .x8 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3252#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ ∃∗ g : ChainPBGhost,
          chainPBAt A g (s.sp + 0x590#64) pb ∗
          chainOrigSlotAt s.sp (s.readReg64 .x23) ∗ Frame)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3196 56
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  have hcond : ConditionHolds CondCode.EQ s.pstate = false := hz
  wp_conv_pre =>
    rw [ChainFrom.chainPBAt_protoRepr_eq_exists A (s.sp + 96#64) pb,
        memRegion_80_words10 (s.sp + 1424#64)]
  wp_pull_exists; rename_i d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 g
  refine SepWP.focus_weaken (ChainFromNorm.chainPBAt_expose_cap A g (s.sp + 96#64) pb) (by sep_focus) ?_
  wp_focus_pure; intro hcap_ne
  refine SepWP.focus_weaken (chainPBRestAt_entails_words9 A g (s.sp + 96#64) pb) (by sep_focus) ?_
  wp_pull_exists; rename_i w8 w9
  wp_focus_pure; intro hw
  wp_steps
  have hrest := words9_entails_chainPBRestAt A g (s.sp + 1424#64) pb w8 w9 hw
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  have hpb := ChainFromNorm.chainPBAt_unexpose_cap A g (s.sp + 1424#64) pb
  refine SepWP.focus_weaken hpb (by sep_focus) ?_
  have h80 := words10_to_memRegion_80 (s.sp + 96#64)
    g.linksCap g.linksPtr (BitVec.ofNat 64 (g.epochs.zip pb.links).length)
    g.nextRoot.cap g.nextRoot.ptr (BitVec.ofNat 64 pb.nextRoot.length)
    pb.currentEpoch pb.sendEpoch w8 w9
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h80
  refine SepWP.focus_weaken h80 (by sep_focus) ?_
  refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, ?_⟩
  rw [chainOrigSlotAt_of_ne hx23]
  refine Entails.sepExists_right g ?_
  exact Entails.of_eq (by ac_rfl)

/-- `+3252 -> +3848`: when `<spqr::chain::Chain>::from_pb` returns `Err(err)` at
`s.sp + 0x1260#64`, copies the 24-byte error payload to `s.sp + 0x1060..0x1078` and branches
to `+3848`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_post_from_pb_err_31510 {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (err : Error) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3252#64)
    (hrun : s.status = .Running)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3848#64) s
      (chainErrorAt (s.sp + 0x1260#64) err ∗
        memRegion (s.sp + 0x1060#64) 24 ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
          ((s.sp + 0x1060#64) ↦₆₄ w1) ∗
          ((s.sp + 0x1068#64) ↦₆₄ w2) ∗
          ((s.sp + 0x1070#64) ↦₆₄ w3) ∗
          memRegion (s.sp + 0x1260#64) 88 ∗ Frame)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3252 28
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  rw [memRegion_24_words3 (s.sp + 4192#64)]
  wp_pull_exists; rename_i d0 d1 d2
  have herr := chainErrorAt_entails_words (s.sp + 4704#64) err
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at herr
  refine SepWP.focus_weaken herr (by sep_focus) ?_
  wp_pull_exists; rename_i w1 w2 w3
  wp_steps
  have h88 := words4_and_56_to_memRegion_88 (s.sp + 4704#64)
    LibsignalTripleRatchetRepr.noneCap w1 w2 w3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h88
  refine SepWP.focus_weaken h88 (by sep_focus) ?_
  refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, ?_⟩
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_))
  exact Entails.of_eq (by ac_rfl)

/-- `+3252 -> +3420`: when `<spqr::chain::Chain>::from_pb` returns `Ok(ch)` at
`s.sp + 0x1260#64`, relocates the 88-byte `chainRepr` to `s.sp + 0x590..0x5e8`, tests `x21`
against `noneCap`, and reaches `+3420`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_post_from_pb_ok_31510 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (ch : Chain) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3252#64)
    (hrun : s.status = .Running)
    (hx25 : s.readReg64 .x25 = s.sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3420#64) s
      (chainRepr A (s.sp + 0x1260#64) ch ∗
        memRegion (s.sp + 0x1060#64) 24 ∗
        memRegion (s.sp + 0xd40#64) 80 ∗
        memRegion (s.sp + 0xde0#64) 80 ∗
        memRegion (s.sp + 0x590#64) 88 ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.pstate = addsPState64 (s.readReg64 .x21) 1#64 ∧
        sf.readReg32 .x20 =
          (if (s.readReg64 (Reg.gpr 21#5) + 1#64 != 0#64) = true then 0#32 else 1#32) ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ chainRepr A (s.sp + 0x590#64) ch ∗
          memRegion (s.sp + 0x1260#64) 88 ∗
          memRegion (s.sp + 0x1060#64) 24 ∗
          memRegion (s.sp + 0xd40#64) 80 ∗
          memRegion (s.sp + 0xde0#64) 80 ∗ Frame)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3252 168
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [memRegion_24_words3 (s.sp + 4192#64),
        memRegion_80_words10 (s.sp + 3392#64),
        memRegion_80_words10 (s.sp + 3552#64),
        ChainFromNorm.memRegion_88_words11 (s.sp + 1424#64)]
  wp_pull_exists
  refine SepWP.focus_weaken (ChainFromNorm.chainRepr_entails_words11 A (s.sp + 4704#64) ch) (by sep_focus) ?_
  wp_pull_exists; rename_i G pad
  wp_focus_pure; intro hcap_ne
  have hadd_ne : (G.linksCap + 1#64 == 0#64) = false :=
    ChainFromNorm.add_one_beq_zero_of_ne_noneCap hcap_ne
  wp_steps
  have hpack := ChainFromNorm.words11_entails_chainRepr A (s.sp + 1424#64) G ch pad
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack
  have h88 := ChainFromNorm.words11_to_memRegion_88 (s.sp + 4704#64)
    G.linksCap G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
    G.nextRoot.cap G.nextRoot.ptr (BitVec.ofNat 64 ch.nextRoot.length)
    ch.currentEpoch ch.sendEpoch (ch.params.maxOooKeys ++ ch.params.maxJump) (pad ++ ch.dir.toI32)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h88
  have h24 := words3_to_memRegion_24 (s.sp + 4192#64)
    G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h24
  have h80_d40 := words10_to_memRegion_80 (s.sp + 3392#64)
    G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
    G.nextRoot.cap G.nextRoot.ptr (BitVec.ofNat 64 ch.nextRoot.length)
    ch.currentEpoch ch.sendEpoch (ch.params.maxOooKeys ++ ch.params.maxJump) (pad ++ ch.dir.toI32)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h80_d40
  have h80_de0 := words10_to_memRegion_80 (s.sp + 3552#64)
    G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
    G.nextRoot.cap G.nextRoot.ptr (BitVec.ofNat 64 ch.nextRoot.length)
    ch.currentEpoch ch.sendEpoch (ch.params.maxOooKeys ++ ch.params.maxJump) (pad ++ ch.dir.toI32)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h80_de0
  refine SepWP.focus_weaken hpack (by sep_focus) ?_
  refine SepWP.focus_weaken h88 (by sep_focus) ?_
  refine SepWP.focus_weaken h24 (by sep_focus) ?_
  refine SepWP.focus_weaken h80_d40 (by sep_focus) ?_
  refine SepWP.focus_weaken h80_de0 (by sep_focus) ?_
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `+3420 -> +3456`: when `s.pstate.z = true` (`key = none`), branches to `+3456`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_branch_key_none_315b8 {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3420#64)
    (hrun : s.status = .Running)
    (hz : s.pstate.z = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3456#64) s P
      (fun sf Q => sf = s.setPC ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3456#64) ∧ Q = P) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3420 4
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  have hcond : ConditionHolds CondCode.EQ s.pstate = true := hz
  wp_steps
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨rfl, rfl⟩

/-- `+3420 -> +3424`: when `s.pstate.z = false` (`key = some es`), falls through to `+3424`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_branch_key_some_315b8 {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3420#64)
    (hrun : s.status = .Running)
    (hz : s.pstate.z = false) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3424#64) s P
      (fun sf Q => sf = s.setPC ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3424#64) ∧ Q = P) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3420 4
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  have hcond : ConditionHolds CondCode.EQ s.pstate = false := hz
  wp_steps
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨rfl, rfl⟩

/-! ## 5. `+3568..+3880`: `spqr::chain_from_version_negotiation` Path -/

/-- `+3568 -> +3896`: when `state_pb.version_negotiation = none`, loads `noneCap` from
`[s.sp + 0x30]` and branches to `+3896`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_from_vn_none_3164c {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3568#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3896#64) s
      (CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) none ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) none ∗ Frame)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3568 12
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName,
    CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `+3568 -> +3964`: when `state_pb.version_negotiation = some v` with `v.minVersion ≤ 0`,
branches to `+3964`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_from_vn_le_zero_3164c {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (v : VersionNegotiationPB) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3568#64)
    (hrun : s.status = .Running)
    (hle : BitVec.slt 0#32 v.minVersion = false)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3964#64) s
      (CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗ Frame)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3568 24
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName,
    CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  rw [versionNegotiationPBAt_eq_exists_pin A (s.sp + 48#64) v]
  wp_pull_exists; rename_i pin
  have hexp := versionNegotiationPBAt_expose_cap A pin (s.sp + 48#64) v
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hexp
  refine SepWP.focus_weaken hexp (by sep_focus) ?_
  wp_focus_pure; intro hcap_ne
  have hadd_ne : (pin.cap + 1#64 == 0#64) = false :=
    ChainFromNorm.add_one_beq_zero_of_ne_noneCap hcap_ne
  have hcond_le : v.minVersion.sle 0#32 = true := by
    revert hle
    simp only [BitVec.slt, BitVec.sle, decide_eq_false_iff_not, decide_eq_true_eq]
    omega
  wp_steps
  have hunexp := versionNegotiationPBAt_unexpose_cap A pin (s.sp + 48#64) v
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hunexp
  refine SepWP.focus_weaken hunexp (by sep_focus) ?_
  refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, ?_⟩
  exact Entails.sepExists_right pin (Entails.of_eq (by ac_rfl))

/-- `+3568 -> chain_from_version_negotiation`: when `state_pb.version_negotiation = some v`
with `0 < v.minVersion`, calls `spqr::chain_from_version_negotiation` (return `+3608`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_pre_from_vn_3164c {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (v : VersionNegotiationPB) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3568#64)
    (hrun : s.status = .Running)
    (hgt : BitVec.slt 0#32 v.minVersion = true)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "spqr::chain_from_version_negotiation" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) s
      (CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x30#64 ∧
        sf.readReg64 .x8 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3608#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ ∃∗ pin : VecPin,
          ChainFromVersionNegotiation.versionNegotiationPBAt A pin (s.sp + 0x30#64) v ∗ Frame)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3568 40
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName,
    CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  rw [versionNegotiationPBAt_eq_exists_pin A (s.sp + 48#64) v]
  wp_pull_exists; rename_i pin
  have hexp := versionNegotiationPBAt_expose_cap A pin (s.sp + 48#64) v
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hexp
  refine SepWP.focus_weaken hexp (by sep_focus) ?_
  wp_focus_pure; intro hcap_ne
  have hadd_ne : (pin.cap + 1#64 == 0#64) = false :=
    ChainFromNorm.add_one_beq_zero_of_ne_noneCap hcap_ne
  have hcond_le : v.minVersion.sle 0#32 = false := by
    revert hgt
    simp only [BitVec.slt, BitVec.sle, decide_eq_false_iff_not, decide_eq_true_eq]
    omega
  wp_steps
  have hunexp := versionNegotiationPBAt_unexpose_cap A pin (s.sp + 48#64) v
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hunexp
  refine SepWP.focus_weaken hunexp (by sep_focus) ?_
  refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, ?_⟩
  exact Entails.sepExists_right pin (Entails.of_eq (by ac_rfl))

/-- `+3608 -> +3880`: when `spqr::chain_from_version_negotiation` returns `Err(err)` at
`s.sp + 0x1260#64`, writes `spqrSendResultAt A ret none` and drops `st1` at `s.sp + 0x190#64`,
landing at `+3880`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_post_from_vn_err_31674 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Name)
      (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec A F b))
    (s : State) (ret : BitVec 64) (err : Error)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3608#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3880#64) s
      (chainErrorAt (s.sp + 0x1260#64) err ∗
        memRegion (s.sp + 0x590#64) 24 ∗
        memRegion ret 72 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret none ∗
          memRegion (s.sp + 0x1260#64) 88 ∗
          memRegion (s.sp + 0x590#64) 24 ∗
          memRegion (s.sp + 0x190#64) 928 ∗
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt b ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdrop_st : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec A F b) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 21008) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1_fnOff (by decide))
    hdrop_states
  simp only [CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec] at hdrop_st
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3608 28
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4668 12
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3856 24
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hdrop_st hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [memRegion_24_words3 (s.sp + 1424#64),
        memRegion_72_split_words3 ret]
  wp_pull_exists; rename_i r0 r1 r2 r3 d0 d1 d2
  have herr := chainErrorAt_entails_words (s.sp + 4704#64) err
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at herr
  refine SepWP.focus_weaken herr (by sep_focus) ?_
  wp_pull_exists; rename_i w1 w2 w3
  wp_conv_pre => rw [stackAt_spqrSendCallee_eq_dropStackPoly64 s.sp]
  wp_steps
  wp_call hdrop_st ⟨s.sp + 400#64, st1⟩
  have h88 := words4_and_56_to_memRegion_88 (s.sp + 4704#64)
    LibsignalTripleRatchetRepr.noneCap w1 w2 w3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h88
  have h24 := words3_to_memRegion_24 (s.sp + 1424#64) w1 w2 w3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h24
  have hret := sendResultAt_none_of_words3 A ret w1 w2 w3
  refine SepWP.focus_weaken h88 (by sep_focus) ?_
  refine SepWP.focus_weaken h24 (by sep_focus) ?_
  refine SepWP.focus_weaken hret (by sep_focus) ?_
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by simp only [wp_norm, arm64_norm, *], by
        dsimp only [chunkedStatesSize]
        exact Entails.of_eq (by simp only [hsp_sf, stackAt_spqrSendCallee_eq_dropStackPoly64]; ac_rfl)⟩

/-- `+3608 -> +3420`: when `spqr::chain_from_version_negotiation` returns `Ok(ch)` at
`s.sp + 0x1260#64`, relocates the 88-byte `chainRepr` to `s.sp + 0x590..0x5e8`, tests `x21`
against `noneCap`, and reaches `+3420`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_post_from_vn_ok_31674 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (ch : Chain) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3608#64)
    (hrun : s.status = .Running)
    (hx25 : s.readReg64 .x25 = s.sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3420#64) s
      (chainRepr A (s.sp + 0x1260#64) ch ∗
        memRegion (s.sp + 0xcf0#64) 80 ∗
        memRegion (s.sp + 0xde0#64) 80 ∗
        memRegion (s.sp + 0x590#64) 88 ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.pstate = addsPState64 (s.readReg64 .x21) 1#64 ∧
        sf.readReg32 .x20 =
          (if (s.readReg64 (Reg.gpr 21#5) + 1#64 != 0#64) = true then 0#32 else 1#32) ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ chainRepr A (s.sp + 0x590#64) ch ∗
          memRegion (s.sp + 0x1260#64) 88 ∗
          memRegion (s.sp + 0xcf0#64) 80 ∗
          memRegion (s.sp + 0xde0#64) 80 ∗ Frame)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3608 104
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3352 68
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [memRegion_80_words10 (s.sp + 3312#64),
        memRegion_80_words10 (s.sp + 3552#64),
        ChainFromNorm.memRegion_88_words11 (s.sp + 1424#64)]
  wp_pull_exists
  refine SepWP.focus_weaken (ChainFromNorm.chainRepr_entails_words11 A (s.sp + 4704#64) ch) (by sep_focus) ?_
  wp_pull_exists; rename_i G pad
  wp_focus_pure; intro hcap_ne
  have hadd_ne : (G.linksCap + 1#64 == 0#64) = false :=
    ChainFromNorm.add_one_beq_zero_of_ne_noneCap hcap_ne
  wp_steps
  have hpack := ChainFromNorm.words11_entails_chainRepr A (s.sp + 1424#64) G ch pad
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack
  have h88 := ChainFromNorm.words11_to_memRegion_88 (s.sp + 4704#64)
    G.linksCap G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
    G.nextRoot.cap G.nextRoot.ptr (BitVec.ofNat 64 ch.nextRoot.length)
    ch.currentEpoch ch.sendEpoch (ch.params.maxOooKeys ++ ch.params.maxJump) (pad ++ ch.dir.toI32)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h88
  have h80_cf0 := words10_to_memRegion_80 (s.sp + 3312#64)
    G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
    G.nextRoot.cap G.nextRoot.ptr (BitVec.ofNat 64 ch.nextRoot.length)
    ch.currentEpoch ch.sendEpoch (ch.params.maxOooKeys ++ ch.params.maxJump) (pad ++ ch.dir.toI32)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h80_cf0
  have h80_de0 := words10_to_memRegion_80 (s.sp + 3552#64)
    G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
    G.nextRoot.cap G.nextRoot.ptr (BitVec.ofNat 64 ch.nextRoot.length)
    ch.currentEpoch ch.sendEpoch (ch.params.maxOooKeys ++ ch.params.maxJump) (pad ++ ch.dir.toI32)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h80_de0
  refine SepWP.focus_weaken hpack (by sep_focus) ?_
  refine SepWP.focus_weaken h88 (by sep_focus) ?_
  refine SepWP.focus_weaken h80_cf0 (by sep_focus) ?_
  refine SepWP.focus_weaken h80_de0 (by sep_focus) ?_
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

end CryptoVerification.SpqrV1.Top.Send
