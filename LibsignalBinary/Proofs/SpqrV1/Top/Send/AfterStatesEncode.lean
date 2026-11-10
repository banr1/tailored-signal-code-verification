/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Decodes
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainStep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::send`: `Message::serialize`, `States::into_pb`, and `VersionNegotiation` Length

Call setup and post-checks for `<Message>::serialize` and `<States>::into_pb`, 352-byte
`PqRatchetState` stack assembly (`0x317fc..0x31968`), and inlined
`Option<VersionNegotiation>::encoded_len` (`0x3191c..0x31afc`) in `spqr::send::<HookRng>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
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
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (ule_self_64 ult_self_64
   ofNat_length_beq_zero_of_lt bv_u32VarintField_nonzero bv_bytesField_nonempty
   bv_add_ofNat_comm bv_add_ofNat_eq adds_no_overflow_of_eq cmp_ls_false_of_lt)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::send::<libsignal_session::HookRng>")
  (ls_lemma% fnOff "<spqr::v1::chunked::states::Message>::serialize")
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::into_pb")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic")
  (ls_stub% "core::panicking::panic_const::panic_const_sub_overflow")

/-! ## 1. `0x317fc..0x31810`: `<Message>::serialize` Call Setup -/

/-- `0x317fc -> 0x5f784` (`+4000 -> +192296`): Sets `x0 = s.sp + 0x1d70#64`, `x8 = s.sp +
    0xff0#64`, `w1 = s.readReg32 .x24`, and calls
    `<spqr::v1::chunked::states::Message>::serialize` (`0x5f784`, return `entry + 4020#64 =
    0x31810`). -/
theorem step_pre_message_serialize_317fc {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4000#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 170572#64) s P
      (fun sf Q => VRegsAt s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x1d70#64 ∧
        sf.readReg32 .x1 = s.readReg32 .x24 ∧
        sf.readReg64 .x8 = s.sp + 0xff0#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4020#64 ∧
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
        Q = P) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 4000 20
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  wp_steps
  exact Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, rfl⟩

/-! ## 2. `0x31810..0x3185c`: `Message::serialize` Post-Check, `memcpy` 928B, and `States::into_pb` Call Setup -/

theorem vecU8At_cons_entails (A : RustAlloc) (v cap ptr : BitVec 64) (b0 : BitVec 8)
    (tail : List (BitVec 8)) :
    vecU8At A v cap ptr (b0 :: tail) ⊢
      ⌜(b0 :: tail).length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 ∧
        (BitVec.ofNat 64 (b0 :: tail).length == 0#64) = false⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ tail) ∗
      memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length) := by
  unfold vecU8At vecHeader
  refine Entails.trans (Entails.of_eq (show
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length)) ∗
      ⌜(b0 :: tail).length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ (b0 :: tail)) ∗
        memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length)) =
    ⌜(b0 :: tail).length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length) ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ (b0 :: tail)) ∗
          memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length)))
    by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
  have hcap_ne : cap ≠ 0 := by intro hc; subst hc; simp at h1
  have hlen_ne : (BitVec.ofNat 64 (b0 :: tail).length == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h0
    have h0n := congrArg BitVec.toNat h0
    simp only [List.length_cons, BitVec.toNat_ofNat, BitVec.toNat_zero] at h0n h1
    omega
  simp only [hcap_ne, ↓reduceIte, ProofLib.pointsToBytes_cons]
  exact Entails.pure_right ⟨h1, h2, h3, hlen_ne⟩ (Entails.of_eq (by ac_rfl))

theorem memRegion_928_split1 (a : BitVec 64) :
    memRegion a 928 = (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 927 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 1) (k := 927) (b' := a + 1#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_one a]

theorem pointsTo8_memRegion_927_to_928 (a : BitVec 64) (b0 : BitVec 8) :
    (a ↦₈ b0) ∗ memRegion (a + 1#64) 927 ⊢ memRegion a 928 := by
  rw [memRegion_928_split1 a]
  exact sepConj_mono_left (Entails.sepExists_right b0 (Entails.refl _))

theorem vecU8At_cons_repack (A : RustAlloc) (v cap ptr : BitVec 64) (b0 : BitVec 8)
    (tail : List (BitVec 8))
    (h1 : (b0 :: tail).length ≤ cap.toNat) (h2 : cap.toNat < 2 ^ 63) (h3 : ptr ≠ 0) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ tail) ∗
      memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length) ⊢
      vecU8 A v (b0 :: tail) := by
  have hcap_ne : cap ≠ 0 := by intro hc; subst hc; simp at h1
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecU8At vecHeader
  simp only [hcap_ne, ↓reduceIte, ProofLib.pointsToBytes_cons]
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜(b0 :: tail).length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ tail) ∗
        memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length)) =
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length)) ∗
      ⌜(b0 :: tail).length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (A.live ptr cap.toNat 1 ∗ ((ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ tail)) ∗
        memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length))
    by ac_rfl))
  exact Entails.pure_right ⟨h1, h2, h3⟩ (Entails.of_eq (by ac_rfl))

theorem memRegion_928_entails_split1 (a : BitVec 64) :
    memRegion a 928 ⊢ (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 927 :=
  Entails.of_eq (memRegion_928_split1 a)

theorem vecU8_cons_entails (A : RustAlloc) (v : BitVec 64) (b0 : BitVec 8)
    (tail : List (BitVec 8)) :
    vecU8 A v (b0 :: tail) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜(b0 :: tail).length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 ∧
          (BitVec.ofNat 64 (b0 :: tail).length == 0#64) = false⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ tail) ∗
        memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length) := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap
    (Entails.sepExists_right ptr (vecU8At_cons_entails A v cap ptr b0 tail))

/-- `0x31810 -> 0x78a48` (`entry + 0xfb4 = entry + 4020#64` to `entry + bv% (ls_rel%
    "spqr::send::<libsignal_session::HookRng>" "memcpy")`): Checks that `msg.serialize idx = 1#8
    :: tail` is non-empty and starts with `1#8`, and sets up the call to `memcpy(s.sp +
    0x1260#64, s.sp + 0x190#64, 928)` (`0x78a48`, return `entry + 4080#64 = 0x3184c`). -/
theorem step_post_message_serialize_to_memcpy_31810 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (tail : List (BitVec 8)) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4020#64)
    (hrun : s.status = .Running)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "memcpy")) s
      (vecU8 A (s.sp + 0xff0#64) (1#8 :: tail) ∗
        memRegion (s.sp + 0x1260#64) 928 ∗ Frame)
      (fun sf Q => VRegsAt s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x1 = s.sp + 0x190#64 ∧
        sf.readReg64 .x2 = 928#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4080#64 ∧
        sf.readReg64 .x24 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Q ⊢ memRegion (s.sp + 0x1260#64) 928 ∗
          vecU8 A (s.sp + 0xff0#64) (1#8 :: tail) ∗ Frame)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 4020 60
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hx26 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  have hsplit := memRegion_928_entails_split1 (s.sp + 4704#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsplit
  have hexp := vecU8_cons_entails A (s.sp + 4080#64) 1#8 tail
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hexp
  refine SepWP.focus_weaken hsplit (by sep_focus) ?_
  refine SepWP.focus_weaken hexp (by sep_focus) ?_
  wp_pull_exists; rename_i b0_tmp cap ptr
  wp_focus_pure; rintro ⟨h1, h2, h3, hlen_ne⟩
  wp_steps
  have h928 := pointsTo8_memRegion_927_to_928 (s.sp + 4704#64) 1#8
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h928
  have hvec := vecU8At_cons_repack A (s.sp + 4080#64) cap ptr 1#8 tail h1 h2 h3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hvec
  refine SepWP.focus_weaken h928 (by sep_focus) ?_
  refine SepWP.focus_weaken hvec (by sep_focus) ?_
  refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `0x3184c -> 0x5ce20` (`+4080 -> +181700`): Sets `x0 = s.sp + 0x1260#64` and `x8 = s.sp +
    0x590#64`, and calls `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20`, return
    `entry + 4096#64 = 0x3185c`). -/
theorem step_post_memcpy_to_into_pb_3184c {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4080#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 159976#64) s P
      (fun sf Q => VRegsAt s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x8 = s.sp + 0x590#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4096#64 ∧
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
        Q = P) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 4080 16
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  wp_steps
  exact Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, rfl⟩

/-! ## 3. `0x3185c..0x31918`: Assembling `PqRatchetState` (`352`B) at `sp + 0x1260..0x13c0` -/

/-- Pure relation characterizing words `+24`, `+32`, `+40` of `VersionNegotiationPB`:
    `chainParams : Option ChainParamsPB` (`12`B at `+24..+36`), `direction : BitVec 32` (`4`B at
    `+36..+40`), `minVersion : BitVec 32` (`4`B at `+40..+44`), and 4 bytes padding at
    `+44..+48`. -/
def vnParamsDirMinVerWords (vn : VersionNegotiationPB) (w3 w4 w5 : BitVec 64) : Prop :=
  (match vn.chainParams with
   | none => ∃ p0 p1 : BitVec 32, w3 = p0 ++ 0#32 ∧ w4 = vn.direction ++ p1
   | some cp => w3 = cp.maxJump ++ 1#32 ∧ w4 = vn.direction ++ cp.maxOooKeys) ∧
  ∃ p2 : BitVec 32, w5 = p2 ++ vn.minVersion

theorem memRegion_40_words5 (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ w1 : BitVec 64, a ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 8#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 16#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (a + 24#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (a + 32#64) ↦₆₄ w5) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 32) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 24) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 16) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 8) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64)]

theorem words5_to_memRegion_40 (a w1 w2 w3 w4 w5 : BitVec 64) :
    (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗
    ((a + 24#64) ↦₆₄ w4) ∗ ((a + 32#64) ↦₆₄ w5) ⊢ memRegion a 40 := by
  rw [memRegion_40_words5 a]
  exact sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w2 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w3 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w4 (Entails.refl _))
      (Entails.sepExists_right w5 (Entails.refl _)))))

theorem optVersionNegRest_entails_words5 (A : RustAlloc) (g : ProtoRepr.VersionNegotiationPBGhost)
    (a : BitVec 64) (opt : Option VersionNegotiationPB) :
    Prost.EncodeToVec.optVersionNegRest A g a opt ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
        match opt with
        | none => emp
        | some vn =>
          ⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
            vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey := by
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha24 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
  have ha32 : a + 8#64 + 24#64 = a + 32#64 := by bv_omega
  have ha40 : a + 8#64 + 32#64 = a + 40#64 := by bv_omega
  cases opt with
  | none =>
    dsimp only [Prost.EncodeToVec.optVersionNegRest]
    rw [memRegion_40_words5 (a + 8#64), ha16, ha24, ha32, ha40]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply ProofLib.Entails.sepExists_elim; intro w5
    apply ProofLib.Entails.sepExists_elim; intro w4
    apply ProofLib.Entails.sepExists_elim; intro w3
    apply ProofLib.Entails.sepExists_elim; intro w2
    apply ProofLib.Entails.sepExists_elim; intro w1
    refine Entails.sepExists_right w1 (Entails.sepExists_right w2
      (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 ?_))))
    exact Entails.of_eq (by ac_rfl)
  | some vn =>
    dsimp only [Prost.EncodeToVec.optVersionNegRest, Prost.EncodeToVec.versionNegotiationRest]
    have ha28 : a + 24#64 + 4#64 = a + 28#64 := by bv_omega
    have ha32' : a + 28#64 + 4#64 = a + 32#64 := by bv_omega
    have ha36 : a + 36#64 = a + 32#64 + 4#64 := by bv_omega
    have ha44 : a + 44#64 = a + 40#64 + 4#64 := by bv_omega
    rw [ProofLib.memRegion_four (a + 44#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply ProofLib.Entails.sepExists_elim; intro p2
    have h5 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 40#64) vn.minVersion p2
    rw [← ha44] at h5
    cases hcp : vn.chainParams with
    | none =>
      dsimp only [ProtoRepr.optChainParamsPBAt]
      rw [ha28, ha36,
          ProofLib.memRegion_split' (b := a + 28#64) (n := 4) (k := 4)
            (b' := a + 32#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_four (a + 28#64),
          ProofLib.memRegion_four (a + 32#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply ProofLib.Entails.sepExists_elim; intro p1
      apply ProofLib.Entails.sepExists_elim; intro p0
      have h3 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 24#64) 0#32 p0
      rw [ha28] at h3
      have h4 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 32#64) p1 vn.direction
      refine Entails.sepExists_right g.authKey.ptr
        (Entails.sepExists_right (BitVec.ofNat 64 vn.authKey.length)
        (Entails.sepExists_right (p0 ++ 0#32)
        (Entails.sepExists_right (vn.direction ++ p1)
        (Entails.sepExists_right (p2 ++ vn.minVersion) ?_))))
      have hpure : vnParamsDirMinVerWords vn (p0 ++ 0#32) (vn.direction ++ p1) (p2 ++ vn.minVersion) := by
        unfold vnParamsDirMinVerWords; rw [hcp]; exact ⟨⟨p0, p1, rfl, rfl⟩, ⟨p2, rfl⟩⟩
      refine Entails.trans ?_ (Entails.of_eq (show
        ⌜g.authKey.ptr = g.authKey.ptr ∧
          BitVec.ofNat 64 vn.authKey.length = BitVec.ofNat 64 vn.authKey.length ∧
          vnParamsDirMinVerWords vn (p0 ++ 0#32) (vn.direction ++ p1) (p2 ++ vn.minVersion)⌝ ∗
        (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          ((a + 24#64) ↦₆₄ (p0 ++ 0#32)) ∗
          ((a + 32#64) ↦₆₄ (vn.direction ++ p1)) ∗
          ((a + 40#64) ↦₆₄ (p2 ++ vn.minVersion)) ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) =
        ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          ((a + 24#64) ↦₆₄ (p0 ++ 0#32)) ∗
          ((a + 32#64) ↦₆₄ (vn.direction ++ p1)) ∗
          ((a + 40#64) ↦₆₄ (p2 ++ vn.minVersion)) ∗
          (⌜g.authKey.ptr = g.authKey.ptr ∧
            BitVec.ofNat 64 vn.authKey.length = BitVec.ofNat 64 vn.authKey.length ∧
            vnParamsDirMinVerWords vn (p0 ++ 0#32) (vn.direction ++ p1) (p2 ++ vn.minVersion)⌝ ∗
            ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) by ac_rfl))
      apply Entails.pure_right ⟨rfl, rfl, hpure⟩
      rw [← h3, ← h4, ← h5]
      exact Entails.of_eq (by ac_rfl)
    | some cp =>
      dsimp only [ProtoRepr.optChainParamsPBAt, ProtoRepr.chainParamsPBAt]
      rw [ha28, ha32', ha36]
      have h3 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 24#64) 1#32 cp.maxJump
      rw [ha28] at h3
      have h4 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 32#64) cp.maxOooKeys vn.direction
      refine Entails.sepExists_right g.authKey.ptr
        (Entails.sepExists_right (BitVec.ofNat 64 vn.authKey.length)
        (Entails.sepExists_right (cp.maxJump ++ 1#32)
        (Entails.sepExists_right (vn.direction ++ cp.maxOooKeys)
        (Entails.sepExists_right (p2 ++ vn.minVersion) ?_))))
      have hpure : vnParamsDirMinVerWords vn (cp.maxJump ++ 1#32) (vn.direction ++ cp.maxOooKeys) (p2 ++ vn.minVersion) := by
        unfold vnParamsDirMinVerWords; rw [hcp]; exact ⟨⟨rfl, rfl⟩, ⟨p2, rfl⟩⟩
      refine Entails.trans ?_ (Entails.of_eq (show
        ⌜g.authKey.ptr = g.authKey.ptr ∧
          BitVec.ofNat 64 vn.authKey.length = BitVec.ofNat 64 vn.authKey.length ∧
          vnParamsDirMinVerWords vn (cp.maxJump ++ 1#32) (vn.direction ++ cp.maxOooKeys) (p2 ++ vn.minVersion)⌝ ∗
        (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          ((a + 24#64) ↦₆₄ (cp.maxJump ++ 1#32)) ∗
          ((a + 32#64) ↦₆₄ (vn.direction ++ cp.maxOooKeys)) ∗
          ((a + 40#64) ↦₆₄ (p2 ++ vn.minVersion)) ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) =
        ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          ((a + 24#64) ↦₆₄ (cp.maxJump ++ 1#32)) ∗
          ((a + 32#64) ↦₆₄ (vn.direction ++ cp.maxOooKeys)) ∗
          ((a + 40#64) ↦₆₄ (p2 ++ vn.minVersion)) ∗
          (⌜g.authKey.ptr = g.authKey.ptr ∧
            BitVec.ofNat 64 vn.authKey.length = BitVec.ofNat 64 vn.authKey.length ∧
            vnParamsDirMinVerWords vn (cp.maxJump ++ 1#32) (vn.direction ++ cp.maxOooKeys) (p2 ++ vn.minVersion)⌝ ∗
            ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) by ac_rfl))
      apply Entails.pure_right ⟨rfl, rfl, hpure⟩
      rw [← h3, ← h4, ← h5]
      exact Entails.of_eq (by ac_rfl)

theorem words5_entails_optVersionNegRest (A : RustAlloc) (g : ProtoRepr.VersionNegotiationPBGhost)
    (a : BitVec 64) (opt : Option VersionNegotiationPB) (w1 w2 w3 w4 w5 : BitVec 64) :
    ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
    ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
    (match opt with
     | none => emp
     | some vn =>
       ⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
         vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
       ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) ⊢
      Prost.EncodeToVec.optVersionNegRest A g a opt := by
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha24 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
  have ha32 : a + 8#64 + 24#64 = a + 32#64 := by bv_omega
  have ha40 : a + 8#64 + 32#64 = a + 40#64 := by bv_omega
  cases opt with
  | none =>
    dsimp only [Prost.EncodeToVec.optVersionNegRest]
    rw [sepConj_emp]
    have h40 := words5_to_memRegion_40 (a + 8#64) w1 w2 w3 w4 w5
    rw [ha16, ha24, ha32, ha40] at h40
    exact h40
  | some vn =>
    dsimp only [Prost.EncodeToVec.optVersionNegRest, Prost.EncodeToVec.versionNegotiationRest]
    refine Entails.trans (Entails.of_eq (show
      ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
        (⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
          vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) =
      ⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
        vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
        (((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
          ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) by ac_rfl)) ?_
    apply Entails.pure_left
    rintro ⟨rfl, rfl, hparams, p2, rfl⟩
    have ha28 : a + 24#64 + 4#64 = a + 28#64 := by bv_omega
    have ha32' : a + 28#64 + 4#64 = a + 32#64 := by bv_omega
    have ha36 : a + 36#64 = a + 32#64 + 4#64 := by bv_omega
    have ha44 : a + 44#64 = a + 40#64 + 4#64 := by bv_omega
    have h5 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 40#64) vn.minVersion p2
    rw [← ha44] at h5
    have hp2_mem : ((a + 44#64) ↦₃₂ p2) ⊢ memRegion (a + 44#64) 4 :=
      ProofLib.pointsTo32_entails_memRegion (a + 44#64) p2
    cases hcp : vn.chainParams with
    | none =>
      rw [hcp] at hparams
      rcases hparams with ⟨p0, p1, rfl, rfl⟩
      dsimp only [ProtoRepr.optChainParamsPBAt]
      have h3 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 24#64) 0#32 p0
      rw [ha28] at h3
      have h4 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 32#64) p1 vn.direction
      rw [← ha36] at h4
      rw [← h3, ← h4, ← h5]
      have hp01_mem : ((a + 28#64) ↦₃₂ p0) ∗ ((a + 32#64) ↦₃₂ p1) ⊢ memRegion (a + 24#64 + 4#64) 8 := by
        rw [ha28,
            ProofLib.memRegion_split' (b := a + 28#64) (n := 4) (k := 4)
              (b' := a + 32#64) rfl (by bv_omega) (by decide)]
        exact sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
          (ProofLib.pointsTo32_entails_memRegion _ _)
      refine Entails.trans (Entails.of_eq (show
        ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          (((a + 24#64) ↦₃₂ 0#32) ∗ ((a + 28#64) ↦₃₂ p0)) ∗
          (((a + 32#64) ↦₃₂ p1) ∗ ((a + 36#64) ↦₃₂ vn.direction)) ∗
          (((a + 40#64) ↦₃₂ vn.minVersion) ∗ ((a + 44#64) ↦₃₂ p2)) ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey =
        (((a + 28#64) ↦₃₂ p0) ∗ ((a + 32#64) ↦₃₂ p1)) ∗
          ((a + 44#64) ↦₃₂ p2) ∗
          (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
            ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
            ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
            ((a + 24#64) ↦₃₂ 0#32) ∗
            ((a + 36#64) ↦₃₂ vn.direction) ∗
            ((a + 40#64) ↦₃₂ vn.minVersion)) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hp01_mem (sepConj_mono_left hp2_mem)) ?_
      exact Entails.of_eq (by ac_rfl)
    | some cp =>
      rw [hcp] at hparams
      rcases hparams with ⟨rfl, rfl⟩
      dsimp only [ProtoRepr.optChainParamsPBAt, ProtoRepr.chainParamsPBAt]
      rw [ha28, ha32']
      have h3 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 24#64) 1#32 cp.maxJump
      rw [ha28] at h3
      have h4 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 32#64) cp.maxOooKeys vn.direction
      rw [← ha36] at h4
      rw [← h3, ← h4, ← h5]
      refine Entails.trans (Entails.of_eq (show
        ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          (((a + 24#64) ↦₃₂ 1#32) ∗ ((a + 28#64) ↦₃₂ cp.maxJump)) ∗
          (((a + 32#64) ↦₃₂ cp.maxOooKeys) ∗ ((a + 36#64) ↦₃₂ vn.direction)) ∗
          (((a + 40#64) ↦₃₂ vn.minVersion) ∗ ((a + 44#64) ↦₃₂ p2)) ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey =
        ((a + 44#64) ↦₃₂ p2) ∗
          (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
            ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
            ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
            ((a + 24#64) ↦₃₂ 1#32) ∗
            ((a + 28#64) ↦₃₂ cp.maxJump) ∗
            ((a + 32#64) ↦₃₂ cp.maxOooKeys) ∗
            ((a + 36#64) ↦₃₂ vn.direction) ∗
            ((a + 40#64) ↦₃₂ vn.minVersion)) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hp2_mem) ?_
      exact Entails.of_eq (by ac_rfl)

def vnWords6At (a w0 w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
  ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)

def chainWords9At (a c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64) : SepProp :=
  (a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ c2) ∗ ((a + 16#64) ↦₆₄ c3) ∗
  ((a + 24#64) ↦₆₄ c4) ∗ ((a + 32#64) ↦₆₄ c5) ∗ ((a + 40#64) ↦₆₄ c6) ∗
  ((a + 48#64) ↦₆₄ c7) ∗ ((a + 56#64) ↦₆₄ c8) ∗ ((a + 64#64) ↦₆₄ c9)

theorem outWords28_entails_memRegion_224 (out : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64) :
    outWords28 out
      w0 w8 w16 w24 w32 w40 w48 w56
      w64 w72 w80 w88 w96 w104 w112 w120
      w128 w136 w144 w152 w160 w168 w176 w184
      w192 w200 w208 w216 ⊢
    memRegion out optProtoInnerStateSize := by
  rw [memRegion_out_224_eq out]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w8
    (Entails.sepExists_right w16 (Entails.sepExists_right w24
    (Entails.sepExists_right w32 (Entails.sepExists_right w40
    (Entails.sepExists_right w48 (Entails.sepExists_right w56
    (Entails.sepExists_right w64 (Entails.sepExists_right w72
    (Entails.sepExists_right w80 (Entails.sepExists_right w88
    (Entails.sepExists_right w96 (Entails.sepExists_right w104
    (Entails.sepExists_right w112 (Entails.sepExists_right w120
    (Entails.sepExists_right w128 (Entails.sepExists_right w136
    (Entails.sepExists_right w144 (Entails.sepExists_right w152
    (Entails.sepExists_right w160 (Entails.sepExists_right w168
    (Entails.sepExists_right w176 (Entails.sepExists_right w184
    (Entails.sepExists_right w192 (Entails.sepExists_right w200
    (Entails.sepExists_right w208 (Entails.sepExists_right w216 (Entails.refl _))))))))))))))))))))))))))))

theorem memRegion_48_vnWords6 (a : BitVec 64) :
    memRegion a 48 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        vnWords6At a w0 w1 w2 w3 w4 w5 := by
  rw [show (48 : Nat) = 8 * 6 from rfl, ProofLib.memRegion_cells a 6 (by decide)]
  unfold vnWords6At
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right, BitVec.add_assoc]
  rfl

theorem vnWords6_to_memRegion_48 (a w0 w1 w2 w3 w4 w5 : BitVec 64) :
    vnWords6At a w0 w1 w2 w3 w4 w5 ⊢ memRegion a 48 := by
  rw [memRegion_48_vnWords6 a]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.refl _))))))

theorem chainWords9_to_memRegion_72 (a c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64) :
    chainWords9At a c1 c2 c3 c4 c5 c6 c7 c8 c9 ⊢ memRegion a 72 :=
  words9_to_memRegion_72 a c1 c2 c3 c4 c5 c6 c7 c8 c9

theorem memRegion_80_chainWords (a : BitVec 64) :
    memRegion a 80 =
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
      ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
      ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64,
      ∃∗ c9 : BitVec 64,
        (a ↦₆₄ c0) ∗ chainWords9At (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 := by
  rw [show (80 : Nat) = 8 * 10 from rfl, ProofLib.memRegion_cells a 10 (by decide)]
  unfold chainWords9At
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right, BitVec.add_assoc]
  rfl

theorem memRegion_352_split (a : BitVec 64) :
    memRegion a 352 =
      memRegion a 48 ∗ memRegion (a + 48#64) 80 ∗ memRegion (a + 128#64) optProtoInnerStateSize := by
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 304) (b' := a + 48#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 80) (k := 224) (b' := a + 128#64)
        rfl (by bv_omega) (by decide)]
  rfl

/-- `0x3185c -> 0x31968` (`+4096 -> +4364`) when `w0 = noneCap` (`version_negotiation = none`):
    Copies `vnWords6At (s.sp + 0x30#64)` to `s.sp + 0x1260#64`, stores `x25` at `s.sp +
    0x1290#64` and copies `chainWords9At (s.sp + 0xd90#64)` to `s.sp + 0x1298#64`, copies
    `outWords28 (s.sp + 0x590#64)` to `s.sp + 0x12e0#64`, stores `x20` at `[s.sp + 0x20#64]`,
    loads `x26 = noneCap`, and branches to `0x31968`. -/
theorem step_copy_pq_state_none_3185c {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (v_20 w1 w2 w3 w4 w5 : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64)
    (i0 i8 i16 i24 i32 i40 i48 i56
     i64 i72 i80 i88 i96 i104 i112 i120
     i128 i136 i144 i152 i160 i168 i176 i184
     i192 i200 i208 i216 : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4096#64)
    (hrun : s.status = .Running)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4364#64) s
      (((s.sp + 0x20#64) ↦₆₄ v_20) ∗
        vnWords6At (s.sp + 0x30#64) noneCap w1 w2 w3 w4 w5 ∗
        chainWords9At (s.sp + 0xd90#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
        outWords28 (s.sp + 0x590#64)
          i0 i8 i16 i24 i32 i40 i48 i56
          i64 i72 i80 i88 i96 i104 i112 i120
          i128 i136 i144 i152 i160 i168 i176 i184
          i192 i200 i208 i216 ∗
        memRegion (s.sp + 0x1260#64) 352 ∗ Frame)
      (fun sf Q => VRegsAt s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x26 = noneCap ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Q ⊢ ((s.sp + 0x20#64) ↦₆₄ s.readReg64 .x20) ∗
          vnWords6At (s.sp + 0x1260#64) noneCap w1 w2 w3 w4 w5 ∗
          ((s.sp + 0x1290#64) ↦₆₄ s.readReg64 .x25) ∗
          chainWords9At (s.sp + 0x1298#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
          outWords28 (s.sp + 0x12e0#64)
            i0 i8 i16 i24 i32 i40 i48 i56
            i64 i72 i80 i88 i96 i104 i112 i120
            i128 i136 i144 i152 i160 i168 i176 i184
            i192 i200 i208 i216 ∗
          memRegion (s.sp + 0x30#64) 48 ∗
          memRegion (s.sp + 0xd90#64) 72 ∗
          memRegion (s.sp + 0x590#64) 224 ∗ Frame)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 4096 192
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hx26 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  rw [memRegion_352_split (s.sp + 4704#64),
      memRegion_48_vnWords6 (s.sp + 4704#64),
      memRegion_80_chainWords (s.sp + 4704#64 + 48#64),
      memRegion_out_224_eq (s.sp + 4704#64 + 128#64)]
  wp_pull_exists
  dsimp only [vnWords6At, chainWords9At, outWords28]
  wp_steps
  have hvn48 := vnWords6_to_memRegion_48 (s.sp + 48#64) noneCap w1 w2 w3 w4 w5
  simp only [vnWords6At, BitVec.add_assoc, BitVec.reduceAdd] at hvn48
  have hch72 := chainWords9_to_memRegion_72 (s.sp + 3472#64) c1 c2 c3 c4 c5 c6 c7 c8 c9
  simp only [chainWords9At, BitVec.add_assoc, BitVec.reduceAdd] at hch72
  have hin224 := outWords28_entails_memRegion_224 (s.sp + 1424#64)
    i0 i8 i16 i24 i32 i40 i48 i56
    i64 i72 i80 i88 i96 i104 i112 i120
    i128 i136 i144 i152 i160 i168 i176 i184
    i192 i200 i208 i216
  simp only [outWords28, optProtoInnerStateSize, BitVec.add_assoc, BitVec.reduceAdd] at hin224
  refine SepWP.focus_weaken hvn48 (by sep_focus) ?_
  refine SepWP.focus_weaken hch72 (by sep_focus) ?_
  refine SepWP.focus_weaken hin224 (by sep_focus) ?_
  refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, ?_⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

/-- `0x3185c -> 0x3191c` (`+4096 -> +4288`) when `(w0 + 1#64 == 0#64) = false`
    (`version_negotiation = some vn`): Copies `vnWords6At (s.sp + 0x30#64)` to `s.sp +
    0x1260#64`, stores `x25` at `s.sp + 0x1290#64` and copies `chainWords9At (s.sp + 0xd90#64)`
    to `s.sp + 0x1298#64`, copies `outWords28 (s.sp + 0x590#64)` to `s.sp + 0x12e0#64`, stores
    `x20` at `[s.sp + 0x20#64]`, loads `x26 = w0`, and falls through to `0x3191c`. -/
theorem step_copy_pq_state_some_3185c {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (v_20 w0 w1 w2 w3 w4 w5 : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64)
    (i0 i8 i16 i24 i32 i40 i48 i56
     i64 i72 i80 i88 i96 i104 i112 i120
     i128 i136 i144 i152 i160 i168 i176 i184
     i192 i200 i208 i216 : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4096#64)
    (hrun : s.status = .Running)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hw0 : (w0 + 1#64 == 0#64) = false)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4288#64) s
      (((s.sp + 0x20#64) ↦₆₄ v_20) ∗
        vnWords6At (s.sp + 0x30#64) w0 w1 w2 w3 w4 w5 ∗
        chainWords9At (s.sp + 0xd90#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
        outWords28 (s.sp + 0x590#64)
          i0 i8 i16 i24 i32 i40 i48 i56
          i64 i72 i80 i88 i96 i104 i112 i120
          i128 i136 i144 i152 i160 i168 i176 i184
          i192 i200 i208 i216 ∗
        memRegion (s.sp + 0x1260#64) 352 ∗ Frame)
      (fun sf Q => VRegsAt s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x26 = w0 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Q ⊢ ((s.sp + 0x20#64) ↦₆₄ s.readReg64 .x20) ∗
          vnWords6At (s.sp + 0x1260#64) w0 w1 w2 w3 w4 w5 ∗
          ((s.sp + 0x1290#64) ↦₆₄ s.readReg64 .x25) ∗
          chainWords9At (s.sp + 0x1298#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
          outWords28 (s.sp + 0x12e0#64)
            i0 i8 i16 i24 i32 i40 i48 i56
            i64 i72 i80 i88 i96 i104 i112 i120
            i128 i136 i144 i152 i160 i168 i176 i184
            i192 i200 i208 i216 ∗
          memRegion (s.sp + 0x30#64) 48 ∗
          memRegion (s.sp + 0xd90#64) 72 ∗
          memRegion (s.sp + 0x590#64) 224 ∗ Frame)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 4096 192
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hx26 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  rw [memRegion_352_split (s.sp + 4704#64),
      memRegion_48_vnWords6 (s.sp + 4704#64),
      memRegion_80_chainWords (s.sp + 4704#64 + 48#64),
      memRegion_out_224_eq (s.sp + 4704#64 + 128#64)]
  wp_pull_exists
  dsimp only [vnWords6At, chainWords9At, outWords28]
  wp_steps
  have hvn48 := vnWords6_to_memRegion_48 (s.sp + 48#64) w0 w1 w2 w3 w4 w5
  simp only [vnWords6At, BitVec.add_assoc, BitVec.reduceAdd] at hvn48
  have hch72 := chainWords9_to_memRegion_72 (s.sp + 3472#64) c1 c2 c3 c4 c5 c6 c7 c8 c9
  simp only [chainWords9At, BitVec.add_assoc, BitVec.reduceAdd] at hch72
  have hin224 := outWords28_entails_memRegion_224 (s.sp + 1424#64)
    i0 i8 i16 i24 i32 i40 i48 i56
    i64 i72 i80 i88 i96 i104 i112 i120
    i128 i136 i144 i152 i160 i168 i176 i184
    i192 i200 i208 i216
  simp only [outWords28, optProtoInnerStateSize, BitVec.add_assoc, BitVec.reduceAdd] at hin224
  refine SepWP.focus_weaken hvn48 (by sep_focus) ?_
  refine SepWP.focus_weaken hch72 (by sep_focus) ?_
  refine SepWP.focus_weaken hin224 (by sep_focus) ?_
  refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, ?_⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

/-! ## 4. Inline `Option<VersionNegotiation>::encoded_len` (`0x3191c .. 0x31afc`) -/

/-- `0x31968 -> 0x31afc` (`+4364 -> +4768`): Sets `x20 = 0#64 = BitVec.ofNat 64
    (optVersionNegotiationPBFieldEncodedLen none)` and jumps to `0x31afc`. -/
theorem step_vn_len_none_31968_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4364#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4768#64) s F
      (fun s' P' => VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen none) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧ (P' ⊢ F)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 4364 8
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  wp_steps
  refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by simp only [optVersionNegotiationPBFieldEncodedLen]; wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, Entails.refl _⟩

/-- `0x3191c -> 0x31940` (`+4288 -> +4324`): Loads `x8 = [sp + 0x1270]` (`vn.authKey.length`)
    and computes `x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey)`. -/
theorem step_vn_len_authKey_3191c_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4288#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : vn.authKey.length < 2 ^ 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4324#64) s
      (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
      (fun s' P' => VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧ s'.readReg64 .x23 = s.readReg64 .x23 ∧
        s'.readReg64 .x24 = s.readReg64 .x24 ∧ s'.readReg64 .x25 = s.readReg64 .x25 ∧
        s'.readReg64 .x26 = s.readReg64 .x26 ∧ s'.readReg64 .x27 = s.readReg64 .x27 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 4288 36
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  dsimp only [versionNegotiationRest]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  obtain ⟨hbeqz, hbnez⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hlen
  cases hemp : vn.authKey.isEmpty
  · have hstep := EncodedLen.bv_bytesField_nonempty hemp
    simp only [hemp, Bool.not_false] at hbeqz hbnez
    wp_steps
    refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by simp only [arm64_norm, wp_norm, *],
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have hzero : bytesFieldEncodedLen vn.authKey = vn.authKey.length := by
      unfold bytesFieldEncodedLen
      cases h : vn.authKey with
      | nil => rfl
      | cons _ _ => rw [h] at hemp; cases hemp
    wp_steps
    refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by simp only [arm64_norm, wp_norm, hzero, *],
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `0x31940 -> 0x31974` (`+4324 -> +4376`): Loads `x9 = signExtend64 [sp + 0x1284]`
    (`vn.direction`) and computes `x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen
    vn.direction)`. -/
theorem step_vn_len_dir_31940_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4324#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4376#64) s
      (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
      (fun s' P' => VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧
        s'.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧ s'.readReg64 .x23 = s.readReg64 .x23 ∧
        s'.readReg64 .x24 = s.readReg64 .x24 ∧ s'.readReg64 .x25 = s.readReg64 .x25 ∧
        s'.readReg64 .x26 = s.readReg64 .x26 ∧ s'.readReg64 .x27 = s.readReg64 .x27 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 4324 40
  spqr_send_fetches_range b (Rust.withPanics ext) 4372 4
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  dsimp only [versionNegotiationRest]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  by_cases hdir : vn.direction = 0#32
  · have hdir_eq : i32VarintFieldEncodedLen vn.direction = 0 := by simp [i32VarintFieldEncodedLen, hdir]
    have hbeq_d : (vn.direction == 0#32) = true := beq_iff_eq.mpr hdir
    have hbne_d : (vn.direction != 0#32) = false := by simp [hdir]
    wp_steps
    refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by simp only [arm64_norm, wp_norm, *],
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
  · have hbeq_d : (vn.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
    have hbne_d : (vn.direction != 0#32) = true := bne_iff_ne.mpr hdir
    have hstep_d := bv_i32VarintField_nonzero hdir
    wp_steps
    refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by simp only [arm64_norm, wp_norm, *],
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `0x31974 -> 0x319a0` (`+4376 -> +4420`): Loads `x10 = signExtend64 [sp + 0x1288]`
    (`vn.minVersion`) and computes `x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen
    vn.minVersion)`. -/
theorem step_vn_len_minVer_31974_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4376#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4420#64) s
      (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
      (fun s' P' => VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧ s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧ s'.readReg64 .x23 = s.readReg64 .x23 ∧
        s'.readReg64 .x24 = s.readReg64 .x24 ∧ s'.readReg64 .x25 = s.readReg64 .x25 ∧
        s'.readReg64 .x26 = s.readReg64 .x26 ∧ s'.readReg64 .x27 = s.readReg64 .x27 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 4376 44
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  dsimp only [versionNegotiationRest]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  by_cases hmv : vn.minVersion = 0#32
  · have hmv_eq : i32VarintFieldEncodedLen vn.minVersion = 0 := by simp [i32VarintFieldEncodedLen, hmv]
    have hbeq_mv : (vn.minVersion == 0#32) = true := beq_iff_eq.mpr hmv
    have hbne_mv : (vn.minVersion != 0#32) = false := by simp [hmv]
    wp_steps
    refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by simp only [arm64_norm, wp_norm, *],
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
  · have hbeq_mv : (vn.minVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hmv
    have hbne_mv : (vn.minVersion != 0#32) = true := bne_iff_ne.mpr hmv
    have hstep_mv := bv_i32VarintField_nonzero hmv
    wp_steps
    refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by simp only [arm64_norm, wp_norm, *],
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `0x319a0 -> 0x31ad4` (`+4420 -> +4728`): Computes `x11 = BitVec.ofNat 64
    (optChainParamsPBFieldEncodedLen vn.chainParams)`. -/
theorem step_vn_len_chainParams_319a0_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4420#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4728#64) s
      (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
      (fun s' P' => VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧ s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x11 = BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen vn.chainParams) ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧ s'.readReg64 .x23 = s.readReg64 .x23 ∧
        s'.readReg64 .x24 = s.readReg64 .x24 ∧ s'.readReg64 .x25 = s.readReg64 .x25 ∧
        s'.readReg64 .x26 = s.readReg64 .x26 ∧ s'.readReg64 .x27 = s.readReg64 .x27 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 4420 64
  spqr_send_fetches_range b (Rust.withPanics ext) 4680 48
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  dsimp only [versionNegotiationRest]
  cases hcp : vn.chainParams with
  | none =>
    simp only [ProtoRepr.optChainParamsPBAt, optChainParamsPBFieldEncodedLen, BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by simp only [arm64_norm, wp_norm, optChainParamsPBFieldEncodedLen, *],
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
  | some cp =>
    simp only [ProtoRepr.optChainParamsPBAt, ProtoRepr.chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
    by_cases hmj : cp.maxJump = 0#32 <;> by_cases hmo : cp.maxOooKeys = 0#32
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by simp [u32VarintFieldEncodedLen, hmj]
      have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      wp_steps
      refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by rw [← bv_optChainParams_some_combine]; simp only [arm64_norm, wp_norm, *],
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by simp [u32VarintFieldEncodedLen, hmj]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := EncodedLen.bv_u32VarintField_nonzero hmo
      wp_steps
      refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by rw [← bv_optChainParams_some_combine]; simp only [arm64_norm, wp_norm, *],
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    · have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      wp_steps
      refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by rw [← bv_optChainParams_some_combine]; simp only [arm64_norm, wp_norm, *],
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    · have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := EncodedLen.bv_u32VarintField_nonzero hmo
      wp_steps
      refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by rw [← bv_optChainParams_some_combine]; simp only [arm64_norm, wp_norm, *],
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `0x31ad4 -> 0x31afc` (`+4728 -> +4768`): Sums `x8`, `x9`, `x10`, `x11` and computes `x20 =
    BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn))`. -/
theorem step_vn_len_combine_31ad4_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4728#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion))
    (hx11 : s.readReg64 .x11 = BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen vn.chainParams)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4768#64) s F
      (fun s' P' => VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn)) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧ (P' ⊢ F)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 4728 40
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  have hvn_sum := bv_vn_sum_eq vn
  have hopt_vn := bv_optVN_some_eq vn
  wp_steps
  refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by simp only [arm64_norm, wp_norm, *],
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, Entails.refl _⟩

theorem step_vn_len_none_31968 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4364#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4768#64) s F
      (fun s' P' =>
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen none) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧ (P' ⊢ F)) :=
  SepWP.mono (step_vn_len_none_31968_vregs s F hpc hrun) (fun _ _ _ _ h => h.2)

theorem step_vn_len_authKey_3191c {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4288#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : vn.authKey.length < 2 ^ 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4324#64) s
      (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
      (fun s' P' =>
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧ s'.readReg64 .x23 = s.readReg64 .x23 ∧
        s'.readReg64 .x24 = s.readReg64 .x24 ∧ s'.readReg64 .x25 = s.readReg64 .x25 ∧
        s'.readReg64 .x26 = s.readReg64 .x26 ∧ s'.readReg64 .x27 = s.readReg64 .x27 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)) :=
  SepWP.mono (step_vn_len_authKey_3191c_vregs A s g vn F hpc hrun hsp_align hlen) (fun _ _ _ _ h => h.2)

theorem step_vn_len_dir_31940 {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4324#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4376#64) s
      (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
      (fun s' P' =>
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧
        s'.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧ s'.readReg64 .x23 = s.readReg64 .x23 ∧
        s'.readReg64 .x24 = s.readReg64 .x24 ∧ s'.readReg64 .x25 = s.readReg64 .x25 ∧
        s'.readReg64 .x26 = s.readReg64 .x26 ∧ s'.readReg64 .x27 = s.readReg64 .x27 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)) :=
  SepWP.mono (step_vn_len_dir_31940_vregs A s g vn F hpc hrun hsp_align) (fun _ _ _ _ h => h.2)

theorem step_vn_len_minVer_31974 {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4376#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4420#64) s
      (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
      (fun s' P' =>
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧ s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧ s'.readReg64 .x23 = s.readReg64 .x23 ∧
        s'.readReg64 .x24 = s.readReg64 .x24 ∧ s'.readReg64 .x25 = s.readReg64 .x25 ∧
        s'.readReg64 .x26 = s.readReg64 .x26 ∧ s'.readReg64 .x27 = s.readReg64 .x27 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)) :=
  SepWP.mono (step_vn_len_minVer_31974_vregs A s g vn F hpc hrun hsp_align) (fun _ _ _ _ h => h.2)

theorem step_vn_len_chainParams_319a0 {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4420#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4728#64) s
      (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
      (fun s' P' =>
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧ s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x11 = BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen vn.chainParams) ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧ s'.readReg64 .x23 = s.readReg64 .x23 ∧
        s'.readReg64 .x24 = s.readReg64 .x24 ∧ s'.readReg64 .x25 = s.readReg64 .x25 ∧
        s'.readReg64 .x26 = s.readReg64 .x26 ∧ s'.readReg64 .x27 = s.readReg64 .x27 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)) :=
  SepWP.mono (step_vn_len_chainParams_319a0_vregs A s g vn F hpc hrun hsp_align) (fun _ _ _ _ h => h.2)

theorem step_vn_len_combine_31ad4 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4728#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion))
    (hx11 : s.readReg64 .x11 = BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen vn.chainParams)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4768#64) s F
      (fun s' P' =>
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn)) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧ (P' ⊢ F)) :=
  SepWP.mono (step_vn_len_combine_31ad4_vregs s vn F hpc hrun hx8 hx9 hx10 hx11) (fun _ _ _ _ h => h.2)

end CryptoVerification.SpqrV1.Top.Send

