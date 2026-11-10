/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncode
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::send` Phase 3d Setup, `PqRatchetState` Assembly, and `VersionNegotiation` Length (`+4000..+4768`)

Proves `<Message>::serialize` setup and post-check, 928-byte `States` `memcpy`,
`<States>::into_pb` setup, 352-byte `PqRatchetState` stack assembly, and inlined
`Option<VersionNegotiation>::encoded_len` (`+4288..+4768`) in
`spqr::send::<signal_session_ratchet::Coins>`.
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



open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation


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
  (ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>")
  (ls_lemma% fnOff "<spqr::v1::chunked::states::Message>::serialize")
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::into_pb")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic")
  (ls_stub% "core::panicking::panic_const::panic_const_sub_overflow")


/-! ## 1. `+4000..+4020`: `<Message>::serialize` Call Setup -/

/-- `+4000 -> <Message>::serialize`: sets `x0 = s.sp + 0x1d70#64`, `x8 = s.sp + 0xff0#64`,
`w1 = s.readReg32 .x24`, and calls `<spqr::v1::chunked::states::Message>::serialize`
(return `+4020`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_pre_message_serialize_317fc {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4000#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "<spqr::v1::chunked::states::Message>::serialize" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) s P
      (fun sf Q => VRegsAt s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x1d70#64 ∧
        sf.readReg32 .x1 = s.readReg32 .x24 ∧
        sf.readReg64 .x8 = s.sp + 0xff0#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4020#64 ∧
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
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4000 20
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  wp_steps
  exact Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, rfl⟩

/-! ## 2. `+4020..+4096`: `Message::serialize` Post-Check, `memcpy`, and `States::into_pb` Setup -/

/-- `+4020 -> memcpy`: checks `msg.serialize idx = 1#8 :: tail` and sets up
`memcpy(s.sp + 0x1260#64, s.sp + 0x190#64, 928)` (return `+4080`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_post_message_serialize_to_memcpy_31810 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (tail : List (BitVec 8)) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4020#64)
    (hrun : s.status = .Running)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")) s
      (vecU8 A (s.sp + 0xff0#64) (1#8 :: tail) ∗
        memRegion (s.sp + 0x1260#64) 928 ∗ Frame)
      (fun sf Q => VRegsAt s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x1 = s.sp + 0x190#64 ∧
        sf.readReg64 .x2 = 928#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4080#64 ∧
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
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4020 60
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hx26 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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

/-- `+4080 -> <States>::into_pb`: sets `x0 = s.sp + 0x1260#64` and `x8 = s.sp + 0x590#64`
and calls `<spqr::v1::chunked::states::States>::into_pb` (return `+4096`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_post_memcpy_to_into_pb_3184c {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4080#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "<spqr::v1::chunked::states::States>::into_pb" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) s P
      (fun sf Q => VRegsAt s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x8 = s.sp + 0x590#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4096#64 ∧
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
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4080 16
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  wp_steps
  exact Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, rfl⟩

/-! ## 3. `+4096..+4364`: Assembling `PqRatchetState` (352 B) at `sp + 0x1260..0x13c0` -/

/-- `+4096 -> +4364` (`version_negotiation = none`): copies `vnWords6At`, `chainWords9At`,
and `outWords28` into `s.sp + 0x1260..0x13c0`, stores `x20` at `[s.sp + 0x20#64]`, loads
`x26 = noneCap`, and branches to `+4364`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_copy_pq_state_none_3185c {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (v_20 w1 w2 w3 w4 w5 : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64)
    (i0 i8 i16 i24 i32 i40 i48 i56
     i64 i72 i80 i88 i96 i104 i112 i120
     i128 i136 i144 i152 i160 i168 i176 i184
     i192 i200 i208 i216 : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4096#64)
    (hrun : s.status = .Running)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4364#64) s
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
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4096 192
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hx26 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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

/-- `+4096 -> +4288` (`version_negotiation = some vn`): copies `vnWords6At`, `chainWords9At`,
and `outWords28` into `s.sp + 0x1260..0x13c0`, stores `x20` at `[s.sp + 0x20#64]`, loads
`x26 = w0`, and falls through to `+4288`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_copy_pq_state_some_3185c {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (v_20 w0 w1 w2 w3 w4 w5 : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64)
    (i0 i8 i16 i24 i32 i40 i48 i56
     i64 i72 i80 i88 i96 i104 i112 i120
     i128 i136 i144 i152 i160 i168 i176 i184
     i192 i200 i208 i216 : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4096#64)
    (hrun : s.status = .Running)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hw0 : (w0 + 1#64 == 0#64) = false)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4288#64) s
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
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4096 192
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hx26 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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

/-! ## 4. `+4288..+4768`: Inline `Option<VersionNegotiation>::encoded_len` -/

/-- `+4364 -> +4768`: sets `x20 = 0#64 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen none)`
and jumps to `+4768`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_none_31968_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4364#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4768#64) s F
      (fun s' P' => VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen none) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧ (P' ⊢ F)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4364 8
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  wp_steps
  refine Prost.EncodeToVec.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by simp only [optVersionNegotiationPBFieldEncodedLen]; wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, Entails.refl _⟩

/-- `+4288 -> +4324`: loads `vn.authKey.length` from `[sp + 0x1270]` and computes
`x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey)`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_authKey_3191c_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4288#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : vn.authKey.length < 2 ^ 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4324#64) s
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
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4288 36
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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

/-- `+4324 -> +4376`: loads `vn.direction` from `[sp + 0x1284]` and computes
`x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction)`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_dir_31940_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4324#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4376#64) s
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
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4324 40
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4372 4
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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

/-- `+4376 -> +4420`: loads `vn.minVersion` from `[sp + 0x1288]` and computes
`x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion)`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_minVer_31974_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4376#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4420#64) s
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
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4376 44
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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

/-- `+4420 -> +4728`: computes `x11 = BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen vn.chainParams)`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_chainParams_319a0_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4420#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4728#64) s
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
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4420 64
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4680 48
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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

/-- `+4728 -> +4768`: sums `x8..x11` into
`x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn))`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_combine_31ad4_vregs {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4728#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion))
    (hx11 : s.readReg64 .x11 = BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen vn.chainParams)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4768#64) s F
      (fun s' P' => VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn)) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧ (P' ⊢ F)) := by
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4728 40
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_none_31968 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4364#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4768#64) s F
      (fun s' P' =>
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen none) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧ (P' ⊢ F)) :=
  SepWP.mono (CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_none_31968_vregs s F hpc hrun) (fun _ _ _ _ h => h.2)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_authKey_3191c {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4288#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : vn.authKey.length < 2 ^ 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4324#64) s
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
  SepWP.mono (CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_authKey_3191c_vregs A s g vn F hpc hrun hsp_align hlen) (fun _ _ _ _ h => h.2)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_dir_31940 {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4324#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4376#64) s
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
  SepWP.mono (CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_dir_31940_vregs A s g vn F hpc hrun hsp_align) (fun _ _ _ _ h => h.2)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_minVer_31974 {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4376#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4420#64) s
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
  SepWP.mono (CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_minVer_31974_vregs A s g vn F hpc hrun hsp_align) (fun _ _ _ _ h => h.2)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_chainParams_319a0 {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4420#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4728#64) s
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
  SepWP.mono (CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_chainParams_319a0_vregs A s g vn F hpc hrun hsp_align) (fun _ _ _ _ h => h.2)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_combine_31ad4 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4728#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion))
    (hx11 : s.readReg64 .x11 = BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen vn.chainParams)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4768#64) s F
      (fun s' P' =>
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn)) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧ (P' ⊢ F)) :=
  SepWP.mono (CryptoVerification.Cli.SpqrV1.Top.Send.step_vn_len_combine_31ad4_vregs s vn F hpc hrun hx8 hx9 hx10 hx11) (fun _ _ _ _ h => h.2)

end CryptoVerification.SpqrV1.Top.Send
