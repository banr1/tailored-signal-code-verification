/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExit
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Proof
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: V1 Ratchet `<Message>::deserialize` Steps & `States` Relocation Helpers

Pre/post `<Message>::deserialize` steppers (`+1532..+1568`), 928-byte `States` `memcpy` relocation
helpers, and stack splits for `<States>::from_pb` and `<States>::recv` in `spqr::recv` (`0x5462c`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `+1532..+1568`: `Message::deserialize` Pre/Post Steps -/

/-- Pre-call step `+1532 -> entry + 44552` (`0x54c28..0x54c3c -> 0x5f434`): sets `x0 = s0.sp -
    3056#64`, `x1 = pre.epoch`, `x2 = remPtr`, `x3 = BitVec.ofNat 64 pre.remaining.length`, `x25
    = s0.sp - 4640#64`, and `x30 = entry + 1556#64`. -/
theorem step_pre_msgDeserialize_1532 (b : BitVec 64) (ext : String → Option (State → State))
    (s0 s : State) (pre : MsgPreamble) (remPtr : BitVec 64) (P : SepProp)
    (hs0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 1532#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 44552#64) s P
      (fun sf Pf =>
        Pf = P ∧
        sf.sp = s0.sp - 4992#64 ∧
        TraceVRegs sf s ∧
        sf.readReg64 .x0 = s0.sp - 3056#64 ∧
        sf.readReg64 .x1 = pre.epoch ∧
        sf.readReg64 .x2 = remPtr ∧
        sf.readReg64 .x3 = BitVec.ofNat 64 pre.remaining.length ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = pre.epoch ∧
        sf.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length ∧
        sf.readReg64 .x24 = remPtr ∧
        sf.readReg64 .x25 = s0.sp - 4640#64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 1556#64) := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range b (Rust.withPanics ext) 1532 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  wp_steps
  exact ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨rfl, by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩

/-- Post-call error step `+1556 -> +2060` (`0x54c40..0x54c48 -> 0x54e38`) when
    `Message.deserialize spqrPolyApi pre.epoch pre.remaining = .error err`: reads `0xff#8` from
    `s0.sp - 3048#64` (`[sp, #1944]`) and takes `b.eq +2060`. -/
theorem step_post_msgDeserialize_err_1556 (b : BitVec 64) (ext : String → Option (State → State))
    (s0 s : State) (Rest : SepProp)
    (hs0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 1556#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 2060#64) s
      (((s0.sp - 3048#64) ↦₈ 0xff#8) ∗ Rest)
      (fun sf Pf =>
        Pf = (((s0.sp - 3048#64) ↦₈ 0xff#8) ∗ Rest) ∧
        sf.sp = s0.sp - 4992#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        TraceVRegs sf s) := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range b (Rust.withPanics ext) 1556 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  wp_steps
  exact ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨rfl, by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩

@[simp, arm64_norm]
theorem tag_zeroExtend_beq_255_false {tag : BitVec 8} (htag : tag ≠ 0xff#8) :
    (tag.zeroExtend 32 == 255#32) = false := by
  revert tag htag; decide

@[simp, arm64_norm]
theorem tag_zeroExtend_sub_255_beq_0_false {tag : BitVec 8} (htag : tag ≠ 0xff#8) :
    (tag.zeroExtend 32 - 255#32 == 0#32) = false := by
  revert tag htag; decide

@[simp, arm64_norm]
theorem tag_zeroExtend_sub_255_bne_0_true {tag : BitVec 8} (htag : tag ≠ 0xff#8) :
    (tag.zeroExtend 32 - 255#32 != 0#32) = true := by
  revert tag htag; decide

/-- Post-call ok step `+1556 -> +1568` (`0x54c40..0x54c48 -> 0x54c4c`) when `tag ≠ 0xff#8`:
    reads `tag` from `s0.sp - 3048#64` (`[sp, #1944]`), does not branch to `+2060`, and reaches
    `+1568` with `(sf.readReg64 .x8).truncate 8 = tag`. -/
theorem step_post_msgDeserialize_ok_1556 (b : BitVec 64) (ext : String → Option (State → State))
    (s0 s : State) (tag : BitVec 8) (Rest : SepProp)
    {post : State → SepProp → Prop}
    (hs0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 1556#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htag : tag ≠ 0xff#8)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 1568#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 4992#64 →
      TraceVRegs sf s →
      (sf.readReg64 .x8).truncate 8 = tag →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (((s0.sp - 3048#64) ↦₈ tag) ∗ Rest) post) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((s0.sp - 3048#64) ↦₈ tag) ∗ Rest) post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have htag_eq := tag_zeroExtend_beq_255_false htag
  have htag_cond := tag_zeroExtend_sub_255_beq_0_false htag
  have htag_ne := tag_zeroExtend_sub_255_bne_0_true htag
  have htrunc : ((tag.zeroExtend 32).zeroExtend 64).truncate 8 = tag := by
    revert tag; bv_kernel
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
  spqr_recv_fetches_range b (Rust.withPanics ext) 1556 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  wp_steps
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem memRegion_4064_split_2096 (sp0 : BitVec 64) :
    memRegion (sp0 - 4064#64) 3968 ⊢
      memRegion (sp0 - 4064#64) 1968 ∗
      memRegion (sp0 - 2096#64) 928 ∗
      memRegion (sp0 - 1168#64) 1072 := by
  rw [show (3968 : Nat) = 1968 + (928 + 1072) by decide,
      memRegion_split (sp0 - 4064#64) 1968 (928 + 1072) (by decide),
      show (sp0 - 4064#64) + 1968#64 = sp0 - 2096#64 by bv_omega,
      memRegion_split (sp0 - 2096#64) 928 1072 (by decide),
      show (sp0 - 2096#64) + 928#64 = sp0 - 1168#64 by bv_omega]
  exact Entails.refl _

theorem memRegion_4064_join_2096 (sp0 : BitVec 64) :
    memRegion (sp0 - 4064#64) 1968 ∗
      memRegion (sp0 - 2096#64) 928 ∗
      memRegion (sp0 - 1168#64) 1072 ⊢
    memRegion (sp0 - 4064#64) 3968 := by
  rw [show (3968 : Nat) = 1968 + (928 + 1072) by decide,
      memRegion_split (sp0 - 4064#64) 1968 (928 + 1072) (by decide),
      show (sp0 - 4064#64) + 1968#64 = sp0 - 2096#64 by bv_omega,
      memRegion_split (sp0 - 2096#64) 928 1072 (by decide),
      show (sp0 - 2096#64) + 928#64 = sp0 - 1168#64 by bv_omega]
  exact Entails.refl _

/-! ## 2. `928`B `States` `memcpy` Relocation Helpers -/

@[simp, arm64_norm, wp_norm]
theorem recv_chunkedStatesWord0_add_one_beq_zero {F : ShaCompress}
    (st0 : States spqrPolyApi (spqrAuthApi F)) :
    (chunkedStatesWord0 st0 + 1#64 == 0#64) = false := by
  cases st0 with
  | ct1Sampled s => exact polyEncoderTagVal_add_one_beq_zero s.sending_ct1.s
  | _ => rfl

theorem recv_pointsToBytes_8_eq_one_cell (a : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 8) :
    (a ↦ₛ bs) ⊢ ∃∗ w : BitVec 64, ⌜bs = unpack64 w⌝ ∗ (a ↦₆₄ w) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp only [List.length] at hlen; omega)
  refine Entails.sepExists_right (ProofLib.pack64 b0 b1 b2 b3 b4 b5 b6 b7) ?_
  have hpack : unpack64 (ProofLib.pack64 b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] :=
    ProofLib.unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7
  rw [hpack]
  apply Entails.pure_right rfl
  rw [ProofLib.pointsTo64_eq_pointsToBytes, hpack]
  exact Entails.refl _

theorem recv_pointsToBytes_16_eq_two_cells (a : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 16) :
    (a ↦ₛ bs) ⊢ ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ⌜bs = unpack64 w2 ++ unpack64 w3⌝ ∗
      (a ↦₆₄ w2) ∗ ((a + 8#64) ↦₆₄ w3) := by
  have h16 : (a ↦ₛ bs) = (a ↦ₛ bs.take 8) ∗ ((a + 8#64) ↦ₛ bs.drop 8) := by
    have hbs : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
    have hl1 : (bs.take 8).length = 8 := by simp [hlen]
    conv_lhs => rw [hbs]
    rw [ProofLib.pointsToBytes_append, hl1]
  have hl1 : (bs.take 8).length = 8 := by simp [hlen]
  have hl2 : (bs.drop 8).length = 8 := by simp [hlen]
  rw [h16]
  refine Entails.trans
    (sepConj_mono (recv_pointsToBytes_8_eq_one_cell a hl1)
      (recv_pointsToBytes_8_eq_one_cell (a + 8#64) hl2)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  have hpull :
      ((⌜bs.take 8 = unpack64 w2⌝ ∗ (a ↦₆₄ w2)) ∗
       ⌜bs.drop 8 = unpack64 w3⌝ ∗ ((a + 8#64) ↦₆₄ w3)) =
      ⌜bs.take 8 = unpack64 w2⌝ ∗ ⌜bs.drop 8 = unpack64 w3⌝ ∗
        ((a ↦₆₄ w2) ∗ ((a + 8#64) ↦₆₄ w3)) := by ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hw2
  apply Entails.pure_left; intro hw3
  refine Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_)
  have hbs : bs = unpack64 w2 ++ unpack64 w3 := by
    rw [← hw2, ← hw3, List.take_append_drop 8 bs]
  apply Entails.pure_right hbs
  exact Entails.of_eq (by ac_rfl)

theorem recv_pointsToBytes_920_split_3words_896 (a : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 920) :
    (a ↦ₛ bs) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ bs896 : List (BitVec 8),
        ⌜bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 ∧ bs896.length = 896⌝ ∗
        (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗ ((a + 24#64) ↦ₛ bs896) := by
  let b16 := bs.take 16
  let r16 := bs.drop 16
  let b8 := r16.take 8
  let bs896 := r16.drop 8
  have hb16 : b16.length = 16 := by simp [b16, hlen]
  have hr16 : r16.length = 904 := by simp [r16, hlen]
  have hb8 : b8.length = 8 := by simp [b8, hr16]
  have hbs896 : bs896.length = 896 := by simp [bs896, hr16]
  have hsplit : (a ↦ₛ bs) = (a ↦ₛ b16) ∗ ((a + 16#64) ↦ₛ b8) ∗ ((a + 24#64) ↦ₛ bs896) := by
    have hbs1 : bs = b16 ++ (b8 ++ bs896) := by
      simp only [b16, r16, b8, bs896, List.take_append_drop]
    conv_lhs => rw [hbs1]
    rw [ProofLib.pointsToBytes_append a b16, hb16,
        ProofLib.pointsToBytes_append (a + 16#64) b8, hb8]
    have ha24 : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
    rw [ha24]
  rw [hsplit]
  refine Entails.trans
    (sepConj_mono (recv_pointsToBytes_16_eq_two_cells a hb16)
      (sepConj_mono_left (recv_pointsToBytes_8_eq_one_cell (a + 16#64) hb8))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  have hpull :
      ((⌜b16 = unpack64 w1 ++ unpack64 w2⌝ ∗ (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2)) ∗
       (⌜b8 = unpack64 w3⌝ ∗ ((a + 16#64) ↦₆₄ w3)) ∗
       ((a + 24#64) ↦ₛ bs896)) =
      ⌜b16 = unpack64 w1 ++ unpack64 w2⌝ ∗ ⌜b8 = unpack64 w3⌝ ∗
        ((a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗ ((a + 24#64) ↦ₛ bs896)) := by ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hw12
  apply Entails.pure_left; intro hw3
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right bs896 ?_)))
  have hbs_eq : bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 := by
    calc bs = b16 ++ (b8 ++ bs896) := by simp only [b16, r16, b8, bs896, List.take_append_drop]
      _ = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 := by
          rw [hw12, hw3]
          simp only [List.append_assoc]
  exact Entails.pure_right ⟨hbs_eq, hbs896⟩ (Entails.refl _)

theorem recv_words3_and_896_entails_pointsToBytes_920 (a w1 w2 w3 : BitVec 64)
    {bs bs896 : List (BitVec 8)}
    (hbs : bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896) :
    (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗ ((a + 24#64) ↦ₛ bs896) ⊢
      (a ↦ₛ bs) := by
  subst hbs
  simp only [List.append_assoc]
  rw [pointsToBytes_append a (unpack64 w1), unpack64_length, ← pointsTo64_eq_pointsToBytes a w1,
      pointsToBytes_append (a + 8#64) (unpack64 w2), unpack64_length,
      ← pointsTo64_eq_pointsToBytes (a + 8#64) w2,
      pointsToBytes_append ((a + 8#64) + 8#64) (unpack64 w3), unpack64_length,
      ← pointsTo64_eq_pointsToBytes ((a + 8#64) + 8#64) w3]
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha24 : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
  rw [ha16, ha24]
  exact Entails.of_eq (by ac_rfl)

theorem chunkedStatesAt_entails_reloc_words (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st0 : States spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A a st0 ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ bs896 : List (BitVec 8),
        ⌜bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 ∧ bs896.length = 896⌝ ∗
        (a ↦₆₄ chunkedStatesWord0 st0) ∗
        ((a + 8#64) ↦₆₄ w1) ∗
        ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦ₛ bs896) ∗
        relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs := by
  rw [chunkedStatesAt_eq_word0_tail920 A a st0]
  refine Entails.trans (sepConj_mono_right (Relocatable.of_chunkedStatesTail920At A st0 (a + 8#64))) ?_
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro hlen920
  have hsplit := recv_pointsToBytes_920_split_3words_896 (a + 8#64) hlen920
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha24 : (a + 8#64) + 16#64 = a + 24#64 := by bv_omega
  have ha32 : (a + 8#64) + 24#64 = a + 32#64 := by bv_omega
  rw [ha16, ha24, ha32] at hsplit
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hsplit)) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w2
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs896
  refine Entails.sepExists_right bs (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right bs896 ?_))))
  exact Entails.of_eq (by ac_rfl)

theorem reassemble_chunkedStatesAt_words (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (w1 w2 w3 : BitVec 64)
    {bs bs896 : List (BitVec 8)}
    (hbs : bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896) :
    (a ↦₆₄ chunkedStatesWord0 st0) ∗
      ((a + 8#64) ↦₆₄ w1) ∗
      ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦ₛ bs896) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs ⊢
      chunkedStatesAt A a st0 := by
  rw [chunkedStatesAt_eq_word0_tail920 A a st0]
  refine sepConj_mono_right ?_
  have h920 := recv_words3_and_896_entails_pointsToBytes_920 (a + 8#64) w1 w2 w3 hbs
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha24 : (a + 8#64) + 16#64 = a + 24#64 := by bv_omega
  have ha32 : (a + 8#64) + 24#64 = a + 32#64 := by bv_omega
  rw [ha16, ha24, ha32] at h920
  have hreord :
      ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦ₛ bs896) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs =
      (((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
       ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦ₛ bs896)) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left h920) ?_
  exact relocatedHeap_recompose (fun dst => chunkedStatesTail920At A dst st0) bs (a + 8#64)

theorem reassemble_src_928_after_memcpy (a w0 w1 w2 w3 : BitVec 64)
    {bs896 : List (BitVec 8)} (hlen896 : bs896.length = 896) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
      ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦ₛ bs896) ⊢
      memRegion a 928 := by
  have hm : ((a + 32#64) ↦ₛ bs896) ⊢ memRegion (a + 32#64) 896 := by
    rw [← hlen896]; exact pointsToBytes_entails_memRegion (a + 32#64) bs896
  rw [show (928 : Nat) = 8 + (8 + (8 + (8 + 896))) by decide,
      memRegion_split a 8 920 (by decide),
      memRegion_split (a + 8#64) 8 912 (by decide),
      show (a + 8#64) + 8#64 = a + 16#64 by bv_omega,
      memRegion_split (a + 16#64) 8 904 (by decide),
      show (a + 16#64) + 8#64 = a + 24#64 by bv_omega,
      memRegion_split (a + 24#64) 8 896 (by decide),
      show (a + 24#64) + 8#64 = a + 32#64 by bv_omega]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion a w0)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (a + 8#64) w1)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (a + 16#64) w2)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (a + 24#64) w3) hm)))

/-- Split `memRegion (sp0 - 1168#64) 1072` into:
    - `memRegion (sp0 - 1168#64) 8`
    - `memRegion (sp0 - 1160#64) 928` (destination of `<States>::from_pb` relocation)
    - `memRegion (sp0 - 232#64) 88`
    - `memRegion (sp0 - 144#64) 24` (`[x29, #-48 .. #-24]` scratch words)
    - `memRegion (sp0 - 120#64) 24`. -/
theorem memRegion_1168_split_statesFromPb (sp0 : BitVec 64) :
    memRegion (sp0 - 1168#64) 1072 ⊢
      memRegion (sp0 - 1168#64) 8 ∗
      memRegion (sp0 - 1160#64) 928 ∗
      memRegion (sp0 - 232#64) 88 ∗
      memRegion (sp0 - 144#64) 24 ∗
      memRegion (sp0 - 120#64) 24 := by
  rw [show (1072 : Nat) = 8 + (928 + (88 + (24 + 24))) by decide,
      memRegion_split (sp0 - 1168#64) 8 (928 + (88 + (24 + 24))) (by decide),
      show (sp0 - 1168#64) + 8#64 = sp0 - 1160#64 by bv_omega,
      memRegion_split (sp0 - 1160#64) 928 (88 + (24 + 24)) (by decide),
      show (sp0 - 1160#64) + 928#64 = sp0 - 232#64 by bv_omega,
      memRegion_split (sp0 - 232#64) 88 (24 + 24) (by decide),
      show (sp0 - 232#64) + 88#64 = sp0 - 144#64 by bv_omega,
      memRegion_split (sp0 - 144#64) 24 24 (by decide),
      show (sp0 - 144#64) + 24#64 = sp0 - 120#64 by bv_omega]
  exact Entails.refl _

theorem memRegion_1168_join_statesFromPb (sp0 : BitVec 64) :
    memRegion (sp0 - 1168#64) 8 ∗
      memRegion (sp0 - 1160#64) 928 ∗
      memRegion (sp0 - 232#64) 88 ∗
      memRegion (sp0 - 144#64) 24 ∗
      memRegion (sp0 - 120#64) 24 ⊢
    memRegion (sp0 - 1168#64) 1072 := by
  rw [show (1072 : Nat) = 8 + (928 + (88 + (24 + 24))) by decide,
      memRegion_split (sp0 - 1168#64) 8 (928 + (88 + (24 + 24))) (by decide),
      show (sp0 - 1168#64) + 8#64 = sp0 - 1160#64 by bv_omega,
      memRegion_split (sp0 - 1160#64) 928 (88 + (24 + 24)) (by decide),
      show (sp0 - 1160#64) + 928#64 = sp0 - 232#64 by bv_omega,
      memRegion_split (sp0 - 232#64) 88 (24 + 24) (by decide),
      show (sp0 - 232#64) + 88#64 = sp0 - 144#64 by bv_omega,
      memRegion_split (sp0 - 144#64) 24 24 (by decide),
      show (sp0 - 144#64) + 24#64 = sp0 - 120#64 by bv_omega]
  exact Entails.refl _

/-- Expose the 4 leading words `(a, a + 8, a + 16, a + 24)` of `resultChunkedStatesAt A a
    (.error (.err err))`. -/
theorem resultChunkedStatesAt_err_expose (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (err : Error) :
    resultChunkedStatesAt A (F := F) a (.error (.err err)) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ⌜∀ r : BitVec 64, ((r + 8#64) ↦₆₄ w1) ⊢ ((r + 8#64) ↦₈ spqrErrorByte err) ∗ memRegion (r + 9#64) 7⌝ ∗
        (a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        memRegion (a + 32#64) 896 := by
  dsimp only [resultChunkedStatesAt]
  refine Entails.trans (sepConj_mono_right (err_payload_expose a (spqrErrorByte err) 919 (by decide) (by decide))) ?_
  simp only [sepExists_sepConj_right, Nat.reduceSub]
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w3
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_))
  exact Entails.of_eq (by ac_rfl)

/-- Expose the 4 leading words `(a, a + 8, a + 16, a + 24)` of `resultV1RecvAt A a (.error (.err
    err))`. -/
theorem resultV1RecvAt_err_expose (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (err : Error) :
    resultV1RecvAt A (F := F) a (.error (.err err)) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ⌜∀ r : BitVec 64, ((r + 8#64) ↦₆₄ w1) ⊢ ((r + 8#64) ↦₈ States.RecvCt2Chunk.spqrErrorByte err) ∗ memRegion (r + 9#64) 7⌝ ∗
        (a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        memRegion (a + 32#64) 928 := by
  dsimp only [resultV1RecvAt]
  refine Entails.trans (sepConj_mono_right (err_payload_expose a (States.RecvCt2Chunk.spqrErrorByte err) 951 (by decide) (by decide))) ?_
  simp only [sepExists_sepConj_right, Nat.reduceSub]
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w3
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_))
  exact Entails.of_eq (by ac_rfl)

/-! ## 4. Stepping `<Message>::deserialize` (+1532..+1636) and `<States>::from_pb` (+1636..+1736) -/

theorem spqrRecvRoAt_expose_statesFromPb (b : BitVec 64) :
    spqrRecvRoAt b ⊢
      statesFromPbJumpTableAt b ∗
      (∃∗ P_ro : SepProp, ⌜statesFromPbJumpTableAt b ∗ P_ro ⊢ spqrRecvRoAt b⌝ ∗ P_ro) := by
  unfold spqrRecvRoAt
  refine Entails.trans
    (Entails.of_eq (show
      Prost.MessageMerge.v1StateJumpTablesAt b ∗
        statesFromPbJumpTableAt b ∗
        States.Recv.statesRecvRoAt b ∗
        statesIntoPbJumpTableAt b =
      statesFromPbJumpTableAt b ∗
        (Prost.MessageMerge.v1StateJumpTablesAt b ∗
          States.Recv.statesRecvRoAt b ∗
          statesIntoPbJumpTableAt b) by ac_rfl)) ?_
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right _ (Entails.pure_right ?_ (Entails.refl _))
  exact Entails.of_eq (by ac_rfl)

theorem spqrRecvRoAt_expose_statesRecv (b : BitVec 64) :
    spqrRecvRoAt b ⊢
      States.Recv.statesRecvRoAt b ∗
      (∃∗ P_ro : SepProp, ⌜States.Recv.statesRecvRoAt b ∗ P_ro ⊢ spqrRecvRoAt b⌝ ∗ P_ro) := by
  unfold spqrRecvRoAt
  refine Entails.trans
    (Entails.of_eq (show
      Prost.MessageMerge.v1StateJumpTablesAt b ∗
        statesFromPbJumpTableAt b ∗
        States.Recv.statesRecvRoAt b ∗
        statesIntoPbJumpTableAt b =
      States.Recv.statesRecvRoAt b ∗
        (Prost.MessageMerge.v1StateJumpTablesAt b ∗
          statesFromPbJumpTableAt b ∗
          statesIntoPbJumpTableAt b) by ac_rfl)) ?_
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right _ (Entails.pure_right ?_ (Entails.refl _))
  exact Entails.of_eq (by ac_rfl)

@[simp, arm64_norm]
theorem statesFromPb_noneCap_add_one_beq_zero :
    (noneCap + 1#64 == 0#64) = true := rfl

theorem optEpochSecretAt_expose_words (A : RustAlloc) (a : BitVec 64) (key : Option EpochSecret) :
    States.Recv.optEpochSecretAt A a key ⊢
      ∃∗ kw0 : BitVec 64, ∃∗ kw1 : BitVec 64, ∃∗ kw2 : BitVec 64, ∃∗ kw3 : BitVec 64, ∃∗ P_key : SepProp,
        ⌜∀ b : BitVec 64,
          (b ↦₆₄ kw0) ∗ ((b + 8#64) ↦₆₄ kw1) ∗ ((b + 16#64) ↦₆₄ kw2) ∗ ((b + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
            States.Recv.optEpochSecretAt A b key⌝ ∗
        P_key ∗
        (a ↦₆₄ kw0) ∗ ((a + 8#64) ↦₆₄ kw1) ∗ ((a + 16#64) ↦₆₄ kw2) ∗ ((a + 24#64) ↦₆₄ kw3) := by
  cases key with
  | none =>
    dsimp only [States.Recv.optEpochSecretAt]
    rw [memRegion_24_words3 (a + 8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro kw3
    apply Entails.sepExists_elim; intro kw2
    apply Entails.sepExists_elim; intro kw1
    refine Entails.sepExists_right noneCap
      (Entails.sepExists_right kw1
        (Entails.sepExists_right kw2
          (Entails.sepExists_right kw3
            (Entails.sepExists_right emp ?_))))
    refine Entails.pure_right ?_ (Entails.of_eq (by ac_rfl))
    intro b
    have h24 := words3_to_memRegion_24 (b + 8#64) kw1 kw2 kw3
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h24
    refine Entails.trans
      (Entails.of_eq (show
        (b ↦₆₄ noneCap) ∗ ((b + 8#64) ↦₆₄ kw1) ∗
          ((b + 16#64) ↦₆₄ kw2) ∗ ((b + 24#64) ↦₆₄ kw3) ∗ emp =
        (b ↦₆₄ noneCap) ∗
          (((b + 8#64) ↦₆₄ kw1) ∗ ((b + 16#64) ↦₆₄ kw2) ∗ ((b + 24#64) ↦₆₄ kw3)) by ac_rfl)) ?_
    exact sepConj_mono_right h24
  | some sec =>
    dsimp only [States.Recv.optEpochSecretAt, States.RecvCt2Chunk.epochSecretAt,
      vecU8, vecU8At, vecHeader]
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro cap
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro ptr
    let P_key : SepProp :=
      ⌜sec.secret.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ sec.secret) ∗
          memRegion (ptr + BitVec.ofNat 64 sec.secret.length) (cap.toNat - sec.secret.length)
    refine Entails.sepExists_right cap
      (Entails.sepExists_right ptr
        (Entails.sepExists_right (BitVec.ofNat 64 sec.secret.length)
          (Entails.sepExists_right sec.epoch
            (Entails.sepExists_right P_key ?_))))
    refine Entails.pure_right ?_ (Entails.of_eq (by dsimp only [P_key]; ac_rfl))
    intro b
    refine Entails.trans
      (Entails.of_eq (show
        (b ↦₆₄ cap) ∗ ((b + 8#64) ↦₆₄ ptr) ∗
          ((b + 16#64) ↦₆₄ BitVec.ofNat 64 sec.secret.length) ∗
          ((b + 24#64) ↦₆₄ sec.epoch) ∗ P_key =
        (((b ↦₆₄ cap) ∗ ((b + 8#64) ↦₆₄ ptr) ∗
          ((b + 16#64) ↦₆₄ BitVec.ofNat 64 sec.secret.length)) ∗ P_key) ∗
          ((b + 24#64) ↦₆₄ sec.epoch) by ac_rfl)) ?_
    exact sepConj_mono_left (Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _)))

/-- Split `memRegion (sp0 - 4064#64) 2896` for `<States>::recv` (`+1736 .. +1828`) into:
    - `memRegion (sp0 - 4064#64) 32`
    - `memRegion (sp0 - 4032#64) 16` (`[sp, #960]` for `v.key` words 2..3)
    - `memRegion (sp0 - 4016#64) 928` (`[sp, #976]` destination for `v.state`)
    - `memRegion (sp0 - 3088#64) 24` (`[sp, #1904 .. #1928]` scratch for `q0, x8`)
    - `memRegion (sp0 - 3064#64) 8`
    - `memRegion (sp0 - 3056#64) 960` (`sret` buffer for `<States>::recv`)
    - `memRegion (sp0 - 2096#64) 928`. -/
theorem memRegion_2896_split_statesRecv (sp0 : BitVec 64) :
    memRegion (sp0 - 4064#64) 2896 ⊢
      memRegion (sp0 - 4064#64) 32 ∗
      memRegion (sp0 - 4032#64) 16 ∗
      memRegion (sp0 - 4016#64) 928 ∗
      memRegion (sp0 - 3088#64) 24 ∗
      memRegion (sp0 - 3064#64) 8 ∗
      memRegion (sp0 - 3056#64) 960 ∗
      memRegion (sp0 - 2096#64) 928 := by
  rw [show (2896 : Nat) = 32 + (16 + (928 + (24 + (8 + (960 + 928))))) by decide,
      memRegion_split (sp0 - 4064#64) 32 (16 + (928 + (24 + (8 + (960 + 928))))) (by decide),
      show (sp0 - 4064#64) + 32#64 = sp0 - 4032#64 by bv_omega,
      memRegion_split (sp0 - 4032#64) 16 (928 + (24 + (8 + (960 + 928)))) (by decide),
      show (sp0 - 4032#64) + 16#64 = sp0 - 4016#64 by bv_omega,
      memRegion_split (sp0 - 4016#64) 928 (24 + (8 + (960 + 928))) (by decide),
      show (sp0 - 4016#64) + 928#64 = sp0 - 3088#64 by bv_omega,
      memRegion_split (sp0 - 3088#64) 24 (8 + (960 + 928)) (by decide),
      show (sp0 - 3088#64) + 24#64 = sp0 - 3064#64 by bv_omega,
      memRegion_split (sp0 - 3064#64) 8 (960 + 928) (by decide),
      show (sp0 - 3064#64) + 8#64 = sp0 - 3056#64 by bv_omega,
      memRegion_split (sp0 - 3056#64) 960 928 (by decide),
      show (sp0 - 3056#64) + 960#64 = sp0 - 2096#64 by bv_omega]
  exact Entails.refl _

theorem memRegion_2896_join_statesRecv_err (sp0 w1 w2 w3 : BitVec 64) :
    memRegion (sp0 - 4064#64) 32 ∗
      memRegion (sp0 - 4032#64) 16 ∗
      memRegion (sp0 - 4016#64) 928 ∗
      ((sp0 - 3088#64) ↦₆₄ w1) ∗
      ((sp0 - 3080#64) ↦₆₄ w2) ∗
      ((sp0 - 3072#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 3064#64) 8 ∗
      ((sp0 - 3056#64) ↦₆₄ noneCap) ∗
      ((sp0 - 3048#64) ↦₆₄ w1) ∗
      ((sp0 - 3040#64) ↦₆₄ w2) ∗
      ((sp0 - 3032#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 3024#64) 928 ∗
      memRegion (sp0 - 2096#64) 928 ⊢
    memRegion (sp0 - 4064#64) 2896 := by
  have h24 := words3_to_memRegion_24 (sp0 - 3088#64) w1 w2 w3
  rw [bv_sub_add_lit sp0 3088 8, bv_sub_add_lit sp0 3088 16] at h24
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h24
  have h32 := words4_to_memRegion_32 (sp0 - 3056#64) noneCap w1 w2 w3
  rw [bv_sub_add_lit sp0 3056 8, bv_sub_add_lit sp0 3056 16, bv_sub_add_lit sp0 3056 24] at h32
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h32
  have h960 :
      ((sp0 - 3056#64) ↦₆₄ noneCap) ∗
        ((sp0 - 3048#64) ↦₆₄ w1) ∗
        ((sp0 - 3040#64) ↦₆₄ w2) ∗
        ((sp0 - 3032#64) ↦₆₄ w3) ∗
        memRegion (sp0 - 3024#64) 928 ⊢
      memRegion (sp0 - 3056#64) 960 := by
    rw [show (960 : Nat) = 32 + 928 by decide,
        memRegion_split (sp0 - 3056#64) 32 928 (by decide),
        show (sp0 - 3056#64) + 32#64 = sp0 - 3024#64 by bv_omega]
    refine Entails.trans
      (Entails.of_eq (show
        ((sp0 - 3056#64) ↦₆₄ noneCap) ∗
          ((sp0 - 3048#64) ↦₆₄ w1) ∗
          ((sp0 - 3040#64) ↦₆₄ w2) ∗
          ((sp0 - 3032#64) ↦₆₄ w3) ∗
          memRegion (sp0 - 3024#64) 928 =
        (((sp0 - 3056#64) ↦₆₄ noneCap) ∗
          ((sp0 - 3048#64) ↦₆₄ w1) ∗
          ((sp0 - 3040#64) ↦₆₄ w2) ∗
          ((sp0 - 3032#64) ↦₆₄ w3)) ∗
          memRegion (sp0 - 3024#64) 928 by ac_rfl)) ?_
    exact sepConj_mono_left h32
  rw [show (2896 : Nat) = 32 + (16 + (928 + (24 + (8 + (960 + 928))))) by decide,
      memRegion_split (sp0 - 4064#64) 32 (16 + (928 + (24 + (8 + (960 + 928))))) (by decide),
      show (sp0 - 4064#64) + 32#64 = sp0 - 4032#64 by bv_omega,
      memRegion_split (sp0 - 4032#64) 16 (928 + (24 + (8 + (960 + 928)))) (by decide),
      show (sp0 - 4032#64) + 16#64 = sp0 - 4016#64 by bv_omega,
      memRegion_split (sp0 - 4016#64) 928 (24 + (8 + (960 + 928))) (by decide),
      show (sp0 - 4016#64) + 928#64 = sp0 - 3088#64 by bv_omega,
      memRegion_split (sp0 - 3088#64) 24 (8 + (960 + 928)) (by decide),
      show (sp0 - 3088#64) + 24#64 = sp0 - 3064#64 by bv_omega,
      memRegion_split (sp0 - 3064#64) 8 (960 + 928) (by decide),
      show (sp0 - 3064#64) + 8#64 = sp0 - 3056#64 by bv_omega,
      memRegion_split (sp0 - 3056#64) 960 928 (by decide),
      show (sp0 - 3056#64) + 960#64 = sp0 - 2096#64 by bv_omega]
  refine Entails.trans
    (Entails.of_eq (show
      memRegion (sp0 - 4064#64) 32 ∗
        memRegion (sp0 - 4032#64) 16 ∗
        memRegion (sp0 - 4016#64) 928 ∗
        ((sp0 - 3088#64) ↦₆₄ w1) ∗
        ((sp0 - 3080#64) ↦₆₄ w2) ∗
        ((sp0 - 3072#64) ↦₆₄ w3) ∗
        memRegion (sp0 - 3064#64) 8 ∗
        ((sp0 - 3056#64) ↦₆₄ noneCap) ∗
        ((sp0 - 3048#64) ↦₆₄ w1) ∗
        ((sp0 - 3040#64) ↦₆₄ w2) ∗
        ((sp0 - 3032#64) ↦₆₄ w3) ∗
        memRegion (sp0 - 3024#64) 928 ∗
        memRegion (sp0 - 2096#64) 928 =
      memRegion (sp0 - 4064#64) 32 ∗
        memRegion (sp0 - 4032#64) 16 ∗
        memRegion (sp0 - 4016#64) 928 ∗
        (((sp0 - 3088#64) ↦₆₄ w1) ∗
          ((sp0 - 3080#64) ↦₆₄ w2) ∗
          ((sp0 - 3072#64) ↦₆₄ w3)) ∗
        memRegion (sp0 - 3064#64) 8 ∗
        (((sp0 - 3056#64) ↦₆₄ noneCap) ∗
          ((sp0 - 3048#64) ↦₆₄ w1) ∗
          ((sp0 - 3040#64) ↦₆₄ w2) ∗
          ((sp0 - 3032#64) ↦₆₄ w3) ∗
          memRegion (sp0 - 3024#64) 928) ∗
        memRegion (sp0 - 2096#64) 928 by ac_rfl)) ?_
  exact sepConj_mono_right
    (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono h24
          (sepConj_mono_right (sepConj_mono_left h960)))))

theorem memRegion_2992_join_statesRecv_ok (sp0 w1 w2 w3 kw0 kw1 kw2 kw3 : BitVec 64) :
    ((sp0 - 3088#64) ↦₆₄ w1) ∗
      ((sp0 - 3080#64) ↦₆₄ w2) ∗
      ((sp0 - 3072#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 3064#64) 8 ∗
      memRegion (sp0 - 3056#64) 928 ∗
      ((sp0 - 2128#64) ↦₆₄ kw0) ∗
      ((sp0 - 2120#64) ↦₆₄ kw1) ∗
      ((sp0 - 2112#64) ↦₆₄ kw2) ∗
      ((sp0 - 2104#64) ↦₆₄ kw3) ∗
      memRegion (sp0 - 2096#64) 928 ∗
      memRegion (sp0 - 1168#64) 8 ∗
      memRegion (sp0 - 1160#64) 928 ∗
      memRegion (sp0 - 232#64) 136 ⊢
    memRegion (sp0 - 3088#64) 2992 := by
  have h24 := words3_to_memRegion_24 (sp0 - 3088#64) w1 w2 w3
  rw [bv_sub_add_lit sp0 3088 8, bv_sub_add_lit sp0 3088 16] at h24
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h24
  have h32 := words4_to_memRegion_32 (sp0 - 2128#64) kw0 kw1 kw2 kw3
  rw [bv_sub_add_lit sp0 2128 8, bv_sub_add_lit sp0 2128 16, bv_sub_add_lit sp0 2128 24] at h32
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h32
  rw [show (2992 : Nat) = 24 + (8 + (928 + (32 + (928 + (8 + (928 + 136)))))) by decide,
      memRegion_split (sp0 - 3088#64) 24 (8 + (928 + (32 + (928 + (8 + (928 + 136)))))) (by decide),
      show (sp0 - 3088#64) + 24#64 = sp0 - 3064#64 by bv_omega,
      memRegion_split (sp0 - 3064#64) 8 (928 + (32 + (928 + (8 + (928 + 136))))) (by decide),
      show (sp0 - 3064#64) + 8#64 = sp0 - 3056#64 by bv_omega,
      memRegion_split (sp0 - 3056#64) 928 (32 + (928 + (8 + (928 + 136)))) (by decide),
      show (sp0 - 3056#64) + 928#64 = sp0 - 2128#64 by bv_omega,
      memRegion_split (sp0 - 2128#64) 32 (928 + (8 + (928 + 136))) (by decide),
      show (sp0 - 2128#64) + 32#64 = sp0 - 2096#64 by bv_omega,
      memRegion_split (sp0 - 2096#64) 928 (8 + (928 + 136)) (by decide),
      show (sp0 - 2096#64) + 928#64 = sp0 - 1168#64 by bv_omega,
      memRegion_split (sp0 - 1168#64) 8 (928 + 136) (by decide),
      show (sp0 - 1168#64) + 8#64 = sp0 - 1160#64 by bv_omega,
      memRegion_split (sp0 - 1160#64) 928 136 (by decide),
      show (sp0 - 1160#64) + 928#64 = sp0 - 232#64 by bv_omega]
  refine Entails.trans
    (Entails.of_eq (show
      ((sp0 - 3088#64) ↦₆₄ w1) ∗
        ((sp0 - 3080#64) ↦₆₄ w2) ∗
        ((sp0 - 3072#64) ↦₆₄ w3) ∗
        memRegion (sp0 - 3064#64) 8 ∗
        memRegion (sp0 - 3056#64) 928 ∗
        ((sp0 - 2128#64) ↦₆₄ kw0) ∗
        ((sp0 - 2120#64) ↦₆₄ kw1) ∗
        ((sp0 - 2112#64) ↦₆₄ kw2) ∗
        ((sp0 - 2104#64) ↦₆₄ kw3) ∗
        memRegion (sp0 - 2096#64) 928 ∗
        memRegion (sp0 - 1168#64) 8 ∗
        memRegion (sp0 - 1160#64) 928 ∗
        memRegion (sp0 - 232#64) 136 =
      (((sp0 - 3088#64) ↦₆₄ w1) ∗
        ((sp0 - 3080#64) ↦₆₄ w2) ∗
        ((sp0 - 3072#64) ↦₆₄ w3)) ∗
        memRegion (sp0 - 3064#64) 8 ∗
        memRegion (sp0 - 3056#64) 928 ∗
        (((sp0 - 2128#64) ↦₆₄ kw0) ∗
          ((sp0 - 2120#64) ↦₆₄ kw1) ∗
          ((sp0 - 2112#64) ↦₆₄ kw2) ∗
          ((sp0 - 2104#64) ↦₆₄ kw3)) ∗
        memRegion (sp0 - 2096#64) 928 ∗
        memRegion (sp0 - 1168#64) 8 ∗
        memRegion (sp0 - 1160#64) 928 ∗
        memRegion (sp0 - 232#64) 136 by ac_rfl)) ?_
  exact sepConj_mono h24
    (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_left h32)))

theorem sp_sub_3056_add_928 (sp0 : BitVec 64) :
    (sp0 - 3056#64) + 928#64 = sp0 - 2128#64 :=
  bv_sub_add_lit sp0 3056 928

theorem messageAt_entails_memRegion_48 (a : BitVec 64) (msg : Message spqrPolyApi) :
    messageAt spqrPolyApi a msg ⊢ memRegion a 48 := by
  refine Entails.trans (messageAt_expose_bytes39 spqrPolyApi a msg) ?_
  apply Entails.sepExists_elim; intro tag
  apply Entails.sepExists_elim; intro bs39
  apply Entails.pure_left; rintro ⟨_, hbs39, _⟩
  rw [show (48 : Nat) = 8 + (1 + 39) by decide,
      memRegion_split a 8 (1 + 39) (by decide),
      memRegion_split' (b := a + 8#64) (n := 1) (k := 39) (b' := a + 9#64) rfl (by bv_omega) (by decide),
      ← hbs39]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion a msg.epoch)
    (sepConj_mono (ProofLib.pointsTo8_entails_memRegion (a + 8#64) tag)
      (ProofLib.pointsToBytes_entails_memRegion (a + 9#64) bs39))

theorem memRegion_4416_join_statesFromPb_err (sp0 w1 w2 w3 : BitVec 64)
    (msg : Message spqrPolyApi) :
    memRegion (sp0 - 4512#64) 224 ∗
      memRegion (sp0 - 4288#64) 176 ∗
      messageAt spqrPolyApi (sp0 - 4112#64) msg ∗
      memRegion (sp0 - 4064#64) 1968 ∗
      ((sp0 - 2096#64) ↦₆₄ noneCap) ∗
      ((sp0 - 2088#64) ↦₆₄ w1) ∗
      ((sp0 - 2080#64) ↦₆₄ w2) ∗
      ((sp0 - 2072#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 2064#64) 896 ∗
      memRegion (sp0 - 1168#64) 8 ∗
      memRegion (sp0 - 1160#64) 928 ∗
      memRegion (sp0 - 232#64) 88 ∗
      ((sp0 - 144#64) ↦₆₄ w1) ∗
      ((sp0 - 136#64) ↦₆₄ w2) ∗
      ((sp0 - 128#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 120#64) 24 ⊢
    memRegion (sp0 - 4512#64) 4416 := by
  have hmsg := messageAt_entails_memRegion_48 (sp0 - 4112#64) msg
  have h32 := words4_to_memRegion_32 (sp0 - 2096#64) noneCap w1 w2 w3
  rw [bv_sub_add_lit sp0 2096 8, bv_sub_add_lit sp0 2096 16, bv_sub_add_lit sp0 2096 24] at h32
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h32
  have h24 := words3_to_memRegion_24 (sp0 - 144#64) w1 w2 w3
  rw [bv_sub_add_lit sp0 144 8, bv_sub_add_lit sp0 144 16] at h24
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h24
  rw [show (4416 : Nat) = 224 + (176 + (48 + (1968 + (32 + (896 + (8 + (928 + (88 + (24 + 24))))))))) by decide,
      memRegion_split (sp0 - 4512#64) 224 (176 + (48 + (1968 + (32 + (896 + (8 + (928 + (88 + (24 + 24))))))))) (by decide),
      show (sp0 - 4512#64) + 224#64 = sp0 - 4288#64 by bv_omega,
      memRegion_split (sp0 - 4288#64) 176 (48 + (1968 + (32 + (896 + (8 + (928 + (88 + (24 + 24)))))))) (by decide),
      show (sp0 - 4288#64) + 176#64 = sp0 - 4112#64 by bv_omega,
      memRegion_split (sp0 - 4112#64) 48 (1968 + (32 + (896 + (8 + (928 + (88 + (24 + 24))))))) (by decide),
      show (sp0 - 4112#64) + 48#64 = sp0 - 4064#64 by bv_omega,
      memRegion_split (sp0 - 4064#64) 1968 (32 + (896 + (8 + (928 + (88 + (24 + 24)))))) (by decide),
      show (sp0 - 4064#64) + 1968#64 = sp0 - 2096#64 by bv_omega,
      memRegion_split (sp0 - 2096#64) 32 (896 + (8 + (928 + (88 + (24 + 24))))) (by decide),
      show (sp0 - 2096#64) + 32#64 = sp0 - 2064#64 by bv_omega,
      memRegion_split (sp0 - 2064#64) 896 (8 + (928 + (88 + (24 + 24)))) (by decide),
      show (sp0 - 2064#64) + 896#64 = sp0 - 1168#64 by bv_omega,
      memRegion_split (sp0 - 1168#64) 8 (928 + (88 + (24 + 24))) (by decide),
      show (sp0 - 1168#64) + 8#64 = sp0 - 1160#64 by bv_omega,
      memRegion_split (sp0 - 1160#64) 928 (88 + (24 + 24)) (by decide),
      show (sp0 - 1160#64) + 928#64 = sp0 - 232#64 by bv_omega,
      memRegion_split (sp0 - 232#64) 88 (24 + 24) (by decide),
      show (sp0 - 232#64) + 88#64 = sp0 - 144#64 by bv_omega,
      memRegion_split (sp0 - 144#64) 24 24 (by decide),
      show (sp0 - 144#64) + 24#64 = sp0 - 120#64 by bv_omega]
  refine Entails.trans
    (Entails.of_eq (show
      memRegion (sp0 - 4512#64) 224 ∗
        memRegion (sp0 - 4288#64) 176 ∗
        messageAt spqrPolyApi (sp0 - 4112#64) msg ∗
        memRegion (sp0 - 4064#64) 1968 ∗
        ((sp0 - 2096#64) ↦₆₄ noneCap) ∗
        ((sp0 - 2088#64) ↦₆₄ w1) ∗
        ((sp0 - 2080#64) ↦₆₄ w2) ∗
        ((sp0 - 2072#64) ↦₆₄ w3) ∗
        memRegion (sp0 - 2064#64) 896 ∗
        memRegion (sp0 - 1168#64) 8 ∗
        memRegion (sp0 - 1160#64) 928 ∗
        memRegion (sp0 - 232#64) 88 ∗
        ((sp0 - 144#64) ↦₆₄ w1) ∗
        ((sp0 - 136#64) ↦₆₄ w2) ∗
        ((sp0 - 128#64) ↦₆₄ w3) ∗
        memRegion (sp0 - 120#64) 24 =
      memRegion (sp0 - 4512#64) 224 ∗
        memRegion (sp0 - 4288#64) 176 ∗
        messageAt spqrPolyApi (sp0 - 4112#64) msg ∗
        memRegion (sp0 - 4064#64) 1968 ∗
        (((sp0 - 2096#64) ↦₆₄ noneCap) ∗
          ((sp0 - 2088#64) ↦₆₄ w1) ∗
          ((sp0 - 2080#64) ↦₆₄ w2) ∗
          ((sp0 - 2072#64) ↦₆₄ w3)) ∗
        memRegion (sp0 - 2064#64) 896 ∗
        memRegion (sp0 - 1168#64) 8 ∗
        memRegion (sp0 - 1160#64) 928 ∗
        memRegion (sp0 - 232#64) 88 ∗
        (((sp0 - 144#64) ↦₆₄ w1) ∗
          ((sp0 - 136#64) ↦₆₄ w2) ∗
          ((sp0 - 128#64) ↦₆₄ w3)) ∗
        memRegion (sp0 - 120#64) 24 by ac_rfl)) ?_
  exact sepConj_mono_right
    (sepConj_mono_right
      (sepConj_mono hmsg
        (sepConj_mono_right
          (sepConj_mono h32
            (sepConj_mono_right
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono_right
                    (sepConj_mono_left h24)))))))))

theorem memRegion_4416_join_statesRecv_err (sp0 w1 w2 w3 : BitVec 64)
    (msg : Message spqrPolyApi) :
    memRegion (sp0 - 4512#64) 224 ∗
      memRegion (sp0 - 4288#64) 176 ∗
      messageAt spqrPolyApi (sp0 - 4112#64) msg ∗
      memRegion (sp0 - 4064#64) 32 ∗
      memRegion (sp0 - 4032#64) 16 ∗
      memRegion (sp0 - 4016#64) 928 ∗
      ((sp0 - 3088#64) ↦₆₄ w1) ∗
      ((sp0 - 3080#64) ↦₆₄ w2) ∗
      ((sp0 - 3072#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 3064#64) 8 ∗
      ((sp0 - 3056#64) ↦₆₄ noneCap) ∗
      ((sp0 - 3048#64) ↦₆₄ w1) ∗
      ((sp0 - 3040#64) ↦₆₄ w2) ∗
      ((sp0 - 3032#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 3024#64) 928 ∗
      memRegion (sp0 - 2096#64) 928 ∗
      memRegion (sp0 - 1168#64) 8 ∗
      memRegion (sp0 - 1160#64) 928 ∗
      memRegion (sp0 - 232#64) 136 ⊢
    memRegion (sp0 - 4512#64) 4416 := by
  have hmsg := messageAt_entails_memRegion_48 (sp0 - 4112#64) msg
  have h2896 := memRegion_2896_join_statesRecv_err sp0 w1 w2 w3
  rw [show (4416 : Nat) = 224 + (176 + (48 + (2896 + (8 + (928 + 136))))) by decide,
      memRegion_split (sp0 - 4512#64) 224 (176 + (48 + (2896 + (8 + (928 + 136))))) (by decide),
      show (sp0 - 4512#64) + 224#64 = sp0 - 4288#64 by bv_omega,
      memRegion_split (sp0 - 4288#64) 176 (48 + (2896 + (8 + (928 + 136)))) (by decide),
      show (sp0 - 4288#64) + 176#64 = sp0 - 4112#64 by bv_omega,
      memRegion_split (sp0 - 4112#64) 48 (2896 + (8 + (928 + 136))) (by decide),
      show (sp0 - 4112#64) + 48#64 = sp0 - 4064#64 by bv_omega,
      memRegion_split (sp0 - 4064#64) 2896 (8 + (928 + 136)) (by decide),
      show (sp0 - 4064#64) + 2896#64 = sp0 - 1168#64 by bv_omega,
      memRegion_split (sp0 - 1168#64) 8 (928 + 136) (by decide),
      show (sp0 - 1168#64) + 8#64 = sp0 - 1160#64 by bv_omega,
      memRegion_split (sp0 - 1160#64) 928 136 (by decide),
      show (sp0 - 1160#64) + 928#64 = sp0 - 232#64 by bv_omega]
  refine Entails.trans
    (Entails.of_eq (show
      memRegion (sp0 - 4512#64) 224 ∗
        memRegion (sp0 - 4288#64) 176 ∗
        messageAt spqrPolyApi (sp0 - 4112#64) msg ∗
        memRegion (sp0 - 4064#64) 32 ∗
        memRegion (sp0 - 4032#64) 16 ∗
        memRegion (sp0 - 4016#64) 928 ∗
        ((sp0 - 3088#64) ↦₆₄ w1) ∗
        ((sp0 - 3080#64) ↦₆₄ w2) ∗
        ((sp0 - 3072#64) ↦₆₄ w3) ∗
        memRegion (sp0 - 3064#64) 8 ∗
        ((sp0 - 3056#64) ↦₆₄ noneCap) ∗
        ((sp0 - 3048#64) ↦₆₄ w1) ∗
        ((sp0 - 3040#64) ↦₆₄ w2) ∗
        ((sp0 - 3032#64) ↦₆₄ w3) ∗
        memRegion (sp0 - 3024#64) 928 ∗
        memRegion (sp0 - 2096#64) 928 ∗
        memRegion (sp0 - 1168#64) 8 ∗
        memRegion (sp0 - 1160#64) 928 ∗
        memRegion (sp0 - 232#64) 136 =
      memRegion (sp0 - 4512#64) 224 ∗
        memRegion (sp0 - 4288#64) 176 ∗
        messageAt spqrPolyApi (sp0 - 4112#64) msg ∗
        (memRegion (sp0 - 4064#64) 32 ∗
          memRegion (sp0 - 4032#64) 16 ∗
          memRegion (sp0 - 4016#64) 928 ∗
          ((sp0 - 3088#64) ↦₆₄ w1) ∗
          ((sp0 - 3080#64) ↦₆₄ w2) ∗
          ((sp0 - 3072#64) ↦₆₄ w3) ∗
          memRegion (sp0 - 3064#64) 8 ∗
          ((sp0 - 3056#64) ↦₆₄ noneCap) ∗
          ((sp0 - 3048#64) ↦₆₄ w1) ∗
          ((sp0 - 3040#64) ↦₆₄ w2) ∗
          ((sp0 - 3032#64) ↦₆₄ w3) ∗
          memRegion (sp0 - 3024#64) 928 ∗
          memRegion (sp0 - 2096#64) 928) ∗
        memRegion (sp0 - 1168#64) 8 ∗
        memRegion (sp0 - 1160#64) 928 ∗
        memRegion (sp0 - 232#64) 136 by ac_rfl)) ?_
  exact sepConj_mono_right
    (sepConj_mono_right
      (sepConj_mono hmsg
        (sepConj_mono_left h2896)))

theorem st_expose_len_bound (A : RustAlloc) (st : VecArg) :
    st.at A ⊢ ⌜st.bytes.length < 2 ^ 63⌝ ∗ st.at A := by
  refine Entails.trans (InImage.SpqrRecvEmpty.msg_expose_hdr A st) ?_
  apply Entails.pure_left; intro hlt
  exact Entails.pure_right hlt (InImage.SpqrRecvEmpty.msg_unexpose_hdr A st)

theorem memRegion_136_split_fp_spill (sp0 : BitVec 64) :
    memRegion (sp0 - 232#64) 136 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        memRegion (sp0 - 232#64) 88 ∗
        ((sp0 - 144#64) ↦₆₄ w0) ∗
        ((sp0 - 136#64) ↦₆₄ w1) ∗
        ((sp0 - 128#64) ↦₆₄ w2) ∗
        memRegion (sp0 - 120#64) 24 := by
  rw [show (136 : Nat) = 88 + (24 + 24) by decide,
      memRegion_split (sp0 - 232#64) 88 (24 + 24) (by decide),
      show (sp0 - 232#64) + 88#64 = sp0 - 144#64 by bv_omega,
      memRegion_split (sp0 - 144#64) 24 24 (by decide),
      show (sp0 - 144#64) + 24#64 = sp0 - 120#64 by bv_omega,
      memRegion_24_words3 (sp0 - 144#64),
      show (sp0 - 144#64) + 8#64 = sp0 - 136#64 by bv_omega,
      show (sp0 - 144#64) + 16#64 = sp0 - 128#64 by bv_omega]
  simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2 ?_))
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_136_join_fp_spill (sp0 w0 w1 w2 : BitVec 64) :
    memRegion (sp0 - 232#64) 88 ∗
      ((sp0 - 144#64) ↦₆₄ w0) ∗
      ((sp0 - 136#64) ↦₆₄ w1) ∗
      ((sp0 - 128#64) ↦₆₄ w2) ∗
      memRegion (sp0 - 120#64) 24 ⊢
    memRegion (sp0 - 232#64) 136 := by
  have h24 := words3_to_memRegion_24 (sp0 - 144#64) w0 w1 w2
  rw [show (sp0 - 144#64) + 8#64 = sp0 - 136#64 by bv_omega,
      show (sp0 - 144#64) + 16#64 = sp0 - 128#64 by bv_omega] at h24
  rw [show (136 : Nat) = 88 + (24 + 24) by decide,
      memRegion_split (sp0 - 232#64) 88 (24 + 24) (by decide),
      show (sp0 - 232#64) + 88#64 = sp0 - 144#64 by bv_omega,
      memRegion_split (sp0 - 144#64) 24 24 (by decide),
      show (sp0 - 144#64) + 24#64 = sp0 - 120#64 by bv_omega]
  refine Entails.trans
    (Entails.of_eq (show
      memRegion (sp0 - 232#64) 88 ∗
        ((sp0 - 144#64) ↦₆₄ w0) ∗
        ((sp0 - 136#64) ↦₆₄ w1) ∗
        ((sp0 - 128#64) ↦₆₄ w2) ∗
        memRegion (sp0 - 120#64) 24 =
      memRegion (sp0 - 232#64) 88 ∗
        (((sp0 - 144#64) ↦₆₄ w0) ∗
         ((sp0 - 136#64) ↦₆₄ w1) ∗
         ((sp0 - 128#64) ↦₆₄ w2)) ∗
        memRegion (sp0 - 120#64) 24 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_left h24)

end CryptoVerification.SpqrV1.Top.Recv

