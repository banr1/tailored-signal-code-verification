/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegUntrusted
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1DropSS3A
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP1
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Stage P1 Untrusted-Identity Exit Segments

Bitvector, ADRP, and memory-packing lemmas together with `SepWP` segment theorems (`+0x06e4 →
<String as Clone>::clone → +0x3588 → +0x359c → retAddr`) for the `is_trusted_identity ==
Ok(false)` exit path.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_dealloc")

/-! ## 1. Bitvector, ADRP, and Memory Packing Lemmas -/

/-- Evaluates reduced `bfi x23, x8, #8, #56` mask expression. -/
@[local simp, local wp_norm, local arm64_norm]
theorem bfi_mask_lsr8_id (cap : BitVec 64) :
    (cap &&& 255#64 ||| (cap >>> 8 &&& 72057594037927935#64) <<< 8) = cap := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
theorem evalBitfield_bfi_lsr8 (cap : BitVec 64) :
    evalBitfield .W64 .BFM cap (cap >>> 8) 56 55 = cap := by
  change (if (BitfieldOp.BFM == BitfieldOp.UBFM) = true then cap >>> 8 <<< 8
      else cap &&& 255#64 ||| (cap >>> 8 &&& 72057594037927935#64) <<< 8) = cap
  have h : (BitfieldOp.BFM == BitfieldOp.UBFM) = false := rfl
  simp [h, bfi_mask_lsr8_id]

@[local simp]
theorem extractLsb_hi_lo_append (w : BitVec 64) :
    w.extractLsb' 32 32 ++ w.extractLsb' 0 32 = w := by
  bv_bits

theorem adrp_logLevel_0x17bc_std3 {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (he : entry = b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) :
    (((entry + 0x17bc#64) &&& 0xfffffffffffff000#64) +
        bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 6076) -
          (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 6076))) =
      b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 6076))) ∧
    ((((bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) + (b + 0x17bc#64)) &&&
        0xfffffffffffff000#64) +
        bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 6076) -
          (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 6076))) =
      b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 6076))) := by
  subst he
  constructor
  · rw [BitVec.add_assoc, ProofLib.ObjectLoad.adrp_page_of_aligned hb,
      show (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") + 0x17bc#64 : BitVec 64) &&&
        0xfffffffffffff000#64 =
        bv% (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 6076)) by decide]
    bv_omega
  · rw [show bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") + (b + 0x17bc#64) =
        b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") + 0x17bc#64) by bv_omega,
      ProofLib.ObjectLoad.adrp_page_of_aligned hb,
      show (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") + 0x17bc#64 : BitVec 64) &&&
        0xfffffffffffff000#64 =
        bv% (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 6076)) by decide]
    bv_omega

/-- 40-byte word realignment at any base address `a` (`s.sp + 0xa98#64` or `outPtr + 8#64`). -/
theorem realign_40 (a w0 w1 w2 w3 w4 : BitVec 64) :
    ((a ↦₆₄ w0) ∗
     ((a + 8#64) ↦₆₄ w1) ∗
     ((a + 16#64) ↦₆₄ w2) ∗
     ((a + 24#64) ↦₆₄ w3) ∗
     ((a + 32#64) ↦₆₄ w4)) =
    ((a ↦₃₂ w0.extractLsb' 0 32) ∗
     ((a + 4#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
     ((a + 12#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
     ((a + 20#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
     ((a + 28#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
     ((a + 36#64) ↦₃₂ w4.extractLsb' 32 32)) := by
  simp only [pointsTo64_append32]
  rw [pointsTo64_split32 a w0, pointsTo64_split32 (a + 8#64) w1,
      pointsTo64_split32 (a + 16#64) w2, pointsTo64_split32 (a + 24#64) w3,
      pointsTo64_split32 (a + 32#64) w4]
  sep_norm

/-- Unpack `vecU8 A (sp + 0x3e0#64) bs` for `+0x07e8..+0x0804` (`cap` and `ptr` read as 64-bit words,
`len` read as two 32-bit halves). -/
theorem vecU8_unpack_3e0 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (sp + 0x3e0#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((sp + 0x3e0#64) ↦₆₄ cap) ∗
        ((sp + 0x3e8#64) ↦₆₄ ptr) ∗
        ((sp + 0x3f0#64) ↦₃₂ (BitVec.ofNat 64 bs.length).extractLsb' 0 32) ∗
        ((sp + 0x3f4#64) ↦₃₂ (BitVec.ofNat 64 bs.length).extractLsb' 32 32) ∗
        SegUntrusted.vecU8Buf A cap ptr bs := by
  unfold vecU8 vecU8At vecHeader SegUntrusted.vecU8Buf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  sep_norm
  rw [pointsTo64_split32 (sp + 0x3f0#64) (BitVec.ofNat 64 bs.length)]
  sep_norm
  exact Entails.refl _

/-- Split `memRegion (sp + 0x3e0#64) 368` into `memRegion (sp + 0x3e0#64) 24`,
`(sp + 0x3f8#64) ↦₈ d0 ∗ (sp + 0x3f9#64) ↦ₛ pad` (`pad.length = 7`), and
`memRegion (sp + 0x400#64) 336`. -/
theorem memRegion_368_untrusted_entails (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 368 ⊢
      ∃∗ d0 : BitVec 8, ∃∗ pad : List (BitVec 8),
        ⌜pad.length = 7⌝ ∗
        memRegion (sp + 0x3e0#64) 24 ∗
        ((sp + 0x3f8#64) ↦₈ d0) ∗
        ((sp + 0x3f9#64) ↦ₛ pad) ∗
        memRegion (sp + 0x400#64) 336 := by
  rw [memRegion_split (sp + 0x3e0#64) 48 320 (by decide)]
  refine Entails.trans (sepConj_mono_left (SegUntrusted.memRegion_48_untrusted_entails (sp + 0x3e0#64))) ?_
  sep_norm
  apply Entails.sepExists_elim; intro d0
  apply Entails.sepExists_elim; intro pad
  refine Entails.sepExists_right d0 (Entails.sepExists_right pad ?_)
  rw [memRegion_split (sp + 0x400#64) 16 320 (by decide)]
  sep_norm
  exact Entails.refl _

/-- Reassemble `memRegion (sp + 0x3e0#64) 368` after `p1_untrusted_post_clone_wp`. -/
theorem cells_3e0_entails_memRegion_368 (sp cap ptr len devWord : BitVec 64) :
    (((sp + 0x3e0#64) ↦₆₄ cap) ∗
     ((sp + 0x3e8#64) ↦₆₄ ptr) ∗
     ((sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
     ((sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32) ∗
     ((sp + 0x3f8#64) ↦₆₄ devWord) ∗
     memRegion (sp + 0x400#64) 336) ⊢
      memRegion (sp + 0x3e0#64) 368 := by
  have hlen :
      (((sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
       ((sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32)) =
      ((sp + 0x3f0#64) ↦₆₄ len) := by
    have h4 : sp + 0x3f4#64 = (sp + 0x3f0#64) + 4#64 := by bv_omega
    rw [h4, pointsTo32_pair, extractLsb_hi_lo_append]
  rw [memRegion_split (sp + 0x3e0#64) 8 360 (by decide),
      memRegion_split (sp + 0x3e0#64 + 8#64) 8 352 (by decide),
      memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64) 8 344 (by decide),
      memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 8#64) 8 336 (by decide)]
  sep_norm
  have hgrp :
      (((sp + 0x3e0#64) ↦₆₄ cap) ∗
       ((sp + 0x3e8#64) ↦₆₄ ptr) ∗
       ((sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
       ((sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32) ∗
       ((sp + 0x3f8#64) ↦₆₄ devWord) ∗
       memRegion (sp + 0x400#64) 336) =
      (((sp + 0x3e0#64) ↦₆₄ cap) ∗
       ((sp + 0x3e8#64) ↦₆₄ ptr) ∗
       (((sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
        ((sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32)) ∗
       ((sp + 0x3f8#64) ↦₆₄ devWord) ∗
       memRegion (sp + 0x400#64) 336) := by ac_rfl
  rw [hgrp, hlen]
  exact sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3e0#64) cap)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3e8#64) ptr)
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3f0#64) len)
        (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3f8#64) devWord)
          (Entails.refl _))))

/-- Unpack `memRegion a 48` into the shape read/written at `outPtr + 0..0x30` by `p3_err_tail_b_wp`. -/
theorem memRegion_48_out_entails (outPtr : BitVec 64) :
    memRegion outPtr 48 ⊢
      ∃∗ u0 : BitVec 64, ∃∗ u08 : BitVec 32, ∃∗ u0c : BitVec 64,
      ∃∗ u14 : BitVec 64, ∃∗ u1c : BitVec 64, ∃∗ u24 : BitVec 64, ∃∗ u2c : BitVec 32,
        ((outPtr + 0x0#64) ↦₆₄ u0) ∗
        ((outPtr + 0x8#64) ↦₃₂ u08) ∗
        ((outPtr + 0xc#64) ↦₆₄ u0c) ∗
        ((outPtr + 0x14#64) ↦₆₄ u14) ∗
        ((outPtr + 0x1c#64) ↦₆₄ u1c) ∗
        ((outPtr + 0x24#64) ↦₆₄ u24) ∗
        ((outPtr + 0x2c#64) ↦₃₂ u2c) := by
  rw [memRegion_split outPtr 8 40 (by decide),
      memRegion_split (outPtr + 8#64) 8 32 (by decide),
      memRegion_split (outPtr + 8#64 + 8#64) 8 24 (by decide),
      memRegion_split (outPtr + 8#64 + 8#64 + 8#64) 8 16 (by decide),
      memRegion_split (outPtr + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  repeat rw [ProofLib.memRegion_eight]
  sep_norm
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w5
  have h40 := realign_40 (outPtr + 8#64) w1 w2 w3 w4 w5
  try simp only [BitVec.add_assoc] at h40; try simp only [BitVec.reduceAdd] at h40
  refine Entails.sepExists_right w0
    (Entails.sepExists_right (w1.extractLsb' 0 32)
      (Entails.sepExists_right (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (Entails.sepExists_right (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
          (Entails.sepExists_right (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
            (Entails.sepExists_right (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
              (Entails.sepExists_right (w5.extractLsb' 32 32) ?_))))))
  simp only [BitVec.add_zero]
  rw [h40]
  exact Entails.refl _

/-- Reassemble `apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val))` from the 7 atoms
written at `outPtr + 0..0x30` plus `SegUntrusted.vecU8Buf A cap ptr peer.name.bytes`. -/
theorem untrusted_out_entails (A : RustAlloc) (outPtr cap ptr devWord e4 : BitVec 64)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : peer.device :: pad = unpack64 devWord) :
    (((outPtr + 0x0#64) ↦₆₄ 0x800000000000000c#64) ∗
     ((outPtr + 0x8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
     ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
     ((outPtr + 0x14#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
     ((outPtr + 0x1c#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
     ((outPtr + 0x24#64) ↦₆₄ (e4.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
     ((outPtr + 0x2c#64) ↦₃₂ e4.extractLsb' 32 32) ∗
     SegUntrusted.vecU8Buf A cap ptr peer.name.bytes) ⊢
      apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) := by
  have h40 := (realign_40 (outPtr + 8#64) cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord e4).symm
  try simp only [BitVec.add_assoc] at h40; try simp only [BitVec.reduceAdd] at h40
  have hgrp :
      (((outPtr + 0x0#64) ↦₆₄ 0x800000000000000c#64) ∗
       ((outPtr + 0x8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
       ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((outPtr + 0x14#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((outPtr + 0x1c#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
       ((outPtr + 0x24#64) ↦₆₄ (e4.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
       ((outPtr + 0x2c#64) ↦₃₂ e4.extractLsb' 32 32) ∗
       SegUntrusted.vecU8Buf A cap ptr peer.name.bytes) =
      (((outPtr + 0x0#64) ↦₆₄ 0x800000000000000c#64) ∗
       (((outPtr + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
        ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
        ((outPtr + 0x14#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
        ((outPtr + 0x1c#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
        ((outPtr + 0x24#64) ↦₆₄ (e4.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
        ((outPtr + 0x2c#64) ↦₃₂ e4.extractLsb' 32 32)) ∗
       SegUntrusted.vecU8Buf A cap ptr peer.name.bytes) := by
    sep_norm
  rw [hgrp, h40]
  have hgrp2 :
      (((outPtr + 0x0#64) ↦₆₄ 0x800000000000000c#64) ∗
       (((outPtr + 8#64) ↦₆₄ cap) ∗
        ((outPtr + 16#64) ↦₆₄ ptr) ∗
        ((outPtr + 24#64) ↦₆₄ BitVec.ofNat 64 peer.name.bytes.length) ∗
        ((outPtr + 32#64) ↦₆₄ devWord) ∗
        ((outPtr + 40#64) ↦₆₄ e4)) ∗
       SegUntrusted.vecU8Buf A cap ptr peer.name.bytes) =
      ((outPtr ↦₆₄ speWord speUntrustedIdentity) ∗
       (((outPtr + 8#64) ↦₆₄ cap) ∗
        ((outPtr + 16#64) ↦₆₄ ptr) ∗
        ((outPtr + 24#64) ↦₆₄ BitVec.ofNat 64 peer.name.bytes.length) ∗
        SegUntrusted.vecU8Buf A cap ptr peer.name.bytes) ∗
       ((outPtr + 32#64) ↦₆₄ devWord) ∗
       ((outPtr + 40#64) ↦₆₄ e4)) := by
    have h0 : outPtr + 0x0#64 = outPtr := by bv_lin
    have htag : (0x800000000000000c#64 : BitVec 64) = speWord speUntrustedIdentity := rfl
    rw [h0, htag]
    ac_rfl
  rw [hgrp2]
  unfold apiDecResultAt apiErrAt addrCloneAt AddrGhost.val
  have hvec := SegUntrusted.vecU8_intro A (outPtr + 8#64) cap ptr peer.name.bytes
  have hdev := SegUntrusted.pointsTo64_entails_byte_memRegion7 (outPtr + 32#64) peer.device pad devWord hpad hw4
  have he4 := pointsTo64_entails_memRegion (outPtr + 40#64) e4
  try simp only [BitVec.add_assoc] at hvec hdev ⊢; try simp only [BitVec.reduceAdd] at hvec hdev ⊢
  rw [sepConj_assoc (vecU8 A (outPtr + 8#64) _)]
  exact sepConj_mono_right (sepConj_mono hvec (sepConj_mono hdev he4))

/-- Unpack `decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0` into `sp + 0xc70..0xcc8`. -/
theorem savedRegsAt_eq_sp_c70 (sp : BitVec 64) (s0 : State) :
    decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 =
      (((sp + 0xc70#64) ↦₆₄ s0.readReg64 .x29) ∗
       ((sp + 0xc78#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((sp + 0xc80#64) ↦₆₄ s0.readReg64 .x28) ∗
       ((sp + 0xc88#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((sp + 0xc90#64) ↦₆₄ s0.readReg64 .x26) ∗
       ((sp + 0xc98#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((sp + 0xca0#64) ↦₆₄ s0.readReg64 .x24) ∗
       ((sp + 0xca8#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((sp + 0xcb0#64) ↦₆₄ s0.readReg64 .x22) ∗
       ((sp + 0xcb8#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((sp + 0xcc0#64) ↦₆₄ s0.readReg64 .x20) ∗
       ((sp + 0xcc8#64) ↦₆₄ s0.readReg64 .x19)) := by
  unfold decryptPrekeySavedRegsAt
  have h0 : (sp + 0xcd0#64) - 0x60#64 = sp + 0xc70#64 := by bv_lin
  have h1 : 8#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xc78#64 := by bv_lin
  have h2 : 16#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xc80#64 := by bv_lin
  have h3 : 24#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xc88#64 := by bv_lin
  have h4 : 32#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xc90#64 := by bv_lin
  have h5 : 40#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xc98#64 := by bv_lin
  have h6 : 48#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xca0#64 := by bv_lin
  have h7 : 56#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xca8#64 := by bv_lin
  have h8 : 64#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xcb0#64 := by bv_lin
  have h9 : 72#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xcb8#64 := by bv_lin
  have h10 : 80#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xcc0#64 := by bv_lin
  have h11 : 88#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xcc8#64 := by bv_lin
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h0]

theorem coro_268_split32 (coroPtr w : BitVec 64) :
    ((coroPtr + 0x268#64) ↦₆₄ w) =
      ((coroPtr + 0x268#64) ↦₃₂ w.extractLsb' 0 32) ∗
      ((coroPtr + 0x26c#64) ↦₃₂ w.extractLsb' 32 32) := by
  rw [pointsTo64_split32 (coroPtr + 0x268#64) w]
  sep_norm

theorem vecGhostAt_eq_cap_sep (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.cap) ∗
      (((a + 8#64) ↦₆₄ g.ptr) ∗
       ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
       (if g.cap = 0 then emp
        else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
          memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))) := by
  unfold vecGhostAt vecU8At vecHeader
  ac_rfl

theorem stringClone_ok_cli {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr stringCloneHookName) (stringCloneSpec A) := by
  have h := SegUntrusted.stringClone_ok_at_dec (b := b) (C := C) (ctl := ctl)
    (name := stringCloneHookName) (k := 0) hA (Nat.add_zero _)
  try simp only [BitVec.ofNat_eq_ofNat] at h
  try simp only [BitVec.add_zero] at h
  exact h

/-! ## 2. Segment 1: `+0x06e4 -> <String as Clone>::clone` -/

set_option maxHeartbeats 800000 in
/-- Segment P1.Untrusted-ToClone (`+0x06e4 -> stringClone`) over `tripleRatchetProgAtExt`:
Checks `x20 == -2` and `tbz w23, #0` (`x23 = 0#64`), branches to `+0x07d8`, loads
`x21 = [coroPtr + 0x330] = remoteAddrPtr`, sets `x8 = s.sp + 0x3e0#64`, `x0 = remoteAddrPtr`,
`x30 = entry + 0x7e8#64`, and calls `<alloc::string::String as core::clone::Clone>::clone`,
preserving `calleeSavedVRegs`. -/
theorem p1_untrusted_to_clone_vregs_wp_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (s : State) (coroPtr remoteAddrPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx23 : s.readReg64 .x23 = 0#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr stringCloneHookName)
      s
      (((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = remoteAddrPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = remoteAddrPtr ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x7e8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x6e4 0x6f0
  closure_fetches_range_cli b (Rust.withPanics ext) 0x7d8 0x7e4
  dsimp only [tripleRatchetProgAtExt, stringCloneHookName] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x7e4#64 +
      bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" -
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2020)) % 2^64) =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<alloc::string::String as core::clone::Clone>::clone" := by
    have hfn_clone :
        libsignalSessionCode.fnOff "<alloc::string::String as core::clone::Clone>::clone" =
          ls_off% "<alloc::string::String as core::clone::Clone>::clone" := by
      simp only [arm64_norm]
    rw [hentry, Program.fnAddr_rebase, hfn_clone]
    sep_norm
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0xfffffffffffffffe#64 := hx20
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 0#64 := hx23
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p1_untrusted_to_clone_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr remoteAddrPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx23 : s.readReg64 .x23 = 0#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr stringCloneHookName)
      s
      (((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = remoteAddrPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = remoteAddrPtr ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x7e8#64) :=
  SepWP.mono
    (p1_untrusted_to_clone_vregs_wp_ext b (tripleRatchetExterns C ctl abs) s coroPtr remoteAddrPtr
      hpc hrun hsp_align hx19 hx20 hx23)
    (fun _ _ _ _ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩)

/-! ## 3. Segment 2: `+0x07e8 -> +0x3588` (Post-Clone Error Funnel + Payload Stager) -/

set_option maxHeartbeats 1600000 in
/-- Segment P1.Untrusted-PostClone (`+0x07e8 -> +0x3588`):
Constructs `SignalProtocolError::UntrustedIdentityException(peer)` from the cloned `String` at
`s.sp + 0x3e0..0x3f8` and `peer.device = [remoteAddrPtr + 0x18]`, steps through `+0x16c8..+0x16f4`,
`+0x17b8..+0x17d8` (`[logOff] = 0#64`), and `+0x1898..+0x18b4`, staging the 36-byte payload at
`s.sp + 0x370..0x394` with `w22 = cap.extractLsb' 0 32`, `x26 = outPtr`, `x28 = 0x800000000000000c#64`,
and arriving at `entry + 0x3588#64`. -/
theorem p1_untrusted_post_clone_vregs_wp_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (s : State) (coroPtr remoteAddrPtr outPtr cap ptr len devWord
    u_250 u_258 u_260 u_268 u_270 u_278
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8
    u_370 u_378 u_380 u_388 : BitVec 64)
    (u_390 : BitVec 32)
    (d0 b_390 : BitVec 8)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hb : b &&& 0xfff#64 = 0#64)
    (hw4 : peer.device :: pad = unpack64 devWord)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x7e8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = remoteAddrPtr)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64) s
      (((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
       ((s.sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
       ((s.sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32) ∗
       ((s.sp + 0x3f8#64) ↦₈ d0) ∗
       ((s.sp + 0x3f9#64) ↦ₛ pad) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗
       ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗
       ((coroPtr + 0x268#64) ↦₆₄ u_268) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗
       ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₆₄ u_a98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ u_aa0) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ u_aa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ u_ab0) ∗
       ((s.sp + 0xab8#64) ↦₆₄ u_ab8) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ u_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ u_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ u_390))
      (fun s1 P_f =>
        (P_f ⊢
          ((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
          ((s.sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ devWord) ∗
          ((coroPtr + 0x250#64) ↦₆₄ 0x800000000000000c#64) ∗
          ((coroPtr + 0x258#64) ↦₆₄ cap) ∗
          ((coroPtr + 0x260#64) ↦₆₄ ptr) ∗
          ((coroPtr + 0x268#64) ↦₆₄ len) ∗
          ((coroPtr + 0x270#64) ↦₆₄ devWord) ∗
          ((coroPtr + 0x278#64) ↦₆₄ s.readReg64 .x27) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((s.sp + 0xa90#64) ↦₆₄ 0x800000000000000c#64) ∗
          ((s.sp + 0xa98#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((s.sp + 0xa9c#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
          ((s.sp + 0xaa4#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
          ((s.sp + 0xaac#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
          ((s.sp + 0xab4#64) ↦₆₄ ((s.readReg64 .x27).extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
          ((s.sp + 0xabc#64) ↦₃₂ (s.readReg64 .x27).extractLsb' 32 32) ∗
          ((s.sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
          ((s.sp + 0x378#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
          ((s.sp + 0x380#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
          ((s.sp + 0x388#64) ↦₆₄ ((s.readReg64 .x27).extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
          ((s.sp + 0x390#64) ↦₃₂ (s.readReg64 .x27).extractLsb' 32 32)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x28 = 0x800000000000000c#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdev_pack := SegUntrusted.pointsTo64_of_cons_unpack64 (s.sp + 0x3f8#64) peer.device pad devWord hw4
  try simp only [BitVec.add_assoc] at hdev_pack; try simp only [BitVec.reduceAdd] at hdev_pack
  have hrealign_a98 := realign_40 (s.sp + 0xa98#64) cap ptr len devWord (s.readReg64 .x27)
  try simp only [BitVec.add_assoc] at hrealign_a98; try simp only [BitVec.reduceAdd] at hrealign_a98
  closure_fetches_range_cli b (Rust.withPanics ext) 0x7e8 0x818
  closure_fetches_range_cli b (Rust.withPanics ext) 0x16c8 0x16f4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x17b8 0x17d8
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1898 0x18b4
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (adrp_logLevel_0x17bc_std3 hb hentry).1
  have hadrp := (adrp_logLevel_0x17bc_std3 hb hentry).2
  have h5b810 :
      (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) +
        bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
    bv_arith
  have hcond_err : ConditionHolds CondCode.NE (addsPState64 0x800000000000000c#64 2#64) = true :=
    cond_ne_adds64_of_ne_neg2_std3 (by decide)
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = remoteAddrPtr := hx21
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  apply SepWP.fold (Entails.of_eq (coro_268_split32 coroPtr u_268)) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq hdev_pack) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq (coro_268_split32 coroPtr len).symm) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq hrealign_a98) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem p1_untrusted_post_clone_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr remoteAddrPtr outPtr cap ptr len devWord
    u_250 u_258 u_260 u_268 u_270 u_278
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8
    u_370 u_378 u_380 u_388 : BitVec 64)
    (u_390 : BitVec 32)
    (d0 b_390 : BitVec 8)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hb : b &&& 0xfff#64 = 0#64)
    (hw4 : peer.device :: pad = unpack64 devWord)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x7e8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = remoteAddrPtr)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64) s
      (((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗ ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
       ((s.sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗ ((s.sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32) ∗
       ((s.sp + 0x3f8#64) ↦₈ d0) ∗ ((s.sp + 0x3f9#64) ↦ₛ pad) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗ ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗ ((coroPtr + 0x268#64) ↦₆₄ u_268) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗ ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗ ((s.sp + 0xa98#64) ↦₆₄ u_a98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ u_aa0) ∗ ((s.sp + 0xaa8#64) ↦₆₄ u_aa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ u_ab0) ∗ ((s.sp + 0xab8#64) ↦₆₄ u_ab8) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗ ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ u_380) ∗ ((s.sp + 0x388#64) ↦₆₄ u_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ u_390))
      (fun s1 P_f =>
        (P_f ⊢
          ((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗ ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗ ((s.sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ devWord) ∗
          ((coroPtr + 0x250#64) ↦₆₄ 0x800000000000000c#64) ∗ ((coroPtr + 0x258#64) ↦₆₄ cap) ∗
          ((coroPtr + 0x260#64) ↦₆₄ ptr) ∗ ((coroPtr + 0x268#64) ↦₆₄ len) ∗
          ((coroPtr + 0x270#64) ↦₆₄ devWord) ∗ ((coroPtr + 0x278#64) ↦₆₄ s.readReg64 .x27) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((s.sp + 0xa90#64) ↦₆₄ 0x800000000000000c#64) ∗
          ((s.sp + 0xa98#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((s.sp + 0xa9c#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
          ((s.sp + 0xaa4#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
          ((s.sp + 0xaac#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
          ((s.sp + 0xab4#64) ↦₆₄ ((s.readReg64 .x27).extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
          ((s.sp + 0xabc#64) ↦₃₂ (s.readReg64 .x27).extractLsb' 32 32) ∗
          ((s.sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
          ((s.sp + 0x378#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
          ((s.sp + 0x380#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
          ((s.sp + 0x388#64) ↦₆₄ ((s.readReg64 .x27).extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
          ((s.sp + 0x390#64) ↦₃₂ (s.readReg64 .x27).extractLsb' 32 32)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧ s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x28 = 0x800000000000000c#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29) :=
  SepWP.mono
    (p1_untrusted_post_clone_vregs_wp_ext b (tripleRatchetExterns C ctl abs) s
      coroPtr remoteAddrPtr outPtr cap ptr len devWord
      u_250 u_258 u_260 u_268 u_270 u_278
      u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8
      u_370 u_378 u_380 u_388 u_390 d0 b_390 peer pad
      hb hw4 hpc hrun hsp_align hx19 hx21 hx25)
    (fun _ _ _ _ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)

/-! ## 4. Segment 3: `+0x3588 -> +0x359c` (`current_session` Teardown) -/

/-- Segment P1.ErrDropNone (`+0x3588 -> +0x359c` when `coroPtr + 0xf8 = -1`) over `ext`. -/
theorem p1_err_drop_none_vregs_wp_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64) s
      (((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x3588 0x3594
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem p1_err_drop_none_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64) s
      (((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29) :=
  SepWP.mono (p1_err_drop_none_vregs_wp_ext b (tripleRatchetExterns C ctl abs) s coroPtr
    hpc hrun hsp_align hx19)
    (fun _ _ _ _ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)

/-- Segment P1.ErrDropSome (`+0x3588 -> dropSessionStructure3` when `ssCap ≠ -1`) over `ext`. -/
theorem p1_err_drop_ss_to_call_vregs_wp_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (s : State) (coroPtr ssCap : BitVec 64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr DropSS3.dropSessionStructure3Name) s
      (((coroPtr + 0xf8#64) ↦₆₄ ssCap))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ ssCap)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1_std3 hcap_ne
  closure_fetches_range_cli b (Rust.withPanics ext) 0x3588 0x3598
  dsimp only [tripleRatchetProgAtExt, DropSS3.dropSessionStructure3Name] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x3598#64 +
      bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" -
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 13720)) % 2^64) =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" := by
    rw [hentry, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
    sep_norm
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p1_err_drop_ss_to_call_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (s : State) (coroPtr ssCap : BitVec 64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr DropSS3.dropSessionStructure3Name) s
      (((coroPtr + 0xf8#64) ↦₆₄ ssCap))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ ssCap)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64) :=
  SepWP.mono (p1_err_drop_ss_to_call_vregs_wp_ext b (tripleRatchetExterns C ctl abs) s
    coroPtr ssCap hcap_ne hpc hrun hsp_align hx19)
    (fun _ _ _ _ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩)

/-! ## 5. Segment 4: `+0x359c -> retAddr` (`previous_sessions` Teardown & Epilogue) -/

set_option maxHeartbeats 800000 in
theorem p3_err_tail_b_vregs_wp_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr errTag prevStatesPtr
    w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64)
    (hrun : s.status = .Running) (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (tripleRatchetProgAtExt b ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x359c 0x35a0
  closure_fetches_range_cli b (Rust.withPanics ext) 0x35d0 0x35d4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x35ec 0x362c
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by simp only [BitVec.add_zero]),
    by simp_all [arm64_norm], rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
theorem p1_err_tail_prev_dealloc_core_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      (rustDeallocSpec A))
    (s : State) (coroPtr outPtr errTag prevCap prevPtr
    w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap_nz : prevCap ≠ 0#64) (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (tripleRatchetProgAtExt b ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
       memRegion prevPtr (prevCap.toNat * 24) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_nz
  have hmul1 : 24#64 * prevCap = BitVec.ofNat 64 (prevCap.toNat * 24) := by bv_omega
  have hmul2 : prevCap * 24#64 = BitVec.ofNat 64 (prevCap.toNat * 24) := by bv_omega
  closure_fetches_range_cli b (Rust.withPanics ext) 0x359c 0x35a0
  closure_fetches_range_cli b (Rust.withPanics ext) 0x35d0 0x362c
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  wp_steps
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by simp only [BitVec.add_zero]; ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem p1_err_tail_prev_dealloc_vregs_wp_ext {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocHooks A ext)
    (s : State) (coroPtr outPtr errTag prevCap prevPtr
    w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap_nz : prevCap ≠ 0#64) (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (tripleRatchetProgAtExt b ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
       memRegion prevPtr (prevCap.toNat * 24) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p1_err_tail_prev_dealloc_core_wp b ext
    (dealloc_ok_at_ext b A ext hA
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
      (num% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))
      (by
        unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName deallocName
        fnoff_eq))
    s coroPtr outPtr errTag prevCap prevPtr
    w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr
    w_22 w_390 u_ret08 u_ret2c b_2c0
    hcap_nz hcap_lt hpc hrun hsp_align hx19 hx22 hx25 hx26 hx28

theorem p1_err_tail_prev_dealloc_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs)
    (s : State) (coroPtr outPtr errTag prevCap prevPtr
    w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap_nz : prevCap ≠ 0#64) (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (tripleRatchetProgAt b C ctl abs) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
       memRegion prevPtr (prevCap.toNat * 24) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr) :=
  SepWP.mono
    (p1_err_tail_prev_dealloc_core_wp b (tripleRatchetExterns C ctl abs)
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok
        (b := b) (C := C) (ctl := ctl) (abs := abs) hA)
      s coroPtr outPtr errTag prevCap prevPtr
      w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
      savedX25 savedX26 savedX27 savedX28 savedX29 retAddr
      w_22 w_390 u_ret08 u_ret2c b_2c0
      hcap_nz hcap_lt hpc hrun hsp_align hx19 hx22 hx25 hx26 hx28)
    (fun _ _ _ _ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, _⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
