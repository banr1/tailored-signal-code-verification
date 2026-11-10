/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S2Sym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Handshake `DecryptPq` Segment S2 Symbolic Steps

Basic-block `SepWP` lemmas (`+0x2a4 → +0x3e4 / +0x500 / +0x30c`) around
`find_receiver_chain_key` for `try_decrypt_with_state::<signal_session_handshake::Coins>` on
`tripleRatchetProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Segment S2 (`+0x2a4 → +0x3e4 / +0x500 / +0x30c`) -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_bl_wp {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s0 s : State}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x2a4#64)
    (hmeta : tryDecryptWPInv s0 s) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr findReceiverChainKeyName) s
      emp
      (fun s1 P1 =>
        P1 = emp ∧
        tryDecryptWPInv s0 s1 ∧
        s1.readReg64 Reg.lr = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x2a8#64 ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧
        s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x8 = s.readReg64 .x8 ∧
        CalleeSavedPreserved s s1) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  have hcal : (tripleRatchetProgAt b C ctl abs).fnAddr findReceiverChainKeyName =
      (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        (0x2a4#64 + BitVec.signExtend 64 (-(BitVec.ofNat 28 (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 676 - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key"))) : BitVec 28)) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.fnAddr_tryDecrypt_rel64 libsignalSessionCode_fnOff_0xe8fc (by decide)
  dec_fetches_cli b (tripleRatchetExterns C ctl abs) hfn 0x2a4 4
  rw [hcal]
  clear hcal hfn
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_err_1a_wp {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {w0 d0 : BitVec 64} {w1_lo w1_hi d1_lo d1_hi : BitVec 32}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x2a8#64)
    (hmeta : tryDecryptWPInv s0 s) :
    let prog := tripleRatchetProgAt img.base C ctl abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x2d0#64) s
      (((sp + 0x190#64) ↦₃₂ 2#32) ∗
       ((sp + 0x198#64) ↦₆₄ w0) ∗
       ((sp + 0x1a0#64) ↦₃₂ w1_lo) ∗
       ((sp + 0x1a4#64) ↦₃₂ w1_hi) ∗
       ((sp + 0x2c0#64) ↦₆₄ d0) ∗
       ((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗
       ((sp + 0x2cc#64) ↦₃₂ d1_hi))
      (fun sf P =>
        P = (((sp + 0x190#64) ↦₃₂ 2#32) ∗
             ((sp + 0x198#64) ↦₆₄ w0) ∗
             ((sp + 0x1a0#64) ↦₃₂ w1_lo) ∗
             ((sp + 0x1a4#64) ↦₃₂ w1_hi) ∗
             ((sp + 0x2c0#64) ↦₆₄ w0) ∗
             ((sp + 0x2c8#64) ↦₃₂ w1_lo) ∗
             ((sp + 0x2cc#64) ↦₃₂ w1_hi)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr (C := C) (ctl := ctl) (abs := abs) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base (tripleRatchetExterns C ctl abs) hfn 0x2a8 40
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  wp_finish
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_err_1b_wp {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {w0 w1 b0 b1 s1 s2 : BitVec 64} {d8c d2d0 s0_w : BitVec 32}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x2d0#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx12 : s.readReg64 .x12 = (s0.sp - 1504#64) + 0x2c0#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64) :
    let prog := tripleRatchetProgAt img.base C ctl abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x2f4#64) s
      (((sp + 0x18c#64) ↦₃₂ d8c) ∗
       ((sp + 0x2b0#64) ↦₆₄ b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ b1) ∗
       ((sp + 0x2c0#64) ↦₆₄ w0) ∗
       ((sp + 0x2c8#64) ↦₆₄ w1) ∗
       ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
       ((sp + 0x340#64) ↦₃₂ s0_w) ∗
       ((sp + 0x344#64) ↦₆₄ s1) ∗
       ((sp + 0x34c#64) ↦₆₄ s2))
      (fun sf P =>
        P = (((sp + 0x18c#64) ↦₃₂ 24#32) ∗
             ((sp + 0x2b0#64) ↦₆₄ b0) ∗
             ((sp + 0x2b8#64) ↦₆₄ b1) ∗
             ((sp + 0x2c0#64) ↦₆₄ w0) ∗
             ((sp + 0x2c8#64) ↦₆₄ w1) ∗
             ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
             ((sp + 0x340#64) ↦₃₂ d2d0) ∗
             ((sp + 0x344#64) ↦₆₄ b0) ∗
             ((sp + 0x34c#64) ↦₆₄ b1)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x26 = speWord 20 ∧
        sf.readVReg128 1#5 = w1 ++ w0) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr (C := C) (ctl := ctl) (abs := abs) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base (tripleRatchetExterns C ctl abs) hfn 0x2d0 36
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  wp_finish
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm, speWord], by simp_all [arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_err_1c_wp {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {w0 w1 u0 u1 c0 c1 g0 g1 g2 g3 : BitVec 64} {u2 g4 : BitVec 32}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x2f4#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx12 : s.readReg64 .x12 = (s0.sp - 1504#64) + 0x2c0#64)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hq1 : s.readVReg128 1#5 = w1 ++ w0) :
    let prog := tripleRatchetProgAt img.base C ctl abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC img) s
      (((sp + 0x168#64) ↦₆₄ g0) ∗
       ((sp + 0x170#64) ↦₆₄ g1) ∗
       ((sp + 0x178#64) ↦₆₄ g2) ∗
       ((sp + 0x180#64) ↦₆₄ g3) ∗
       ((sp + 0x188#64) ↦₃₂ g4) ∗
       ((sp + 0x330#64) ↦₆₄ c0) ∗
       ((sp + 0x338#64) ↦₆₄ c1) ∗
       ((sp + 0x340#64) ↦₆₄ u0) ∗
       ((sp + 0x348#64) ↦₆₄ u1) ∗
       ((sp + 0x350#64) ↦₃₂ u2))
      (fun sf P =>
        P = (((sp + 0x168#64) ↦₆₄ w0) ∗
             ((sp + 0x170#64) ↦₆₄ w1) ∗
             ((sp + 0x178#64) ↦₆₄ u0) ∗
             ((sp + 0x180#64) ↦₆₄ u1) ∗
             ((sp + 0x188#64) ↦₃₂ u2) ∗
             ((sp + 0x330#64) ↦₆₄ w0) ∗
             ((sp + 0x338#64) ↦₆₄ w1) ∗
             ((sp + 0x340#64) ↦₆₄ u0) ∗
             ((sp + 0x348#64) ↦₆₄ u1) ∗
             ((sp + 0x350#64) ↦₃₂ u2)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x26 = s.readReg64 .x26) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr (C := C) (ctl := ctl) (abs := abs) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base (tripleRatchetExterns C ctl abs) hfn 0x2f4 24
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC]
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  wp_finish
  exact ⟨by simp_all [arm64_norm], ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok_branch_wp {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {tag : BitVec 32} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (htag : (tag != 2#32) = true)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x2a8#64)
    (hmeta : tryDecryptWPInv s0 s) :
    let prog := tripleRatchetProgAt img.base C ctl abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x3b4#64) s
      ((sp + 0x190#64) ↦₃₂ tag)
      (fun sf P =>
        P = ((sp + 0x190#64) ↦₃₂ tag) ∧
        tryDecryptWPInv s0 sf ∧
        (sf.readReg64 .x9).setWidth 32 = tag ∧
        CalleeSavedPreserved s sf) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr (C := C) (ctl := ctl) (abs := abs) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base (tripleRatchetExterns C ctl abs) hfn 0x2a8 12
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  wp_finish
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok_none_wp {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {w0 : BitVec 32} {w1 w2 w3 w4 d0 d1 : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x3b4#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx9 : (s.readReg64 .x9).setWidth 32 = 0#32)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64) :
    let prog := tripleRatchetProgAt img.base C ctl abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS3PC img) s
      (((sp + 0x194#64) ↦₃₂ w0) ∗
       ((sp + 0x198#64) ↦₆₄ w1) ∗
       ((sp + 0x1a0#64) ↦₆₄ w2) ∗
       ((sp + 0x1a8#64) ↦₆₄ w3) ∗
       ((sp + 0x1b0#64) ↦₆₄ w4) ∗
       ((sp + 0x380#64) ↦₆₄ d0) ∗
       ((sp + 0x388#64) ↦₆₄ d1))
      (fun sf P =>
        P = (((sp + 0x194#64) ↦₃₂ w0) ∗
             ((sp + 0x198#64) ↦₆₄ w1) ∗
             ((sp + 0x1a0#64) ↦₆₄ w2) ∗
             ((sp + 0x1a8#64) ↦₆₄ w3) ∗
             ((sp + 0x1b0#64) ↦₆₄ w4) ∗
             ((sp + 0x380#64) ↦₆₄ w3) ∗
             ((sp + 0x388#64) ↦₆₄ w4)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        CalleeSavedPreserved s sf) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr (C := C) (ctl := ctl) (abs := abs) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base (tripleRatchetExterns C ctl abs) hfn 0x3b4 28
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS3PC]
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  wp_finish
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok_some_wp {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {w0 c0 : BitVec 32} {w1 w2 w3 w4 b0 b1 c1 c2 d0 d1 : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x3b4#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx9 : (s.readReg64 .x9).setWidth 32 = 1#32)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64) :
    let prog := tripleRatchetProgAt img.base C ctl abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS4PC img) s
      (((sp + 0x194#64) ↦₃₂ w0) ∗
       ((sp + 0x198#64) ↦₆₄ w1) ∗
       ((sp + 0x1a0#64) ↦₆₄ w2) ∗
       ((sp + 0x1a8#64) ↦₆₄ w3) ∗
       ((sp + 0x1b0#64) ↦₆₄ w4) ∗
       ((sp + 0x2b0#64) ↦₆₄ b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ b1) ∗
       ((sp + 0x2c0#64) ↦₃₂ c0) ∗
       ((sp + 0x2c4#64) ↦₆₄ c1) ∗
       ((sp + 0x2cc#64) ↦₆₄ c2) ∗
       ((sp + 0x380#64) ↦₆₄ d0) ∗
       ((sp + 0x388#64) ↦₆₄ d1))
      (fun sf P =>
        P = (((sp + 0x194#64) ↦₃₂ w0) ∗
             ((sp + 0x198#64) ↦₆₄ w1) ∗
             ((sp + 0x1a0#64) ↦₆₄ w2) ∗
             ((sp + 0x1a8#64) ↦₆₄ w3) ∗
             ((sp + 0x1b0#64) ↦₆₄ w4) ∗
             ((sp + 0x2b0#64) ↦₆₄ w3) ∗
             ((sp + 0x2b8#64) ↦₆₄ w4) ∗
             ((sp + 0x2c0#64) ↦₃₂ w0) ∗
             ((sp + 0x2c4#64) ↦₆₄ w1) ∗
             ((sp + 0x2cc#64) ↦₆₄ w2) ∗
             ((sp + 0x380#64) ↦₆₄ w3) ∗
             ((sp + 0x388#64) ↦₆₄ w4)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        CalleeSavedPreserved s sf) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr (C := C) (ctl := ctl) (abs := abs) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base (tripleRatchetExterns C ctl abs) hfn 0x3b4 48
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS4PC]
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  wp_finish
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_call_findReceiverChainKey_reaches {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl :
    BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hfrck : FindReceiverChainKeyOk img C A ctl abs)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hS2 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2State A ctl img x trG tr st1 R s0 s) :
    let prog := tripleRatchetProgAt img.base C ctl abs
    let sp := s0.sp - 1504#64
    reaches_pc prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x2a8#64) s
      (fun s_ret =>
        tryDecryptMidMeta img s0 s_ret ∧
        s_ret.readReg64 .x19 = x.ret ∧
        s_ret.readReg64 .x20 = sp + 0x140#64 ∧
        s_ret.readReg64 .x21 = x.ss ∧
        s_ret.readReg64 .x22 = x.msgA ∧
        s_ret.readReg64 .x23 = sp + 0x500#64 ∧
        (s_ret.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s_ret.readReg64 .x25 = sp + 0x190#64 ∧
        s_ret.readReg64 .x27 = sp + 0x38#64 ∧
        s_ret.readReg64 .x28 = sp + 0x2c0#64 ∧
        (s_ret.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 0x38#64) trG tr ∗
          memRegion x.ret 48 ∗
          memRegion sp 0x20 ∗
          ((sp + 0x20#64) ↦₆₄ x.locA) ∗
          ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 0x2c#64) 4 ∗
          ((sp + 0x30#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 0x140#64) 0x50 ∗
          findReceiverChainKeyResultAt (sp + 0x190#64) (tr.ratchet.findReceiverChainKey
            x.msg.senderRatchetKey) ∗
          memRegion (sp + 0x1b8#64) 0x3c8 ∗
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hS2 with ⟨hpc, hmeta, hx0, hx1, hx8, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
      hmem⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr (C := C) (ctl := ctl) (abs := abs) himg
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS2PC] at hpc
  rw [hentry] at hpc
  have hwp_bl := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_bl_wp hpc (tryDecryptMidMeta.to_wpInv hmeta)
  have hmem_emp : s.mem ⊨ emp ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x440 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    rw [emp_sepConj]; exact hmem
  have hinv_s : img.FrozenLoaded s ∧ s.symtab = img.symtab := ⟨hmeta.2.2.2.2.2.2.1,
      hmeta.2.2.2.2.2.2.2.1⟩
  refine reaches_pc_seq_callInv hinv_s (sepWP_to_reaches_pc hwp_bl hmem_emp) ?_
  intro s_call hpc_call _ ⟨P1, hm_call, ⟨hP1, hwpInv_call, hlr_call, hx0_c, hx1_c, hx8_c,
      hcs_c⟩⟩ hinv_call
  subst hP1
  rw [emp_sepConj] at hm_call
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap at hm_call
  rw [trAt_eq_ratchetAt_trRestAt, signalMessageAt_eq_srk_rest,
      memRegion_0x140_split_findReceiverChainKey,
      stackAt_tryDecryptSubStack_sub s0.sp findReceiverChainKeyStack (by decide)] at hm_call
  have hsp_call : s_call.sp = sp := hwpInv_call.2.1
  have halign_call : s_call.spAligned = true := hwpInv_call.2.2.2.1
  have hlr_call' : s_call.readReg64 Reg.lr = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x2a8#64 := by
    rw [hentry]; exact hlr_call
  let fg : FindReceiverChainKeyGhost :=
    { self := sp + 0x38#64
      G := trG.ratchet
      st := tr.ratchet
      theirA := x.msgA + 0x38#64
      their := x.msg.senderRatchetKey
      ret := sp + 0x190#64 }
  let F_call : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trRestAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1b8#64) 0x3c8 ∗
    protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗
    signalMessageRestAt A x.msgG x.msgA x.msg ∗
    CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
    memRegion (s0.sp - 262144#64) (tryDecryptSubStack - findReceiverChainKeyStack) ∗
    tryDecryptSavedRegs s0.sp s0 ∗
    A.pool ∗ R
  have hpre_call :
      s_call.mem ⊨
        (⌜s_call.readReg64 .x0 = fg.self ∧ s_call.readReg64 .x1 = fg.theirA ∧
            s_call.readReg64 .x8 = fg.ret⌝ ∗
         ratchetAt A fg.self fg.G fg.st ∗
         (fg.theirA ↦ₛ fg.their.bytes.toList) ∗
         memRegion fg.ret 40 ∗
         logOff img ∗
         stackAt s_call.sp findReceiverChainKeyStack) ∗ F_call := by
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c.trans hx0, hx1_c.trans hx1, hx8_c.trans hx8⟩, ?_⟩
    rw [hsp_call]
    dsimp only [fg, F_call, sp] at hm_call ⊢
    convert hm_call using 1; sep_ac_rfl
  refine reaches_pc_call_inImage hfrck fg F_call hpc_call hwpInv_call.1 hlr_call' hinv_call
      hpre_call
    (fun s_ret hpc_ret hrun_ret hsp_ret hcs_ret hinv_ret hpost_ret => ?_) halign_call
  refine reaches_pc_refl hpc_ret hrun_ret ?_
  have hcs : CalleeSavedPreserved s s_ret := CalleeSavedPreserved.trans hcs_c hcs_ret
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ret
  rcases hpost_ret with ⟨htr_ret, hm_ret⟩
  have hsp_ret' : s_ret.sp = s0.sp - 1504#64 := hsp_ret.trans hsp_call
  have halign_ret : s_ret.spAligned = true := by
    rw [State.spAligned, hsp_ret', ← hwpInv_call.2.1]
    exact halign_call
  have hmeta_ret : tryDecryptMidMeta img s0 s_ret :=
    ⟨hrun_ret, hsp_ret', hwpInv_call.2.2.1, halign_ret,
     (hcs_ret.2.2.2.2.2.2.2.2.2.2.1).trans hwpInv_call.2.2.2.2.1,
     htr_ret.trans hwpInv_call.2.2.2.2.2.1, hinv_ret.1, hinv_ret.2,
     (hcs.2.2.2.2.2.2.2.2.2.2.2).trans hmeta.2.2.2.2.2.2.2.2⟩
  refine ⟨hmeta_ret,
    (hcs.1).trans hx19,
    (hcs.2.1).trans hx20,
    (hcs.2.2.1).trans hx21,
    (hcs.2.2.2.1).trans hx22,
    (hcs.2.2.2.2.1).trans hx23,
    by change (s_ret.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hcs.2.2.2.2.2.1]; exact hx24,
    (hcs.2.2.2.2.2.2.1).trans hx25,
    (hcs.2.2.2.2.2.2.2.2.1).trans hx27,
    (hcs.2.2.2.2.2.2.2.2.2.1).trans hx28,
    ?_⟩
  rw [hsp_call] at hm_ret
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap
  rw [trAt_eq_ratchetAt_trRestAt, signalMessageAt_eq_srk_rest,
      stackAt_tryDecryptSubStack_sub s0.sp findReceiverChainKeyStack (by decide)]
  dsimp only [fg, F_call, sp] at hm_ret ⊢
  convert hm_ret using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_err_wp {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {w0 w1 g0 g1 g2 g3 b0 b1 d0 c0 c1 s1 s2 : BitVec 64}
    {g4 d8c d1_lo d1_hi d2d0 s0_w : BitVec 32}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x2a8#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64) :
    let prog := tripleRatchetProgAt img.base C ctl abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC img) s
      (((sp + 0x168#64) ↦₆₄ g0) ∗
       ((sp + 0x170#64) ↦₆₄ g1) ∗
       ((sp + 0x178#64) ↦₆₄ g2) ∗
       ((sp + 0x180#64) ↦₆₄ g3) ∗
       ((sp + 0x188#64) ↦₃₂ g4) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗
       ((sp + 0x190#64) ↦₃₂ 2#32) ∗
       ((sp + 0x198#64) ↦₆₄ w0) ∗
       ((sp + 0x1a0#64) ↦₆₄ w1) ∗
       ((sp + 0x2b0#64) ↦₆₄ b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ b1) ∗
       ((sp + 0x2c0#64) ↦₆₄ d0) ∗
       ((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗
       ((sp + 0x2cc#64) ↦₃₂ d1_hi) ∗
       ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
       ((sp + 0x330#64) ↦₆₄ c0) ∗
       ((sp + 0x338#64) ↦₆₄ c1) ∗
       ((sp + 0x340#64) ↦₃₂ s0_w) ∗
       ((sp + 0x344#64) ↦₆₄ s1) ∗
       ((sp + 0x34c#64) ↦₆₄ s2))
      (fun sf P =>
        let u0 := b0.extractLsb' 0 32 ++ d2d0
        let u1 := b1.extractLsb' 0 32 ++ b0.extractLsb' 32 32
        let u2 := b1.extractLsb' 32 32
        P = (((sp + 0x168#64) ↦₆₄ w0) ∗
             ((sp + 0x170#64) ↦₆₄ w1) ∗
             ((sp + 0x178#64) ↦₆₄ u0) ∗
             ((sp + 0x180#64) ↦₆₄ u1) ∗
             ((sp + 0x188#64) ↦₃₂ u2) ∗
             ((sp + 0x18c#64) ↦₃₂ 24#32) ∗
             ((sp + 0x190#64) ↦₃₂ 2#32) ∗
             ((sp + 0x198#64) ↦₆₄ w0) ∗
             ((sp + 0x1a0#64) ↦₆₄ w1) ∗
             ((sp + 0x2b0#64) ↦₆₄ b0) ∗
             ((sp + 0x2b8#64) ↦₆₄ b1) ∗
             ((sp + 0x2c0#64) ↦₆₄ w0) ∗
             ((sp + 0x2c8#64) ↦₆₄ w1) ∗
             ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
             ((sp + 0x330#64) ↦₆₄ w0) ∗
             ((sp + 0x338#64) ↦₆₄ w1) ∗
             ((sp + 0x340#64) ↦₆₄ u0) ∗
             ((sp + 0x348#64) ↦₆₄ u1) ∗
             ((sp + 0x350#64) ↦₃₂ u2)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x26 = speWord 20) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have hsplit_1a0 :
      ((sp + 0x1a0#64) ↦₆₄ w1) =
        ((sp + 0x1a0#64) ↦₃₂ w1.extractLsb' 0 32) ∗
        ((sp + 0x1a4#64) ↦₃₂ w1.extractLsb' 32 32) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo64_split32 (sp + 0x1a0#64) w1
  have hsplit_2c8 :
      ((sp + 0x2c8#64) ↦₆₄ w1) =
        ((sp + 0x2c8#64) ↦₃₂ w1.extractLsb' 0 32) ∗
        ((sp + 0x2cc#64) ↦₃₂ w1.extractLsb' 32 32) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo64_split32 (sp + 0x2c8#64) w1
  have h1a := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_err_1a_wp (C := C) (ctl := ctl) (abs := abs)
    (w0 := w0) (w1_lo := w1.extractLsb' 0 32) (w1_hi := w1.extractLsb' 32 32)
    (d0 := d0) (d1_lo := d1_lo) (d1_hi := d1_hi) himg hpc hmeta
  refine SepWP.rw_pre (by rw [hsplit_1a0]) ?_
  refine SepWP.bind_framed
    (F := ((sp + 0x168#64) ↦₆₄ g0) ∗
          ((sp + 0x170#64) ↦₆₄ g1) ∗
          ((sp + 0x178#64) ↦₆₄ g2) ∗
          ((sp + 0x180#64) ↦₆₄ g3) ∗
          ((sp + 0x188#64) ↦₃₂ g4) ∗
          ((sp + 0x18c#64) ↦₃₂ d8c) ∗
          ((sp + 0x2b0#64) ↦₆₄ b0) ∗
          ((sp + 0x2b8#64) ↦₆₄ b1) ∗
          ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
          ((sp + 0x330#64) ↦₆₄ c0) ∗
          ((sp + 0x338#64) ↦₆₄ c1) ∗
          ((sp + 0x340#64) ↦₃₂ s0_w) ∗
          ((sp + 0x344#64) ↦₆₄ s1) ∗
          ((sp + 0x34c#64) ↦₆₄ s2))
    h1a ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s1a P1a ⟨hP1a, hmeta1a, hx12_1a, hx19_1a, hx20_1a, hx25_1a⟩ hpc1a
  subst hP1a
  have h1b := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_err_1b_wp (C := C) (ctl := ctl) (abs := abs)
    (w0 := w0) (w1 := w1) (b0 := b0) (b1 := b1) (s1 := s1) (s2 := s2)
    (d8c := d8c) (d2d0 := d2d0) (s0_w := s0_w)
    himg hpc1a hmeta1a hx12_1a (hx25_1a.trans hx25)
  refine SepWP.bind_framed
    (F := ((sp + 0x190#64) ↦₃₂ 2#32) ∗
          ((sp + 0x198#64) ↦₆₄ w0) ∗
          ((sp + 0x1a0#64) ↦₆₄ w1) ∗
          ((sp + 0x168#64) ↦₆₄ g0) ∗
          ((sp + 0x170#64) ↦₆₄ g1) ∗
          ((sp + 0x178#64) ↦₆₄ g2) ∗
          ((sp + 0x180#64) ↦₆₄ g3) ∗
          ((sp + 0x188#64) ↦₃₂ g4) ∗
          ((sp + 0x330#64) ↦₆₄ c0) ∗
          ((sp + 0x338#64) ↦₆₄ c1))
    h1b ?_ ?_
  · rw [hsplit_1a0, hsplit_2c8]
    dsimp only [sp]; sep_ac_rfl
  intro s1b P1b ⟨hP1b, hmeta1b, hx12_1b, hx19_1b, hx20_1b, hx26_1b, hq1_1b⟩ hpc1b
  subst hP1b
  have hrealign :
      (((sp + 0x340#64) ↦₃₂ d2d0) ∗
       ((sp + 0x344#64) ↦₆₄ b0) ∗
       ((sp + 0x34c#64) ↦₆₄ b1)) =
      (((sp + 0x340#64) ↦₆₄ (b0.extractLsb' 0 32 ++ d2d0)) ∗
       ((sp + 0x348#64) ↦₆₄ (b1.extractLsb' 0 32 ++ b0.extractLsb' 32 32)) ∗
       ((sp + 0x350#64) ↦₃₂ b1.extractLsb' 32 32)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using realign_20_bytes (sp + 0x340#64) d2d0 b0 b1
  have h1c := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_err_1c_wp (C := C) (ctl := ctl) (abs := abs)
    (w0 := w0) (w1 := w1)
    (u0 := b0.extractLsb' 0 32 ++ d2d0)
    (u1 := b1.extractLsb' 0 32 ++ b0.extractLsb' 32 32)
    (u2 := b1.extractLsb' 32 32)
    (c0 := c0) (c1 := c1) (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3) (g4 := g4)
    himg hpc1b hmeta1b hx12_1b (hx20_1b.trans (hx20_1a.trans hx20)) hq1_1b
  refine SepWP.bind_framed
    (F := ((sp + 0x18c#64) ↦₃₂ 24#32) ∗
          ((sp + 0x190#64) ↦₃₂ 2#32) ∗
          ((sp + 0x198#64) ↦₆₄ w0) ∗
          ((sp + 0x1a0#64) ↦₆₄ w1) ∗
          ((sp + 0x2b0#64) ↦₆₄ b0) ∗
          ((sp + 0x2b8#64) ↦₆₄ b1) ∗
          ((sp + 0x2c0#64) ↦₆₄ w0) ∗
          ((sp + 0x2c8#64) ↦₆₄ w1) ∗
          ((sp + 0x2d0#64) ↦₃₂ d2d0))
    h1c ?_ ?_
  · rw [← hrealign]
    dsimp only [sp]; sep_ac_rfl
  intro sf Pf ⟨hPf, hmetaf, hx19_f, hx20_f, hx26_f⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨by dsimp only [sp]; sep_ac_rfl, hmetaf,
    hx19_f.trans (hx19_1b.trans hx19_1a),
    hx20_f.trans (hx20_1b.trans hx20_1a),
    hx26_f.trans hx26_1b⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok_none_full_wp {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {w0 : BitVec 32} {w1 w2 w3 w4 d0 d1 : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x2a8#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64) :
    let prog := tripleRatchetProgAt img.base C ctl abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS3PC img) s
      (((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦₃₂ w0) ∗
       ((sp + 0x198#64) ↦₆₄ w1) ∗
       ((sp + 0x1a0#64) ↦₆₄ w2) ∗
       ((sp + 0x1a8#64) ↦₆₄ w3) ∗
       ((sp + 0x1b0#64) ↦₆₄ w4) ∗
       ((sp + 0x380#64) ↦₆₄ d0) ∗
       ((sp + 0x388#64) ↦₆₄ d1))
      (fun sf P =>
        P = (((sp + 0x190#64) ↦₃₂ 0#32) ∗
             ((sp + 0x194#64) ↦₃₂ w0) ∗
             ((sp + 0x198#64) ↦₆₄ w1) ∗
             ((sp + 0x1a0#64) ↦₆₄ w2) ∗
             ((sp + 0x1a8#64) ↦₆₄ w3) ∗
             ((sp + 0x1b0#64) ↦₆₄ w4) ∗
             ((sp + 0x380#64) ↦₆₄ w3) ∗
             ((sp + 0x388#64) ↦₆₄ w4)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        CalleeSavedPreserved s sf) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have hbr := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok_branch_wp (C := C) (ctl := ctl) (abs := abs)
    (tag := 0#32) himg (by decide) hpc hmeta
  refine SepWP.bind_framed
    (F := ((sp + 0x194#64) ↦₃₂ w0) ∗
          ((sp + 0x198#64) ↦₆₄ w1) ∗
          ((sp + 0x1a0#64) ↦₆₄ w2) ∗
          ((sp + 0x1a8#64) ↦₆₄ w3) ∗
          ((sp + 0x1b0#64) ↦₆₄ w4) ∗
          ((sp + 0x380#64) ↦₆₄ d0) ∗
          ((sp + 0x388#64) ↦₆₄ d1))
    hbr ?_ ?_
  · dsimp only [sp]
  intro s1 P1 ⟨hP1, hmeta1, hx9_1, hcs1⟩ hpc1
  subst hP1
  have hx25_1 : s1.readReg64 .x25 = sp + 0x190#64 := (hcs1.2.2.2.2.2.2.1).trans hx25
  have hx28_1 : s1.readReg64 .x28 = sp + 0x2c0#64 := (hcs1.2.2.2.2.2.2.2.2.2.1).trans hx28
  have hnone := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok_none_wp (C := C) (ctl := ctl) (abs := abs)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (d0 := d0) (d1 := d1)
    himg hpc1 hmeta1 hx9_1 hx25_1 hx28_1
  refine SepWP.bind_framed (F := (sp + 0x190#64) ↦₃₂ 0#32) hnone ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro sf Pf ⟨hPf, hmetaf, hx12_f, hcsf⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨?_, hmetaf, hx12_f, CalleeSavedPreserved.trans hcs1 hcsf⟩
  dsimp only [sp]; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok_some_full_wp {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {w0 c0 : BitVec 32} {w1 w2 w3 w4 b0 b1 c1 c2 d0 d1 : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x2a8#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64) :
    let prog := tripleRatchetProgAt img.base C ctl abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS4PC img) s
      (((sp + 0x190#64) ↦₃₂ 1#32) ∗
       ((sp + 0x194#64) ↦₃₂ w0) ∗
       ((sp + 0x198#64) ↦₆₄ w1) ∗
       ((sp + 0x1a0#64) ↦₆₄ w2) ∗
       ((sp + 0x1a8#64) ↦₆₄ w3) ∗
       ((sp + 0x1b0#64) ↦₆₄ w4) ∗
       ((sp + 0x2b0#64) ↦₆₄ b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ b1) ∗
       ((sp + 0x2c0#64) ↦₃₂ c0) ∗
       ((sp + 0x2c4#64) ↦₆₄ c1) ∗
       ((sp + 0x2cc#64) ↦₆₄ c2) ∗
       ((sp + 0x380#64) ↦₆₄ d0) ∗
       ((sp + 0x388#64) ↦₆₄ d1))
      (fun sf P =>
        P = (((sp + 0x190#64) ↦₃₂ 1#32) ∗
             ((sp + 0x194#64) ↦₃₂ w0) ∗
             ((sp + 0x198#64) ↦₆₄ w1) ∗
             ((sp + 0x1a0#64) ↦₆₄ w2) ∗
             ((sp + 0x1a8#64) ↦₆₄ w3) ∗
             ((sp + 0x1b0#64) ↦₆₄ w4) ∗
             ((sp + 0x2b0#64) ↦₆₄ w3) ∗
             ((sp + 0x2b8#64) ↦₆₄ w4) ∗
             ((sp + 0x2c0#64) ↦₃₂ w0) ∗
             ((sp + 0x2c4#64) ↦₆₄ w1) ∗
             ((sp + 0x2cc#64) ↦₆₄ w2) ∗
             ((sp + 0x380#64) ↦₆₄ w3) ∗
             ((sp + 0x388#64) ↦₆₄ w4)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        CalleeSavedPreserved s sf) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have hbr := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok_branch_wp (C := C) (ctl := ctl) (abs := abs)
    (tag := 1#32) himg (by decide) hpc hmeta
  refine SepWP.bind_framed
    (F := ((sp + 0x194#64) ↦₃₂ w0) ∗
          ((sp + 0x198#64) ↦₆₄ w1) ∗
          ((sp + 0x1a0#64) ↦₆₄ w2) ∗
          ((sp + 0x1a8#64) ↦₆₄ w3) ∗
          ((sp + 0x1b0#64) ↦₆₄ w4) ∗
          ((sp + 0x2b0#64) ↦₆₄ b0) ∗
          ((sp + 0x2b8#64) ↦₆₄ b1) ∗
          ((sp + 0x2c0#64) ↦₃₂ c0) ∗
          ((sp + 0x2c4#64) ↦₆₄ c1) ∗
          ((sp + 0x2cc#64) ↦₆₄ c2) ∗
          ((sp + 0x380#64) ↦₆₄ d0) ∗
          ((sp + 0x388#64) ↦₆₄ d1))
    hbr ?_ ?_
  · dsimp only [sp]
  intro s1 P1 ⟨hP1, hmeta1, hx9_1, hcs1⟩ hpc1
  subst hP1
  have hx25_1 : s1.readReg64 .x25 = sp + 0x190#64 := (hcs1.2.2.2.2.2.2.1).trans hx25
  have hx28_1 : s1.readReg64 .x28 = sp + 0x2c0#64 := (hcs1.2.2.2.2.2.2.2.2.2.1).trans hx28
  have hsome := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok_some_wp (C := C) (ctl := ctl) (abs := abs)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (b0 := b0) (b1 := b1) (c0 := c0) (c1 := c1) (c2 := c2) (d0 := d0) (d1 := d1)
    himg hpc1 hmeta1 hx9_1 hx25_1 hx28_1
  refine SepWP.bind_framed (F := (sp + 0x190#64) ↦₃₂ 1#32) hsome ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro sf Pf ⟨hPf, hmetaf, hx12_f, hcsf⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨?_, hmetaf, hx12_f, CalleeSavedPreserved.trans hcs1 hcsf⟩
  dsimp only [sp]; sep_ac_rfl

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
