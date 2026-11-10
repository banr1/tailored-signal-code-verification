/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import ProofLib.SepLogic.WPp

/-!
# Segment 8 (`aes_256_cbc_decrypt`) Proofs for `try_decrypt_with_state`

Verifies Segment 8 (`+0x678 → +0x6a4 / +0x30c`) of `try_decrypt_with_state`, covering the
`aes_256_cbc_decrypt` call, ciphertext error formatting, and relocatable `[LibsignalPlacement]`
contracts for blocks `130` and `433` (`549`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

theorem aesDecrypt_some_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState pt : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = some pt)
    (h8 : AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (ApplyRatchetState A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have hfn := hfn_tryDecrypt
  have haes := aesDec_ok_at_ext img C A ctl S ext hC
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  rw [segS8PC_eq_ext himg ext] at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic
    ((libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr tryDecryptName + 1700#64)
    hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  decrypt_fetches_ext img.base ext hfn 0x678 44
  have hS9_pc : segApplyRatchetPC img = (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr tryDecryptName + 1700#64 :=
    segS9PC_eq_ext himg ext
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr tryDecryptName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP_frozen hfl hsym (mid := entry + bv% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hfl1 hsym1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_frame_frozen (img := img) (spec := aesDecSpec C.D A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := entry + bv% (1688))
    hfl1 hsym1 haes (by rfl) (by exact hstat)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      tryDecrypt_onPanic_of_callee C A ctl S img x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hfl1 hsym1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hfl2 hsym2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecSpec, AesCall.frame]
    rw [bytesToKey32_keyToBytes32, bytesToBlock_blockToBytesLE, hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
      (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
    have hcap_ne : ptCap + 1#64 ≠ 0#64 := add_one_ne_zero_of_lt_2_63 hpt_lt
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl2 hsym2 (mid := entry + bv% (1700))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun2)
    intro hfl3 hsym3
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by rfl) (by exact hrun2)
    intro _ _ hmf
    refine ⟨?_, ⟨hrun2, hsp2, hsp0,
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2, ?_, htr2, hfl3, hsym3, by simp only [wp_norm, hvregs_2]⟩,
      by simp only [wp_norm, hx19_2],
      by simp only [wp_norm, hx20_2],
      by simp only [wp_norm, hx21_2],
      by simp only [wp_norm, hx23_2],
      by simp only [wp_norm, hx24_2],
      newPqrCap, newPqrPtr, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
    · rw [hS9_pc]; rfl
    · simp only [wp_norm, hx29_2]
    · unfold tryDecryptCommonHeap signalMessageAt
      rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
          stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
          applyRatchet_reg10_split (s0.sp - 1504#64),
          applyRatchet_reg3e8_split (s0.sp - 1504#64)]
      have hvec := vecU8At_parts_entails_vecU8' A (s0.sp - 528#64) ptCap ptPtr pt hpt_le hpt_lt hpt_nz
      have hmf1 := Satisfies.mono_focus hvec (by sep_focus) hmf
      have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
      have hmf3 := Satisfies.mono_focus (applyRatchet_sp_entails_memRegion s0.sp msgW x.locA x.remA) (by sep_focus) hmf2
      clear hmf hmf1 hmf2
      simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf3 ⊢
      rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
      sep_close

theorem aesDecrypt_some_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hS : TripleRatchetHooks C A S abs)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState pt : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = some pt)
    (h8 : AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
      (ApplyRatchetState A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) :=
  aesDecrypt_some_ok_ext img C A ctl S (tripleRatchetExterns C ctl abs) himg (Stage2Contracts.of_tripleRatchetProgAt' hS)
    x trG tr st1 mks newPqrState pt draws R s0 s hd h8 hL

theorem aesDecrypt_none_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = none)
    (h8 : AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (ErrTailState A ctl img x trG tr st1
        (.invalidMessage x.msgType .badCiphertext) draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have hfn := hfn_tryDecrypt
  have haes := aesDec_ok_at_ext img C A ctl S ext hC
  have hfmt := formatInner_ok_at_ext img C A ctl S ext hC
  have hdealloc := dealloc_ok_at_ext img C A ctl S ext hC
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  rw [segS8PC_eq_ext himg ext] at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic
    ((libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr tryDecryptName + 780#64)
    hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  decrypt_fetches_ext img.base ext hfn 0x678 44
  decrypt_fetches_ext img.base ext hfn 0xa1c 88
  decrypt_fetches_ext img.base ext hfn 0x964 8
  decrypt_fetches_ext img.base ext hfn 0x9d0 12
  have hErr_pc : errTailPC img = (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr tryDecryptName + 780#64 :=
    errTailPC_eq_ext himg ext
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr tryDecryptName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP_frozen hfl hsym (mid := entry + bv% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hfl1 hsym1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_frame_frozen (img := img) (spec := aesDecSpec C.D A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := entry + bv% (1688))
    hfl1 hsym1 haes (by rfl) (by exact hstat)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      tryDecrypt_onPanic_of_callee C A ctl S img x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hfl1 hsym1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hfl2 hsym2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecSpec, AesCall.frame]
    rw [bytesToKey32_keyToBytes32, bytesToBlock_blockToBytesLE, hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    refine SepWPp.elim_exists_focus
      (Φ := fun p : BitVec 64 => ⌜p ≠ 0⌝ ∗ ((s0.sp - 520#64) ↦₆₄ p))
      (by sep_focus) fun p => ?_
    simp only [sepConj_assoc]
    apply SepWPp.elim_pure; intro hp_nz
    simp only [← sepConj_assoc]
    refine SepWPp.mono_focus (aesDecrypt_none_prep s0.sp) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 512#64) (by sep_focus) fun w512 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun b1120 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1104#64) (by sep_focus) fun w1104 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1096#64) (by sep_focus) fun w1096 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 480#64) (by sep_focus) fun w480 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 472#64) (by sep_focus) fun w472 => ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl2 hsym2 (mid := entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun2)
    intro hfl2' hsym2'
    refine SepWPp.call_frame_frozen (img := img) (spec := formatInnerSpec A)
      (x := s0.sp - 1144#64)
      (T := memRegion (s0.sp - 1144#64) 24 ∗ A.pool ∗
            stackAt (s0.sp - 1504#64) extHookStack)
      (ret_pc := entry + bv% (2656))
      hfl2' hsym2' hfmt (by rfl) (by exact hrun2)
      (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
      (by dsimp only [formatInnerSpec]; simp only [wp_norm, hsp2]; rfl)
      (by simp only [wp_norm]) (by sep_focus)
      (fun _ _ _ _ h => allowPanic_not_exited h)
      (fun sf hpan _ hm_pan =>
        tryDecrypt_onPanic_of_callee C A ctl S img x s0 _ sf _ R
          (htr2 ▸ List.prefix_refl _) hm_pan) ?_
    clear hfl2' hsym2'
    intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hfl3 hsym3
    simp only [wp_norm, hsp2] at hsp3
    rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
    simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
    dsimp only [formatInnerSpec]
    simp only [wp_norm, hsp2, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr3
    simp only [htr2] at htr3
    rw [formatInner_post_eq_badCiphertext A s0.sp]
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · refine SepWPp.mono_focus (newPqr_zero_prep A newPqrCap newPqrPtr newPqrState hpqr_cap) (by sep_focus) ?_
      rw [emp_sepConj]
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_frozen hfl3 hsym3 (mid := entry + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hfl4 hsym4
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun3)
      intro _ _ hmf
      refine ⟨?_, ⟨hrun3, hsp3, hsp0,
          AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3, ?_, htr3, hfl4, hsym4, by simp only [wp_norm, hvregs_3]⟩,
        by simp only [wp_norm, hx19_3],
        by simp only [wp_norm, hx20_3],
        by simp only [wp_norm, hx26_3]; rfl, ?_⟩
      · rw [hErr_pc]; rfl
      · simp only [wp_norm, hx29_3]
      · unfold tryDecryptCommonHeap signalMessageAt speBodyAt
        rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_split s0.sp]
        have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
        clear hmf hmf1
        simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
        rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
        sep_close
    · refine SepWPp.mono_focus (newPqr_dealloc_prep' A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
      rw [stackAt_ext_split_alloc (s0.sp - 1504#64)]
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_frozen hfl3 hsym3 (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hfl3' hsym3'
      refine SepWPp.call_frame_frozen (img := img) (spec := rustDeallocSpec A)
        (x := (newPqrPtr, newPqrCap.toNat, 1))
        (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) allocHookStack)
        (ret_pc := entry + bv% (2520))
        hfl3' hsym3' hdealloc (by rfl) (by exact hrun3)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustDeallocSpec]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [rustDeallocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun sf _ _ hm_pan => by dsimp only [rustDeallocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hfl3' hsym3'
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hfl4 hsym4
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustDeallocSpec]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr4
      simp only [htr3] at htr4
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_frozen hfl4 hsym4 (mid := entry + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun4)
      intro hfl5 hsym5
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun4)
      intro _ _ hmf
      refine ⟨?_, ⟨hrun4, hsp4, hsp0,
          AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4, ?_, htr4, hfl5, hsym5, by simp only [wp_norm, hvregs_4]⟩,
        by simp only [wp_norm, hx19_4],
        by simp only [wp_norm, hx20_4],
        by simp only [wp_norm, hx26_4]; rfl, ?_⟩
      · rw [hErr_pc]; rfl
      · simp only [wp_norm, hx29_4]
      · unfold tryDecryptCommonHeap signalMessageAt speBodyAt
        rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            stackAt_ext_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_split s0.sp]
        have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
        clear hmf hmf1
        simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
        rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
        sep_close

theorem aesDecrypt_none_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hS : TripleRatchetHooks C A S abs)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = none)
    (h8 : AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
      (ErrTailState A ctl img x trG tr st1
        (.invalidMessage x.msgType .badCiphertext) draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) :=
  aesDecrypt_none_ok_ext img C A ctl S (tripleRatchetExterns C ctl abs) himg (Stage2Contracts.of_tripleRatchetProgAt' hS)
    x trG tr st1 mks newPqrState draws R s0 s hd h8 hL

theorem aesDecrypt_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) :
    S8SpecExt img C A ctl uuidTryParse S ext := by
  intro himg hC x trG tr st1 mks newPqrState draws R s0 s h8 hL
  cases hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
  | none =>
    exact aesDecrypt_none_ok_ext img C A ctl S ext himg hC x trG tr st1 mks newPqrState draws R s0 s hd h8 hL
  | some pt =>
    exact aesDecrypt_some_ok_ext img C A ctl S ext himg hC x trG tr st1 mks newPqrState pt draws R s0 s hd h8 hL

theorem aesDecrypt_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) :
    AesDecryptSpec img C A ctl uuidTryParse S abs :=
  fun himg hS => aesDecrypt_ok_ext img C A ctl S (tripleRatchetExterns C ctl abs) himg (Stage2Contracts.of_tripleRatchetProgAt' hS)

theorem aesDecrypt_some_ok_x (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hC : Stage2ContractsX img C A encFn decFn ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState pt : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (CBC.blockToBytesLE mks.iv) = some pt)
    (h8 : AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (ApplyRatchetState A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have hfn := hfn_tryDecrypt
  have haes := aesDec_ok_at_x img C A encFn decFn ext hC
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  rw [segS8PC_eq_ext himg ext] at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic
    ((libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr tryDecryptName + 1700#64)
    hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  decrypt_fetches_ext img.base ext hfn 0x678 44
  have hS9_pc : segApplyRatchetPC img = (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr tryDecryptName + 1700#64 :=
    segS9PC_eq_ext himg ext
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr tryDecryptName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP_frozen hfl hsym (mid := entry + bv% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hfl1 hsym1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_inImage_frame (img := img) (spec := aesDecFnSpec decFn A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := entry + bv% (1688))
    hfl1 hsym1 haes (by rfl) (by exact hstat)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecFnSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      tryDecryptFn_onPanic_of_callee C decFn A ctl S img x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hfl1 hsym1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hfl2 hsym2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecFnSpec, AesCall.frame]
    rw [hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
      (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
    have hcap_ne : ptCap + 1#64 ≠ 0#64 := add_one_ne_zero_of_lt_2_63 hpt_lt
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl2 hsym2 (mid := entry + bv% (1700))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun2)
    intro hfl3 hsym3
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by rfl) (by exact hrun2)
    intro _ _ hmf
    refine ⟨?_, ⟨hrun2, hsp2, hsp0,
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2, ?_, htr2, hfl3, hsym3, by simp only [wp_norm, hvregs_2]⟩,
      by simp only [wp_norm, hx19_2],
      by simp only [wp_norm, hx20_2],
      by simp only [wp_norm, hx21_2],
      by simp only [wp_norm, hx23_2],
      by simp only [wp_norm, hx24_2],
      newPqrCap, newPqrPtr, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
    · rw [hS9_pc]; rfl
    · simp only [wp_norm, hx29_2]
    · unfold tryDecryptCommonHeap signalMessageAt
      rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
          stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
          applyRatchet_reg10_split (s0.sp - 1504#64),
          applyRatchet_reg3e8_split (s0.sp - 1504#64)]
      have hvec := vecU8At_parts_entails_vecU8' A (s0.sp - 528#64) ptCap ptPtr pt hpt_le hpt_lt hpt_nz
      have hmf1 := Satisfies.mono_focus hvec (by sep_focus) hmf
      have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
      have hmf3 := Satisfies.mono_focus (applyRatchet_sp_entails_memRegion s0.sp msgW x.locA x.remA) (by sep_focus) hmf2
      clear hmf hmf1 hmf2
      simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf3 ⊢
      rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
      sep_close

theorem aesDecrypt_none_ok_x (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hC : Stage2ContractsX img C A encFn decFn ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (CBC.blockToBytesLE mks.iv) = none)
    (h8 : AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (ErrTailStateX A ctl img x trG tr st1
        (.invalidMessage x.msgType .badCiphertext) draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have hfn := hfn_tryDecrypt
  have haes := aesDec_ok_at_x img C A encFn decFn ext hC
  have hfmt := formatInner_ok_at_x img C A encFn decFn ext hC
  have hdealloc := dealloc_ok_at_x img C A encFn decFn ext hC
  have hlog_c00 := logOff_eq_at_c00_ext himg ext
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  rw [segS8PC_eq_ext himg ext] at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic
    ((libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr tryDecryptName + 780#64)
    hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  decrypt_fetches_ext img.base ext hfn 0x678 44
  decrypt_fetches_ext img.base ext hfn 0xa1c 88
  decrypt_fetches_ext img.base ext hfn 0xc00 16
  decrypt_fetches_ext img.base ext hfn 0xc70 40
  decrypt_fetches_ext img.base ext hfn 0x964 8
  decrypt_fetches_ext img.base ext hfn 0x9d0 12
  have hErr_pc : errTailPC img = (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr tryDecryptName + 780#64 :=
    errTailPC_eq_ext himg ext
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr tryDecryptName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP_frozen hfl hsym (mid := entry + bv% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hfl1 hsym1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_inImage_frame (img := img) (spec := aesDecFnSpec decFn A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := entry + bv% (1688))
    hfl1 hsym1 haes (by rfl) (by exact hstat)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecFnSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      tryDecryptFn_onPanic_of_callee C decFn A ctl S img x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hfl1 hsym1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hfl2 hsym2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecFnSpec, AesCall.frame]
    rw [hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    simp only [← sepConj_assoc]
    refine SepWPp.mono_focus (aesDecrypt_none_prep_x s0.sp) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 520#64) (by sep_focus) fun p => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 512#64) (by sep_focus) fun w512 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun b1120 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1104#64) (by sep_focus) fun w1104 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1096#64) (by sep_focus) fun w1096 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 480#64) (by sep_focus) fun w480 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 472#64) (by sep_focus) fun w472 => ?_
    by_cases hp : p = 0#64
    · -- p = 0#64 (`DecodeError = 0`): cbz x8, 0x34f9c (+0xc00) -> +0xc70 -> ErrTailStateX (b = false)
      rw [aesDecrypt_none_reg1144_split s0.sp, hlog_c00]
      simp only [sepConj_assoc]
      refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
      refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
      simp only [← sepConj_assoc]
      by_cases hpqr_cap : newPqrCap = 0#64
      · refine SepWPp.mono_focus (newPqr_zero_prep A newPqrCap newPqrPtr newPqrState hpqr_cap) (by sep_focus) ?_
        rw [emp_sepConj]
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_frozen hfl2 hsym2 (mid := entry + bv% (780))
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun2)
        intro hfl3 hsym3
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun2)
        intro _ _ hmf
        refine ⟨?_, ⟨hrun2, hsp2, hsp0,
            AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2, ?_, htr2, hfl3, hsym3, by simp only [wp_norm, hvregs_2]⟩,
          by simp only [wp_norm, hx19_2],
          by simp only [wp_norm, hx20_2],
          false, fun _ => rfl,
          by simp only [wp_norm]; rfl, ?_⟩
        · rw [hErr_pc]; rfl
        · simp only [wp_norm, hx29_2]
        · unfold tryDecryptCommonHeap signalMessageAt
          rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp,
              hlog_c00]
          have hmf0 := Satisfies.mono_focus (aesDecrypt_none_p0_spe_entails_memRegion s0.sp _ _ b1120) (by sep_focus) hmf
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf0
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA w1104 w1096 errTag p w512 w480 w472 msgW) (by sep_focus) hmf1
          clear hmf hmf0 hmf1
          simp only [wp_norm, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close
      · refine SepWPp.mono_focus (newPqr_dealloc_prep' A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_frozen hfl2 hsym2 (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun2)
        intro hfl2' hsym2'
        refine SepWPp.call_inImage_frame (img := img) (spec := rustDeallocExternSpecWithStack A extHookStack)
          (x := (newPqrPtr, newPqrCap.toNat, 1))
          (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
                memRegion newPqrPtr newPqrCap.toNat ∗
                stackAt (s0.sp - 1504#64) extHookStack)
          (ret_pc := entry + bv% (2520))
          hfl2' hsym2' hdealloc (by rfl) (by exact hrun2)
          (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
          (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp2]; rfl)
          (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm], layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt⟩)
          (by sep_focus)
          (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
          (fun sf _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
        clear hfl2' hsym2'
        intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hfl4 hsym4
        simp only [wp_norm, hsp2] at hsp4
        rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
        simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
        dsimp only [rustDeallocExternSpecWithStack]
        simp only [wp_norm, hsp2, sepConj_assoc]
        apply SepWPp.elim_pure; intro htr4
        simp only [htr2] at htr4
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_frozen hfl4 hsym4 (mid := entry + bv% (780))
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun4)
        intro hfl5 hsym5
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun4)
        intro _ _ hmf
        refine ⟨?_, ⟨hrun4, hsp4, hsp0,
            AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4, ?_, htr4, hfl5, hsym5, by simp only [wp_norm, hvregs_4]⟩,
          by simp only [wp_norm, hx19_4],
          by simp only [wp_norm, hx20_4],
          false, fun _ => rfl,
          by simp only [wp_norm, hx26_4]; rfl, ?_⟩
        · rw [hErr_pc]; rfl
        · simp only [wp_norm, hx29_4]
        · unfold tryDecryptCommonHeap signalMessageAt
          rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp,
              hlog_c00]
          have hmf0 := Satisfies.mono_focus (aesDecrypt_none_p0_spe_entails_memRegion s0.sp _ _ b1120) (by sep_focus) hmf
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf0
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA w1104 w1096 errTag p w512 w480 w472 msgW) (by sep_focus) hmf1
          clear hmf hmf0 hmf1
          simp only [wp_norm, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close
    · -- p ≠ 0#64: cbz x8 not taken -> bl format_inner -> ErrTailState.toX (b = true)
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_frozen hfl2 hsym2 (mid := entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun2)
      intro hfl2' hsym2'
      refine SepWPp.call_inImage_frame (img := img) (spec := formatInnerSpec A)
        (x := s0.sp - 1144#64)
        (T := memRegion (s0.sp - 1144#64) 24 ∗ A.pool ∗
              stackAt (s0.sp - 1504#64) extHookStack)
        (ret_pc := entry + bv% (2656))
        hfl2' hsym2' hfmt (by rfl) (by exact hrun2)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
        (by dsimp only [formatInnerSpec]; simp only [wp_norm, hsp2]; rfl)
        (by simp only [wp_norm]) (by sep_focus)
        (fun _ _ _ _ h => allowPanic_not_exited h)
        (fun sf hpan _ hm_pan =>
          tryDecryptFn_onPanic_of_callee C decFn A ctl S img x s0 _ sf _ R
            (htr2 ▸ List.prefix_refl _) hm_pan) ?_
      clear hfl2' hsym2'
      intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hfl3 hsym3
      simp only [wp_norm, hsp2] at hsp3
      rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
      simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
      dsimp only [formatInnerSpec]
      simp only [wp_norm, hsp2, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr3
      simp only [htr2] at htr3
      rw [formatInner_post_eq_badCiphertext A s0.sp]
      simp only [← sepConj_assoc]
      by_cases hpqr_cap : newPqrCap = 0#64
      · refine SepWPp.mono_focus (newPqr_zero_prep A newPqrCap newPqrPtr newPqrState hpqr_cap) (by sep_focus) ?_
        rw [emp_sepConj]
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_frozen hfl3 hsym3 (mid := entry + bv% (780))
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun3)
        intro hfl4 hsym4
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun3)
        intro _ _ hmf
        refine ErrTailState.toX ⟨?_, ⟨hrun3, hsp3, hsp0,
            AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3, ?_, htr3, hfl4, hsym4, by simp only [wp_norm, hvregs_3]⟩,
          by simp only [wp_norm, hx19_3],
          by simp only [wp_norm, hx20_3],
          by simp only [wp_norm, hx26_3]; rfl, ?_⟩
        · rw [hErr_pc]; rfl
        · simp only [wp_norm, hx29_3]
        · unfold tryDecryptCommonHeap signalMessageAt speBodyAt
          rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp]
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
          clear hmf hmf1
          simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close
      · refine SepWPp.mono_focus (newPqr_dealloc_prep' A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_frozen hfl3 hsym3 (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun3)
        intro hfl3' hsym3'
        refine SepWPp.call_inImage_frame (img := img) (spec := rustDeallocExternSpecWithStack A extHookStack)
          (x := (newPqrPtr, newPqrCap.toNat, 1))
          (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
                memRegion newPqrPtr newPqrCap.toNat ∗
                stackAt (s0.sp - 1504#64) extHookStack)
          (ret_pc := entry + bv% (2520))
          hfl3' hsym3' hdealloc (by rfl) (by exact hrun3)
          (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
          (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp3]; rfl)
          (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm], layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt⟩)
          (by sep_focus)
          (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
          (fun sf _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
        clear hfl3' hsym3'
        intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hfl4 hsym4
        simp only [wp_norm, hsp3] at hsp4
        rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
        simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
        dsimp only [rustDeallocExternSpecWithStack]
        simp only [wp_norm, hsp3, sepConj_assoc]
        apply SepWPp.elim_pure; intro htr4
        simp only [htr3] at htr4
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_frozen hfl4 hsym4 (mid := entry + bv% (780))
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun4)
        intro hfl5 hsym5
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun4)
        intro _ _ hmf
        refine ErrTailState.toX ⟨?_, ⟨hrun4, hsp4, hsp0,
            AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4, ?_, htr4, hfl5, hsym5, by simp only [wp_norm, hvregs_4]⟩,
          by simp only [wp_norm, hx19_4],
          by simp only [wp_norm, hx20_4],
          by simp only [wp_norm, hx26_4]; rfl, ?_⟩
        · rw [hErr_pc]; rfl
        · simp only [wp_norm, hx29_4]
        · unfold tryDecryptCommonHeap signalMessageAt speBodyAt
          rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp]
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
          clear hmf hmf1
          simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close

theorem aesDecrypt_ok_x (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State)) :
    S8SpecX img C encFn decFn A ctl uuidTryParse S ext := by
  intro himg hC x trG tr st1 mks newPqrState draws R s0 s h8 hL
  cases hd : decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (CBC.blockToBytesLE mks.iv) with
  | none =>
    exact aesDecrypt_none_ok_x img C A ctl S encFn decFn ext himg hC x trG tr st1 mks newPqrState draws R s0 s hd h8 hL
  | some pt =>
    exact aesDecrypt_some_ok_x img C A ctl S encFn decFn ext himg hC x trG tr st1 mks newPqrState pt draws R s0 s hd h8 hL

/-! ## Relocatable `[LibsignalPlacement]` Segment 8 Proofs (Blocks `130` and `549`) -/

abbrev lsAesDecSym : String :=
  "_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_decrypt"

abbrev lsFormatInnerSym : String :=
  "_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_inner"

theorem aesDecrypt_some_159_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsAesDecSym) (aesDecSpec C.D A))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState pt : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = some pt)
    (h8 : AesDecryptStatePlaced (blkPl_131).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_131).rebase (blkPl_131).base H) s s' ∧
      (ApplyRatchetStatePlaced (blkPl_131).base A ctl x trG tr st1 newPqrState pt draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_131).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_131).base + 1700#64) hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl (mid := lsρ lsAesDecSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hcl1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_frame_placed (spec := aesDecSpec C.D A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_131).base + 1688#64)
    hcl1 haes (by rfl) (by exact hstat)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hcl1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecSpec, AesCall.frame]
    rw [bytesToKey32_keyToBytes32, bytesToBlock_blockToBytesLE, hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
      (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
    have hcap_ne : ptCap + 1#64 ≠ 0#64 := add_one_ne_zero_of_lt_2_63 hpt_lt
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_131).base + 1700#64)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun2)
    intro hcl3
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by rfl) (by exact hrun2)
    intro _ _ hmf
    refine ⟨rfl, ⟨hrun2, hsp2, hsp0,
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2, ?_, htr2, hcl3, by simp only [wp_norm, hvregs_2]⟩,
      by simp only [wp_norm, hx19_2],
      by simp only [wp_norm, hx20_2],
      by simp only [wp_norm, hx21_2],
      by simp only [wp_norm, hx23_2],
      by simp only [wp_norm, hx24_2],
      newPqrCap, newPqrPtr, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
    · simp only [wp_norm, hx29_2]
    · unfold tryDecryptCommonHeap signalMessageAt
      rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
          stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
          applyRatchet_reg10_split (s0.sp - 1504#64),
          applyRatchet_reg3e8_split (s0.sp - 1504#64)]
      have hvec := vecU8At_parts_entails_vecU8' A (s0.sp - 528#64) ptCap ptPtr pt hpt_le hpt_lt hpt_nz
      have hmf1 := Satisfies.mono_focus hvec (by sep_focus) hmf
      have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
      have hmf3 := Satisfies.mono_focus (applyRatchet_sp_entails_memRegion s0.sp msgW x.locA x.remA) (by sep_focus) hmf2
      clear hmf hmf1 hmf2
      simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf3 ⊢
      rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
      sep_close

theorem aesDecrypt_none_159_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsAesDecSym) (aesDecSpec C.D A))
    (hfmt : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = none)
    (h8 : AesDecryptStatePlaced (blkPl_131).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_131).rebase (blkPl_131).base H) s s' ∧
      (ErrTailStatePlaced (blkPl_131).base A ctl x trG tr st1
        (.invalidMessage x.msgType .badCiphertext) draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_131).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_131).base + 780#64) hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl (mid := lsρ lsAesDecSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hcl1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_frame_placed (spec := aesDecSpec C.D A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_131).base + 1688#64)
    hcl1 haes (by rfl) (by exact hstat)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hcl1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecSpec, AesCall.frame]
    rw [bytesToKey32_keyToBytes32, bytesToBlock_blockToBytesLE, hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    refine SepWPp.elim_exists_focus
      (Φ := fun p : BitVec 64 => ⌜p ≠ 0⌝ ∗ ((s0.sp - 520#64) ↦₆₄ p))
      (by sep_focus) fun p => ?_
    simp only [sepConj_assoc]
    apply SepWPp.elim_pure; intro hp_nz
    simp only [← sepConj_assoc]
    refine SepWPp.mono_focus (aesDecrypt_none_prep s0.sp) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 512#64) (by sep_focus) fun w512 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun b1120 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1104#64) (by sep_focus) fun w1104 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1096#64) (by sep_focus) fun w1096 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 480#64) (by sep_focus) fun w480 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 472#64) (by sep_focus) fun w472 => ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsFormatInnerSym)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun2)
    intro hcl2'
    refine SepWPp.call_frame_placed (spec := formatInnerSpec A)
      (x := s0.sp - 1144#64)
      (T := memRegion (s0.sp - 1144#64) 24 ∗ A.pool ∗
            stackAt (s0.sp - 1504#64) extHookStack)
      (ret_pc := (blkPl_131).base + 2656#64)
      hcl2' hfmt (by rfl) (by exact hrun2)
      (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
      (by dsimp only [formatInnerSpec]; simp only [wp_norm, hsp2]; rfl)
      (by simp only [wp_norm]) (by sep_focus)
      (fun _ _ _ _ h => allowPanic_not_exited h)
      (fun sf hpan _ hm_pan =>
        tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R
          (htr2 ▸ List.prefix_refl _) hm_pan) ?_
    clear hcl2'
    intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
    simp only [wp_norm, hsp2] at hsp3
    rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
    simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
    dsimp only [formatInnerSpec]
    simp only [wp_norm, hsp2, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr3
    simp only [htr2] at htr3
    rw [formatInner_post_eq_badCiphertext A s0.sp]
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · refine SepWPp.mono_focus (newPqr_zero_prep A newPqrCap newPqrPtr newPqrState hpqr_cap) (by sep_focus) ?_
      rw [emp_sepConj]
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_131).base + 780#64)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl4
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun3)
      intro _ _ hmf
      refine ⟨rfl, ⟨hrun3, hsp3, hsp0,
          AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3, ?_, htr3, hcl4, by simp only [wp_norm, hvregs_3]⟩,
        by simp only [wp_norm, hx19_3],
        by simp only [wp_norm, hx20_3],
        by simp only [wp_norm, hx26_3]; rfl, ?_⟩
      · simp only [wp_norm, hx29_3]
      · unfold tryDecryptCommonHeap signalMessageAt speBodyAt
        rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_split s0.sp]
        have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
        clear hmf hmf1
        simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
        rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
        sep_close
    · refine SepWPp.mono_focus (newPqr_dealloc_prep' A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
      rw [stackAt_ext_split_alloc (s0.sp - 1504#64)]
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl3 (mid := lsρ lsRustDeallocSym)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl3'
      refine SepWPp.call_frame_placed (spec := rustDeallocSpec A)
        (x := (newPqrPtr, newPqrCap.toNat, 1))
        (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) allocHookStack)
        (ret_pc := (blkPl_131).base + 2520#64)
        hcl3' hdealloc (by rfl) (by exact hrun3)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustDeallocSpec]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [rustDeallocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun sf _ _ hm_pan => by dsimp only [rustDeallocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hcl3'
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustDeallocSpec]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr4
      simp only [htr3] at htr4
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_131).base + 780#64)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun4)
      intro hcl5
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun4)
      intro _ _ hmf
      refine ⟨rfl, ⟨hrun4, hsp4, hsp0,
          AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4, ?_, htr4, hcl5, by simp only [wp_norm, hvregs_4]⟩,
        by simp only [wp_norm, hx19_4],
        by simp only [wp_norm, hx20_4],
        by simp only [wp_norm, hx26_4]; rfl, ?_⟩
      · simp only [wp_norm, hx29_4]
      · unfold tryDecryptCommonHeap signalMessageAt speBodyAt
        rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            stackAt_ext_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_split s0.sp]
        have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
        clear hmf hmf1
        simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
        rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
        sep_close

theorem aesDecrypt_159_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsAesDecSym) (aesDecSpec C.D A))
    (hfmt : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S8SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S := by
  intro x trG tr st1 mks newPqrState draws R s0 s h8 hL
  cases hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
  | none =>
    exact aesDecrypt_none_159_placed_ok C A ctl S H haes hfmt hdealloc x trG tr st1 mks newPqrState draws R s0 s hd h8 hL
  | some pt =>
    exact aesDecrypt_some_159_placed_ok C A ctl S H haes x trG tr st1 mks newPqrState pt draws R s0 s hd h8 hL

theorem aesDecrypt_some_159_placed_ok_x [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsAesDecSym) (aesDecFnSpec decFn A))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState pt : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (CBC.blockToBytesLE mks.iv) = some pt)
    (h8 : AesDecryptStatePlaced (blkPl_131).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_131).rebase (blkPl_131).base H) s s' ∧
      (ApplyRatchetStatePlaced (blkPl_131).base A ctl x trG tr st1 newPqrState pt draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_131).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_131).base + 1700#64) hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl (mid := lsρ lsAesDecSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hcl1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_frame_placed (spec := aesDecFnSpec decFn A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_131).base + 1688#64)
    hcl1 haes (by rfl) (by exact hstat)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecFnSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      tryDecryptFn_onPanic_of_callee_placed C decFn A ctl S x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hcl1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecFnSpec, AesCall.frame]
    rw [hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
      (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
    have hcap_ne : ptCap + 1#64 ≠ 0#64 := add_one_ne_zero_of_lt_2_63 hpt_lt
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_131).base + 1700#64)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun2)
    intro hcl3
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by rfl) (by exact hrun2)
    intro _ _ hmf
    refine ⟨rfl, ⟨hrun2, hsp2, hsp0,
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2, ?_, htr2, hcl3, by simp only [wp_norm, hvregs_2]⟩,
      by simp only [wp_norm, hx19_2],
      by simp only [wp_norm, hx20_2],
      by simp only [wp_norm, hx21_2],
      by simp only [wp_norm, hx23_2],
      by simp only [wp_norm, hx24_2],
      newPqrCap, newPqrPtr, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
    · simp only [wp_norm, hx29_2]
    · unfold tryDecryptCommonHeap signalMessageAt
      rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
          stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
          applyRatchet_reg10_split (s0.sp - 1504#64),
          applyRatchet_reg3e8_split (s0.sp - 1504#64)]
      have hvec := vecU8At_parts_entails_vecU8' A (s0.sp - 528#64) ptCap ptPtr pt hpt_le hpt_lt hpt_nz
      have hmf1 := Satisfies.mono_focus hvec (by sep_focus) hmf
      have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
      have hmf3 := Satisfies.mono_focus (applyRatchet_sp_entails_memRegion s0.sp msgW x.locA x.remA) (by sep_focus) hmf2
      clear hmf hmf1 hmf2
      simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf3 ⊢
      rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
      sep_close

theorem aesDecrypt_none_159_placed_ok_x [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsAesDecSym) (aesDecFnSpec decFn A))
    (hfmt : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A extHookStack))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (CBC.blockToBytesLE mks.iv) = none)
    (h8 : AesDecryptStatePlaced (blkPl_131).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_131).rebase (blkPl_131).base H) s s' ∧
      (ErrTailStateXPlaced (blkPl_131).base A ctl x trG tr st1
        (.invalidMessage x.msgType .badCiphertext) draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  have hlog_c00 := logOff_eq_placed
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_131).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_131).base + 780#64) hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl (mid := lsρ lsAesDecSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hcl1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_frame_placed (spec := aesDecFnSpec decFn A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_131).base + 1688#64)
    hcl1 haes (by rfl) (by exact hstat)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecFnSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      tryDecryptFn_onPanic_of_callee_placed C decFn A ctl S x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hcl1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecFnSpec, AesCall.frame]
    rw [hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    simp only [← sepConj_assoc]
    refine SepWPp.mono_focus (aesDecrypt_none_prep_x s0.sp) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 520#64) (by sep_focus) fun p => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 512#64) (by sep_focus) fun w512 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun b1120 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1104#64) (by sep_focus) fun w1104 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1096#64) (by sep_focus) fun w1096 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 480#64) (by sep_focus) fun w480 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 472#64) (by sep_focus) fun w472 => ?_
    by_cases hp : p = 0#64
    · rw [aesDecrypt_none_reg1144_split s0.sp]
      simp only [sepConj_assoc]
      refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
      refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
      simp only [← sepConj_assoc]
      by_cases hpqr_cap : newPqrCap = 0#64
      · refine SepWPp.mono_focus (newPqr_zero_prep A newPqrCap newPqrPtr newPqrState hpqr_cap) (by sep_focus) ?_
        rw [emp_sepConj]
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_131).base + 780#64)
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun2)
        intro hcl3
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun2)
        intro _ _ hmf
        refine ⟨rfl, ⟨hrun2, hsp2, hsp0,
            AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2, ?_, htr2, hcl3, by simp only [wp_norm, hvregs_2]⟩,
          by simp only [wp_norm, hx19_2],
          by simp only [wp_norm, hx20_2],
          false, fun _ => rfl,
          by simp only [wp_norm]; rfl, ?_⟩
        · simp only [wp_norm, hx29_2]
        · unfold tryDecryptCommonHeap signalMessageAt
          rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp,
              hlog_c00]
          have hmf0 := Satisfies.mono_focus (aesDecrypt_none_p0_spe_entails_memRegion s0.sp _ _ b1120) (by sep_focus) hmf
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf0
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA w1104 w1096 errTag p w512 w480 w472 msgW) (by sep_focus) hmf1
          clear hmf hmf0 hmf1
          simp only [wp_norm, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close
      · refine SepWPp.mono_focus (newPqr_dealloc_prep' A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsRustDeallocSym)
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun2)
        intro hcl2'
        refine SepWPp.call_frame_placed (spec := rustDeallocExternSpecWithStack A extHookStack)
          (x := (newPqrPtr, newPqrCap.toNat, 1))
          (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
                memRegion newPqrPtr newPqrCap.toNat ∗
                stackAt (s0.sp - 1504#64) extHookStack)
          (ret_pc := (blkPl_131).base + 2520#64)
          hcl2' hdealloc (by rfl) (by exact hrun2)
          (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
          (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp2]; rfl)
          (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm], layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt⟩)
          (by sep_focus)
          (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
          (fun sf _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
        clear hcl2'
        intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
        simp only [wp_norm, hsp2] at hsp4
        rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
        simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
        dsimp only [rustDeallocExternSpecWithStack]
        simp only [wp_norm, hsp2, sepConj_assoc]
        apply SepWPp.elim_pure; intro htr4
        simp only [htr2] at htr4
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_131).base + 780#64)
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun4)
        intro hcl5
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun4)
        intro _ _ hmf
        refine ⟨rfl, ⟨hrun4, hsp4, hsp0,
            AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4, ?_, htr4, hcl5, by simp only [wp_norm, hvregs_4]⟩,
          by simp only [wp_norm, hx19_4],
          by simp only [wp_norm, hx20_4],
          false, fun _ => rfl,
          by simp only [wp_norm, hx26_4]; rfl, ?_⟩
        · simp only [wp_norm, hx29_4]
        · unfold tryDecryptCommonHeap signalMessageAt
          rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp,
              hlog_c00]
          have hmf0 := Satisfies.mono_focus (aesDecrypt_none_p0_spe_entails_memRegion s0.sp _ _ b1120) (by sep_focus) hmf
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf0
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA w1104 w1096 errTag p w512 w480 w472 msgW) (by sep_focus) hmf1
          clear hmf hmf0 hmf1
          simp only [wp_norm, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close
    · simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsFormatInnerSym)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun2)
      intro hcl2'
      refine SepWPp.call_frame_placed (spec := formatInnerSpec A)
        (x := s0.sp - 1144#64)
        (T := memRegion (s0.sp - 1144#64) 24 ∗ A.pool ∗
              stackAt (s0.sp - 1504#64) extHookStack)
        (ret_pc := (blkPl_131).base + 2656#64)
        hcl2' hfmt (by rfl) (by exact hrun2)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
        (by dsimp only [formatInnerSpec]; simp only [wp_norm, hsp2]; rfl)
        (by simp only [wp_norm]) (by sep_focus)
        (fun _ _ _ _ h => allowPanic_not_exited h)
        (fun sf hpan _ hm_pan =>
          tryDecryptFn_onPanic_of_callee_placed C decFn A ctl S x s0 _ sf _ R
            (htr2 ▸ List.prefix_refl _) hm_pan) ?_
      clear hcl2'
      intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
      simp only [wp_norm, hsp2] at hsp3
      rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
      simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
      dsimp only [formatInnerSpec]
      simp only [wp_norm, hsp2, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr3
      simp only [htr2] at htr3
      rw [formatInner_post_eq_badCiphertext A s0.sp]
      simp only [← sepConj_assoc]
      by_cases hpqr_cap : newPqrCap = 0#64
      · refine SepWPp.mono_focus (newPqr_zero_prep A newPqrCap newPqrPtr newPqrState hpqr_cap) (by sep_focus) ?_
        rw [emp_sepConj]
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_131).base + 780#64)
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun3)
        intro hcl4
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun3)
        intro _ _ hmf
        refine ErrTailStatePlaced.toX ⟨rfl, ⟨hrun3, hsp3, hsp0,
            AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3, ?_, htr3, hcl4, by simp only [wp_norm, hvregs_3]⟩,
          by simp only [wp_norm, hx19_3],
          by simp only [wp_norm, hx20_3],
          by simp only [wp_norm, hx26_3]; rfl, ?_⟩
        · simp only [wp_norm, hx29_3]
        · unfold tryDecryptCommonHeap signalMessageAt speBodyAt
          rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp]
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
          clear hmf hmf1
          simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close
      · refine SepWPp.mono_focus (newPqr_dealloc_prep' A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl3 (mid := lsρ lsRustDeallocSym)
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun3)
        intro hcl3'
        refine SepWPp.call_frame_placed (spec := rustDeallocExternSpecWithStack A extHookStack)
          (x := (newPqrPtr, newPqrCap.toNat, 1))
          (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
                memRegion newPqrPtr newPqrCap.toNat ∗
                stackAt (s0.sp - 1504#64) extHookStack)
          (ret_pc := (blkPl_131).base + 2520#64)
          hcl3' hdealloc (by rfl) (by exact hrun3)
          (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
          (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp3]; rfl)
          (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm], layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt⟩)
          (by sep_focus)
          (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
          (fun sf _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
        clear hcl3'
        intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
        simp only [wp_norm, hsp3] at hsp4
        rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
        simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
        dsimp only [rustDeallocExternSpecWithStack]
        simp only [wp_norm, hsp3, sepConj_assoc]
        apply SepWPp.elim_pure; intro htr4
        simp only [htr3] at htr4
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_131).base + 780#64)
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun4)
        intro hcl5
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun4)
        intro _ _ hmf
        refine ErrTailStatePlaced.toX ⟨rfl, ⟨hrun4, hsp4, hsp0,
            AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4, ?_, htr4, hcl5, by simp only [wp_norm, hvregs_4]⟩,
          by simp only [wp_norm, hx19_4],
          by simp only [wp_norm, hx20_4],
          by simp only [wp_norm, hx26_4]; rfl, ?_⟩
        · simp only [wp_norm, hx29_4]
        · unfold tryDecryptCommonHeap signalMessageAt speBodyAt
          rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp]
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
          clear hmf hmf1
          simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close

theorem aesDecrypt_159_placed_ok_x [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsAesDecSym) (aesDecFnSpec decFn A))
    (hfmt : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A extHookStack)) :
    S8SeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C decFn A ctl uuidTryParse S := by
  intro x trG tr st1 mks newPqrState draws R s0 s h8 hL
  cases hd : decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (CBC.blockToBytesLE mks.iv) with
  | none =>
    exact aesDecrypt_none_159_placed_ok_x C A ctl S decFn H haes hfmt hdealloc x trG tr st1 mks newPqrState draws R s0 s hd h8 hL
  | some pt =>
    exact aesDecrypt_some_159_placed_ok_x C A ctl S decFn H haes x trG tr st1 mks newPqrState pt draws R s0 s hd h8 hL

theorem aesDecrypt_some_549_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsAesDecSym) (aesDecSpec C.D A))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState pt : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = some pt)
    (h8 : AesDecryptStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      (ApplyRatchetStatePlaced (blkPl_434).base A ctl x trG tr st1 newPqrState pt draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_434).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + 1700#64) hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl (mid := lsρ lsAesDecSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hcl1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_frame_placed (spec := aesDecSpec C.D A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_434).base + 1688#64)
    hcl1 haes (by rfl) (by exact hstat)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hcl1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecSpec, AesCall.frame]
    rw [bytesToKey32_keyToBytes32, bytesToBlock_blockToBytesLE, hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
      (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
    have hcap_ne : ptCap + 1#64 ≠ 0#64 := add_one_ne_zero_of_lt_2_63 hpt_lt
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_434).base + 1700#64)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun2)
    intro hcl3
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by rfl) (by exact hrun2)
    intro _ _ hmf
    refine ⟨rfl, ⟨hrun2, hsp2, hsp0,
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2, ?_, htr2, hcl3, by simp only [wp_norm, hvregs_2]⟩,
      by simp only [wp_norm, hx19_2],
      by simp only [wp_norm, hx20_2],
      by simp only [wp_norm, hx21_2],
      by simp only [wp_norm, hx23_2],
      by simp only [wp_norm, hx24_2],
      newPqrCap, newPqrPtr, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
    · simp only [wp_norm, hx29_2]
    · unfold tryDecryptCommonHeap signalMessageAt
      rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
          stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
          applyRatchet_reg10_split (s0.sp - 1504#64),
          applyRatchet_reg3e8_split (s0.sp - 1504#64)]
      have hvec := vecU8At_parts_entails_vecU8' A (s0.sp - 528#64) ptCap ptPtr pt hpt_le hpt_lt hpt_nz
      have hmf1 := Satisfies.mono_focus hvec (by sep_focus) hmf
      have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
      have hmf3 := Satisfies.mono_focus (applyRatchet_sp_entails_memRegion s0.sp msgW x.locA x.remA) (by sep_focus) hmf2
      clear hmf hmf1 hmf2
      simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf3 ⊢
      rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
      sep_close

theorem aesDecrypt_none_549_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsAesDecSym) (aesDecSpec C.D A))
    (hfmt : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = none)
    (h8 : AesDecryptStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      (ErrTailStatePlaced (blkPl_434).base A ctl x trG tr st1
        (.invalidMessage x.msgType .badCiphertext) draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_434).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + 780#64) hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl (mid := lsρ lsAesDecSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hcl1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_frame_placed (spec := aesDecSpec C.D A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_434).base + 1688#64)
    hcl1 haes (by rfl) (by exact hstat)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hcl1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecSpec, AesCall.frame]
    rw [bytesToKey32_keyToBytes32, bytesToBlock_blockToBytesLE, hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    refine SepWPp.elim_exists_focus
      (Φ := fun p : BitVec 64 => ⌜p ≠ 0⌝ ∗ ((s0.sp - 520#64) ↦₆₄ p))
      (by sep_focus) fun p => ?_
    simp only [sepConj_assoc]
    apply SepWPp.elim_pure; intro hp_nz
    simp only [← sepConj_assoc]
    refine SepWPp.mono_focus (aesDecrypt_none_prep s0.sp) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 512#64) (by sep_focus) fun w512 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun b1120 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1104#64) (by sep_focus) fun w1104 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1096#64) (by sep_focus) fun w1096 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 480#64) (by sep_focus) fun w480 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 472#64) (by sep_focus) fun w472 => ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsFormatInnerSym)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun2)
    intro hcl2'
    refine SepWPp.call_frame_placed (spec := formatInnerSpec A)
      (x := s0.sp - 1144#64)
      (T := memRegion (s0.sp - 1144#64) 24 ∗ A.pool ∗
            stackAt (s0.sp - 1504#64) extHookStack)
      (ret_pc := (blkPl_434).base + 2656#64)
      hcl2' hfmt (by rfl) (by exact hrun2)
      (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
      (by dsimp only [formatInnerSpec]; simp only [wp_norm, hsp2]; rfl)
      (by simp only [wp_norm]) (by sep_focus)
      (fun _ _ _ _ h => allowPanic_not_exited h)
      (fun sf hpan _ hm_pan =>
        tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R
          (htr2 ▸ List.prefix_refl _) hm_pan) ?_
    clear hcl2'
    intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
    simp only [wp_norm, hsp2] at hsp3
    rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
    simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
    dsimp only [formatInnerSpec]
    simp only [wp_norm, hsp2, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr3
    simp only [htr2] at htr3
    rw [formatInner_post_eq_badCiphertext A s0.sp]
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · refine SepWPp.mono_focus (newPqr_zero_prep A newPqrCap newPqrPtr newPqrState hpqr_cap) (by sep_focus) ?_
      rw [emp_sepConj]
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_434).base + 780#64)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl4
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun3)
      intro _ _ hmf
      refine ⟨rfl, ⟨hrun3, hsp3, hsp0,
          AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3, ?_, htr3, hcl4, by simp only [wp_norm, hvregs_3]⟩,
        by simp only [wp_norm, hx19_3],
        by simp only [wp_norm, hx20_3],
        by simp only [wp_norm, hx26_3]; rfl, ?_⟩
      · simp only [wp_norm, hx29_3]
      · unfold tryDecryptCommonHeap signalMessageAt speBodyAt
        rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_split s0.sp]
        have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
        clear hmf hmf1
        simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
        rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
        sep_close
    · refine SepWPp.mono_focus (newPqr_dealloc_prep' A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
      rw [stackAt_ext_split_alloc (s0.sp - 1504#64)]
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl3 (mid := lsρ lsRustDeallocSym)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl3'
      refine SepWPp.call_frame_placed (spec := rustDeallocSpec A)
        (x := (newPqrPtr, newPqrCap.toNat, 1))
        (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) allocHookStack)
        (ret_pc := (blkPl_434).base + 2520#64)
        hcl3' hdealloc (by rfl) (by exact hrun3)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustDeallocSpec]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [rustDeallocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun sf _ _ hm_pan => by dsimp only [rustDeallocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hcl3'
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustDeallocSpec]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr4
      simp only [htr3] at htr4
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_434).base + 780#64)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun4)
      intro hcl5
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun4)
      intro _ _ hmf
      refine ⟨rfl, ⟨hrun4, hsp4, hsp0,
          AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4, ?_, htr4, hcl5, by simp only [wp_norm, hvregs_4]⟩,
        by simp only [wp_norm, hx19_4],
        by simp only [wp_norm, hx20_4],
        by simp only [wp_norm, hx26_4]; rfl, ?_⟩
      · simp only [wp_norm, hx29_4]
      · unfold tryDecryptCommonHeap signalMessageAt speBodyAt
        rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            stackAt_ext_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_split s0.sp]
        have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
        clear hmf hmf1
        simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
        rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
        sep_close

theorem aesDecrypt_549_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsAesDecSym) (aesDecSpec C.D A))
    (hfmt : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S8SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S := by
  intro x trG tr st1 mks newPqrState draws R s0 s h8 hL
  cases hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
  | none =>
    exact aesDecrypt_none_549_placed_ok C A ctl S H haes hfmt hdealloc x trG tr st1 mks newPqrState draws R s0 s hd h8 hL
  | some pt =>
    exact aesDecrypt_some_549_placed_ok C A ctl S H haes x trG tr st1 mks newPqrState pt draws R s0 s hd h8 hL

theorem aesDecrypt_some_549_placed_ok_x [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsAesDecSym) (aesDecFnSpec decFn A))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState pt : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (CBC.blockToBytesLE mks.iv) = some pt)
    (h8 : AesDecryptStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      (ApplyRatchetStatePlaced (blkPl_434).base A ctl x trG tr st1 newPqrState pt draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_434).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + 1700#64) hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl (mid := lsρ lsAesDecSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hcl1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_frame_placed (spec := aesDecFnSpec decFn A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_434).base + 1688#64)
    hcl1 haes (by rfl) (by exact hstat)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecFnSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      tryDecryptFn_onPanic_of_callee_placed C decFn A ctl S x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hcl1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecFnSpec, AesCall.frame]
    rw [hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
      (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
    have hcap_ne : ptCap + 1#64 ≠ 0#64 := add_one_ne_zero_of_lt_2_63 hpt_lt
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_434).base + 1700#64)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun2)
    intro hcl3
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by rfl) (by exact hrun2)
    intro _ _ hmf
    refine ⟨rfl, ⟨hrun2, hsp2, hsp0,
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2, ?_, htr2, hcl3, by simp only [wp_norm, hvregs_2]⟩,
      by simp only [wp_norm, hx19_2],
      by simp only [wp_norm, hx20_2],
      by simp only [wp_norm, hx21_2],
      by simp only [wp_norm, hx23_2],
      by simp only [wp_norm, hx24_2],
      newPqrCap, newPqrPtr, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
    · simp only [wp_norm, hx29_2]
    · unfold tryDecryptCommonHeap signalMessageAt
      rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
          stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
          applyRatchet_reg10_split (s0.sp - 1504#64),
          applyRatchet_reg3e8_split (s0.sp - 1504#64)]
      have hvec := vecU8At_parts_entails_vecU8' A (s0.sp - 528#64) ptCap ptPtr pt hpt_le hpt_lt hpt_nz
      have hmf1 := Satisfies.mono_focus hvec (by sep_focus) hmf
      have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
      have hmf3 := Satisfies.mono_focus (applyRatchet_sp_entails_memRegion s0.sp msgW x.locA x.remA) (by sep_focus) hmf2
      clear hmf hmf1 hmf2
      simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf3 ⊢
      rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
      sep_close

theorem aesDecrypt_none_549_placed_ok_x [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsAesDecSym) (aesDecFnSpec decFn A))
    (hfmt : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A extHookStack))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (CBC.blockToBytesLE mks.iv) = none)
    (h8 : AesDecryptStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      (ErrTailStateXPlaced (blkPl_434).base A ctl x trG tr st1
        (.invalidMessage x.msgType .badCiphertext) draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  have hlog_c00 := logOff_eq_placed
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_434).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + 780#64) hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl (mid := lsρ lsAesDecSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hcl1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_frame_placed (spec := aesDecFnSpec decFn A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_434).base + 1688#64)
    hcl1 haes (by rfl) (by exact hstat)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecFnSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      tryDecryptFn_onPanic_of_callee_placed C decFn A ctl S x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hcl1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecFnSpec, AesCall.frame]
    rw [hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    simp only [← sepConj_assoc]
    refine SepWPp.mono_focus (aesDecrypt_none_prep_x s0.sp) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 520#64) (by sep_focus) fun p => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 512#64) (by sep_focus) fun w512 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun b1120 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1104#64) (by sep_focus) fun w1104 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1096#64) (by sep_focus) fun w1096 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 480#64) (by sep_focus) fun w480 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 472#64) (by sep_focus) fun w472 => ?_
    by_cases hp : p = 0#64
    · rw [aesDecrypt_none_reg1144_split s0.sp]
      simp only [sepConj_assoc]
      refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
      refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
      simp only [← sepConj_assoc]
      by_cases hpqr_cap : newPqrCap = 0#64
      · refine SepWPp.mono_focus (newPqr_zero_prep A newPqrCap newPqrPtr newPqrState hpqr_cap) (by sep_focus) ?_
        rw [emp_sepConj]
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_434).base + 780#64)
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun2)
        intro hcl3
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun2)
        intro _ _ hmf
        refine ⟨rfl, ⟨hrun2, hsp2, hsp0,
            AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2, ?_, htr2, hcl3, by simp only [wp_norm, hvregs_2]⟩,
          by simp only [wp_norm, hx19_2],
          by simp only [wp_norm, hx20_2],
          false, fun _ => rfl,
          by simp only [wp_norm]; rfl, ?_⟩
        · simp only [wp_norm, hx29_2]
        · unfold tryDecryptCommonHeap signalMessageAt
          rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp,
              hlog_c00]
          have hmf0 := Satisfies.mono_focus (aesDecrypt_none_p0_spe_entails_memRegion s0.sp _ _ b1120) (by sep_focus) hmf
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf0
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA w1104 w1096 errTag p w512 w480 w472 msgW) (by sep_focus) hmf1
          clear hmf hmf0 hmf1
          simp only [wp_norm, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close
      · refine SepWPp.mono_focus (newPqr_dealloc_prep' A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsRustDeallocSym)
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun2)
        intro hcl2'
        refine SepWPp.call_frame_placed (spec := rustDeallocExternSpecWithStack A extHookStack)
          (x := (newPqrPtr, newPqrCap.toNat, 1))
          (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
                memRegion newPqrPtr newPqrCap.toNat ∗
                stackAt (s0.sp - 1504#64) extHookStack)
          (ret_pc := (blkPl_434).base + 2520#64)
          hcl2' hdealloc (by rfl) (by exact hrun2)
          (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
          (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp2]; rfl)
          (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm], layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt⟩)
          (by sep_focus)
          (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
          (fun sf _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
        clear hcl2'
        intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
        simp only [wp_norm, hsp2] at hsp4
        rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
        simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
        dsimp only [rustDeallocExternSpecWithStack]
        simp only [wp_norm, hsp2, sepConj_assoc]
        apply SepWPp.elim_pure; intro htr4
        simp only [htr2] at htr4
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_434).base + 780#64)
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun4)
        intro hcl5
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun4)
        intro _ _ hmf
        refine ⟨rfl, ⟨hrun4, hsp4, hsp0,
            AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4, ?_, htr4, hcl5, by simp only [wp_norm, hvregs_4]⟩,
          by simp only [wp_norm, hx19_4],
          by simp only [wp_norm, hx20_4],
          false, fun _ => rfl,
          by simp only [wp_norm, hx26_4]; rfl, ?_⟩
        · simp only [wp_norm, hx29_4]
        · unfold tryDecryptCommonHeap signalMessageAt
          rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp,
              hlog_c00]
          have hmf0 := Satisfies.mono_focus (aesDecrypt_none_p0_spe_entails_memRegion s0.sp _ _ b1120) (by sep_focus) hmf
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf0
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA w1104 w1096 errTag p w512 w480 w472 msgW) (by sep_focus) hmf1
          clear hmf hmf0 hmf1
          simp only [wp_norm, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close
    · simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsFormatInnerSym)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun2)
      intro hcl2'
      refine SepWPp.call_frame_placed (spec := formatInnerSpec A)
        (x := s0.sp - 1144#64)
        (T := memRegion (s0.sp - 1144#64) 24 ∗ A.pool ∗
              stackAt (s0.sp - 1504#64) extHookStack)
        (ret_pc := (blkPl_434).base + 2656#64)
        hcl2' hfmt (by rfl) (by exact hrun2)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
        (by dsimp only [formatInnerSpec]; simp only [wp_norm, hsp2]; rfl)
        (by simp only [wp_norm]) (by sep_focus)
        (fun _ _ _ _ h => allowPanic_not_exited h)
        (fun sf hpan _ hm_pan =>
          tryDecryptFn_onPanic_of_callee_placed C decFn A ctl S x s0 _ sf _ R
            (htr2 ▸ List.prefix_refl _) hm_pan) ?_
      clear hcl2'
      intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
      simp only [wp_norm, hsp2] at hsp3
      rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
      simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
      dsimp only [formatInnerSpec]
      simp only [wp_norm, hsp2, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr3
      simp only [htr2] at htr3
      rw [formatInner_post_eq_badCiphertext A s0.sp]
      simp only [← sepConj_assoc]
      by_cases hpqr_cap : newPqrCap = 0#64
      · refine SepWPp.mono_focus (newPqr_zero_prep A newPqrCap newPqrPtr newPqrState hpqr_cap) (by sep_focus) ?_
        rw [emp_sepConj]
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_434).base + 780#64)
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun3)
        intro hcl4
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun3)
        intro _ _ hmf
        refine ErrTailStatePlaced.toX ⟨rfl, ⟨hrun3, hsp3, hsp0,
            AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3, ?_, htr3, hcl4, by simp only [wp_norm, hvregs_3]⟩,
          by simp only [wp_norm, hx19_3],
          by simp only [wp_norm, hx20_3],
          by simp only [wp_norm, hx26_3]; rfl, ?_⟩
        · simp only [wp_norm, hx29_3]
        · unfold tryDecryptCommonHeap signalMessageAt speBodyAt
          rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp]
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
          clear hmf hmf1
          simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close
      · refine SepWPp.mono_focus (newPqr_dealloc_prep' A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl3 (mid := lsρ lsRustDeallocSym)
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun3)
        intro hcl3'
        refine SepWPp.call_frame_placed (spec := rustDeallocExternSpecWithStack A extHookStack)
          (x := (newPqrPtr, newPqrCap.toNat, 1))
          (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
                memRegion newPqrPtr newPqrCap.toNat ∗
                stackAt (s0.sp - 1504#64) extHookStack)
          (ret_pc := (blkPl_434).base + 2520#64)
          hcl3' hdealloc (by rfl) (by exact hrun3)
          (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
          (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp3]; rfl)
          (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm], layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt⟩)
          (by sep_focus)
          (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
          (fun sf _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
        clear hcl3'
        intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
        simp only [wp_norm, hsp3] at hsp4
        rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
        simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
        dsimp only [rustDeallocExternSpecWithStack]
        simp only [wp_norm, hsp3, sepConj_assoc]
        apply SepWPp.elim_pure; intro htr4
        simp only [htr3] at htr4
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_434).base + 780#64)
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun4)
        intro hcl5
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun4)
        intro _ _ hmf
        refine ErrTailStatePlaced.toX ⟨rfl, ⟨hrun4, hsp4, hsp0,
            AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4, ?_, htr4, hcl5, by simp only [wp_norm, hvregs_4]⟩,
          by simp only [wp_norm, hx19_4],
          by simp only [wp_norm, hx20_4],
          by simp only [wp_norm, hx26_4]; rfl, ?_⟩
        · simp only [wp_norm, hx29_4]
        · unfold tryDecryptCommonHeap signalMessageAt speBodyAt
          rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp]
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
          clear hmf hmf1
          simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close

theorem aesDecrypt_549_placed_ok_x [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsAesDecSym) (aesDecFnSpec decFn A))
    (hfmt : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A extHookStack)) :
    S8SeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C decFn A ctl uuidTryParse S := by
  intro x trG tr st1 mks newPqrState draws R s0 s h8 hL
  cases hd : decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (CBC.blockToBytesLE mks.iv) with
  | none =>
    exact aesDecrypt_none_549_placed_ok_x C A ctl S decFn H haes hfmt hdealloc x trG tr st1 mks newPqrState draws R s0 s hd h8 hL
  | some pt =>
    exact aesDecrypt_some_549_placed_ok_x C A ctl S decFn H haes x trG tr st1 mks newPqrState pt draws R s0 s hd h8 hL

end CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt
