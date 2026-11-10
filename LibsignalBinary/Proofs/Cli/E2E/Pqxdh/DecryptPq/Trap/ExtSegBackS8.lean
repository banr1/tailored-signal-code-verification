/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegBackDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegBackDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegBackDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Contract-Backed (`Stage2ContractsExt`) Segment `S8` for Handshake `try_decrypt_with_state::<Coins>`

Proves `s8_some_ok_ext`, `s8_none_ok_ext`, `s8_ok_core_ext`, and `s8_ok_ext` (`S8Spec_ext`)
directly on `tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.CBC (blockToBytesLE)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto MessageKeys SessionState TripleRatchet aesCbcDecrypt
  macLength)
open CryptoVerification (libsignalSessionCode libsignalSessionImage)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (signalMessageAt uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (AesCall SpqrModel TrGhost TryDecryptGhost
  aesDecSpec extHookStack formatInnerSpec rustDeallocExternSpecWithStack tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq (speBodyAt)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD (add_one_ne_zero_of_lt_2_63
  boxU8At_msg_ct bytesToBlock_blockToBytesLE bytesToKey32_keyToBytes32 errTail_reg190_split
  errTail_sp_entails_memRegion errTail_sp_split formatInner_post_eq_badCiphertext
  length_blockToBytesLE length_keyToBytes32 messageKeysAt_eq mks_parts_entails_memRegion
  newPqr_dealloc_prep' newPqr_zero_prep noPanic_callee s8_none_prep s8_scr_split s9_reg10_split
  s9_reg3e8_split s9_sp_entails_memRegion sepWPp_to_steps_or_panic setMem_trace setPC_trace
  setPState_trace stackAt_sub_split vecU8At_parts_entails_vecU8' writeReg64_trace)
open CryptoVerification.SignalSession.Cli.Slots (Stage2ContractsExt)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegBackS8

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero

local macro "decrypt_fetches_ext_cli_pq " b:term:max ext:term:max
    hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli $b
    (Rust.withPanics $ext) $hfn
    (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
    $k0 $len)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s8_some_ok_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2ContractsExt img C A ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState pt : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = some pt)
    (h8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9State A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.hfn_tryDecrypt
  have haes := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.aesDec_ok_at_ext img hC
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.segS8PC_eq_ext himg ext] at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      s8_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic
    ((libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% (1700))
    hmem hL ?_
  clear hmem
  apply CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  decrypt_fetches_ext_cli_pq img.base ext hfn 0x678 44
  have hS9_pc : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS9PC img =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% (1700) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.segS9PC_eq_ext himg ext
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP_frozen hfl hsym
    (mid := entry + bv% ((2 ^ 64 + ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hfl1 hsym1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.call_inImage_frame (img := img) (spec := aesDecSpec C.D A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := entry + bv% (1688))
    hfl1 hsym1 haes (by rfl) (by exact hstat)
    (CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecrypt_onPanic_of_callee C A ctl S img x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hfl1 hsym1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hfl2 hsym2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2,
      hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
      hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecSpec, AesCall.frame]
    rw [bytesToKey32_keyToBytes32, bytesToBlock_blockToBytesLE, hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
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
        CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2, ?_, htr2, hfl3, hsym3,
        by simp only [wp_norm, hvregs_2]⟩,
      by simp only [wp_norm, hx19_2],
      by simp only [wp_norm, hx20_2],
      by simp only [wp_norm, hx21_2],
      by simp only [wp_norm, hx23_2],
      by simp only [wp_norm, hx24_2],
      newPqrCap, newPqrPtr, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
    · rw [hS9_pc]; rfl
    · simp only [wp_norm, hx29_2]
    · unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap signalMessageAt
      rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
          stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
          s9_reg10_split (s0.sp - 1504#64),
          s9_reg3e8_split (s0.sp - 1504#64)]
      have hvec := vecU8At_parts_entails_vecU8' A (s0.sp - 528#64) ptCap ptPtr pt hpt_le hpt_lt hpt_nz
      have hmf1 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus hvec (by sep_focus) hmf
      have hmf2 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
      have hmf3 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus (s9_sp_entails_memRegion s0.sp msgW x.locA x.remA) (by sep_focus) hmf2
      clear hmf hmf1 hmf2
      simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf3 ⊢
      rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
      sep_close

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s8_none_ok_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2ContractsExt img C A ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = none)
    (h8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1
        (.invalidMessage x.msgType .badCiphertext) draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.hfn_tryDecrypt
  have haes := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.aesDec_ok_at_ext img hC
  have hfmt := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.formatInner_ok_at_ext img hC.toStage2ContractsX
  have hdealloc := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.dealloc_ok_at_ext img hC.toStage2ContractsX
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.segS8PC_eq_ext himg ext] at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap signalMessageAt at hmem
  rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      s8_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic
    ((libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% (780))
    hmem hL ?_
  clear hmem
  apply CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  decrypt_fetches_ext_cli_pq img.base ext hfn 0x678 44
  decrypt_fetches_ext_cli_pq img.base ext hfn 0xa1c 88
  decrypt_fetches_ext_cli_pq img.base ext hfn 0x964 8
  decrypt_fetches_ext_cli_pq img.base ext hfn 0x9d0 12
  have hErr_pc : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC img =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% (780) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.errTailPC_eq_ext himg ext
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP_frozen hfl hsym
    (mid := entry + bv% ((2 ^ 64 + ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
  wp_steps
  apply SepWP.done (by rfl) (by exact hstat)
  intro hfl1 hsym1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.call_inImage_frame (img := img) (spec := aesDecSpec C.D A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := entry + bv% (1688))
    hfl1 hsym1 haes (by rfl) (by exact hstat)
    (CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecSpec, AesCall.pre]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf hpan _ hm_pan =>
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecrypt_onPanic_of_callee C A ctl S img x s0 _ sf _ R
        (htr ▸ List.prefix_refl _) hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hfl1 hsym1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hfl2 hsym2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2,
      hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
      hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecSpec, AesCall.frame]
    rw [bytesToKey32_keyToBytes32, bytesToBlock_blockToBytesLE, hd]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_pure; intro htr2
    simp only [htr] at htr2
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_exists_focus
      (Φ := fun p : BitVec 64 => ⌜p ≠ 0⌝ ∗ ((s0.sp - 520#64) ↦₆₄ p))
      (by sep_focus) fun p => ?_
    simp only [sepConj_assoc]
    apply CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_pure; intro hp_nz
    simp only [← sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.mono_focus (s8_none_prep s0.sp) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_memRegion8_focus (a := s0.sp - 512#64) (by sep_focus) fun w512 => ?_
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun b1120 => ?_
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_memRegion8_focus (a := s0.sp - 1104#64) (by sep_focus) fun w1104 => ?_
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_memRegion8_focus (a := s0.sp - 1096#64) (by sep_focus) fun w1096 => ?_
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_memRegion8_focus (a := s0.sp - 480#64) (by sep_focus) fun w480 => ?_
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_memRegion8_focus (a := s0.sp - 472#64) (by sep_focus) fun w472 => ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl2 hsym2
      (mid := entry + bv% ((2 ^ 64 + ls_off% "alloc::fmt::format::format_inner" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun2)
    intro hfl2' hsym2'
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.call_inImage_frame (img := img) (spec := formatInnerSpec A)
      (x := s0.sp - 1144#64)
      (T := memRegion (s0.sp - 1144#64) 24 ∗ A.pool ∗
            stackAt (s0.sp - 1504#64) extHookStack)
      (ret_pc := entry + bv% (2656))
      hfl2' hsym2' hfmt (by rfl) (by exact hrun2)
      (CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
      (by dsimp only [formatInnerSpec]; simp only [wp_norm, hsp2]; rfl)
      (by simp only [wp_norm]) (by sep_focus)
      (fun _ _ _ _ h => allowPanic_not_exited h)
      (fun sf hpan _ hm_pan =>
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecrypt_onPanic_of_callee C A ctl S img x s0 _ sf _ R
          (htr2 ▸ List.prefix_refl _) hm_pan) ?_
    clear hfl2' hsym2'
    intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hfl3 hsym3
    simp only [wp_norm, hsp2] at hsp3
    rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3,
      hx28_3, hx29_3, hvregs_3⟩
    simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2,
      hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
    dsimp only [formatInnerSpec]
    simp only [wp_norm, hsp2, sepConj_assoc]
    apply CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_pure; intro htr3
    simp only [htr2] at htr3
    rw [formatInner_post_eq_badCiphertext A s0.sp]
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.mono_focus (newPqr_zero_prep A newPqrCap newPqrPtr newPqrState hpqr_cap) (by sep_focus) ?_
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
          CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3, ?_, htr3, hfl4, hsym4,
          by simp only [wp_norm, hvregs_3]⟩,
        by simp only [wp_norm, hx19_3],
        by simp only [wp_norm, hx20_3],
        by simp only [wp_norm, hx26_3]; rfl, ?_⟩
      · rw [hErr_pc]; rfl
      · simp only [wp_norm, hx29_3]
      · unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap signalMessageAt speBodyAt
        rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_split s0.sp]
        have hmf1 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
        have hmf2 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA
          newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
        clear hmf hmf1
        simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
        rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
        sep_close
    · refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.mono_focus (newPqr_dealloc_prep' A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_frozen hfl3 hsym3
        (mid := entry + bv% ((2 ^ 64 + ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hfl3' hsym3'
      refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.call_inImage_frame (img := img) (spec := rustDeallocExternSpecWithStack A extHookStack)
        (x := (newPqrPtr, newPqrCap.toNat, 1))
        (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) extHookStack)
        (ret_pc := entry + bv% (2520))
        hfl3' hsym3' hdealloc (by rfl) (by exact hrun3)
        (CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun sf _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hfl3' hsym3'
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hfl4 hsym4
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4,
        hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3] at hx19_4 hx20_4 hx21_4 hx22_4
      simp only [wp_norm, hx23_3, hx24_3, hx25_3, hx26_3] at hx23_4 hx24_4 hx25_4 hx26_4
      simp only [wp_norm, hx27_3, hx28_3, hx29_3, hvregs_3] at hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustDeallocExternSpecWithStack]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_pure; intro htr4
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
          CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4, ?_, htr4, hfl5, hsym5,
          by simp only [wp_norm, hvregs_4]⟩,
        by simp only [wp_norm, hx19_4],
        by simp only [wp_norm, hx20_4],
        by simp only [wp_norm, hx26_4]; rfl, ?_⟩
      · rw [hErr_pc]; rfl
      · simp only [wp_norm, hx29_4]
      · unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap signalMessageAt speBodyAt
        rw [boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_split s0.sp]
        have hmf1 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
        have hmf2 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA
          newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
        clear hmf hmf1
        simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
        rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
        sep_close

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s8_ok_core_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2ContractsExt img C A ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (h8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
    | some pt =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9State A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
    | none =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
            draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  cases hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
  | none =>
    exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s8_none_ok_ext
      img C A ctl S ext himg hC x trG tr st1 mks newPqrState draws R s0 s hd h8 hL
  | some pt =>
    exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s8_some_ok_ext
      img C A ctl S ext himg hC x trG tr st1 mks newPqrState pt draws R s0 s hd h8 hL

/-- Headline `S8` theorem proving `DecryptPq.S8Spec_ext img C A ctl uuidTryParse S ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s8_ok_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec_ext img C A ctl uuidTryParse S ext := by
  intro himg hC _hM x trG tr st1 mks newPqrState draws R s0 s h8 hL
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s8_ok_core_ext
    img C A ctl S ext himg hC x trG tr st1 mks newPqrState draws R s0 s h8 hL

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegBackS8
