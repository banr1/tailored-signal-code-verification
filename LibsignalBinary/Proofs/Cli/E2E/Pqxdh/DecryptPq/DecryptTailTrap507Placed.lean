/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.VerifyMacTrap507Placed
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecrypt
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchet
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs

/-!
# Relocatable Segments `S8` and `S9` (`AesDecrypt` and `ApplyRatchet`) on Block `507`

Relocatable `[LibsignalPlacement]` verification of Segment `S8` (`aes_256_cbc_decrypt`,
`S8SeamPlaced`) and Segment `S9` (`TR::apply_to_session_state`,
`clear_unacknowledged_pre_key_message`, and return epilogue, `S9SeamPlaced`) on Block `507`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.CliHandshake.TryDecPlaced

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Decrypt hiding
  ErrTailStatePlaced ErrTailStateXPlaced LoadRatchetStatePlaced FindChainStatePlaced
  DhStepStatePlaced ConsumeMsgKeyStatePlaced PqRecvStatePlaced DeriveKeysStatePlaced
  VerifyMacStatePlaced AesDecryptStatePlaced ApplyRatchetStatePlaced
  ErrTailSeamPlaced S0SeamPlaced S1SeamPlaced S2SeamPlaced S3SeamPlaced S4SeamPlaced
  S5SeamPlaced S6SeamPlaced S7SeamPlaced S8SeamPlaced S9SeamPlaced
open CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt
open CryptoVerification.Cli.SpqrV1.M4

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem aesDecrypt_some_507_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsAesDecSym) (aesDecSpec C.D A))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState pt : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = some pt)
    (h8 : AesDecryptStatePlaced (blkPl_508).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_508).rebase (blkPl_508).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_508).rebase (blkPl_508).base H) s s' ∧
      (ApplyRatchetStatePlaced (blkPl_508).base A ctl x trG tr st1 newPqrState pt draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_508).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold cliTryDecryptCommonHeapPlaced signalMessageAt at hmem
  rw [lsLogOff_eq_logOff_placed,
      boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  rw [cliTryDecryptSpecPlaced_onPanic_eq]
  refine sepWPp_to_steps_or_panic ((blkPl_508).base + 1700#64) hmem hL ?_
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
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := AuthDecrypt.length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_frame_placed (spec := aesDecSpec C.D A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_508).base + 1688#64)
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
    apply SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_508).base + 1700#64)
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
    · unfold cliTryDecryptCommonHeapPlaced signalMessageAt
      rw [lsLogOff_eq_logOff_placed,
          boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
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

theorem aesDecrypt_none_507_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsAesDecSym) (aesDecSpec C.D A))
    (hfmt : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = none)
    (h8 : AesDecryptStatePlaced (blkPl_508).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_508).rebase (blkPl_508).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_508).rebase (blkPl_508).base H) s s' ∧
      (ErrTailStatePlaced (blkPl_508).base A ctl x trG tr st1
        (.invalidMessage x.msgType .badCiphertext) draws R s0 s' ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_508).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold cliTryDecryptCommonHeapPlaced signalMessageAt at hmem
  rw [lsLogOff_eq_logOff_placed,
      boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  rw [cliTryDecryptSpecPlaced_onPanic_eq]
  refine sepWPp_to_steps_or_panic ((blkPl_508).base + 780#64) hmem hL ?_
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
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := AuthDecrypt.length_keyToBytes32 _
  have hiv_len : (CBC.blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  refine SepWPp.call_frame_placed (spec := aesDecSpec C.D A)
    (x := ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
           s0.sp - 1504#64 + 0x540#64, CBC.blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩)
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_508).base + 1688#64)
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
      (ret_pc := (blkPl_508).base + 2656#64)
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
      apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_508).base + 780#64)
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
      · unfold cliTryDecryptCommonHeapPlaced signalMessageAt speBodyAt
        rw [lsLogOff_eq_logOff_placed,
            boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
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
        (ret_pc := (blkPl_508).base + 2520#64)
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
      apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_508).base + 780#64)
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
      · unfold cliTryDecryptCommonHeapPlaced signalMessageAt speBodyAt
        rw [lsLogOff_eq_logOff_placed,
            boxU8At_msg_ct A x.msgA x.msgG.ctPtr x.msg.ciphertext,
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

theorem aesDecrypt_507_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsAesDecSym) (aesDecSpec C.D A))
    (hfmt : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S8SeamPlaced ((blkPC_508).rebase (blkPl_508).base H) (blkPl_508).base C A ctl uuidTryParse S := by
  intro x trG tr st1 mks newPqrState draws R s0 s h8 hL
  cases hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
  | none =>
    exact aesDecrypt_none_507_placed_ok C A ctl S H haes hfmt hdealloc x trG tr st1 mks newPqrState draws R s0 s hd h8 hL
  | some pt =>
    exact aesDecrypt_some_507_placed_ok C A ctl S H haes x trG tr st1 mks newPqrState pt draws R s0 s hd h8 hL

theorem applyRatchet_from_6d0_507_placed [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsmpl.base 58) (withLsCodeRoLoaded lsmpl (trApplySpec A)))
    (hClearUpk : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsmpl.base 35) (withLsCodeRoLoaded lsmpl (clearUpkSpec A)))
    (hmemcpy : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (newPqrCap newPqrPtr ptCap ptPtr : BitVec 64)
    (R : SepProp) (s0 s1 : State)
    (hok : (x.model C S uuidTryParse).1 = .ok pt)
    (hst : (x.model C S uuidTryParse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage)
    (hpad : trG.ratchet.senderPad.length = 100)
    (hnew_le : newPqrState.length ≤ newPqrCap.toNat)
    (hnew_lt : newPqrCap.toNat < 2 ^ 63)
    (hnew_nz : newPqrPtr ≠ 0)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_nz : ptPtr ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hpc1 : s1.pc = (blkPl_508).base + 1744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1504#64)
    (hsp_al1 : s1.spAligned = true)
    (htr1 : s1.trace = s0.trace)
    (hcl1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hx9_1 : s1.readReg64 .x9 = s0.sp - 800#64)
    (hx19_1 : s1.readReg64 .x19 = x.ret)
    (hx20_1 : s1.readReg64 .x20 = s0.sp - 1184#64)
    (hx21_1 : s1.readReg64 .x21 = x.ss)
    (hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length)
    (_hx29_1 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0) :
    SepWPp ((blkPC_508).rebase (blkPl_508).base H) (s0.readReg64 .lr) s1
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trWithoutPqAt A (s0.sp - 1448#64) trG.ratchet tr ∗
       ((s0.sp - 1272#64) ↦₆₄ trG.pq.cap) ∗
       ((s0.sp - 1264#64) ↦₆₄ trG.pq.ptr) ∗
       ((s0.sp - 1256#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       (if newPqrCap = 0 then emp else (A.live newPqrPtr newPqrCap.toNat 1 ∗ (newPqrPtr ↦ₛ newPqrState)) ∗
         memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
       ((s0.sp - 528#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 520#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 512#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (if ptCap = 0 then emp else (A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt)) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       memRegion x.ret 8 ∗
       memRegion (x.ret + 8#64) 8 ∗
       memRegion (x.ret + 16#64) 8 ∗
       memRegion (x.ret + 24#64) 8 ∗
       memRegion (x.ret + 32#64) 16 ∗
       memRegion (s0.sp - 1504#64) 8 ∗
       ((s0.sp - 1496#64) ↦₆₄ newPqrCap) ∗
       memRegion (s0.sp - 1488#64) 24 ∗
       ((s0.sp - 1464#64) ↦₆₄ newPqrPtr) ∗
       memRegion (s0.sp - 1456#64) 8 ∗
       memRegion (s0.sp - 1184#64) 8 ∗
       memRegion (s0.sp - 1176#64) 8 ∗
       memRegion (s0.sp - 1168#64) 8 ∗
       memRegion (s0.sp - 1160#64) 16 ∗
       memRegion (s0.sp - 1144#64) 8 ∗
       memRegion (s0.sp - 1136#64) 8 ∗
       memRegion (s0.sp - 1128#64) 8 ∗
       memRegion (s0.sp - 1120#64) 16 ∗
       memRegion (s0.sp - 1104#64) 264 ∗
       memRegion (s0.sp - 840#64) 120 ∗
       ((s0.sp - 720#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 712#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 704#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       memRegion (s0.sp - 696#64) 168 ∗
       memRegion (s0.sp - 504#64) 0x198 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       cliTapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
       logOff tryDecryptPlacedImg ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 sf ∗ R)) := by
  simp only [wp_norm] at hpc1 hsp1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1184#64) (by sep_focus) fun w1184 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1176#64) (by sep_focus) fun w1176 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1168#64) (by sep_focus) fun w1168 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun w1128 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 8#64) (by sep_focus) fun wret8 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 16#64) (by sep_focus) fun wret16 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 24#64) (by sep_focus) fun wret24 => ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsMemcpySym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  rw [cliTryDecryptSpecPlaced_onPanic_eq]
  refine SepWPp.mono_focus
    (trAt_of_withoutPq A s0.sp trG tr newPqrCap newPqrPtr newPqrState hnew_le hnew_lt hnew_nz)
    (by sep_focus) ?_
  rw [trAt_eq_stack_heap A (s0.sp - 1448#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } hpad]
  refine SepWPp.elim_exists_focus
    (Φ := fun pad : BitVec 32 =>
      ((s0.sp - 1448#64) ↦ₛ trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
        { tr with pqrState := newPqrState } pad) ∗
      trHeapPart A { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState })
    (by sep_focus) fun pad => ?_
  have hbs_len : (trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad).length = 264 :=
    length_trStackBytes _ _ pad hpad
  generalize hbs_def : trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad = bs at hbs_len ⊢
  rw [show memRegion (s0.sp - 1104#64) 264 = memRegion (s0.sp - 1104#64) bs.length by rw [hbs_len]]
  simp only [← sepConj_assoc]
  refine SepWPp.call_frame_placed (spec := sessionMemcpyRegionSpec)
    (x := (s0.sp - 1104#64, s0.sp - 1448#64, bs))
    (T := memRegion (s0.sp - 1104#64) bs.length ∗ ((s0.sp - 1448#64) ↦ₛ bs))
    (ret_pc := (blkPl_508).base + bv% (1248))
    hcl2 hmemcpy (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm, hbs_len]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx24_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx24_2 hvregs_2
  dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
  simp only [wp_norm, sepConj_assoc]
  apply SepWPp.elim_pure; rintro ⟨_, htr2⟩
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  rw [← hbs_def]
  refine SepWPp.mono_focus
    (trAt_of_stack_heap A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } pad hpad)
    (by sep_focus) ?_
  rw [hbs_def]
  rw [stackAt_sub_split (s0.sp - 1504#64) trApplyStack (by decide)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsmpl.base 58)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  refine SepWPp.call_cro_frame_placed (spec := trApplySpec A)
    (x := ⟨s0.sp - 1104#64, { trG with pq := ⟨newPqrCap, newPqrPtr⟩ },
           { tr with pqrState := newPqrState }, x.ss, x.G.afterTrFrom, st1⟩)
    (T := trAt A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
            { tr with pqrState := newPqrState } ∗
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          stackAt (s0.sp - 1504#64) trApplyStack ∗ A.pool)
    (ret_pc := (blkPl_508).base + bv% (1260))
    hcl3 hTrApply (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [trApplySpec]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [trApplySpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by
      have h0m : s0.trace <+: (s2.writeReg64 .x0 (s0.sp - 1104#64)
        |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 ((blkPl_508).base + bv% (1260))
        |>.setPC (lsmpl.base 58)).trace := by
        rw [show (s2.writeReg64 .x0 (s0.sp - 1104#64)
          |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 ((blkPl_508).base + bv% (1260))
          |>.setPC (lsmpl.base 58)).trace = s2.trace from rfl, htr20]
      exact tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx24_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx24_3 hvregs_3
  dsimp only [trApplySpec]
  simp only [wp_norm, hsp2, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr3
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  apply SepWPp.elim_exists; intro G1
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hG1
  refine SepWPp.mono_focus (trApplyStack_to_clearUpkStack s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl3 (mid := lsmpl.base 35)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hcl4
  refine SepWPp.call_cro_frame_placed (spec := clearUpkSpec A)
    (x := ⟨x.ss, G1, ({ tr with pqrState := newPqrState }).applyToSessionState st1⟩)
    (T := sessionStateAt A x.ss G1 (({ tr with pqrState := newPqrState }).applyToSessionState st1) ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) clearUpkStack)
    (ret_pc := (blkPl_508).base + bv% (1268))
    hcl4 hClearUpk (by rfl) (by exact hrun3)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
    (by dsimp only [clearUpkSpec]; simp only [wp_norm, hsp3]; rfl)
    (by simp only [wp_norm])
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [clearUpkSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [clearUpkSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl4
  intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
  simp only [wp_norm, hsp3] at hsp4
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _hx29_4, hvregs_4⟩
  simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx24_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx24_4 hvregs_4
  dsimp only [clearUpkSpec]
  simp only [wp_norm, hsp3, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr4
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  refine SepWPp.mono_focus (clearUpkStack_to_subStack s0.sp) (by sep_focus) ?_
  refine SepWPp.mono_focus
    (applyRatchet_local_frame_entails_memRegion s0.sp newPqrCap newPqrPtr ptCap ptPtr
      (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      ptCap ptPtr (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      bs hbs_len) (by sep_focus) ?_
  refine SepWPp.mono_focus (Entails.refl (tryDecryptSavedRegs s0.sp s0)) (by sep_focus) ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret) (by sep_focus) fun wret => ?_
  unfold tryDecryptSavedRegs
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun4)
  refine ⟨fun hmf => ?_, by simp only [wp_norm], ?_⟩
  · dsimp only [cliTryDecryptSpecPlaced, withLsCodeRoLoaded,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec]
    rw [lsLogOff_eq_logOff_placed, hok]
    rw [← hst] at hmf
    have hdec := decRel_of_trApplyRel hG1
    have hsaved := tryDecryptSavedRegs_entails_memRegion s0.sp s0
    unfold tryDecryptSavedRegs at hsaved
    have hmf1 := Satisfies.mono_focus hsaved (by sep_focus) hmf
    have hmf3 := Satisfies.mono_focus (stackAt_rootStack_of_parts s0.sp) (by sep_focus) hmf1
    rw [show (bv% (2 ^ 64 - 2) : BitVec 64) = okTagVec from rfl] at hmf3
    have hmf4 := Satisfies.mono_focus
      (decResultAt_ok_of_parts A x.ret pt ptCap ptPtr hpt_le hpt_lt hpt_nz) (by sep_focus) hmf3
    have hss : sessionStateAt A x.ss { G1 with pending := none, kyber := none } (x.model C S uuidTryParse).2 ⊢
        ∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
          sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 := by
      refine Entails.trans ?_
        (Entails.sepExists_intro
          (P := fun G' : SessionGhost =>
            ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
            sessionStateAt A x.ss G' (x.model C S uuidTryParse).2)
          { G1 with pending := none, kyber := none })
      exact Entails.pure_right hdec (Entails.refl _)
    have hmf5 := Satisfies.mono_focus hss (by sep_focus) hmf4
    clear hmf hmf1 hmf3 hmf4
    have hno_pan : (Except.ok pt : Except SignalProtocolError (List (BitVec 8))) ≠ .error .panic := nofun
    simp only [wp_norm, sepConj_assoc, satisfies_pure_sepConj] at hmf5 ⊢
    refine ⟨⟨hno_pan, htr40⟩, ?_⟩
    generalize (∃∗ G', ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
      sessionStateAt A x.ss G' (x.model C S uuidTryParse).2) = SS at hmf5 ⊢
    sep_close
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, hvregs_4]

theorem applyRatchet_507_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsmpl.base 58) (withLsCodeRoLoaded lsmpl (trApplySpec A)))
    (hClearUpk : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsmpl.base 35) (withLsCodeRoLoaded lsmpl (clearUpkSpec A)))
    (hmemcpy : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hdealloc : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S9SeamPlaced ((blkPC_508).rebase (blkPl_508).base H) (blkPl_508).base C A ctl uuidTryParse S := by
  intro x trG tr st1 newPqrState pt R s0 s hok hst h9
  rcases h9 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx23, hx24, newPqrCap, newPqrPtr, hnew_le, hnew_lt, hnew_nz, hmem⟩
  have h6d0 := @applyRatchet_from_6d0_507_placed _ C A ctl S H hTrApply hClearUpk hmemcpy x trG tr st1
    newPqrState pt newPqrCap newPqrPtr
  clear hTrApply hClearUpk
  have hpad : trG.ratchet.senderPad.length = 100 := by
    have htr_front := hmem
    rw [← sepConj_assoc, sepConj_comm (sessionStateAt A x.ss x.G.afterTrFrom st1), sepConj_assoc] at htr_front
    exact trAt_senderPad_len htr_front
  unfold cliTryDecryptCommonHeapPlaced at hmem
  rw [lsLogOff_eq_logOff_placed,
      trAt_eq_withoutPq A s0.sp trG tr,
      applyRatchet_scr_split s0.sp,
      applyRatchet_ret_split x.ret,
      show s0.sp - 1504#64 + 0x3d0#64 = s0.sp - 528#64 by bv_omega,
      show s0.sp - 1504#64 + 0x8#64 = s0.sp - 1496#64 by bv_omega,
      show s0.sp - 1504#64 + 0x10#64 = s0.sp - 1488#64 by bv_omega,
      show s0.sp - 1504#64 + 0x28#64 = s0.sp - 1464#64 by bv_omega,
      show s0.sp - 1504#64 + 0x30#64 = s0.sp - 1456#64 by bv_omega,
      show s0.sp - 1504#64 + 0x3e8#64 = s0.sp - 504#64 by bv_omega] at hmem
  change s.pc = (blkPl_508).base + 1700#64 at hpc
  simp only [wp_norm] at hx20 hx23 hx29
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_reaches_outcome hmem ?_
  refine SepWPp.elim_pure_focus
    (φ := tr.pqrState.length ≤ trG.pq.cap.toNat ∧ trG.pq.cap.toNat < 2 ^ 63 ∧ trG.pq.ptr ≠ 0)
    (by sep_focus) fun ⟨hpq_le, hpq_lt, hpq_nz⟩ => ?_
  refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
    (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
  rw [show s0.sp - 528#64 + 8#64 = s0.sp - 520#64 by bv_omega,
      show s0.sp - 528#64 + 16#64 = s0.sp - 512#64 by bv_omega]
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 720#64) (by sep_focus) fun w720 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 712#64) (by sep_focus) fun w712 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 704#64) (by sep_focus) fun w704 => ?_
  by_cases hpq_cap : trG.pq.cap = 0#64
  · refine SepWPp.mono_focus (newPqr_zero_prep A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap) (by sep_focus) ?_
    rw [emp_sepConj]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_508).base + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    refine AuthDecrypt.SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun) (by simp only [wp_norm, hsp])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al)
        htr hcl1
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19])
        (by simp only [wp_norm, hx20])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx24])
        (by simp only [wp_norm, hx29])
        (by simp only [wp_norm, hvregs]))
  · refine SepWPp.mono_focus (newPqr_dealloc_prep' A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap hpq_le hpq_lt) (by sep_focus) ?_
    rw [stackAt_sub_split (s0.sp - 1504#64) allocHookStack (by decide)]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_508).base + bv% (1728))
    wp_steps
    apply SepWP.setPC_setMem_ite_false (by simp only [beq_iff_eq, hpq_cap, not_false_eq_true])
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl0
    apply SepWPp.of_sepWP_placed hcl0 (mid := lsρ lsRustDeallocSym)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    refine SepWPp.call_frame_placed (spec := rustDeallocSpec A)
      (x := (trG.pq.ptr, trG.pq.cap.toNat, 1))
      (T := A.pool ∗ A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat ∗
            stackAt (s0.sp - 1504#64) allocHookStack)
      (ret_pc := (blkPl_508).base + bv% (1740))
      hcl1 hdealloc (by rfl) (by exact hrun)
      (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
      (by dsimp only [rustDeallocSpec]; simp only [wp_norm, hsp]; rfl)
      (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
      (by sep_focus)
      (fun _ _ _ _ h => by dsimp only [rustDeallocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
      (fun sf _ hm_pan => by dsimp only [rustDeallocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
    clear hcl0 hcl1
    intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
    simp only [wp_norm, hsp] at hsp1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, hx19, hx20, hx21, hx24, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx24_1 hx29_1 hvregs_1
    dsimp only [rustDeallocSpec]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr1
    have htr10 : s1.trace = s0.trace := htr1.trans htr
    refine SepWPp.mono_focus (allocHookStack_to_subStack s0.sp) (by sep_focus) ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_508).base + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun1)
    intro hcl2
    rw [← logOff_tryDecryptPlacedImg]
    refine AuthDecrypt.SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun1) (by simp only [wp_norm, hsp1])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1)
        htr10 hcl2
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19_1])
        (by simp only [wp_norm, hx20_1])
        (by simp only [wp_norm, hx21_1])
        (by simp only [wp_norm, hx24_1])
        (by simp only [wp_norm, hx29_1])
        (by simp only [wp_norm, hvregs_1]))

end CryptoVerification.CliHandshake.TryDecPlaced
