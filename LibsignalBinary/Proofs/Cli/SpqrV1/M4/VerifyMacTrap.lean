/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.ShardFill.TryDecryptStateRatchetCoins
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.VerifyMac
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Trap-at-RNG Segment `S7` (`VerifyMac`) for CLI Ratchet

Proves `verifyMac_false_ok_trap` and `verifyMac_ok_trap` over any `ext` satisfying
`Stage2Contracts_trap img.base C A uuidTryParse S ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt
open CryptoVerification.Cli.LibsignalTripleRatchet
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? _root_.Arm64.Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero

theorem verifyMac_false_ok_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hS2 : Stage2Contracts_trap img.base C A uuidTryParse S ext)
    (hVMac : VerifyMacWithAddressesOkExt img C A uuidTryParse ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false)
    (h7 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.hfn_tryDecrypt
  decrypt_fetches_ext_cli img.base ext hfn 0x63c 60
  decrypt_fetches_ext_cli img.base ext hfn 0x914 88
  decrypt_fetches_ext_cli img.base ext hfn 0x9d0 12
  decrypt_fetches_ext_cli img.base ext hfn 0xcbc 12
  have hS7_pc := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.segS7PC_eq_ext himg ext
  have hErr_pc := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.errTailPC_eq_ext himg ext
  have hAlloc := hS2.toAllocContracts
  have hshim : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      sessionShimSpec :=
    hAlloc.shim_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
      (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))
  have halloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (rustAllocSpec A) :=
    hAlloc.alloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
      (num% (ls_off% "__rustc::__rust_alloc" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))
  have hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (rustDeallocSpec A) :=
    hAlloc.dealloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
      (num% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))
  have hpan_ext := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.externAt_handle_error_ext img ext
  have halign := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hadrp := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.adrp_macFailedStr_ext halign ext
  have hbl_vmac := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.bl_verifyMac_target_ext img ext
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  rw [hS7_pc] at hpc
  dsimp only [tripleRatchetProgAtExt, VerifyMacWithAddressesOkExt] at *
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr verifyMacWithAddressesName = vmac_entry
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)] at hmem
  simp only [wp_norm, ← sepConj_assoc] at hpc hx20 hx22 hx23 hx25 hx27 hx28 hmem
  refine sepWPp_to_steps_or_panic (entry + bv% (780)) hmem hL ?_
  apply SepWPp.of_sepWP_frozen hfl hsym (mid := vmac_entry)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hfl1 hsym1
  refine SepWPp.call_inImage_frame (img := img) (spec := verifyMacWithAddressesSpec img C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          logOff img ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStack)
    (ret_pc := entry + bv% (1632))
    hfl1 hsym1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpec]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpec] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 (entry + bv% (1632))
        |>.setPC vmac_entry).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecrypt_onPanic_of_callee C A ctl S img x s0 _ sf _ R h0m hm_pan) ?_
  clear hfl1 hsym1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hfl1 hsym1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpec]
  rw [hok]
  unfold verifyMacResultAt
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [writeReg64_trace, setPC_trace, htr] at htr1
  rw [stackAt_vmac_split_alloc (s0.sp - 1504#64)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl1 hsym1 (mid := entry + bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hfl2 hsym2
  refine SepWPp.call_frame_frozen (img := img) (spec := sessionShimSpec) (x := ())
    (T := emp) (ret_pc := entry + bv% (2328))
    hfl2 hsym2 hshim (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [sessionShimSpec]; rw [pure_sepConj]; simp)
    trivial
    (by rw [emp_sepConj])
    (fun _ _ _ _ h => by dsimp only [sessionShimSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [sessionShimSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl2 hsym2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hfl2 hsym2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2
  dsimp only [sessionShimSpec]
  apply SepWPp.elim_pure; intro htr2
  simp only [writeReg64_trace, setPC_trace, setPState_trace, htr1] at htr2
  apply SepWPp.of_sepWP_frozen hfl2 hsym2 (mid := entry + bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hfl3 hsym3
  refine SepWPp.call_frame_frozen (img := img) (spec := rustAllocSpec A) (x := (23, 1))
    (T := A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
    (ret_pc := entry + bv% (2340))
    hfl3 hsym3 halloc (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [rustAllocSpec]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by decide, ⟨0, rfl⟩, by decide⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [rustAllocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [rustAllocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl3 hsym3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hfl3 hsym3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
  dsimp only [rustAllocSpec]
  simp only [wp_norm, hsp2, sepConj_assoc]
  set p := s3.readReg64 .x0
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte]
    refine SepWPp.elim_pure_focus (by sep_focus) fun htr3 => ?_
    simp only [writeReg64_trace, setPC_trace, htr2] at htr3
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
    wp_steps
    apply SepWP.setPC_ite_true (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.SepWPp.panic_direct_ext C A ctl S img ext x s0 _ _ _ _ R
      (by rfl) (by exact hrun3) hpan_ext
      (by simp only [writeReg64_trace, setPC_trace, htr3])
  · simp only [hp, ↓reduceIte, sepConj_assoc]
    refine SepWPp.elim_pure_focus (by sep_focus) fun h => ?_
    have htr3 := h.2
    simp only [writeReg64_trace, setPC_trace, htr2] at htr3
    have hmf_ent := verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 0#8
    refine SepWPp.mono_focus hmf_ent (by sep_focus) ?_
    rw [macFailed_alloc_split p]
    refine SepWPp.elim_memRegion8_focus (a := p) (by sep_focus) fun pw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 8#64) (by sep_focus) fun pw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun sw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun sw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun sw2 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun sb0 => ?_
    intro R' hm3
    have hm3_ro := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.rodata_macFailed_intro himg hfl3.roData hm3
    clear hm3
    rw [rodata_macFailed_split1, ← sepConj_assoc] at hm3_ro
    revert R' hm3_ro
    change SepWPp _ _ _ _ _ _
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl3 hsym3 (mid := entry + bv% (2360))
    wp_steps
    apply SepWP.setPC_ite_false (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hfl3b hsym3b
    simp only [sepConj_assoc]
    rw [rodata_macFailed_1_to_2]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl3b hsym3b (mid := entry + bv% (2380))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hfl4 hsym4
    simp only [sepConj_assoc]
    rw [rodata_macFailed_2_back]
    intro R' hm4
    rw [sepConj_assoc] at hm4
    have hm4' := Satisfies.drop_left hm4
    clear hm4
    revert R' hm4'
    change SepWPp _ _ _ _ _ _
    refine SepWPp.mono_focus (macFailed_overlap_prep p) (by sep_focus) ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 15#64) (by sep_focus) fun pw2 => ?_
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · simp only [sepConj_assoc]
      refine SepWPp.mono_focus
        (show (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
          (newPqrPtr ↦ₛ newPqrState) ∗
          memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ⊢ emp by
          simp only [hpqr_cap]; exact Entails.refl _) (by sep_focus) ?_
      simp only [emp_sepConj, ← sepConj_assoc]
      apply SepWPp.of_sepWP_frozen hfl4 hsym4 (mid := entry + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hfl5 hsym5
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun3)
      intro _ _ hmf
      refine ⟨?_, ⟨hrun3, hsp3, hsp0, hsp_al3, ?_, htr3, hfl5, hsym5, by simp only [wp_norm, hvregs_3]⟩,
        by simp only [wp_norm, hx19_3],
        by simp only [wp_norm, hx20_3],
        by simp only [wp_norm]; rfl, ?_⟩
      · rw [hErr_pc]; rfl
      · simp only [wp_norm, hx29_3]
      · unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide),
            stackAt_vmac_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close
    · simp only [sepConj_assoc]
      refine SepWPp.mono_focus (newPqr_dealloc_prep A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_frozen hfl4 hsym4 (mid := entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hfl5 hsym5
      refine SepWPp.call_frame_frozen (img := img) (spec := rustDeallocSpec A)
        (x := (newPqrPtr, newPqrCap.toNat, 1))
        (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) allocHookStack)
        (ret_pc := entry + bv% (2520))
        hfl5 hsym5 hdealloc (by rfl) (by exact hrun3)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustDeallocSpec]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [rustDeallocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun sf _ _ hm_pan => by dsimp only [rustDeallocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hfl5 hsym5
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hfl5 hsym5
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustDeallocSpec]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr4
      simp only [writeReg64_trace, State.trace_writeVReg128, setPC_trace, setMem_trace, htr3] at htr4
      simp only [← sepConj_assoc]
      have hrun4' : (s4.setPC (entry + bv% (780))).status = .Running := by simp only [wp_norm, hrun4]
      have hsp4' : (s4.setPC (entry + bv% (780))).sp = s0.sp - 1504#64 := by simp only [wp_norm, hsp4]
      have hsp_al4' : (s4.setPC (entry + bv% (780))).spAligned = true :=
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4
      have htr4' : (s4.setPC (entry + bv% (780))).trace = s0.trace := by simp only [setPC_trace, htr4]
      apply SepWPp.of_sepWP_frozen hfl5 hsym5 (mid := entry + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) hrun4'
      intro hfl6 hsym6
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) hrun4'
      intro _ _ hmf
      refine ⟨?_, ⟨hrun4', hsp4', hsp0, hsp_al4', ?_, htr4', hfl6, hsym6, by simp only [wp_norm, hvregs_4]⟩,
        by simp only [wp_norm, hx19_4],
        by simp only [wp_norm, hx20_4],
        by simp only [wp_norm, hx26_4]; rfl, ?_⟩
      · rw [hErr_pc]; rfl
      · simp only [wp_norm, hx29_4]
      · unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide),
            stackAt_vmac_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close

theorem verifyMac_ok_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hS2 : Stage2Contracts_trap img.base C A uuidTryParse S ext)
    (hVMac : VerifyMacWithAddressesOkExt img C A uuidTryParse ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (h7 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
      ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
    else
      ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  by_cases hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true
  · simp only [hok, ↓reduceIte]
    exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.verifyMac_true_ok_ext
      img C A ctl S ext himg hVMac x trG tr st1 mks newPqrState draws R s0 s hok h7 hL
  · have hok_false : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false :=
      Bool.eq_false_iff.mpr hok
    simp only [hok_false, Bool.false_eq_true, ↓reduceIte]
    exact verifyMac_false_ok_trap img C A ctl S ext himg hS2 hVMac x trG tr st1 mks newPqrState draws R s0 s hok_false h7 hL

private theorem tryDecryptFnSpec_onPanic_iff (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 s' : State) :
    (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' =
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec
    CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec Spec.inImage
  cases hp : S.recvPanics x.st.pqRatchetState x.msg.pqRatchet with
  | true => simp only [hp, true_or, or_true]
  | false =>
    simp only [CryptoVerification.LibsignalTripleRatchet.Decrypt.Model.modelFn_fst_eq_panic_iff C decFn S x hp]

theorem verifyMac_ok_ext_x (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hS2 : Stage2ContractsX img C A encFn decFn ext)
    (hVMac : VerifyMacWithAddressesOkX img C A uuidTryParse ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (h7 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
      ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
    else
      ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have h := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.verifyMac_ok_x
    img C encFn decFn A ctl S ext himg hS2 hVMac x trG tr st1 mks newPqrState draws R s0 s h7 hL
  simpa only [tryDecryptFnSpec_onPanic_iff C decFn A ctl S img x s0] using h

end CryptoVerification.Cli.LibsignalSpqrV1.M4
