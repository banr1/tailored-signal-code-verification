/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegBackDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegBackS7
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegBackDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegBackDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Contract-Backed (`Stage2ContractsWeak` / `Stage2ContractsExt`) Segment `S7` (`ExtSegBackS7`)

Proves `s7_true_ok_withStack_ext`, `s7_false_ok_withStack_ext`, `s7_ok_withStack_ext`,
`s7_ok_x_ext` (`VerifyMacWithAddressesOkX`), and `s7_ok_ext` (`S7Spec_ext`) for handshake
`try_decrypt_with_state::<Coins>` directly on `tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto MessageKeys SessionState TripleRatchet)
open CryptoVerification (libsignalSessionCode libsignalSessionImage)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec protocolAddressAt serializeAddresses
  serviceIdParse signalMessageAt uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel Stage2ContractsWeak TrGhost
  TryDecryptGhost computeMacStackX extHookStack logOff rootStack rustAllocSpecWithStack
  rustDeallocExternSpecWithStack rustDeallocSpecWithStack sessionShimSpec tripleRatchetProgAtExt
  verifyMacResultAt verifyMacWithAddressesName withStack)
open CryptoVerification.LibsignalTripleRatchet.Mac.VerifyMacWithAddresses
  (verifyMacWithAddressesSpecWithStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (VerifyMacWithAddressesOkX)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq (speBodyAt tryDecryptFrameSize
  tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD (errTail_reg190_s7_split
  errTail_sp_s7_entails_memRegion errTail_sp_split macFailed_alloc_split macFailed_assemble
  macFailed_overlap_prep messageKeysAt_eq mks_parts_entails_memRegion newPqr_dealloc_prep
  noPanic_callee rodata_macFailed_1_to_2 rodata_macFailed_2_back rodata_macFailed_split1
  s7_scr_split sepWPp_to_steps_or_panic setMem_trace setPC_trace setPState_trace stackAt_sub_split
  trAt_eq_rest verifyMacResultAt_parts_entails_memRegion writeReg32_trace writeReg64_trace)
open CryptoVerification.SignalSession.Cli.Slots (Stage2ContractsExt)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegBackS7

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

/-! ## Segment 7 (`+0x63c → +0x678 / +0x30c`) -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.adrp_macFailedStr_ext
    {img : Obj.Image} (halign : img.base &&& 0xfff#64 = 0#64)
    (ext : String → Option (State → State)) :
    (((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% (2344)) &&&
      bv% (2 ^ 64 - 4096)) +
      bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2344)
        (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2348) -
        (page% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2344))) =
    img.base +
      bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2344)
        (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2348)) := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
      BitVec.add_assoc, ProofLib.adrp_page_of_aligned halign, BitVec.add_assoc]
  rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_true_ok_withStack_ext
    {cmStack : Nat} (hhi : cmStack + 288 ≤ tryDecryptSubStack)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hVMac : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpecWithStack img C.F A uuidTryParse cmStack).inImage img))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true)
    (h7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7State A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.hfn_tryDecrypt
  decrypt_fetches_ext_cli_pq img.base ext hfn 0x63c 60
  have hS7_pc := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.segS7PC_eq_ext himg ext
  have hS8_pc := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.segS8PC_eq_ext himg ext
  have hbl_vmac := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.bl_verifyMac_target_ext img ext
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  rw [hS7_pc] at hpc
  dsimp only [tripleRatchetProgAtExt] at *
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr verifyMacWithAddressesName = vmac_entry at hbl_vmac hVMac
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      s7_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) (cmStack + 288) hhi] at hmem
  simp only [wp_norm, ← sepConj_assoc] at hpc hx20 hx22 hx23 hx25 hx27 hx28 hmem
  refine sepWPp_to_steps_or_panic (entry + bv% (1656)) hmem hL ?_
  apply SepWPp.of_sepWP_frozen hfl hsym (mid := vmac_entry)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hfl1 hsym1
  refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.call_inImage_frame (img := img)
    (spec := verifyMacWithAddressesSpecWithStack img C.F A uuidTryParse cmStack)
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
          A.pool ∗ stackAt (s0.sp - 1504#64) (cmStack + 288))
    (ret_pc := entry + bv% (1632))
    hfl1 hsym1 hVMac (by rfl) (by exact hrun)
    (CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpecWithStack]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by
      dsimp only [verifyMacWithAddressesSpecWithStack] at h
      rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpecWithStack] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 (entry + bv% (1632))
        |>.setPC vmac_entry).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecrypt_onPanic_of_callee
        C A ctl S img x s0 _ sf _ R h0m hm_pan) ?_
  clear hfl1 hsym1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hfl1 hsym1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1,
    hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpecWithStack]
  rw [hok]
  unfold verifyMacResultAt
  simp only [↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl1 hsym1 (mid := entry + bv% (1656))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hfl2 hsym2
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by rfl) (by exact hrun1)
  intro _ _ hmf
  refine ⟨?_, ⟨hrun1, hsp1, hsp0, hsp_al1, ?_, htr1, hfl2, hsym2, by simp only [wp_norm, hvregs_1]⟩,
    by simp only [wp_norm, hx19_1],
    by simp only [wp_norm, hx20_1],
    by simp only [wp_norm, hx21_1],
    by simp only [wp_norm, hx22_1],
    by simp only [wp_norm],
    by simp only [wp_norm, hx24_1],
    by simp only [wp_norm, hx25_1],
    by simp only [wp_norm, hx27_1],
    by simp only [wp_norm, hx28_1],
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
  · rw [hS8_pc]; rfl
  · simp only [wp_norm, hx29_1]
  · unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap
    rw [trAt_eq_rest A s0.sp trG tr,
        messageKeysAt_eq (s0.sp - 1504#64) mks,
        s7_scr_split (s0.sp - 1504#64),
        stackAt_sub_split (s0.sp - 1504#64) (cmStack + 288) hhi]
    have hmf1 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus (verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64)
      okTagVec 1#8) (by sep_focus) hmf
    clear hmf
    simp only [wp_norm, sepConj_assoc] at hmf1 ⊢
    sep_close

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_false_ok_withStack_ext
    {cmStack : Nat} (hlo : extHookStack ≤ cmStack + 288) (hhi : cmStack + 288 ≤ tryDecryptSubStack)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hW : Stage2ContractsWeak img C A ext)
    (hVMac : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpecWithStack img C.F A uuidTryParse cmStack).inImage img))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false)
    (h7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7State A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.hfn_tryDecrypt
  decrypt_fetches_ext_cli_pq img.base ext hfn 0x63c 60
  decrypt_fetches_ext_cli_pq img.base ext hfn 0x914 88
  decrypt_fetches_ext_cli_pq img.base ext hfn 0x9d0 12
  decrypt_fetches_ext_cli_pq img.base ext hfn 0xcbc 12
  have hS7_pc := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.segS7PC_eq_ext himg ext
  have hErr_pc := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.errTailPC_eq_ext himg ext
  have hshim := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.shim_ok_at_ext img hW
  have halloc := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.alloc_ok_at_ext img hW
  have hdealloc := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.dealloc_ok_at_ext img hW
  have hpan_ext := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.externAt_handle_error_ext img ext
  have halign := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hadrp := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.adrp_macFailedStr_ext halign ext
  have hbl_vmac := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.bl_verifyMac_target_ext img ext
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  rw [hS7_pc] at hpc
  dsimp only [tripleRatchetProgAtExt] at *
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr verifyMacWithAddressesName = vmac_entry at hbl_vmac hVMac
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      s7_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) (cmStack + 288) hhi,
      show s0.sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = s0.sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at hmem
  simp only [wp_norm, ← sepConj_assoc] at hpc hx20 hx22 hx23 hx25 hx27 hx28 hmem
  refine sepWPp_to_steps_or_panic (entry + bv% (780)) hmem hL ?_
  apply SepWPp.of_sepWP_frozen hfl hsym (mid := vmac_entry)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hfl1 hsym1
  refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.call_inImage_frame (img := img)
    (spec := verifyMacWithAddressesSpecWithStack img C.F A uuidTryParse cmStack)
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
          A.pool ∗ stackAt (s0.sp - 1504#64) (cmStack + 288))
    (ret_pc := entry + bv% (1632))
    hfl1 hsym1 hVMac (by rfl) (by exact hrun)
    (CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpecWithStack]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by
      dsimp only [verifyMacWithAddressesSpecWithStack] at h
      rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpecWithStack] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 (entry + bv% (1632))
        |>.setPC vmac_entry).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecrypt_onPanic_of_callee
        C A ctl S img x s0 _ sf _ R h0m hm_pan) ?_
  clear hfl1 hsym1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hfl1 hsym1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1,
    hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpecWithStack]
  rw [hok]
  unfold verifyMacResultAt
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.mono_focus
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.stackAt_sub_to_ext s0.sp hlo hhi)
    (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl1 hsym1
    (mid := entry + bv% ((2 ^ 64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hfl2 hsym2
  refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.call_inImage_frame (img := img) (spec := withStack sessionShimSpec extHookStack) (x := ())
    (T := stackAt (s0.sp - 1504#64) extHookStack) (ret_pc := entry + bv% (2328))
    hfl2 hsym2 hshim (by rfl) (by exact hrun1)
    (CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [withStack, sessionShimSpec]; simp only [wp_norm, hsp1, pure_sepConj, true_and, emp_sepConj])
    trivial
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [withStack, sessionShimSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [withStack, sessionShimSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl2 hsym2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hfl2 hsym2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, hx27_1, hx28_1,
    hx29_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2
  dsimp only [withStack, sessionShimSpec]
  simp only [wp_norm, hsp1, sepConj_assoc]
  apply CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_pure; intro htr2
  simp only [htr1] at htr2
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl2 hsym2
    (mid := entry + bv% ((2 ^ 64 + ls_off% "__rustc::__rust_alloc" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hfl3 hsym3
  refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.call_inImage_frame (img := img) (spec := rustAllocSpecWithStack A extHookStack) (x := (23, 1))
    (T := A.pool ∗ stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := entry + bv% (2340))
    hfl3 hsym3 halloc (by rfl) (by exact hrun2)
    (CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [rustAllocSpecWithStack]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by decide, ⟨0, rfl⟩, by decide⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [rustAllocSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [rustAllocSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl3 hsym3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hfl3 hsym3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3,
    hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2,
    hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
  dsimp only [rustAllocSpecWithStack]
  simp only [wp_norm, hsp2, sepConj_assoc]
  set p := s3.readReg64 .x0
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte]
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_pure_focus (by sep_focus) fun htr3 => ?_
    simp only [htr2] at htr3
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP
      (mid := entry + bv% ((2 ^ 64 + ls_off% "alloc::raw_vec::handle_error" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWP.setPC_ite_true (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.panic_direct_ext
      C A ctl S img ext x s0 _ _ _ _ R
      (by rfl) (by exact hrun3) hpan_ext
      (by simp only [writeReg64_trace, setPC_trace, htr3])
  · simp only [hp, ↓reduceIte, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_pure_focus (by sep_focus) fun h => ?_
    have htr3 := h.2
    simp only [htr2] at htr3
    have hmf_ent := verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 0#8
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.mono_focus hmf_ent (by sep_focus) ?_
    rw [macFailed_alloc_split p]
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_memRegion8_focus (a := p) (by sep_focus) fun pw0 => ?_
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_memRegion8_focus (a := p + 8#64) (by sep_focus) fun pw1 => ?_
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun sw0 => ?_
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun sw1 => ?_
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun sw2 => ?_
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun sb0 => ?_
    intro R' hm3
    have hm3_ro := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.rodata_macFailed_intro himg hfl3.roData hm3
    clear hm3
    rw [rodata_macFailed_split1, ← sepConj_assoc] at hm3_ro
    revert R' hm3_ro
    change SepWPp _ _ _ _ _ _
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl3 hsym3 (mid := entry + bv% (2360))
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWP.setPC_ite_false (by simp only [beq_iff_eq]; exact hp)
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
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.mono_focus (macFailed_overlap_prep p) (by sep_focus) ?_
    refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_memRegion8_focus (a := p + 15#64) (by sep_focus) fun pw2 => ?_
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · simp only [sepConj_assoc]
      refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.mono_focus
        (show (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
          (newPqrPtr ↦ₛ newPqrState) ∗
          memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat -
            newPqrState.length)) ⊢ emp by
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
      · unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA
          newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close
    · simp only [sepConj_assoc]
      refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.mono_focus (newPqr_dealloc_prep A newPqrCap newPqrPtr newPqrState hpqr_cap
        hpqr_le hpqr_lt) (by sep_focus) ?_
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_frozen hfl4 hsym4
        (mid := entry + bv% ((2 ^ 64 + ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hfl5 hsym5
      refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.call_inImage_frame (img := img) (spec := rustDeallocExternSpecWithStack A extHookStack)
        (x := (newPqrPtr, newPqrCap.toNat, 1))
        (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) extHookStack)
        (ret_pc := entry + bv% (2520))
        hfl5 hsym5 hdealloc (by rfl) (by exact hrun3)
        (CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by
          dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun sf _ _ hm_pan => by
          dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hfl5 hsym5
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hfl5 hsym5
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4,
        hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3,
        hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpecWithStack]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.elim_pure; intro htr4
      simp only [htr3] at htr4
      simp only [← sepConj_assoc]
      have hrun4' : (s4.setPC (entry + bv% (780))).status = .Running := by simp only [wp_norm, hrun4]
      have hsp4' : (s4.setPC (entry + bv% (780))).sp = s0.sp - 1504#64 := by simp only [wp_norm, hsp4]
      have hsp_al4' : (s4.setPC (entry + bv% (780))).spAligned = true :=
        CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4
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
      · unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA
          newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_ok_withStack_ext
    {cmStack : Nat} (hlo : extHookStack ≤ cmStack + 288) (hhi : cmStack + 288 ≤ tryDecryptSubStack)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hW : Stage2ContractsWeak img C A ext)
    (hVMac : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpecWithStack img C.F A uuidTryParse cmStack).inImage img))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (h7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7State A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
      ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
    else
      ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1
            (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  by_cases hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse)
    x.rem x.loc) tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true
  · simp only [hok, ↓reduceIte]
    exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_true_ok_withStack_ext
      hhi img C A ctl S ext himg hVMac x trG tr st1 mks newPqrState draws R s0 s hok h7 hL
  · have hok_false : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse
      uuidTryParse) x.rem x.loc) tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false :=
      Bool.eq_false_iff.mpr hok
    simp only [hok_false, Bool.false_eq_true, ↓reduceIte]
    exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_false_ok_withStack_ext
      hlo hhi img C A ctl S ext himg hW hVMac x trG tr st1 mks newPqrState draws R s0 s hok_false h7 hL

/-- Specialization of `s7_ok_withStack_ext` to `VerifyMacWithAddressesOkX` (`computeMacStackX`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_ok_x_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hW : Stage2ContractsWeak img C A ext)
    (hVMac : VerifyMacWithAddressesOkX img C A uuidTryParse ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (h7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7State A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
      ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
    else
      ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1
            (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_ok_withStack_ext
    (cmStack := computeMacStackX) (by decide) (by decide) img C A ctl S ext himg hW hVMac
    x trG tr st1 mks newPqrState draws R s0 s h7 hL

/-- Headline `S7` theorem proving `DecryptPq.S7Spec_ext img C A ctl uuidTryParse S ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_ok_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec_ext img C A ctl uuidTryParse S ext := by
  intro himg hC _hM hVMac x trG tr st1 mks newPqrState draws R s0 s h7 hL
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_ok_withStack_ext
    (cmStack := CryptoVerification.LibsignalTripleRatchet.Statements.computeMacStackExt32)
    (by decide) (by decide) img C A ctl S ext himg hC.toStage2ContractsX hVMac
    x trG tr st1 mks newPqrState draws R s0 s h7 hL

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegBackS7
