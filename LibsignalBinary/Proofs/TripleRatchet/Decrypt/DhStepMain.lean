/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepErr
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Segment S3 (`DhStep`) Key-Generation, Sending Chain, and Top-Level Proofs

Composes key generation and the second `RootKey::create_chain` call (`+0x70c → +0x8ac / +0x30c`)
with `dhStep_missing_sender_chain`, `dhStep_recv_create_chain`, and `dhCommit_spec` to establish
`dhStep_ok` (`DhStepSpec`) and relocatable `DhStepBlockWp` contracts.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem dhStep_after_cc1_to_cc2_call {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdpk : DerivePublicKeyBytesOkExt img.base C ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (rk1 : RootKey) (rck : ChainKey) (R : SepProp) (s0 s : State)
    (hrng : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + bv% (ls_off% "libsignal_session_rng_fill" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (rngFillAtSpec ctl x.cur x.rest))
    (hsd : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + bv% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) zeroizeSecretSpec)
    (hafter : DhStepAfterRecvChainState A ctl img x trG tr st1 rk1 rck R s0 s)
    (hcode : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    let draws := min 32 x.rest.length
    let newSenderKey := KeyPair.generate C (coinsOf x.rest)
    ∃ s5, Steps (tripleRatchetProgAtExt img.base ext) s s5 ∧
      s5.pc = (tripleRatchetProgAtExt img.base ext).fnAddr createChainName ∧
      tryDecryptMidMeta img s0 s5 ∧
      s5.readReg64 .x0 = sp + 0x4a0#64 ∧
      s5.readReg64 .x1 = x.msgA + 56#64 ∧
      s5.readReg64 .x2 = sp + 0x420#64 ∧
      s5.readReg64 .x8 = sp + 0x190#64 ∧
      s5.readReg64 .x19 = x.ret ∧
      s5.readReg64 .x20 = sp + 0x140#64 ∧
      s5.readReg64 .x21 = x.ss ∧
      s5.readReg64 .x22 = x.msgA ∧
      s5.readReg64 .x23 = sp + 0x500#64 ∧
      s5.readReg64 .x25 = sp + 0x190#64 ∧
      s5.readReg64 .x26 = sp + 0x2c0#64 ∧
      s5.readReg64 .x27 = sp + 0x38#64 ∧
      s5.readReg64 .x28 = sp + 0x3d0#64 ∧
      s5.readReg64 .x30 = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 2008#64 ∧
      ∃ (msgW : BitVec 32),
        msgW.setWidth 8 = msgTypeByte x.msgType ∧
        (s5.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
          memRegion x.ret 48 ∗
          memRegion sp 0x10 ∗
          ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
          memRegion (sp + 0x14#64) 8 ∗
          ((sp + 0x1c#64) ↦₃₂ msgW) ∗
          ((sp + 0x20#64) ↦₆₄ x.locA) ∗
          ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 0x2c#64) 4 ∗
          ((sp + 0x30#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 0x140#64) 0x50 ∗
          memRegion (sp + 0x190#64) 72 ∗
          memRegion (sp + 0x1d8#64) 0x1f8 ∗
          ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
          memRegion (sp + 0x3f4#64) 12 ∗
          ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
          ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
          memRegion (sp + 0x440#64) 0x60 ∗
          ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
          ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
          ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
          memRegion (sp + 0x4e0#64) 0xa0 ∗
          tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
  obtain ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hmem⟩ := hafter
  set sp := s0.sp - 1504#64
  set draws := min 32 x.rest.length
  set newSenderKey := KeyPair.generate C (coinsOf x.rest)
  set msgW : BitVec 32 := (s.readReg64 .x24).setWidth 32
  have hmsgW : msgW.setWidth 8 = msgTypeByte x.msgType := by
    have h8 : msgW.setWidth 8 = (s.readReg64 .x24).setWidth 8 := by
      dsimp only [msgW]
      bv_kernel
    exact h8.trans hx24
  let BaseRest : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
    memRegion x.ret 48 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50
  have hmem0 : s.mem ⊨
      memRegion sp 0x20 ∗
      ((sp + 0x190#64) ↦₃₂ 0#32) ∗
      ((sp + 0x194#64) ↦ₛ keyToBytes32 rk1) ∗
      ((sp + 0x1b4#64) ↦ₛ chainKeyBytes rck) ∗
      memRegion (sp + 0x1d8#64) 0x3a8 ∗
      (BaseRest ∗ tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [BaseRest, sp]; ac_rfl)) hmem
  obtain ⟨s1, hsteps1, hpc1, hmeta1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1,
    hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hv0_1, hmem1⟩ :=
    dhStep_step_70c_to_778 (ext := ext)
      himg rk1 rck (BaseRest ∗ tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) s0 s
      hpc hmeta hx23 hx25 hx26 hx28 hmem0 hcode
  rw [tryDecryptCommonHeap_split_tape A ctl img x 0 s0] at hmem1
  have hmem1_in : s1.mem ⊨
      memRegion (sp + 0x190#64) 0x20 ∗
      tapeAfter ctl x.cur x.rest 0 ∗
      (memRegion sp 0x10 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       memRegion (sp + 0x1b0#64) 0x220 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       memRegion (sp + 0x400#64) 0xa0 ∗
       ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
       memRegion (sp + 0x4e0#64) 0x20 ∗
       memRegion (sp + 0x500#64) 0x80 ∗
       BaseRest ∗
       (protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        logOff img ∗
        stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ∗ R) :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by dsimp only [msgW, sp]; ac_rfl)) hmem1
  obtain ⟨s2, hsteps2, hpc2, hmeta2, hcs2, hmem2⟩ :=
    dhStep_step_778_to_780 (img := img) (ctl := ctl) (ext := ext)
      x.cur x.rest _ s0 s1 hrng hpc1 hmeta1 hx0_1 hx1_1 hx25_1 hv0_1 hmem1_in
      (hsteps1.codeLoaded hcode)
  have hsteps12 := Steps.trans hsteps1 hsteps2
  have hmem2_in : s2.mem ⊨
      ((sp + 0x190#64) ↦ₛ (Ratchet.keyToBytesVec32 (coinsOf x.rest)).toList) ∗
      (memRegion sp 0x10 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       memRegion (sp + 0x1b0#64) 0x220 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       memRegion (sp + 0x400#64) 0xa0 ∗
       ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
       memRegion (sp + 0x4e0#64) 0x20 ∗
       memRegion (sp + 0x500#64) 0x80 ∗
       BaseRest ∗
       tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    rw [tryDecryptCommonHeap_split_tape A ctl img x draws s0]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [draws, sp]; ac_rfl)) hmem2
  obtain ⟨s3, hsteps3, hpc3, hmeta3, hx0_3, hx8_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3,
    hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hmem3⟩ :=
    dhStep_step_780_to_7a8 (img := img) (ext := ext)
      (Ratchet.keyToBytesVec32 (coinsOf x.rest)) _ s0 s2 hpc2 hmeta2 hmem2_in
      (hsteps12.codeLoaded hcode)
  have hsteps123 := Steps.trans hsteps12 hsteps3
  have hx23_3' : s3.readReg64 .x23 = sp + 0x500#64 := hx23_3.trans (hcs2.2.2.2.2.1.trans hx23_1)
  have hx25_3' : s3.readReg64 .x25 = sp + 0x190#64 := hx25_3.trans (hcs2.2.2.2.2.2.2.1.trans hx25_1)
  have hmem3_in : s3.mem ⊨
      ((sp + 0x190#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      memRegion (sp + 0x400#64) 32 ∗
      memRegion (sp + 0x500#64) 32 ∗
      (memRegion (sp + 0x420#64) 32 ∗
       memRegion (sp + 0x440#64) 0x60 ∗
       memRegion (sp + 0x520#64) 0x60 ∗
       memRegion sp 0x10 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       memRegion (sp + 0x1b0#64) 0x220 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
       memRegion (sp + 0x4e0#64) 0x20 ∗
       BaseRest ∗
       tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    have h400 := split_400_500_for_keygen sp
    have hmem3' : s3.mem ⊨
        (memRegion (sp + 0x400#64) 0xa0 ∗ memRegion (sp + 0x500#64) 0x80) ∗
        (((sp + 0x190#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
         memRegion sp 0x10 ∗
         ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
         memRegion (sp + 0x14#64) 8 ∗
         ((sp + 0x1c#64) ↦₃₂ msgW) ∗
         memRegion (sp + 0x1b0#64) 0x220 ∗
         ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
         memRegion (sp + 0x3f4#64) 12 ∗
         ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
         ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
         ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
         memRegion (sp + 0x4e0#64) 0x20 ∗
         BaseRest ∗
         tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
      Eq.mp (congrArg (s3.mem ⊨ ·) (by dsimp only [newSenderKey, KeyPair.generate, sp]; ac_rfl)) hmem3
    rw [h400] at hmem3'
    exact Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hmem3'
  obtain ⟨s4, hsteps4, hpc4, hmeta4, hcs4, hmem4⟩ :=
    dhStep_step_7a8_to_7b4 (img := img) (C := C) (ext := ext)
      hdpk newSenderKey.privateKey.bytes _ s0 s3 hpc3 hmeta3 hx0_3 hx8_3 hx23_3' hx25_3' hmem3_in
      (hsteps123.codeLoaded hcode)
  have hsteps1234 := Steps.trans hsteps123 hsteps4
  have hmem4_in : s4.mem ⊨
      memRegion (sp + 0x420#64) 32 ∗
      ((sp + 0x500#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      (memRegion (sp + 0x190#64) 32 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       memRegion (sp + 0x440#64) 0x60 ∗
       memRegion (sp + 0x520#64) 0x60 ∗
       memRegion sp 0x10 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       memRegion (sp + 0x1b0#64) 0x220 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
       memRegion (sp + 0x4e0#64) 0x20 ∗
       BaseRest ∗
       tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
    Eq.mp (congrArg (s4.mem ⊨ ·) (by dsimp only [newSenderKey, KeyPair.generate, sp]; ac_rfl)) hmem4
  obtain ⟨s5, hsteps5, hpc5, hmeta5, hx0_5, hx1_5, hx2_5, hx8_5, hx30_5, hcs5, hmem5⟩ :=
    dhStep_step_7b4_to_7d4 (img := img) (ext := ext)
      hsd x.msgA newSenderKey.privateKey.bytes _ s0 s4 hpc4 hmeta4 (by reg_chain) (by reg_chain)
      (by reg_chain) (by reg_chain) hmem4_in
      (hsteps1234.codeLoaded hcode)
  have hsteps12345 := Steps.trans hsteps1234 hsteps5
  have hmem5' : s5.mem ⊨
      (memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 0x220 ∗
       memRegion (sp + 0x4e0#64) 0x20 ∗ memRegion (sp + 0x500#64) 32 ∗ memRegion (sp + 0x520#64) 0x60) ∗
      (((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
       memRegion (sp + 0x440#64) 0x60 ∗
       ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
       memRegion sp 0x10 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       BaseRest ∗
       tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
    Eq.mp (congrArg (s5.mem ⊨ ·) (by dsimp only [sp]; ac_rfl)) hmem5
  rw [split_190_4e0_for_cc2 sp] at hmem5'
  exact ⟨s5, hsteps12345, hpc5, hmeta5, hx0_5, hx1_5, hx2_5, hx8_5, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    hx30_5, msgW, hmsgW,
    Eq.mp (congrArg (s5.mem ⊨ ·) (by dsimp only [BaseRest]; ac_rfl)) hmem5'⟩

/-- Step `+0x70c → +0x8ac` (or `+0x30c` `ErrTailState` on `.error .invalidKeyAgreement`, or panic):
from `DhStepAfterRecvChainState` at `+0x70c`, stages `rk1` and `rck`, generates `newSenderKey =
KeyPair.generate C (coinsOf x.rest)`, calls `RootKey::create_chain` #2 (`+0x7d4`),
and branches on the result tag (`+0x7d8..+0x7f4`). -/
theorem dhStep_keygen_and_send_create_chain {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hcc : CreateChainOkExt img C A ext)
    (hdpk : DerivePublicKeyBytesOkExt img.base C ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (rk1 : RootKey) (rck : ChainKey) (R : SepProp) (s0 s : State)
    (hrng : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + bv% (ls_off% "libsignal_session_rng_fill" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (rngFillAtSpec ctl x.cur x.rest))
    (hsd : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + bv% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) zeroizeSecretSpec)
    (hrk2_ne : s0.sp - 1504#64 + 0x4a0#64 ≠ 0#64)
    (hafter : DhStepAfterRecvChainState A ctl img x trG tr st1 rk1 rck R s0 s)
    (hcode : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    let newSenderKey := KeyPair.generate C (coinsOf x.rest)
    match rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey with
    | .ok (finalRootKey, senderChainKey) =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (DhCommitState A ctl img x trG tr st1 rck newSenderKey finalRootKey senderChainKey R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
    | .error e =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        ((∃ trG' r1, ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e (min 32 x.rest.length) R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  set sp := s0.sp - 1504#64
  set draws := min 32 x.rest.length
  set newSenderKey := KeyPair.generate C (coinsOf x.rest)
  obtain ⟨s5, hsteps5, hpc5, hmeta5, hx0_5, hx1_5, hx2_5, hx8_5, hx19_5, hx20_5, hx21_5,
    hx22_5, hx23_5, hx25_5, hx26_5, hx27_5, hx28_5, hx30_5, msgW, hmsgW, hmem5⟩ :=
    dhStep_after_cc1_to_cc2_call himg hdpk x trG tr st1 rk1 rck R s0 s hrng hsd hafter hcode
  obtain ⟨hrun5, hsp5, hsp0_al, hsp_al5, hx29_5, htrace5, hfr5, hsym5, hvregs5⟩ := hmeta5
  let ccG2 : CreateChainGhost :=
    { rkA := sp + 0x4a0#64
      rk := rk1
      theirA := x.msgA + 56#64
      their := x.msg.senderRatchetKey
      ourA := sp + 0x420#64
      our := newSenderKey.privateKey
      ret := sp + 0x190#64 }
  let Frame2 : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x10 ∗
    ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
    memRegion (sp + 0x14#64) 8 ∗
    ((sp + 0x1c#64) ↦₃₂ msgW) ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1d8#64) 0x1f8 ∗
    ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
    memRegion (sp + 0x3f4#64) 12 ∗
    ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
    memRegion (sp + 0x440#64) 0x60 ∗
    ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
    ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
    memRegion (sp + 0x4e0#64) 0xa0 ∗
    protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗
    signalMessageRestAt A x.msgG x.msgA x.msg ∗
    tapeAfter ctl x.cur x.rest draws ∗
    logOff img ∗
    stackAt (sp - BitVec.ofNat 64 createChainStack) (tryDecryptSubStack - createChainStack) ∗
    tryDecryptSavedRegs s0.sp s0
  have hpre_cc2 : s5.mem ⊨ ((createChainSpec C A).inImage img).pre ccG2 s5 ∗ (Frame2 ∗ R) := by
    dsimp only [createChainSpec, Spec.inImage, ccG2, Frame2]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfr5, hsym5⟩, ⟨hx0_5, hx1_5, hx2_5, hx8_5, hrk2_ne⟩, ?_⟩
    rw [show s5.sp = sp from hsp5]
    unfold tryDecryptCommonHeap at hmem5
    rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
        show s0.sp - 1504#64 = sp from rfl,
        stackAt_subStack_createChain sp] at hmem5
    exact Eq.mp (congrArg (s5.mem ⊨ ·) (by dsimp only [sp, draws, newSenderKey]; ac_rfl)) hmem5
  obtain ⟨sm, hsteps_cc2, hout_cc2, -⟩ :=
    hcc.no_fault_before_outcome ccG2 (Frame2 ∗ R) s5 hpc5 hrun5 hpre_cc2 hsp_al5
      (hsteps5.codeLoaded hcode)
  have hsteps5m : Steps (tripleRatchetProgAtExt img.base ext) s sm := Steps.trans hsteps5 hsteps_cc2
  rcases hout_cc2 with ⟨hret_m, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, -, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · -- Normal return from `RootKey::create_chain` #2
    have hpcm : sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 2008#64 :=
      hret_m.1.trans hx30_5
    have hrunm : sm.status = .Running := hret_m.2.2
    dsimp only [createChainSpec, Spec.inImage, ccG2] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfr_m : img.FrozenLoaded sm := hsteps_cc2.frozenLoaded hfr5
    have hsym_m : sm.symtab = img.symtab := hsteps_cc2.symtab_eq.trans hsym5
    have htrace_m0 := hpost.1
    have hpost := hpost.2
    have hsp_al_m : sm.spAligned = true := by
      unfold State.spAligned at hsp_al5 ⊢
      rw [hspm]
      exact hsp_al5
    have hmeta_m : tryDecryptMidMeta img s0 sm :=
      ⟨hrunm, by reg_chain, hsp0_al, hsp_al_m, by reg_chain, by reg_chain, hfr_m, hsym_m, by reg_chain⟩
    have hpost_grouped : sm.mem ⊨
        createChainResultAt (sp + 0x190#64) (rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey) ∗
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗
        memRegion sp 0x10 ∗
        ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
        memRegion (sp + 0x14#64) 8 ∗
        ((sp + 0x1c#64) ↦₃₂ msgW) ∗
        ((sp + 0x20#64) ↦₆₄ x.locA) ∗
        ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗
        ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x1d8#64) 0x1f8 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
        memRegion (sp + 0x3f4#64) 12 ∗
        ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
        ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
        memRegion (sp + 0x440#64) 0x60 ∗
        ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
        ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
        ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
        memRegion (sp + 0x4e0#64) 0xa0 ∗
        tryDecryptCommonHeap A ctl img x draws s0 ∗ R := by
      dsimp only [Frame2] at hpost
      rw [show s5.sp = sp from hsp5] at hpost
      unfold tryDecryptCommonHeap
      rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
          show s0.sp - 1504#64 = sp from rfl,
          stackAt_subStack_createChain sp]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hpost
    dsimp only
    unfold rootCreateChain at hpost_grouped ⊢
    cases hcc2 : Ratchet.createChain C.F C.X rk1 x.msg.senderRatchetKey.bytes newSenderKey.privateKey.bytes with
    | none =>
      rw [hcc2] at hpost_grouped
      dsimp only at hpost_grouped ⊢
      have hpost_err0 : sm.mem ⊨
          (memRegion (sp + 0x1d8#64) 0x1f8 ∗
           ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
           memRegion (sp + 0x3f4#64) 12 ∗
           ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
           ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
           memRegion (sp + 0x440#64) 0x60 ∗
           ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
           ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
           ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
           memRegion (sp + 0x4e0#64) 0xa0) ∗
          (((sp + 0x1c#64) ↦₃₂ msgW) ∗
           memRegion (sp + 0x140#64) 0x50 ∗
           createChainResultAt (sp + 0x190#64) (.error .invalidKeyAgreement) ∗
           sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗
           memRegion sp 0x10 ∗
           ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
           memRegion (sp + 0x14#64) 8 ∗
           ((sp + 0x20#64) ↦₆₄ x.locA) ∗
           ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗
           ((sp + 0x30#64) ↦₆₄ x.remA) ∗
           tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hpost_grouped
      have hpost_err1 := Satisfies.mono (sepConj_mono_left
        (fold_1d8_after_cc2_err sp rck newSenderKey.publicKey.bytes.toList newSenderKey.privateKey.bytes.toList rk1
          newSenderKey.publicKey.bytes.2 newSenderKey.privateKey.bytes.2)) hpost_err0
      let Rest_err : SepProp :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗
        memRegion sp 0x10 ∗
        ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
        memRegion (sp + 0x14#64) 8 ∗
        ((sp + 0x20#64) ↦₆₄ x.locA) ∗
        ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗
        ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        tryDecryptCommonHeap A ctl img x draws s0 ∗ R
      have hmem_err : sm.mem ⊨
          ((sp + 0x1c#64) ↦₃₂ msgW) ∗
          memRegion (sp + 0x140#64) 0x50 ∗
          createChainResultAt (sp + 0x190#64) (.error .invalidKeyAgreement) ∗
          memRegion (sp + 0x1d8#64) 0x3a8 ∗ Rest_err :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_err]; ac_rfl)) hpost_err1
      obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
        dhStep_cc2_err_branch (A := A) (ext := ext)
          himg msgW Rest_err s0 sm hpcm hmeta_m (by reg_chain) (by reg_chain) (by reg_chain)
          (by reg_chain) hmem_err
          (hsteps5m.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps5m hsteps2, Or.inl ⟨trG, { tr.ratchet with rootKey := (0 : RootKey) }, ?_⟩⟩
      refine ⟨hpcs', hmetas', by reg_chain, hx20s', hx26s', ?_⟩
      dsimp only [Rest_err] at hmems'
      have hmems0 : s'.mem ⊨
          (memRegion sp 0x10 ∗
           ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
           memRegion (sp + 0x14#64) 8 ∗
           ((sp + 0x1c#64) ↦₃₂ msgW)) ∗
          (((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
           sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗
           memRegion (sp + 0x140#64) 0x28 ∗
           speBodyAt A (utf8 "decrypt") (sp + 0x168#64) .invalidKeyAgreement ∗
           memRegion (sp + 0x190#64) 0x3f0 ∗
           tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
        Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp] at hmems' ⊢; ac_rfl)) hmems'
      have hmems0' := Satisfies.mono (sepConj_mono_left (fold_sp_20_after_cc2_err sp rck msgW)) hmems0
      have hsp38_ent :
          (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ⊢
          memRegion sp 0x38 := by
        rw [memRegion_split' (b := sp) (b' := sp + 0x20#64) (n := 0x20) (k := 0x18) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x20#64) (b' := sp + 0x28#64) (n := 0x8) (k := 0x10) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x28#64) (b' := sp + 0x2c#64) (n := 0x4) (k := 0xc) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x2c#64) (b' := sp + 0x30#64) (n := 0x4) (k := 0x8) rfl (by bv_arith) (by decide)]
        exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _)
            (sepConj_mono_right (pointsTo64_entails_memRegion _ _))))
      have hmems1 : s'.mem ⊨
          (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ∗
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗
           memRegion (sp + 0x140#64) 0x28 ∗
           speBodyAt A (utf8 "decrypt") (sp + 0x168#64) .invalidKeyAgreement ∗
           memRegion (sp + 0x190#64) 0x3f0 ∗
           tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
        Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems0'
      have hmems2 := Satisfies.mono (sepConj_mono_left hsp38_ent) hmems1
      dsimp only [sp, draws] at hmems2 ⊢
      exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems2
    | some p2 =>
      rcases p2 with ⟨finalRootKey, sckKey⟩
      rw [hcc2] at hpost_grouped
      dsimp only at hpost_grouped ⊢
      have hpost_ok0 : sm.mem ⊨
          (memRegion (sp + 0x1d8#64) 0x1f8 ∗
           memRegion (sp + 0x440#64) 0x60 ∗
           ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1)) ∗
          (createChainResultAt (sp + 0x190#64) (.ok (finalRootKey, ⟨sckKey, 0⟩)) ∗
           sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗
           memRegion sp 0x10 ∗
           ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
           memRegion (sp + 0x14#64) 8 ∗
           ((sp + 0x1c#64) ↦₃₂ msgW) ∗
           ((sp + 0x20#64) ↦₆₄ x.locA) ∗
           ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗
           ((sp + 0x30#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 0x140#64) 0x50 ∗
           ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
           memRegion (sp + 0x3f4#64) 12 ∗
           ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
           ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
           ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
           ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
           memRegion (sp + 0x4e0#64) 0xa0 ∗
           tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hpost_grouped
      have hpost_ok1 := Satisfies.mono (sepConj_mono_left (fold_after_cc2_ok sp rk1)) hpost_ok0
      let Rest_ok : SepProp :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗
        memRegion sp 0x10 ∗
        ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
        memRegion (sp + 0x14#64) 8 ∗
        ((sp + 0x1c#64) ↦₃₂ msgW) ∗
        ((sp + 0x20#64) ↦₆₄ x.locA) ∗
        ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗
        ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x1d8#64) 0xd8 ∗
        memRegion (sp + 0x2b0#64) 0x10 ∗
        memRegion (sp + 0x2c0#64) 0x110 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
        memRegion (sp + 0x3f4#64) 12 ∗
        ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
        ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
        memRegion (sp + 0x440#64) 0x80 ∗
        ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
        ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
        memRegion (sp + 0x4e0#64) 0xa0 ∗
        tryDecryptCommonHeap A ctl img x draws s0 ∗ R
      have hmem_ok : sm.mem ⊨
          createChainResultAt (sp + 0x190#64) (.ok (finalRootKey, ⟨sckKey, 0⟩)) ∗ Rest_ok :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_ok]; ac_rfl)) hpost_ok1
      obtain ⟨s', hsteps2, hpcs', hmetas', hcss', hmems'⟩ :=
        dhStep_cc2_ok_branch (ext := ext)
          himg finalRootKey ⟨sckKey, 0⟩ Rest_ok s0 sm hpcm hmeta_m hmem_ok
          (hsteps5m.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps5m hsteps2, Or.inl ?_⟩
      refine ⟨hpcs', hmetas', by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
        by reg_chain, by reg_chain, by reg_chain, msgW, hmsgW, ?_⟩
      dsimp only [Rest_ok, sp, draws, newSenderKey] at hmems' ⊢
      exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems'
  · -- Panic in `RootKey::create_chain` #2
    have hpan_td := onPanic_of_createChain (ctl := ctl) (S := S) (x := x) htrace5 hpost
    dsimp only
    cases rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey with
    | ok p2 =>
      rcases p2 with ⟨finalRootKey, senderChainKey⟩
      exact ⟨sm, hsteps5m, Or.inr ⟨hpan, hpan_td⟩⟩
    | error e =>
      exact ⟨sm, hsteps5m, Or.inr ⟨hpan, hpan_td⟩⟩
  · -- Impossible `.Exited` case
    dsimp only [createChainSpec, Spec.inImage] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

/-- Top-level proof of `S3SpecExt` (`+0x500 → +0x3e4 / +0x30c` or panic) on `tripleRatchetProgAtExt img.base ext`. -/
theorem s3_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) :
    S3SpecExt img C A ctl uuidTryParse S ext := by
  intro himg hC hcc hdpk hPkSer hToPb hGrowOne hDropChain
    x trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hx_rest hs3 hcode
  dsimp only
  cases hsc : tr.ratchet.senderChain with
  | none =>
    rw [dhRatchetStep_none C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet hsc,
        decryptDraws_of_senderChain_none C x.st st1 tr x.msg.senderRatchetKey x.rest hfrom hfind hsc]
    obtain ⟨s', hsteps, ⟨_, _, herr⟩ | ⟨_, hoom⟩⟩ :=
      dhStep_missing_sender_chain (A := A) (ctl := ctl) (ext := ext)
        himg x trG tr st1 R s0 s hsc hs3 hcode
    · exact ⟨s', hsteps, Or.inl ⟨trG, tr.ratchet, herr⟩⟩
    · exact hoom.elim
  | some sc =>
    have ⟨hrk1_ne, hrk2_ne⟩ := rk_ne_zero s0.sp (s0.sp - 1504#64) rfl hsp0
    have hstep1 := dhStep_recv_create_chain (S := S) himg hcc x trG tr st1 sc R s0 s hsc hrk1_ne hs3 hcode
    cases hcc1 : rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | error e =>
      rw [hcc1] at hstep1
      rw [dhRatchetStep_some_err1 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc e hsc hcc1,
          decryptDraws_of_cc1_err C x.st st1 tr x.msg.senderRatchetKey x.rest sc e hfrom hfind hsc hcc1]
      exact hstep1
    | ok p1 =>
      rcases p1 with ⟨rk1, rck⟩
      rw [hcc1] at hstep1
      rw [decryptDraws_of_cc1_ok C x.st st1 tr x.msg.senderRatchetKey x.rest sc rk1 rck hfrom hfind hsc hcc1]
      obtain ⟨s1, hsteps1, hafter | hpan1⟩ := hstep1
      · have hrng := DhStepCallees.rngFillAt_ok_at2_td_ext (b := img.base) (cur := x.cur) (rest := x.rest) hC hx_rest
        have hsd := DhStepCallees.staticDrop_ok_at2_td_ext (b := img.base) hC
        have hstep2 := dhStep_keygen_and_send_create_chain (S := S)
          himg hcc hdpk x trG tr st1 rk1 rck R s0 s1 hrng hsd hrk2_ne hafter (hsteps1.codeLoaded hcode)
        dsimp only at hstep2
        cases hcc2 : rootCreateChain C rk1 x.msg.senderRatchetKey
            (KeyPair.generate C (coinsOf x.rest)).privateKey with
        | error e =>
          rw [hcc2] at hstep2
          rw [dhRatchetStep_some_err2 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 rck e hsc hcc1 hcc2]
          obtain ⟨s2, hsteps2, herr2⟩ := hstep2
          exact ⟨s2, Steps.trans hsteps1 hsteps2, herr2⟩
        | ok p2 =>
          rcases p2 with ⟨finalRootKey, senderChainKey⟩
          rw [hcc2] at hstep2
          rw [dhRatchetStep_some_ok C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 finalRootKey rck senderChainKey hsc hcc1 hcc2]
          obtain ⟨s2, hsteps2, hcommit | hpan2⟩ := hstep2
          · have hsteps12 := Steps.trans hsteps1 hsteps2
            have hclamp := clampScalar_keyPair_generate C (coinsOf x.rest)
            obtain ⟨s3, hsteps3, hout3⟩ :=
              DhCommit.s3_commit_spec_ext img C A ctl S ext
                himg hC.toAllocContracts hPkSer hToPb hGrowOne hDropChain
                x trG tr st1 sc rck (KeyPair.generate C (coinsOf x.rest))
                finalRootKey senderChainKey R s0 s2
                hsc hrc_len hclamp hcommit (hsteps12.codeLoaded hcode)
            exact ⟨s3, Steps.trans hsteps12 hsteps3, hout3⟩
          · exact ⟨s2, Steps.trans hsteps1 hsteps2, Or.inr hpan2⟩
      · cases hcc2 : rootCreateChain C rk1 x.msg.senderRatchetKey
            (KeyPair.generate C (coinsOf x.rest)).privateKey with
        | error e =>
          rw [dhRatchetStep_some_err2 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 rck e hsc hcc1 hcc2]
          exact ⟨s1, hsteps1, Or.inr hpan1⟩
        | ok p2 =>
          rcases p2 with ⟨finalRootKey, senderChainKey⟩
          rw [dhRatchetStep_some_ok C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 finalRootKey rck senderChainKey hsc hcc1 hcc2]
          exact ⟨s1, hsteps1, Or.inr hpan1⟩

/-- Top-level proof of `DhStepSpec` (`+0x500 → +0x3e4 / +0x30c` or panic): combines
`dhStep_missing_sender_chain`, `dhStep_recv_create_chain`, `dhStep_keygen_and_send_create_chain`,
and `DhCommit.dhCommit_spec`. -/
theorem dhStep_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) :
    DhStepSpec img C A ctl uuidTryParse S abs := by
  intro himg hHooks hcc hdpk hPkSer hToPb hGrowOne hDropChain
    x trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hs3 hcode
  dsimp only
  cases hsc : tr.ratchet.senderChain with
  | none =>
    rw [dhRatchetStep_none C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet hsc,
        decryptDraws_of_senderChain_none C x.st st1 tr x.msg.senderRatchetKey x.rest hfrom hfind hsc]
    obtain ⟨s', hsteps, ⟨_, _, herr⟩ | ⟨_, hoom⟩⟩ :=
      dhStep_missing_sender_chain (A := A) (ctl := ctl) (ext := tripleRatchetExterns C ctl abs)
        himg x trG tr st1 R s0 s hsc hs3 hcode
    · exact ⟨s', hsteps, Or.inl ⟨trG, tr.ratchet, herr⟩⟩
    · exact hoom.elim
  | some sc =>
    have ⟨hrk1_ne, hrk2_ne⟩ := rk_ne_zero s0.sp (s0.sp - 1504#64) rfl hsp0
    have hstep1 := dhStep_recv_create_chain (S := S) himg hcc x trG tr st1 sc R s0 s hsc hrk1_ne hs3 hcode
    cases hcc1 : rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | error e =>
      rw [hcc1] at hstep1
      rw [dhRatchetStep_some_err1 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc e hsc hcc1,
          decryptDraws_of_cc1_err C x.st st1 tr x.msg.senderRatchetKey x.rest sc e hfrom hfind hsc hcc1]
      exact hstep1
    | ok p1 =>
      rcases p1 with ⟨rk1, rck⟩
      rw [hcc1] at hstep1
      rw [decryptDraws_of_cc1_ok C x.st st1 tr x.msg.senderRatchetKey x.rest sc rk1 rck hfrom hfind hsc hcc1]
      obtain ⟨s1, hsteps1, hafter | hpan1⟩ := hstep1
      · have hrng := DhStepCallees.rngFillAt_ok_at2_td (b := img.base) (C := C) (ctl := ctl)
          (abs := abs) (cur := x.cur) (rest := x.rest)
        have hsd := DhStepCallees.staticDrop_ok_at2_td (b := img.base) (C := C) (ctl := ctl) (abs := abs)
        have hstep2 := dhStep_keygen_and_send_create_chain (S := S)
          himg hcc hdpk x trG tr st1 rk1 rck R s0 s1 hrng hsd hrk2_ne hafter (hsteps1.codeLoaded hcode)
        dsimp only at hstep2
        cases hcc2 : rootCreateChain C rk1 x.msg.senderRatchetKey
            (KeyPair.generate C (coinsOf x.rest)).privateKey with
        | error e =>
          rw [hcc2] at hstep2
          rw [dhRatchetStep_some_err2 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 rck e hsc hcc1 hcc2]
          obtain ⟨s2, hsteps2, herr2⟩ := hstep2
          exact ⟨s2, Steps.trans hsteps1 hsteps2, herr2⟩
        | ok p2 =>
          rcases p2 with ⟨finalRootKey, senderChainKey⟩
          rw [hcc2] at hstep2
          rw [dhRatchetStep_some_ok C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 finalRootKey rck senderChainKey hsc hcc1 hcc2]
          obtain ⟨s2, hsteps2, hcommit | hpan2⟩ := hstep2
          · have hsteps12 := Steps.trans hsteps1 hsteps2
            have hclamp := clampScalar_keyPair_generate C (coinsOf x.rest)
            obtain ⟨s3, hsteps3, hout3⟩ :=
              DhCommit.dhCommit_spec img C A ctl S abs
                himg hHooks hPkSer hToPb hGrowOne hDropChain
                x trG tr st1 sc rck (KeyPair.generate C (coinsOf x.rest))
                finalRootKey senderChainKey R s0 s2
                hsc hrc_len hclamp hcommit (hsteps12.codeLoaded hcode)
            exact ⟨s3, Steps.trans hsteps12 hsteps3, hout3⟩
          · exact ⟨s2, Steps.trans hsteps1 hsteps2, Or.inr hpan2⟩
      · cases hcc2 : rootCreateChain C rk1 x.msg.senderRatchetKey
            (KeyPair.generate C (coinsOf x.rest)).privateKey with
        | error e =>
          rw [dhRatchetStep_some_err2 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 rck e hsc hcc1 hcc2]
          exact ⟨s1, hsteps1, Or.inr hpan1⟩
        | ok p2 =>
          rcases p2 with ⟨finalRootKey, senderChainKey⟩
          rw [dhRatchetStep_some_ok C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 finalRootKey rck senderChainKey hsc hcc1 hcc2]
          exact ⟨s1, hsteps1, Or.inr hpan1⟩

/-! ## 7. Relocatable `[LibsignalPlacement]` Block WPs for `DhStep` -/

/-- Relocatable intermediate state at `entry + 0x70c#64` after `RootKey::create_chain` #1 succeeds. -/
def DhStepAfterRecvChainStatePlaced [LibsignalPlacement] (entry : BitVec 64)
    (A : RustAlloc) (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (rk1 : RootKey) (rck : ChainKey) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = entry + 0x70c#64 ∧
  tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x26 = sp + 0x2c0#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x2c0#64 ∧
  (s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    ((sp + 0x190#64) ↦₃₂ 0#32) ∗
    ((sp + 0x194#64) ↦ₛ keyToBytes32 rk1) ∗
    ((sp + 0x1b4#64) ↦ₛ chainKeyBytes rck) ∗
    memRegion (sp + 0x1d8#64) 0x3a8 ∗
    tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R)

/-- Propagate an allocator failure panic from `createChainSpec` to `tryDecryptSpecPlaced.onPanic`. -/
theorem onPanic_of_createChain_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {ccG : CreateChainGhost} {s0 sc sm : State} {Frame R : SepProp}
    (htrace : sc.trace = s0.trace)
    (hpost : sm.mem ⊨ (createChainSpec C A).onPanic ccG sc sm ∗ (Frame ∗ R)) :
    sm.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 sm ∗ R :=
  onPanic_of_createChain (ccG := ccG) htrace hpost

/-- Bundle of relocatable basic-block `SepWP` obligations for `DhStep` (`+0x500 → +0x8ac / +0x30c`). -/
structure DhStepBlockWp [LibsignalPlacement] (prog : Program)
    (entry rngFillEntry : BitVec 64) where
  missingScAddr : BitVec 64
  hro_missingSc : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) → (m ⊨ (missingScAddr ↦ᵣ invalidSessionStructureStr .missingSenderChain) ∗ P)
  wpp_2dc_to_30c :
    ∀ (s0 s : State) (w2c0 w2c8 : BitVec 64)
      (u34c u344 u338 u330 u2b8 u2b0 u180 u178 u170 u168 : BitVec 64)
      (u340 u2d0 u18c u188 : BitVec 32),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x2dc#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x12 = sp + 0x2c0#64 →
      s.readReg64 .x20 = sp + 0x140#64 → s.readReg64 .x25 = sp + 0x190#64 →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 780#64) s
        ((memRegion (sp + 0x140#64) 0x28 ∗ (sp + 0x168#64) ↦₆₄ u168 ∗ (sp + 0x170#64) ↦₆₄ u170 ∗
          (sp + 0x178#64) ↦₆₄ u178 ∗ (sp + 0x180#64) ↦₆₄ u180 ∗ (sp + 0x188#64) ↦₃₂ u188 ∗
          (sp + 0x18c#64) ↦₃₂ u18c ∗ memRegion (sp + 0x190#64) 0x120 ∗ (sp + 0x2b0#64) ↦₆₄ u2b0 ∗
          (sp + 0x2b8#64) ↦₆₄ u2b8) ∗ (sp + 0x2c0#64) ↦₆₄ w2c0 ∗ (sp + 0x2c8#64) ↦₆₄ w2c8 ∗
         ((sp + 0x2d0#64) ↦₃₂ u2d0 ∗ memRegion (sp + 0x2d4#64) 0x5c ∗ (sp + 0x330#64) ↦₆₄ u330 ∗
          (sp + 0x338#64) ↦₆₄ u338 ∗ (sp + 0x340#64) ↦₃₂ u340 ∗ (sp + 0x344#64) ↦₆₄ u344 ∗
          (sp + 0x34c#64) ↦₆₄ u34c ∗ memRegion (sp + 0x354#64) 0x22c))
        (fun sf P_f =>
          sf.sp = sp ∧ sf.readReg64 .x29 = s0.sp - 96#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = sp + 0x140#64 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_f ∗ R) →
            (m ⊨ (memRegion (sp + 0x140#64) 0x28 ∗ ((sp + 0x168#64) ↦₆₄ w2c0) ∗
                  ((sp + 0x170#64) ↦₆₄ w2c8) ∗ memRegion (sp + 0x178#64) 24 ∗
                  memRegion (sp + 0x190#64) 0x3f0) ∗ R)))
  wpp_7f8_to_2dc :
    ∀ (s0 s : State) (u508 u500 u2c8 u2c0 u2b8 u2b0 : BitVec 64) (u2d0 : BitVec 32),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x7f8#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x25 = sp + 0x190#64 →
      s.readReg64 .x26 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 732#64) s
        (memRegion (sp + 0x140#64) 0x58 ∗ ((sp + 0x198#64) ↦₆₄ speWord 10) ∗
         memRegion (sp + 0x1a0#64) 0x110 ∗ ((sp + 0x2b0#64) ↦₆₄ u2b0) ∗
         ((sp + 0x2b8#64) ↦₆₄ u2b8) ∗ ((sp + 0x2c0#64) ↦₆₄ u2c0) ∗
         ((sp + 0x2c8#64) ↦₆₄ u2c8) ∗ ((sp + 0x2d0#64) ↦₃₂ u2d0) ∗
         memRegion (sp + 0x2d4#64) 0x22c ∗ ((sp + 0x500#64) ↦₆₄ u500) ∗
         ((sp + 0x508#64) ↦₆₄ u508) ∗ memRegion (sp + 0x510#64) 0x70)
        (fun sm P_m =>
          sm.sp = sp ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x12 = sp + 0x2c0#64 ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = sp + 0x140#64 ∧
          sm.readReg64 .x25 = sp + 0x190#64 ∧ sm.readReg64 .x26 = speTag .invalidKeyAgreement ∧
          sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_m ∗ R) → (m ⊨ memRegion (sp + 0x140#64) 0x440 ∗ R)))
  wpp_missing_sc :
    ∀ (s0 s : State) (x : TryDecryptGhost) (u2c0 u2c8 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x500#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x12 = sp + 0x2c0#64 →
      s.readReg64 .x19 = x.ret → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x27 = sp + 0x38#64 →
      s.readReg64 .x28 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 732#64) s
        (((sp + 0x50#64) ↦₃₂ 0#32) ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
         ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
         ((sp + 0x30#64) ↦₆₄ x.remA) ∗ ((sp + 0x2c0#64) ↦₆₄ u2c0) ∗ ((sp + 0x2c8#64) ↦₆₄ u2c8))
        (fun sm P_m =>
          sm.sp = sp ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x12 = sp + 0x2c0#64 ∧
          sm.readReg64 .x19 = x.ret ∧ sm.readReg64 .x20 = sp + 0x140#64 ∧
          sm.readReg64 .x25 = sp + 0x190#64 ∧
          sm.readReg64 .x26 = speTag (.invalidSessionStructure .missingSenderChain) ∧
          sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_m ∗ R) →
            (m ⊨ (((sp + 0x50#64) ↦₃₂ 0#32) ∗ memRegion sp 0x38 ∗
                  ((sp + 0x2c0#64) ↦₆₄ missingScAddr) ∗ ((sp + 0x2c8#64) ↦₆₄ 20#64)) ∗ R)))
  wpp_cc1_err :
    ∀ (s0 s : State) (u1bc u1b4 u1a8 u1a0 : BitVec 64) (u1c4 u1b0 : BitVec 32),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1352#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x25 = sp + 0x190#64 →
      s.readReg64 .x26 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 2040#64) s
        (((sp + 0x190#64) ↦₃₂ 1#32) ∗ ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗ ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
         ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗ ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗ ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
         ((sp + 0x1c4#64) ↦₃₂ u1c4))
        (fun sm P_m =>
          sm.sp = sp ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = sp + 0x140#64 ∧ sm.readReg64 .x23 = sp + 0x500#64 ∧
          sm.readReg64 .x25 = sp + 0x190#64 ∧ sm.readReg64 .x26 = sp + 0x2c0#64 ∧
          sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_m ∗ R) →
            (m ⊨ (((sp + 0x190#64) ↦₃₂ 1#32) ∗ ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗
                  ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗ ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗
                  ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗ ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
                  ((sp + 0x1c4#64) ↦₃₂ u1c4)) ∗ R)))
  wpp_cc1_ok :
    ∀ (s0 s : State),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1352#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x25 = sp + 0x190#64 → s.trace = s0.trace →
      SepWP prog (entry + 1804#64) s ((sp + 0x190#64) ↦₃₂ 0#32)
        (fun sm P_m =>
          sm.sp = sp ∧ CalleeSavedPreserved s sm ∧ sm.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_m ∗ R) → (m ⊨ ((sp + 0x190#64) ↦₃₂ 0#32) ∗ R)))
  wpp_pre_cc1 :
    ∀ (s0 s : State) (x : TryDecryptGhost)
      (p0 p1 p2 p3 k0 k1 k2 k3 u390 u398 u3a0 u3a8 u3b0 u3b8 u3c0 u3c8 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x500#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x12 = sp + 0x2c0#64 →
      s.readReg64 .x19 = x.ret → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x21 = x.ss → s.readReg64 .x22 = x.msgA →
      s.readReg64 .x23 = sp + 0x500#64 → (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType →
      s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x27 = sp + 0x38#64 →
      s.readReg64 .x28 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (lsmpl.base 40) s
        (((sp + 0x50#64) ↦₃₂ 1#32) ∗
         ((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
         ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3) ∗
         ((sp + 0xb8#64) ↦₆₄ k0) ∗ ((sp + 0xc0#64) ↦₆₄ k1) ∗
         ((sp + 0xc8#64) ↦₆₄ k2) ∗ ((sp + 0xd0#64) ↦₆₄ k3) ∗
         ((sp + 0x390#64) ↦₆₄ u390) ∗ ((sp + 0x398#64) ↦₆₄ u398) ∗
         ((sp + 0x3a0#64) ↦₆₄ u3a0) ∗ ((sp + 0x3a8#64) ↦₆₄ u3a8) ∗
         ((sp + 0x3b0#64) ↦₆₄ u3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u3b8) ∗
         ((sp + 0x3c0#64) ↦₆₄ u3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u3c8))
        (fun sc1 P_c1 =>
          sc1.sp = sp ∧ sc1.readReg64 .x0 = sp + 0x3b0#64 ∧
          sc1.readReg64 .x1 = x.msgA + 56#64 ∧ sc1.readReg64 .x2 = sp + 0x390#64 ∧
          sc1.readReg64 .x8 = sp + 0x190#64 ∧ sc1.readReg64 .x19 = x.ret ∧
          sc1.readReg64 .x20 = sp + 0x140#64 ∧ sc1.readReg64 .x21 = x.ss ∧
          sc1.readReg64 .x22 = x.msgA ∧ sc1.readReg64 .x23 = sp + 0x500#64 ∧
          (sc1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
          sc1.readReg64 .x25 = sp + 0x190#64 ∧ sc1.readReg64 .x26 = sp + 0x2c0#64 ∧
          sc1.readReg64 .x27 = sp + 0x38#64 ∧ sc1.readReg64 .x28 = sp + 0x2c0#64 ∧
          sc1.readReg64 .x29 = s0.sp - 96#64 ∧ sc1.readReg64 .x30 = entry + 1352#64 ∧
          sc1.trace = s0.trace ∧ calleeSavedVRegs sc1 = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_c1 ∗ R) →
            (m ⊨ (((sp + 0x50#64) ↦₃₂ 1#32) ∗
                  ((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
                  ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3) ∗
                  ((sp + 0xb8#64) ↦₆₄ 0#64) ∗ ((sp + 0xc0#64) ↦₆₄ 0#64) ∗
                  ((sp + 0xc8#64) ↦₆₄ 0#64) ∗ ((sp + 0xd0#64) ↦₆₄ 0#64) ∗
                  ((sp + 0x390#64) ↦₆₄ p0) ∗ ((sp + 0x398#64) ↦₆₄ p1) ∗
                  ((sp + 0x3a0#64) ↦₆₄ p2) ∗ ((sp + 0x3a8#64) ↦₆₄ p3) ∗
                  ((sp + 0x3b0#64) ↦₆₄ k0) ∗ ((sp + 0x3b8#64) ↦₆₄ k1) ∗
                  ((sp + 0x3c0#64) ↦₆₄ k2) ∗ ((sp + 0x3c8#64) ↦₆₄ k3)) ∗ R)))
  wpp_cc2_ok :
    ∀ (s0 s : State),
      let sp := s0.sp - 1504#64
      s.pc = entry + 2008#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x25 = sp + 0x190#64 → s.trace = s0.trace →
      SepWP prog (entry + 2220#64) s ((sp + 0x190#64) ↦₃₂ 0#32)
        (fun sm P_m =>
          sm.sp = sp ∧ CalleeSavedPreserved s sm ∧ sm.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_m ∗ R) → (m ⊨ ((sp + 0x190#64) ↦₃₂ 0#32) ∗ R)))
  wpp_cc2_err :
    ∀ (s0 s : State) (msgW : BitVec 32) (u1bc u1b4 u1a8 u1a0 : BitVec 64) (u1c4 u1b0 : BitVec 32),
      let sp := s0.sp - 1504#64
      s.pc = entry + 2008#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x25 = sp + 0x190#64 →
      s.readReg64 .x26 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 2040#64) s
        (((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x190#64) ↦₃₂ 1#32) ∗
         ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗ ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
         ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗ ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
         ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗ ((sp + 0x1c4#64) ↦₃₂ u1c4))
        (fun sm P_m =>
          sm.sp = sp ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = sp + 0x140#64 ∧ sm.readReg64 .x23 = sp + 0x500#64 ∧
          sm.readReg64 .x25 = sp + 0x190#64 ∧ sm.readReg64 .x26 = sp + 0x2c0#64 ∧
          sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_m ∗ R) →
            (m ⊨ (((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x190#64) ↦₃₂ 1#32) ∗
                  ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗ ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
                  ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗ ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
                  ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗ ((sp + 0x1c4#64) ↦₃₂ u1c4)) ∗ R)))
  wpp_70c_to_778 :
    ∀ (s0 s : State)
      (r0 r4 c2 u10 u1c u3e0 u4a0 u4bc u510 : BitVec 32)
      (r1 r2 r3 c0 c1 c3 c4 u3d0 u3d8 u3e4 u3ec u400 u408 u440 u448
       u4a4 u4ac u4b4 u4c0 u4c8 u4d0 u4d8 u500 u508 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x70c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x23 = sp + 0x500#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x26 = sp + 0x2c0#64 →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 1912#64) s
        (((sp + 0x10#64) ↦₃₂ u10) ∗ ((sp + 0x1c#64) ↦₃₂ u1c) ∗
         ((sp + 0x194#64) ↦₃₂ r0) ∗ ((sp + 0x198#64) ↦₆₄ r1) ∗
         ((sp + 0x1a0#64) ↦₆₄ r2) ∗ ((sp + 0x1a8#64) ↦₆₄ r3) ∗ ((sp + 0x1b0#64) ↦₃₂ r4) ∗
         ((sp + 0x1b4#64) ↦₆₄ c0) ∗ ((sp + 0x1bc#64) ↦₆₄ c1) ∗ ((sp + 0x1c4#64) ↦₃₂ c2) ∗
         ((sp + 0x1c8#64) ↦₆₄ c3) ∗ ((sp + 0x1d0#64) ↦₆₄ c4) ∗
         ((sp + 0x3d0#64) ↦₆₄ u3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u3d8) ∗ ((sp + 0x3e0#64) ↦₃₂ u3e0) ∗
         ((sp + 0x3e4#64) ↦₆₄ u3e4) ∗ ((sp + 0x3ec#64) ↦₆₄ u3ec) ∗
         ((sp + 0x400#64) ↦₆₄ u400) ∗ ((sp + 0x408#64) ↦₆₄ u408) ∗
         ((sp + 0x440#64) ↦₆₄ u440) ∗ ((sp + 0x448#64) ↦₆₄ u448) ∗
         ((sp + 0x4a0#64) ↦₃₂ u4a0) ∗ ((sp + 0x4a4#64) ↦₆₄ u4a4) ∗
         ((sp + 0x4ac#64) ↦₆₄ u4ac) ∗ ((sp + 0x4b4#64) ↦₆₄ u4b4) ∗ ((sp + 0x4bc#64) ↦₃₂ u4bc) ∗
         ((sp + 0x4c0#64) ↦₆₄ u4c0) ∗ ((sp + 0x4c8#64) ↦₆₄ u4c8) ∗
         ((sp + 0x4d0#64) ↦₆₄ u4d0) ∗ ((sp + 0x4d8#64) ↦₆₄ u4d8) ∗
         ((sp + 0x500#64) ↦₆₄ u500) ∗ ((sp + 0x508#64) ↦₆₄ u508) ∗ ((sp + 0x510#64) ↦₃₂ u510))
        (fun s1 P1 =>
          s1.sp = sp ∧ s1.readReg64 .x0 = sp + 0x190#64 ∧ s1.readReg64 .x1 = 32#64 ∧
          s1.readReg64 .x19 = s.readReg64 .x19 ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
          s1.readReg64 .x21 = s.readReg64 .x21 ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
          s1.readReg64 .x23 = sp + 0x500#64 ∧ s1.readReg64 .x25 = sp + 0x190#64 ∧
          s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x28 = sp + 0x3d0#64 ∧ s1.readReg64 .x29 = s0.sp - 96#64 ∧
          s1.readVReg128 0#5 = 0#128 ∧ s1.trace = s0.trace ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P1 ∗ R) →
            (m ⊨ (((sp + 0x10#64) ↦₃₂ c2) ∗
                  ((sp + 0x1c#64) ↦₃₂ (s.readReg64 .x24).setWidth 32) ∗
                  ((sp + 0x194#64) ↦₃₂ r0) ∗ ((sp + 0x198#64) ↦₆₄ r1) ∗
                  ((sp + 0x1a0#64) ↦₆₄ r2) ∗ ((sp + 0x1a8#64) ↦₆₄ r3) ∗ ((sp + 0x1b0#64) ↦₃₂ r4) ∗
                  ((sp + 0x1b4#64) ↦₆₄ c0) ∗ ((sp + 0x1bc#64) ↦₆₄ c1) ∗ ((sp + 0x1c4#64) ↦₃₂ c2) ∗
                  ((sp + 0x1c8#64) ↦₆₄ c3) ∗ ((sp + 0x1d0#64) ↦₆₄ c4) ∗
                  ((sp + 0x3d0#64) ↦₆₄ c0) ∗ ((sp + 0x3d8#64) ↦₆₄ c1) ∗ ((sp + 0x3e0#64) ↦₃₂ c2) ∗
                  ((sp + 0x3e4#64) ↦₆₄ c3) ∗ ((sp + 0x3ec#64) ↦₆₄ c4) ∗
                  ((sp + 0x400#64) ↦₆₄ c0) ∗ ((sp + 0x408#64) ↦₆₄ c1) ∗
                  ((sp + 0x440#64) ↦₆₄ c3) ∗ ((sp + 0x448#64) ↦₆₄ c4) ∗
                  ((sp + 0x4a0#64) ↦₃₂ r0) ∗ ((sp + 0x4a4#64) ↦₆₄ r1) ∗
                  ((sp + 0x4ac#64) ↦₆₄ r2) ∗ ((sp + 0x4b4#64) ↦₆₄ r3) ∗ ((sp + 0x4bc#64) ↦₃₂ r4) ∗
                  ((sp + 0x4c0#64) ↦₆₄ c3) ∗ ((sp + 0x4c8#64) ↦₆₄ c4) ∗
                  ((sp + 0x4d0#64) ↦₆₄ c0) ∗ ((sp + 0x4d8#64) ↦₆₄ c1) ∗
                  ((sp + 0x500#64) ↦₆₄ r2) ∗ ((sp + 0x508#64) ↦₆₄ r3) ∗
                  ((sp + 0x510#64) ↦₃₂ r4)) ∗ R)))
  wpp_778_to_rng :
    ∀ (s0 s : State) (u0 u1 u2 u3 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1912#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x0 = sp + 0x190#64 → s.readReg64 .x1 = 32#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.readVReg128 0#5 = 0#128 → s.trace = s0.trace →
      SepWP prog rngFillEntry s
        (((sp + 0x190#64) ↦₆₄ u0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ u1) ∗
         ((sp + 0x190#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ u3))
        (fun sc P_c =>
          sc.sp = sp ∧ sc.readReg64 .x0 = sp + 0x190#64 ∧ sc.readReg64 .x1 = 32#64 ∧
          sc.readReg64 .x30 = entry + 1920#64 ∧ CalleeSavedPreserved s sc ∧ sc.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_c ∗ R) →
            (m ⊨ (((sp + 0x190#64) ↦₆₄ 0#64) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ 0#64) ∗
                  ((sp + 0x190#64 + 16#64) ↦₆₄ 0#64) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ 0#64)) ∗ R)))
  wpp_780_to_7a8 :
    ∀ (s0 s : State) (b0 b31 : BitVec 8),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1920#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x23 = sp + 0x500#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 1960#64) s (((sp + 0x190#64) ↦₈ b0) ∗ ((sp + 0x1af#64) ↦₈ b31))
        (fun s' P' =>
          s'.sp = sp ∧ s'.readReg64 .x0 = sp + 0x500#64 ∧ s'.readReg64 .x8 = sp + 0x400#64 ∧
          s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x20 = s.readReg64 .x20 ∧
          s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
          s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = sp + 0x400#64 ∧
          s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
          s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
          s'.readReg64 .x29 = s0.sp - 96#64 ∧ s'.trace = s0.trace ∧
          calleeSavedVRegs s' = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P' ∗ R) →
            (m ⊨ (((sp + 0x190#64) ↦₈ (b0 &&& 0xf8#8)) ∗
                  ((sp + 0x1af#64) ↦₈ ((b31 &&& 0x7f#8) ||| 0x40#8))) ∗ R)))
  wpp_7a8_to_dpk :
    ∀ (s0 s : State) (p0 p1 p2 p3 u0 u1 u2 u3 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1960#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x0 = sp + 0x500#64 → s.readReg64 .x8 = sp + 0x400#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x25 = sp + 0x190#64 → s.trace = s0.trace →
      SepWP prog (lsmpl.base 200) s
        (((sp + 0x190#64) ↦₆₄ p0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ p1) ∗
         ((sp + 0x190#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ p3) ∗
         ((sp + 0x500#64) ↦₆₄ u0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ u1) ∗
         ((sp + 0x500#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ u3))
        (fun sc P_c =>
          sc.sp = sp ∧ sc.readReg64 .x0 = sp + 0x500#64 ∧ sc.readReg64 .x8 = sp + 0x400#64 ∧
          sc.readReg64 .x30 = entry + 1972#64 ∧ CalleeSavedPreserved s sc ∧ sc.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_c ∗ R) →
            (m ⊨ (((sp + 0x190#64) ↦₆₄ p0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ p1) ∗
                  ((sp + 0x190#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ p3) ∗
                  ((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
                  ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3)) ∗ R)))
  wpp_7b4_to_sd :
    ∀ (s0 s : State) (p0 p1 p2 p3 u0 u1 u2 u3 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1972#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x28 = sp + 0x3d0#64 → s.trace = s0.trace →
      SepWP prog (lsmpl.ρ "_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop") s
        (((sp + 0x420#64) ↦₆₄ u0) ∗ ((sp + 0x420#64 + 8#64) ↦₆₄ u1) ∗
         ((sp + 0x420#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x420#64 + 24#64) ↦₆₄ u3) ∗
         ((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
         ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3))
        (fun sc P_c =>
          sc.sp = sp ∧ sc.readReg64 .x0 = sp + 0x500#64 ∧ sc.readReg64 .x30 = entry + 1988#64 ∧
          CalleeSavedPreserved s sc ∧ sc.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_c ∗ R) →
            (m ⊨ (((sp + 0x420#64) ↦₆₄ p0) ∗ ((sp + 0x420#64 + 8#64) ↦₆₄ p1) ∗
                  ((sp + 0x420#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x420#64 + 24#64) ↦₆₄ p3) ∗
                  ((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
                  ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3)) ∗ R)))
  wpp_7c4_to_cc2 :
    ∀ (s0 s2 : State) (msgA : BitVec 64),
      let sp := s0.sp - 1504#64
      s2.pc = entry + 1988#64 → s2.status = .Running → s2.sp = sp → s2.spAligned = true →
      s2.readReg64 .x22 = msgA → s2.readReg64 .x24 = sp + 0x400#64 →
      s2.readReg64 .x29 = s0.sp - 96#64 → s2.trace = s0.trace →
      SepWP prog (lsmpl.base 40) s2 emp
        (fun s' P' =>
          s'.sp = sp ∧ s'.readReg64 .x0 = sp + 0x4a0#64 ∧ s'.readReg64 .x1 = msgA + 56#64 ∧
          s'.readReg64 .x2 = sp + 0x420#64 ∧ s'.readReg64 .x8 = sp + 0x190#64 ∧
          s'.readReg64 .x30 = entry + 2008#64 ∧ CalleeSavedPreserved s2 s' ∧ s'.trace = s0.trace ∧
          (∀ m R, (m ⊨ P' ∗ R) → (m ⊨ R)))

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep
