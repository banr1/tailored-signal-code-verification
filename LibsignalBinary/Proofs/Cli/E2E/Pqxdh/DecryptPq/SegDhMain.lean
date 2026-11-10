/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhErr
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhCc1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHMain
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhSteps
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhCc1
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhErr
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhSteps
import ProofLib.SepLogic.WPp

/-!
# Handshake `DecryptPq` Segment S3 Proof

Combines missing-sender-chain handling, receiving and sending `RootKey::create_chain` calls,
sender key-pair generation, and `s3_commit_spec` to prove `s3_ok : S3Spec`
(`+0x500 → +0x3e4 / +0x30c`) on `tripleRatchetProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_after_cc1_to_cc2_call {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdpk : DerivePublicKeyBytesOk img.base C ctl abs)
    (hA : AllocHooks A abs)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (rk1 : RootKey) (rck : ChainKey) (R : SepProp) (s0 s :
      State)
    (hafter : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.S3AfterCc1State A ctl img x trG tr st1 rk1 rck R s0 s)
    (hcode : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    let draws := min 32 x.rest.length
    let newSenderKey := KeyPair.generate C (coinsOf x.rest)
    ∃ s5, Steps (tripleRatchetProgAt img.base C ctl abs) s s5 ∧
      s5.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr createChainName ∧
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
      s5.readReg64 .x30 = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 2008#64 ∧
      ∃ (msgW : BitVec 32),
        msgW.setWidth 8 = msgTypeByte x.msgType ∧
        (s5.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey :=
            (0 : RootKey) } } ∗
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
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
  obtain ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hmem⟩ := hafter
  set sp := s0.sp - 1504#64
  set draws := min 32 x.rest.length
  set newSenderKey := KeyPair.generate C (coinsOf x.rest)
  set msgW : BitVec 32 := (s.readReg64 .x24).setWidth 32
  have hmsgW : msgW.setWidth 8 = msgTypeByte x.msgType := by
    have h8 : msgW.setWidth 8 = (s.readReg64 .x24).setWidth 8 := by
      dsimp only [msgW]
      bv_omega
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
      (BaseRest ∗ CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [BaseRest, sp]; ac_rfl)) hmem
  obtain ⟨s1, hsteps1, hpc1, hmeta1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1,
    hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hv0_1, hmem1⟩ :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_step_70c_to_778 (C := C) (ctl := ctl) (abs := abs)
      himg rk1 rck (BaseRest ∗ CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) s0 s
      hpc hmeta hx23 hx25 hx26 hx28 hmem0 hcode
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.tryDecryptCommonHeap_split_tape A ctl img x 0 s0] at hmem1
  have hmem1_in : s1.mem ⊨
      memRegion (sp + 0x190#64) 0x20 ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
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
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ∗ R) :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by dsimp only [msgW, sp]; ac_rfl)) hmem1
  obtain ⟨s2, hsteps2, hpc2, hmeta2, hcs2, hmem2⟩ :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_step_778_to_780 (img := img) (C := C) (ctl := ctl) (abs := abs)
      x.cur x.rest _ s0 s1 hA (ProofLib.ObjectLoad.base_aligned_of_loads himg) hpc1 hmeta1 hx0_1 hx1_1
      hx25_1 hv0_1 hmem1_in
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
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.tryDecryptCommonHeap_split_tape A ctl img x draws s0]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [draws, sp]; ac_rfl)) hmem2
  obtain ⟨s3, hsteps3, hpc3, hmeta3, hx0_3, hx8_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3,
    hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hmem3⟩ :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_step_780_to_7a8 (img := img) (C := C) (ctl := ctl) (abs := abs)
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
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
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
         CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
      Eq.mp (congrArg (s3.mem ⊨ ·)
        (by dsimp only [newSenderKey, KeyPair.generate, sp]; ac_rfl)) hmem3
    rw [h400] at hmem3'
    exact Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hmem3'
  obtain ⟨s4, hsteps4, hpc4, hmeta4, hcs4, hmem4⟩ :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_step_7a8_to_7b4 (img := img) (C := C) (ctl := ctl) (abs := abs)
      hdpk newSenderKey.privateKey.bytes _ s0 s3 hpc3 hmeta3 hx0_3 hx8_3 hx23_3' hx25_3' hmem3_in
      (hsteps123.codeLoaded hcode)
  have hsteps1234 := Steps.trans hsteps123 hsteps4
  have hx22_4 : s4.readReg64 .x22 = x.msgA :=
    hcs4.2.2.2.1.trans (hx22_3.trans (hcs2.2.2.2.1.trans (hx22_1.trans hx22)))
  have hx23_4 : s4.readReg64 .x23 = sp + 0x500#64 := hcs4.2.2.2.2.1.trans hx23_3'
  have hx24_4 : s4.readReg64 .x24 = sp + 0x400#64 := hcs4.2.2.2.2.2.1.trans hx24_3
  have hx28_4 : s4.readReg64 .x28 = sp + 0x3d0#64 :=
    hcs4.2.2.2.2.2.2.2.2.2.1.trans (hx28_3.trans (hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28_1))
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
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
    Eq.mp (congrArg (s4.mem ⊨ ·) (by dsimp only [newSenderKey, KeyPair.generate, sp]; ac_rfl)) hmem4
  obtain ⟨s5, hsteps5, hpc5, hmeta5, hx0_5, hx1_5, hx2_5, hx8_5, hx30_5, hcs5, hmem5⟩ :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_step_7b4_to_7d4 (img := img) (C := C) (ctl := ctl) (abs := abs)
      x.msgA newSenderKey.privateKey.bytes _ s0 s4 hpc4 hmeta4 hx22_4 hx23_4 hx24_4 hx28_4 hmem4_in
      (hsteps1234.codeLoaded hcode)
  have hsteps12345 := Steps.trans hsteps1234 hsteps5
  have hcs45 := CalleeSavedPreserved.trans hcs4 hcs5
  have hx19_5 : s5.readReg64 .x19 = x.ret :=
    hcs45.1.trans (hx19_3.trans (hcs2.1.trans (hx19_1.trans hx19)))
  have hx20_5 : s5.readReg64 .x20 = sp + 0x140#64 :=
    hcs45.2.1.trans (hx20_3.trans (hcs2.2.1.trans (hx20_1.trans hx20)))
  have hx21_5 : s5.readReg64 .x21 = x.ss :=
    hcs45.2.2.1.trans (hx21_3.trans (hcs2.2.2.1.trans (hx21_1.trans hx21)))
  have hx22_5 : s5.readReg64 .x22 = x.msgA := hcs5.2.2.2.1.trans hx22_4
  have hx23_5 : s5.readReg64 .x23 = sp + 0x500#64 := hcs5.2.2.2.2.1.trans hx23_4
  have hx25_5 : s5.readReg64 .x25 = sp + 0x190#64 := hcs45.2.2.2.2.2.2.1.trans hx25_3'
  have hx26_5 : s5.readReg64 .x26 = sp + 0x2c0#64 :=
    hcs45.2.2.2.2.2.2.2.1.trans (hx26_3.trans (hcs2.2.2.2.2.2.2.2.1.trans (hx26_1.trans hx26)))
  have hx27_5 : s5.readReg64 .x27 = sp + 0x38#64 :=
    hcs45.2.2.2.2.2.2.2.2.1.trans (hx27_3.trans (hcs2.2.2.2.2.2.2.2.2.1.trans (hx27_1.trans hx27)))
  have hx28_5 : s5.readReg64 .x28 = sp + 0x3d0#64 := hcs5.2.2.2.2.2.2.2.2.2.1.trans hx28_4
  have hmem5' : s5.mem ⊨
      (memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 0x220 ∗
       memRegion (sp + 0x4e0#64) 0x20 ∗ memRegion (sp + 0x500#64) 32 ∗
         memRegion (sp + 0x520#64) 0x60) ∗
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
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
    Eq.mp (congrArg (s5.mem ⊨ ·) (by dsimp only [sp]; ac_rfl)) hmem5
  rw [split_190_4e0_for_cc2 sp] at hmem5'
  exact ⟨s5, hsteps12345, hpc5, hmeta5, hx0_5, hx1_5, hx2_5, hx8_5, hx19_5, hx20_5, hx21_5,
    hx22_5, hx23_5, hx25_5, hx26_5, hx27_5, hx28_5, hx30_5, msgW, hmsgW,
    Eq.mp (congrArg (s5.mem ⊨ ·) (by dsimp only [BaseRest]; ac_rfl)) hmem5'⟩

/-- Step `+0x70c → +0x8ac` (or `+0x30c` `ErrTailState` on `.error .invalidKeyAgreement`, or panic):
from `S3AfterCc1State` at `+0x70c`, stages `rk1` and `rck`, generates `newSenderKey =
KeyPair.generate C (coinsOf x.rest)`, calls `RootKey::create_chain` #2 (`+0x7d4`),
and branches on the result tag (`+0x7d8..+0x7f4`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_keygen_and_send_create_chain {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl :
    BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hcc : CreateChainOk img C A ctl abs)
    (hdpk : DerivePublicKeyBytesOk img.base C ctl abs)
    (hA : AllocHooks A abs)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (rk1 : RootKey) (rck : ChainKey) (R : SepProp) (s0 s :
      State)
    (hrk2_ne : s0.sp - 1504#64 + 0x4a0#64 ≠ 0#64)
    (hafter : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.S3AfterCc1State A ctl img x trG tr st1 rk1 rck R s0 s)
    (hcode : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem) :
    let newSenderKey := KeyPair.generate C (coinsOf x.rest)
    match rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey with
    | .ok (finalRootKey, senderChainKey) =>
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.S3CommitState A ctl img x trG tr st1 rck newSenderKey finalRootKey senderChainKey R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
    | .error e =>
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        ((∃ trG' r1, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG' { tr with ratchet :=
          r1 } st1 e (min 32 x.rest.length) R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  set sp := s0.sp - 1504#64
  set draws := min 32 x.rest.length
  set newSenderKey := KeyPair.generate C (coinsOf x.rest)
  obtain ⟨s5, hsteps5, hpc5, hmeta5, hx0_5, hx1_5, hx2_5, hx8_5, hx19_5, hx20_5, hx21_5,
    hx22_5, hx23_5, hx25_5, hx26_5, hx27_5, hx28_5, hx30_5, msgW, hmsgW, hmem5⟩ :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_after_cc1_to_cc2_call himg hdpk hA x trG tr st1 rk1 rck R s0 s hafter hcode
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
    CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
    logOff img ∗
    stackAt (sp - BitVec.ofNat 64 createChainStack) (tryDecryptSubStack - createChainStack) ∗
    tryDecryptSavedRegs s0.sp s0
  have hpre_cc2 : s5.mem ⊨ ((createChainSpec C A).inImage img).pre ccG2 s5 ∗ (Frame2 ∗ R) := by
    dsimp only [createChainSpec, Spec.inImage, ccG2, Frame2]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfr5, hsym5⟩, ⟨hx0_5, hx1_5, hx2_5, hx8_5, hrk2_ne⟩, ?_⟩
    rw [show s5.sp = sp from hsp5]
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap at hmem5
    rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
        show s0.sp - 1504#64 = sp from rfl,
        stackAt_subStack_createChain sp] at hmem5
    exact Eq.mp (congrArg (s5.mem ⊨ ·) (by dsimp only [sp, draws, newSenderKey]; ac_rfl)) hmem5
  obtain ⟨sm, hsteps_cc2, hout_cc2, _⟩ :=
    hcc.no_fault_before_outcome ccG2 (Frame2 ∗ R) s5 hpc5 hrun5 hpre_cc2 hsp_al5
      (hsteps5.codeLoaded hcode)
  have hsteps5m : Steps (tripleRatchetProgAt img.base C ctl abs) s sm :=
      Steps.trans hsteps5 hsteps_cc2
  rcases hout_cc2 with ⟨hret_m, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, -, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · -- Normal return from `RootKey::create_chain` #2
    have hpcm : sm.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 2008#64 :=
      hret_m.1.trans hx30_5
    have hrunm : sm.status = .Running := hret_m.2.2
    dsimp only [createChainSpec, Spec.inImage, ccG2] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfr_m : img.FrozenLoaded sm := hsteps_cc2.frozenLoaded hfr5
    have hsym_m : sm.symtab = img.symtab := hsteps_cc2.symtab_eq.trans hsym5
    have htrace_m0 := hpost.1
    have hpost := hpost.2
    have htrace_m : sm.trace = s0.trace := htrace_m0.trans htrace5
    have hsp_m : sm.sp = s0.sp - 1504#64 := hspm.trans hsp5
    have hsp_al_m : sm.spAligned = true := by
      unfold State.spAligned at hsp_al5 ⊢
      rw [hspm]
      exact hsp_al5
    have hx19_m : sm.readReg64 .x19 = x.ret := hcsm.1.trans hx19_5
    have hx20_m : sm.readReg64 .x20 = sp + 0x140#64 := hcsm.2.1.trans hx20_5
    have hx21_m : sm.readReg64 .x21 = x.ss := hcsm.2.2.1.trans hx21_5
    have hx22_m : sm.readReg64 .x22 = x.msgA := hcsm.2.2.2.1.trans hx22_5
    have hx23_m : sm.readReg64 .x23 = sp + 0x500#64 := hcsm.2.2.2.2.1.trans hx23_5
    have hx25_m : sm.readReg64 .x25 = sp + 0x190#64 := hcsm.2.2.2.2.2.2.1.trans hx25_5
    have hx26_m : sm.readReg64 .x26 = sp + 0x2c0#64 := hcsm.2.2.2.2.2.2.2.1.trans hx26_5
    have hx27_m : sm.readReg64 .x27 = sp + 0x38#64 := hcsm.2.2.2.2.2.2.2.2.1.trans hx27_5
    have hx28_m : sm.readReg64 .x28 = sp + 0x3d0#64 := hcsm.2.2.2.2.2.2.2.2.2.1.trans hx28_5
    have hx29_m : sm.readReg64 .x29 = s0.sp - 96#64 := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hx29_5
    have hmeta_m : tryDecryptMidMeta img s0 sm :=
      ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hfr_m, hsym_m, hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs5⟩
    have hpost_grouped : sm.mem ⊨
        createChainResultAt (sp + 0x190#64) (rootCreateChain C rk1 x.msg.senderRatchetKey
          newSenderKey.privateKey) ∗
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey :=
          (0 : RootKey) } } ∗
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
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R := by
      dsimp only [Frame2] at hpost
      rw [show s5.sp = sp from hsp5] at hpost
      unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap
      rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
          show s0.sp - 1504#64 = sp from rfl,
          stackAt_subStack_createChain sp]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hpost
    dsimp only
    unfold rootCreateChain at hpost_grouped ⊢
    cases hcc2 : Ratchet.createChain C.F C.X rk1 x.msg.senderRatchetKey.bytes
        newSenderKey.privateKey.bytes with
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
           trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey :=
             (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗
           memRegion sp 0x10 ∗
           ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
           memRegion (sp + 0x14#64) 8 ∗
           ((sp + 0x20#64) ↦₆₄ x.locA) ∗
           ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗
           ((sp + 0x30#64) ↦₆₄ x.remA) ∗
           CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hpost_grouped
      have hpost_err1 := Satisfies.mono (sepConj_mono_left
        (fold_1d8_after_cc2_err sp rck newSenderKey.publicKey.bytes.toList
          newSenderKey.privateKey.bytes.toList rk1
          newSenderKey.publicKey.bytes.2 newSenderKey.privateKey.bytes.2)) hpost_err0
      let Rest_err : SepProp :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey :=
          (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗
        memRegion sp 0x10 ∗
        ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
        memRegion (sp + 0x14#64) 8 ∗
        ((sp + 0x20#64) ↦₆₄ x.locA) ∗
        ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗
        ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R
      have hmem_err : sm.mem ⊨
          ((sp + 0x1c#64) ↦₃₂ msgW) ∗
          memRegion (sp + 0x140#64) 0x50 ∗
          createChainResultAt (sp + 0x190#64) (.error .invalidKeyAgreement) ∗
          memRegion (sp + 0x1d8#64) 0x3a8 ∗ Rest_err :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_err]; ac_rfl)) hpost_err1
      obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_cc2_err_branch (C := C) (A := A) (ctl := ctl) (abs := abs)
          himg msgW Rest_err s0 sm hpcm hmeta_m hx20_m hx23_m hx25_m hx26_m hmem_err
          (hsteps5m.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps5m hsteps2, Or.inl ⟨trG, { tr.ratchet with rootKey :=
          (0 : RootKey) }, ?_⟩⟩
      refine ⟨hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s', ?_⟩
      dsimp only [Rest_err] at hmems'
      have hmems0 : s'.mem ⊨
          (memRegion sp 0x10 ∗
           ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
           memRegion (sp + 0x14#64) 8 ∗
           ((sp + 0x1c#64) ↦₃₂ msgW)) ∗
          (((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
           sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey :=
             (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗
           memRegion (sp + 0x140#64) 0x28 ∗
           speBodyAt A (utf8 "decrypt") (sp + 0x168#64) .invalidKeyAgreement ∗
           memRegion (sp + 0x190#64) 0x3f0 ∗
           CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
        Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp] at hmems' ⊢; ac_rfl)) hmems'
      have hmems0' :=
          Satisfies.mono (sepConj_mono_left (fold_sp_20_after_cc2_err sp rck msgW)) hmems0
      have hsp38_ent :
          (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ⊢
          memRegion sp 0x38 := by
        rw [memRegion_split' (b := sp) (b' := sp + 0x20#64) (n := 0x20) (k :=
            0x18) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x20#64) (b' := sp + 0x28#64) (n := 0x8) (k :=
              0x10) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x28#64) (b' := sp + 0x2c#64) (n := 0x4) (k :=
              0xc) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x2c#64) (b' := sp + 0x30#64) (n := 0x4) (k :=
              0x8) rfl (by bv_arith) (by decide)]
        exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _)
            (sepConj_mono_right (pointsTo64_entails_memRegion _ _))))
      have hmems1 : s'.mem ⊨
          (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ∗
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey :=
             (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗
           memRegion (sp + 0x140#64) 0x28 ∗
           speBodyAt A (utf8 "decrypt") (sp + 0x168#64) .invalidKeyAgreement ∗
           memRegion (sp + 0x190#64) 0x3f0 ∗
           CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
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
           trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey :=
             (0 : RootKey) } } ∗
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
           CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hpost_grouped
      have hpost_ok1 := Satisfies.mono (sepConj_mono_left (fold_after_cc2_ok sp rk1)) hpost_ok0
      let Rest_ok : SepProp :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey :=
          (0 : RootKey) } } ∗
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
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R
      have hmem_ok : sm.mem ⊨
          createChainResultAt (sp + 0x190#64) (.ok (finalRootKey, ⟨sckKey, 0⟩)) ∗ Rest_ok :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_ok]; ac_rfl)) hpost_ok1
      obtain ⟨s', hsteps2, hpcs', hmetas', hcss', hmems'⟩ :=
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_cc2_ok_branch (C := C) (ctl := ctl) (abs := abs)
          himg finalRootKey ⟨sckKey, 0⟩ Rest_ok s0 sm hpcm hmeta_m hmem_ok
          (hsteps5m.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps5m hsteps2, Or.inl ?_⟩
      refine ⟨hpcs', hmetas',
        hcss'.1.trans hx19_m,
        hcss'.2.1.trans hx20_m,
        hcss'.2.2.1.trans hx21_m,
        hcss'.2.2.2.1.trans hx22_m,
        hcss'.2.2.2.2.1.trans hx23_m,
        hcss'.2.2.2.2.2.2.1.trans hx25_m,
        hcss'.2.2.2.2.2.2.2.2.1.trans hx27_m,
        hcss'.2.2.2.2.2.2.2.2.2.1.trans hx28_m,
        msgW, hmsgW, ?_⟩
      dsimp only [Rest_ok, sp, draws, newSenderKey] at hmems' ⊢
      exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems'
  · -- Panic in `RootKey::create_chain` #2
    have hpan_td := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.onPanic_of_createChain (ctl := ctl) (S := S) (x := x) htrace5 hpost
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

/-- Top-level proof of `S3Spec` (`+0x500 → +0x3e4 / +0x30c` or panic): combines
`s3_missing_sender_chain`, `s3_recv_create_chain`, `s3_keygen_and_send_create_chain`,
and `s3_commit_spec`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3Spec img C A ctl uuidTryParse S abs := by
  intro himg hHooks hcc hdpk hPkSer hToPb hGrowOne hDropChain
    x trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hs3 hcode
  dsimp only
  cases hsc : tr.ratchet.senderChain with
  | none =>
    rw [dhRatchetStep_none C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet hsc,
        decryptDraws_of_senderChain_none C x.st st1 tr x.msg.senderRatchetKey x.rest hfrom hfind
          hsc]
    obtain ⟨s', hsteps, ⟨_, _, herr⟩ | ⟨_, hoom⟩⟩ :=
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_missing_sender_chain (C := C) (A := A) (ctl := ctl) (abs := abs)
        himg x trG tr st1 R s0 s hsc hs3 hcode
    · exact ⟨s', hsteps, Or.inl ⟨trG, tr.ratchet, herr⟩⟩
    · exact hoom.elim
  | some sc =>
    have ⟨hrk1_ne, hrk2_ne⟩ := rk_ne_zero s0.sp (s0.sp - 1504#64) rfl hsp0
    have hstep1 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_recv_create_chain (S :=
        S) himg hcc x trG tr st1 sc R s0 s hsc hrk1_ne hs3 hcode
    cases hcc1 : rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey
        sc.ratchetKey.privateKey with
    | error e =>
      rw [hcc1] at hstep1
      rw [dhRatchetStep_some_err1 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc e hsc
          hcc1,
          decryptDraws_of_cc1_err C x.st st1 tr x.msg.senderRatchetKey x.rest sc e hfrom hfind hsc
            hcc1]
      exact hstep1
    | ok p1 =>
      rcases p1 with ⟨rk1, rck⟩
      rw [hcc1] at hstep1
      rw [decryptDraws_of_cc1_ok C x.st st1 tr x.msg.senderRatchetKey x.rest sc rk1 rck hfrom hfind
          hsc hcc1]
      obtain ⟨s1, hsteps1, hafter | hpan1⟩ := hstep1
      · have hstep2 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_keygen_and_send_create_chain (S := S)
          himg hcc hdpk hHooks.alloc x trG tr st1 rk1 rck R s0 s1 hrk2_ne hafter (hsteps1.codeLoaded hcode)
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
              CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.s3_commit_spec img C A ctl S abs
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

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB
