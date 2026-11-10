/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep5
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitPack
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitWp
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12
import ProofLib.SepLogic.WPp

/-!
# `try_decrypt_with_state` S3 Commit Sub-Segment 5

Proves `dhCommit_step5` (`+0xb98 → +0x3e4`), committing `sender_chain`, staging `receiverChainKey`
at `sp + 0x2b0..0x2d4`, and reassembling `ConsumeMsgKeyState`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit

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

namespace DhCommitFacts

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts.reachesOrPanic_mono {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State} {P Q : State → Prop}
    (h1 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s P)
    (h2 : ∀ sf, s.mem.KeepsFrozen sf.mem → sf.symtab = s.symtab → P sf → Q sf) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.seq h1 (fun sf hkf hsym hP => CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.done (h2 sf hkf hsym hP))

end DhCommitFacts

open DhCommitFacts

/-- Sub-segment 5 (`+0xb98 → +0x3e4`): commits `sender_chain`, stages `receiverChainKey` at
`sp + 0x2b0..0x2d4`, and reassembles the stack scratch regions of `ConsumeMsgKeyState`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.dhCommit_step5 (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (x : TryDecryptGhost) (pad : List (BitVec 8))
    (sc : SenderChain) (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (senderChainKey : ChainKey) (msgW : BitVec 32)
    (Frame R : SepProp) (s0 s : State)
    (sp : BitVec 64) (hsp_def : sp = s0.sp - 1504#64)
    (_hpad : pad.length = 100)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 0xb98#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem)
    (hm : s.mem ⊨
      memRegion sp 8 ∗
      ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗
      memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x50#64) ↦₃₂ 1#32) ∗
      ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
      memRegion (sp + 0x140#64) 0x50 ∗
      memRegion (sp + 0x190#64) 104 ∗
      memRegion (sp + 0x1f8#64) 0xb8 ∗
      memRegion (sp + 0x2b0#64) 0x10 ∗
      memRegion (sp + 0x2c0#64) 0x14 ∗
      memRegion (sp + 0x2d4#64) 0xfc ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x450#64) 0x50 ∗
      memRegion (sp + 0x4a0#64) 0x20 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
      ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
      ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x500#64) 96 ∗
      memRegion (sp + 0x560#64) 0x20 ∗
      (Frame ∗ R)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic (tripleRatchetProgAtExt img.base ext) C A ctl uuidTryParse S img x R s0 s
      (fun sf =>
        sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 0x3e4#64 ∧
        sf.status = .Running ∧
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = msgW.zeroExtend 64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = s.readReg64 .x30 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (tripleRatchetProgAtExt img.base ext).CodeLoaded sf.mem ∧
        (sf.mem ⊨
          ((sp + 0x50#64) ↦ₛ optSenderChainBytes (some ⟨newSenderKey, senderChainKey⟩) pad) ∗
          memRegion sp 0x20 ∗
          memRegion (sp + 0x140#64) 0x170 ∗
          ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
          ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 20) ∗
          memRegion (sp + 0x2d4#64) 0x2ac ∗
          (Frame ∗ R))) := by
  let _ := hsp_def
  have hrck_mid_len : (((chainKeyBytes receiverChainKey).drop 16).take 4).length = 4 := by
    simp [chainKeyBytes_length]
  have hrck_drop20_len : ((chainKeyBytes receiverChainKey).drop 20).length = 16 := by
    simp [chainKeyBytes_length]
  have hrck_take16_len : ((chainKeyBytes receiverChainKey).take 16).length = 16 := by
    simp [chainKeyBytes_length]
  have h_old_spk := pointsToBytes_len32_to_cells (sp + 0x54#64) sc.ratchetKey.publicKey.bytes.toList (by simp)
  rw [show sp + 0x54#64 + 8#64 = sp + 0x5c#64 from add_assoc_const _ _ _ _,
      show sp + 0x54#64 + 16#64 = sp + 0x64#64 from add_assoc_const _ _ _ _,
      show sp + 0x54#64 + 24#64 = sp + 0x6c#64 from add_assoc_const _ _ _ _] at h_old_spk
  have h_old_sk := pointsToBytes_len32_to_cells (sp + 0x74#64) sc.ratchetKey.privateKey.bytes.toList (by simp)
  rw [show sp + 0x74#64 + 8#64 = sp + 0x7c#64 from add_assoc_const _ _ _ _,
      show sp + 0x74#64 + 16#64 = sp + 0x84#64 from add_assoc_const _ _ _ _,
      show sp + 0x74#64 + 24#64 = sp + 0x8c#64 from add_assoc_const _ _ _ _] at h_old_sk
  have h_old_sck := pointsToBytes_chainKey_eq_cells (sp + 0x94#64) sc.chainKey
  rw [show sp + 0x94#64 + 8#64 = sp + 0x9c#64 from add_assoc_const _ _ _ _,
      show sp + 0x94#64 + 16#64 = sp + 0xa4#64 from add_assoc_const _ _ _ _,
      show sp + 0x94#64 + 20#64 = sp + 0xa8#64 from add_assoc_const _ _ _ _,
      show sp + 0x94#64 + 28#64 = sp + 0xb0#64 from add_assoc_const _ _ _ _] at h_old_sck
  have h_new_spk := pointsToBytes_len32_to_cells (sp + 0x400#64) newSenderKey.publicKey.bytes.toList (by simp)
  rw [show sp + 0x400#64 + 8#64 = sp + 0x408#64 from add_assoc_const _ _ _ _,
      show sp + 0x400#64 + 16#64 = sp + 0x410#64 from add_assoc_const _ _ _ _,
      show sp + 0x400#64 + 24#64 = sp + 0x418#64 from add_assoc_const _ _ _ _] at h_new_spk
  have h_new_sk := pointsToBytes_len32_to_cells (sp + 0x420#64) newSenderKey.privateKey.bytes.toList (by simp)
  rw [show sp + 0x420#64 + 8#64 = sp + 0x428#64 from add_assoc_const _ _ _ _,
      show sp + 0x420#64 + 16#64 = sp + 0x430#64 from add_assoc_const _ _ _ _,
      show sp + 0x420#64 + 24#64 = sp + 0x438#64 from add_assoc_const _ _ _ _] at h_new_sk
  have h_rck_10 := pointsToBytes_len4_eq_pointsTo32 (sp + 0x10#64) (((chainKeyBytes receiverChainKey).drop 16).take 4) hrck_mid_len
  have h_rck_4c0 := pointsToBytes_len16_to_cells (sp + 0x4c0#64) ((chainKeyBytes receiverChainKey).drop 20) hrck_drop20_len
  rw [show sp + 0x4c0#64 + 8#64 = sp + 0x4c8#64 from add_assoc_const _ _ _ _] at h_rck_4c0
  have h_rck_4d0 := pointsToBytes_len16_to_cells (sp + 0x4d0#64) ((chainKeyBytes receiverChainKey).take 16) hrck_take16_len
  rw [show sp + 0x4d0#64 + 8#64 = sp + 0x4d8#64 from add_assoc_const _ _ _ _] at h_rck_4d0
  have hm_2b0 : s.mem ⊨
      memRegion (sp + 0x2b0#64) 16 ∗
      (memRegion (sp + 0x2c0#64) 20 ∗
       memRegion (sp + 0x450#64) 80 ∗
       memRegion sp 8 ∗
       ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗
       memRegion (sp + 0xc#64) 4 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 104 ∗
       memRegion (sp + 0x1f8#64) 0xb8 ∗
       memRegion (sp + 0x2d4#64) 0xfc ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
       ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
       ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
       memRegion (sp + 0x4a0#64) 0x20 ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
       ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
       ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
       ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
       ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
       memRegion (sp + 0x500#64) 96 ∗
       memRegion (sp + 0x560#64) 0x20 ∗
       (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm
    ac_rfl
  obtain ⟨v2b0, v2b8, hm_2b0⟩ := elim_memRegion_16 hm_2b0
  rw [show sp + 0x2b0#64 + 8#64 = sp + 0x2b8#64 from add_assoc_const _ _ _ _] at hm_2b0
  have hm_2c0 : s.mem ⊨
      memRegion (sp + 0x2c0#64) 20 ∗
      (memRegion (sp + 0x450#64) 80 ∗
       (((sp + 0x2b0#64) ↦₆₄ v2b0) ∗ ((sp + 0x2b8#64) ↦₆₄ v2b8)) ∗
       memRegion sp 8 ∗
       ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗
       memRegion (sp + 0xc#64) 4 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 104 ∗
       memRegion (sp + 0x1f8#64) 0xb8 ∗
       memRegion (sp + 0x2d4#64) 0xfc ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
       ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
       ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
       memRegion (sp + 0x4a0#64) 0x20 ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
       ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
       ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
       ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
       ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
       memRegion (sp + 0x500#64) 96 ∗
       memRegion (sp + 0x560#64) 0x20 ∗
       (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm_2b0
    ac_rfl
  obtain ⟨v2c0, v2c8, v2d0, hm_2c0⟩ := elim_memRegion_20 hm_2c0
  rw [show sp + 0x2c0#64 + 8#64 = sp + 0x2c8#64 from add_assoc_const _ _ _ _,
      show sp + 0x2c0#64 + 16#64 = sp + 0x2d0#64 from add_assoc_const _ _ _ _] at hm_2c0
  have hm_450 : s.mem ⊨
      memRegion (sp + 0x450#64) 80 ∗
      ((((sp + 0x2c0#64) ↦₆₄ v2c0) ∗ ((sp + 0x2c8#64) ↦₆₄ v2c8) ∗ ((sp + 0x2d0#64) ↦₃₂ v2d0)) ∗
       (((sp + 0x2b0#64) ↦₆₄ v2b0) ∗ ((sp + 0x2b8#64) ↦₆₄ v2b8)) ∗
       memRegion sp 8 ∗
       ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗
       memRegion (sp + 0xc#64) 4 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 104 ∗
       memRegion (sp + 0x1f8#64) 0xb8 ∗
       memRegion (sp + 0x2d4#64) 0xfc ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
       ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
       ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
       memRegion (sp + 0x4a0#64) 0x20 ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
       ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
       ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
       ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
       ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
       memRegion (sp + 0x500#64) 96 ∗
       memRegion (sp + 0x560#64) 0x20 ∗
       (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm_2c0
    ac_rfl
  obtain ⟨v450, v458, v460, v468, v470, v478, v480, v488, v490, v498, hm_450⟩ :=
    elim_memRegion_80 hm_450
  rw [show sp + 0x450#64 + 8#64 = sp + 0x458#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 16#64 = sp + 0x460#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 24#64 = sp + 0x468#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 32#64 = sp + 0x470#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 40#64 = sp + 0x478#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 48#64 = sp + 0x480#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 56#64 = sp + 0x488#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 64#64 = sp + 0x490#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 72#64 = sp + 0x498#64 from add_assoc_const _ _ _ _] at hm_450
  let rck16 := packLE32 (((chainKeyBytes receiverChainKey).drop 16).take 4)
  let oldSpk0 := packLE64 (sc.ratchetKey.publicKey.bytes.toList.take 8)
  let oldSpk1 := packLE64 ((sc.ratchetKey.publicKey.bytes.toList.drop 8).take 8)
  let oldSpk2 := packLE64 ((sc.ratchetKey.publicKey.bytes.toList.drop 16).take 8)
  let oldSpk3 := packLE64 (sc.ratchetKey.publicKey.bytes.toList.drop 24)
  let oldSk0 := packLE64 (sc.ratchetKey.privateKey.bytes.toList.take 8)
  let oldSk1 := packLE64 ((sc.ratchetKey.privateKey.bytes.toList.drop 8).take 8)
  let oldSk2 := packLE64 ((sc.ratchetKey.privateKey.bytes.toList.drop 16).take 8)
  let oldSk3 := packLE64 (sc.ratchetKey.privateKey.bytes.toList.drop 24)
  let oldSck0 := sckWord0 sc.chainKey
  let oldSck1 := sckWord8 sc.chainKey
  let oldSck16 := sckWord16 sc.chainKey
  let oldSck2 := sckWord20 sc.chainKey
  let oldSck3 := sckWord28 sc.chainKey
  let spk0 := packLE64 (newSenderKey.publicKey.bytes.toList.take 8)
  let spk1 := packLE64 ((newSenderKey.publicKey.bytes.toList.drop 8).take 8)
  let spk2 := packLE64 ((newSenderKey.publicKey.bytes.toList.drop 16).take 8)
  let spk3 := packLE64 (newSenderKey.publicKey.bytes.toList.drop 24)
  let sk0 := packLE64 (newSenderKey.privateKey.bytes.toList.take 8)
  let sk1 := packLE64 ((newSenderKey.privateKey.bytes.toList.drop 8).take 8)
  let sk2 := packLE64 ((newSenderKey.privateKey.bytes.toList.drop 16).take 8)
  let sk3 := packLE64 (newSenderKey.privateKey.bytes.toList.drop 24)
  let sck0 := sckWord0 senderChainKey
  let sck1 := sckWord8 senderChainKey
  let sck16 := sckWord16 senderChainKey
  let sck2 := sckWord20 senderChainKey
  let sck3 := sckWord28 senderChainKey
  let rck0 := packLE64 (((chainKeyBytes receiverChainKey).take 16).take 8)
  let rck1 := packLE64 (((chainKeyBytes receiverChainKey).take 16).drop 8)
  let rck2 := packLE64 (((chainKeyBytes receiverChainKey).drop 20).take 8)
  let rck3 := packLE64 (((chainKeyBytes receiverChainKey).drop 20).drop 8)
  have hm_wp : s.mem ⊨
      (((sp + 0x8#64) ↦₃₂ sck16) ∗
       ((sp + 0x10#64) ↦₃₂ rck16) ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x54#64) ↦₆₄ oldSpk0) ∗
       ((sp + 0x5c#64) ↦₆₄ oldSpk1) ∗
       ((sp + 0x64#64) ↦₆₄ oldSpk2) ∗
       ((sp + 0x6c#64) ↦₆₄ oldSpk3) ∗
       ((sp + 0x74#64) ↦₆₄ oldSk0) ∗
       ((sp + 0x7c#64) ↦₆₄ oldSk1) ∗
       ((sp + 0x84#64) ↦₆₄ oldSk2) ∗
       ((sp + 0x8c#64) ↦₆₄ oldSk3) ∗
       ((sp + 0x94#64) ↦₆₄ oldSck0) ∗
       ((sp + 0x9c#64) ↦₆₄ oldSck1) ∗
       ((sp + 0xa4#64) ↦₃₂ oldSck16) ∗
       ((sp + 0xa8#64) ↦₆₄ oldSck2) ∗
       ((sp + 0xb0#64) ↦₆₄ oldSck3) ∗
       ((sp + 0x2b0#64) ↦₆₄ v2b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ v2b8) ∗
       ((sp + 0x2c0#64) ↦₆₄ v2c0) ∗
       ((sp + 0x2c8#64) ↦₆₄ v2c8) ∗
       ((sp + 0x2d0#64) ↦₃₂ v2d0) ∗
       ((sp + 0x400#64) ↦₆₄ spk0) ∗
       ((sp + 0x408#64) ↦₆₄ spk1) ∗
       ((sp + 0x410#64) ↦₆₄ spk2) ∗
       ((sp + 0x418#64) ↦₆₄ spk3) ∗
       ((sp + 0x420#64) ↦₆₄ sk0) ∗
       ((sp + 0x428#64) ↦₆₄ sk1) ∗
       ((sp + 0x430#64) ↦₆₄ sk2) ∗
       ((sp + 0x438#64) ↦₆₄ sk3) ∗
       ((sp + 0x450#64) ↦₆₄ v450) ∗
       ((sp + 0x458#64) ↦₆₄ v458) ∗
       ((sp + 0x460#64) ↦₆₄ v460) ∗
       ((sp + 0x468#64) ↦₆₄ v468) ∗
       ((sp + 0x470#64) ↦₆₄ v470) ∗
       ((sp + 0x478#64) ↦₆₄ v478) ∗
       ((sp + 0x480#64) ↦₆₄ v480) ∗
       ((sp + 0x488#64) ↦₆₄ v488) ∗
       ((sp + 0x490#64) ↦₆₄ v490) ∗
       ((sp + 0x498#64) ↦₆₄ v498) ∗
       ((sp + 0x4c0#64) ↦₆₄ rck2) ∗
       ((sp + 0x4c8#64) ↦₆₄ rck3) ∗
       ((sp + 0x4d0#64) ↦₆₄ rck0) ∗
       ((sp + 0x4d8#64) ↦₆₄ rck1) ∗
       ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
       ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
       ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
       ((sp + 0x4f8#64) ↦₆₄ sck1)) ∗
      ((memRegion sp 8 ∗
        memRegion (sp + 0xc#64) 4 ∗
        memRegion (sp + 0x14#64) 8 ∗
        memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x190#64) 104 ∗
        memRegion (sp + 0x1f8#64) 0xb8 ∗
        memRegion (sp + 0x2d4#64) 0xfc ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        memRegion (sp + 0x3f4#64) 12 ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗
        ((sp + 0x448#64) ↦₆₄ sck1) ∗
        memRegion (sp + 0x4a0#64) 0x20 ∗
        memRegion (sp + 0x500#64) 96 ∗
        memRegion (sp + 0x560#64) 0x20 ∗
        Frame) ∗ R) := by
    rw [h_rck_10, h_old_spk, h_old_sk, h_old_sck, h_new_spk, h_new_sk, h_rck_4c0, h_rck_4d0] at hm_450
    refine Satisfies.mono (Entails.of_eq ?_) hm_450
    ac_rfl
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.commit_step5_wp img.base ext sp sck16 rck16 msgW 1#32 oldSck16 v2d0
      oldSpk0 oldSpk1 oldSpk2 oldSpk3 oldSk0 oldSk1 oldSk2 oldSk3
      oldSck0 oldSck1 oldSck2 oldSck3
      spk0 spk1 spk2 spk3 sk0 sk1 sk2 sk3
      sck0 sck1 sck2 sck3
      rck0 rck1 rck2 rck3
      v2b0 v2b8 v2c0 v2c8
      v450 v458 v460 v468 v470 v478 v480 v488 v490 v498
      s hpc hrun hsp hsp_align hx25)
    hm_wp hL ?_
  intro sf Pf hpcf hrunf _hkff _hsymf hLf hmf hpostf
  rcases hpostf with ⟨hspf, hsp_alignf, htrf, hx12f, hx19f, hx20f, hx21f, hx22f,
    hx23f, hx24f, hx25f, hx29f, hx30f, hvregsf, hPf⟩
  have hmf' := Satisfies.mono (sepConj_mono_left hPf) hmf
  have h_sc_54 := pointsToBytes_len32_to_cells (sp + 0x54#64) newSenderKey.publicKey.bytes.toList (by simp)
  rw [show sp + 0x54#64 + 8#64 = sp + 0x5c#64 from add_assoc_const _ _ _ _,
      show sp + 0x54#64 + 16#64 = sp + 0x64#64 from add_assoc_const _ _ _ _,
      show sp + 0x54#64 + 24#64 = sp + 0x6c#64 from add_assoc_const _ _ _ _] at h_sc_54
  have h_sc_74 := pointsToBytes_len32_to_cells (sp + 0x74#64) newSenderKey.privateKey.bytes.toList (by simp)
  rw [show sp + 0x74#64 + 8#64 = sp + 0x7c#64 from add_assoc_const _ _ _ _,
      show sp + 0x74#64 + 16#64 = sp + 0x84#64 from add_assoc_const _ _ _ _,
      show sp + 0x74#64 + 24#64 = sp + 0x8c#64 from add_assoc_const _ _ _ _] at h_sc_74
  have h_sc_94 := pointsToBytes_chainKey_eq_cells (sp + 0x94#64) senderChainKey
  rw [show sp + 0x94#64 + 8#64 = sp + 0x9c#64 from add_assoc_const _ _ _ _,
      show sp + 0x94#64 + 16#64 = sp + 0xa4#64 from add_assoc_const _ _ _ _,
      show sp + 0x94#64 + 20#64 = sp + 0xa8#64 from add_assoc_const _ _ _ _,
      show sp + 0x94#64 + 28#64 = sp + 0xb0#64 from add_assoc_const _ _ _ _] at h_sc_94
  have h_opt_sc := optSenderChainBytes_some_pointsTo (sp + 0x50#64) ⟨newSenderKey, senderChainKey⟩ pad
  rw [show sp + 0x50#64 + 4#64 = sp + 0x54#64 from add_assoc_const _ _ _ _,
      show sp + 0x50#64 + 36#64 = sp + 0x74#64 from add_assoc_const _ _ _ _,
      show sp + 0x50#64 + 68#64 = sp + 0x94#64 from add_assoc_const _ _ _ _] at h_opt_sc
  have h_sc_entails :
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗
       (((sp + 0x54#64) ↦₆₄ spk0) ∗ ((sp + 0x5c#64) ↦₆₄ spk1) ∗ ((sp + 0x64#64) ↦₆₄ spk2) ∗ ((sp + 0x6c#64) ↦₆₄ spk3)) ∗
       (((sp + 0x74#64) ↦₆₄ sk0) ∗ ((sp + 0x7c#64) ↦₆₄ sk1) ∗ ((sp + 0x84#64) ↦₆₄ sk2) ∗ ((sp + 0x8c#64) ↦₆₄ sk3)) ∗
       (((sp + 0x94#64) ↦₆₄ sck0) ∗ ((sp + 0x9c#64) ↦₆₄ sck1) ∗ ((sp + 0xa4#64) ↦₃₂ sck16) ∗
        ((sp + 0xa8#64) ↦₆₄ sck2) ∗ ((sp + 0xb0#64) ↦₆₄ sck3))) ⊢
      ((sp + 0x50#64) ↦ₛ optSenderChainBytes (some ⟨newSenderKey, senderChainKey⟩) pad) := by
    rw [← h_sc_54, ← h_sc_74, ← h_sc_94, h_opt_sc]
    exact Entails.of_eq (by ac_rfl)
  have h_rck_2b0 := pointsToBytes_len16_to_cells (sp + 0x2b0#64) ((chainKeyBytes receiverChainKey).drop 20) hrck_drop20_len
  rw [show sp + 0x2b0#64 + 8#64 = sp + 0x2b8#64 from add_assoc_const _ _ _ _] at h_rck_2b0
  have h_rck_2c0 := pointsToBytes_len16_to_cells (sp + 0x2c0#64) ((chainKeyBytes receiverChainKey).take 16) hrck_take16_len
  rw [show sp + 0x2c0#64 + 8#64 = sp + 0x2c8#64 from add_assoc_const _ _ _ _] at h_rck_2c0
  have h_rck_2d0 := pointsToBytes_len4_eq_pointsTo32 (sp + 0x2d0#64) (((chainKeyBytes receiverChainKey).drop 16).take 4) hrck_mid_len
  have h_rck_2c0_20 := pointsToBytes_rck_take20 (sp + 0x2c0#64) receiverChainKey
  rw [show sp + 0x2c0#64 + 16#64 = sp + 0x2d0#64 from add_assoc_const _ _ _ _] at h_rck_2c0_20
  have h_staged_entails :
      ((((sp + 0x2b0#64) ↦₆₄ rck2) ∗ ((sp + 0x2b8#64) ↦₆₄ rck3)) ∗
       (((sp + 0x2c0#64) ↦₆₄ rck0) ∗ ((sp + 0x2c8#64) ↦₆₄ rck1)) ∗
       ((sp + 0x2d0#64) ↦₃₂ rck16)) ⊢
      (((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 20)) := by
    rw [← h_rck_2b0, ← h_rck_2c0, ← h_rck_2d0, h_rck_2c0_20]
    exact Entails.refl _
  have h_sp0_20 :
      (memRegion sp 8 ∗
       ((sp + 0x8#64) ↦₃₂ sck16) ∗
       memRegion (sp + 0xc#64) 4 ∗
       ((sp + 0x10#64) ↦₃₂ rck16) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW)) ⊢
      memRegion sp 0x20 := by
    have h8 := pointsTo32_entails_memRegion (sp + 0x8#64) sck16
    have h10 := pointsTo32_entails_memRegion (sp + 0x10#64) rck16
    have h1c := pointsTo32_entails_memRegion (sp + 0x1c#64) msgW
    have hs1 := (memRegion_split sp 8 4 (by decide)).symm
    have hs2 := (memRegion_split sp 12 4 (by decide)).symm
    have hs3 := (memRegion_split sp 16 4 (by decide)).symm
    have hs4 := (memRegion_split sp 20 8 (by decide)).symm
    have hs5 := (memRegion_split sp 28 4 (by decide)).symm
    rw [show sp + 12#64 = sp + 0xc#64 from rfl] at hs2
    rw [show sp + 16#64 = sp + 0x10#64 from rfl] at hs3
    rw [show sp + 20#64 = sp + 0x14#64 from rfl] at hs4
    rw [show sp + 28#64 = sp + 0x1c#64 from rfl] at hs5
    refine Entails.trans (sepConj_mono_right (sepConj_mono h8 (sepConj_mono_right (sepConj_mono h10 (sepConj_mono_right h1c))))) ?_
    rw [← sepConj_assoc, hs1, ← sepConj_assoc, hs2, ← sepConj_assoc, hs3, ← sepConj_assoc, hs4, hs5]
    exact Entails.refl _
  have h_sp140_2b0 :
      (memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 104 ∗
       memRegion (sp + 0x1f8#64) 0xb8) ⊢
      memRegion (sp + 0x140#64) 0x170 := by
    have hs1 := (memRegion_split (sp + 0x140#64) 0x50 104 (by decide)).symm
    rw [show sp + 0x140#64 + 80#64 = sp + 0x190#64 from add_assoc_const _ _ _ _,
        show (0x50 + 104 : Nat) = 184 from rfl] at hs1
    have hs2 := (memRegion_split (sp + 0x140#64) 184 0xb8 (by decide)).symm
    rw [show sp + 0x140#64 + 184#64 = sp + 0x1f8#64 from add_assoc_const _ _ _ _,
        show (184 + 0xb8 : Nat) = 0x170 from rfl] at hs2
    rw [← sepConj_assoc, hs1, hs2]
    exact Entails.refl _
  have h_sp2d4_580 :
      (memRegion (sp + 0x2d4#64) 0xfc ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       (((sp + 0x400#64) ↦₆₄ spk0) ∗ ((sp + 0x408#64) ↦₆₄ spk1) ∗ ((sp + 0x410#64) ↦₆₄ spk2) ∗ ((sp + 0x418#64) ↦₆₄ spk3)) ∗
       (((sp + 0x420#64) ↦₆₄ sk0) ∗ ((sp + 0x428#64) ↦₆₄ sk1) ∗ ((sp + 0x430#64) ↦₆₄ sk2) ∗ ((sp + 0x438#64) ↦₆₄ sk3)) ∗
       (((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1)) ∗
       (((sp + 0x450#64) ↦₆₄ spk0) ∗ ((sp + 0x458#64) ↦₆₄ spk1) ∗ ((sp + 0x460#64) ↦₆₄ spk2) ∗ ((sp + 0x468#64) ↦₆₄ spk3) ∗
        ((sp + 0x470#64) ↦₆₄ sk0) ∗ ((sp + 0x478#64) ↦₆₄ sk1) ∗ ((sp + 0x480#64) ↦₆₄ sk2) ∗ ((sp + 0x488#64) ↦₆₄ sk3) ∗
        ((sp + 0x490#64) ↦₆₄ sck0) ∗ ((sp + 0x498#64) ↦₆₄ sck1)) ∗
       memRegion (sp + 0x4a0#64) 0x20 ∗
       (((sp + 0x4c0#64) ↦₆₄ rck2) ∗ ((sp + 0x4c8#64) ↦₆₄ rck3) ∗ ((sp + 0x4d0#64) ↦₆₄ rck0) ∗ ((sp + 0x4d8#64) ↦₆₄ rck1)) ∗
       (((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗ ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1)) ∗
       memRegion (sp + 0x500#64) 96 ∗
       memRegion (sp + 0x560#64) 0x20) ⊢
      memRegion (sp + 0x2d4#64) 0x2ac := by
    have h3d0 : ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ⊢ memRegion (sp + 0x3d0#64) 36 := by
      have h := pointsToBytes_entails_memRegion (sp + 0x3d0#64) (chainKeyBytes receiverChainKey)
      rwa [chainKeyBytes_length] at h
    have h400 := pointsTo64_4_entails_memRegion (sp + 0x400#64) spk0 spk1 spk2 spk3
    rw [show sp + 0x400#64 + 8#64 = sp + 0x408#64 from add_assoc_const _ _ _ _,
        show sp + 0x400#64 + 16#64 = sp + 0x410#64 from add_assoc_const _ _ _ _,
        show sp + 0x400#64 + 24#64 = sp + 0x418#64 from add_assoc_const _ _ _ _] at h400
    have h420 := pointsTo64_4_entails_memRegion (sp + 0x420#64) sk0 sk1 sk2 sk3
    rw [show sp + 0x420#64 + 8#64 = sp + 0x428#64 from add_assoc_const _ _ _ _,
        show sp + 0x420#64 + 16#64 = sp + 0x430#64 from add_assoc_const _ _ _ _,
        show sp + 0x420#64 + 24#64 = sp + 0x438#64 from add_assoc_const _ _ _ _] at h420
    have h440 := pointsTo64_2_entails_memRegion (sp + 0x440#64) sck0 sck1
    rw [show sp + 0x440#64 + 8#64 = sp + 0x448#64 from add_assoc_const _ _ _ _] at h440
    have h450 := pointsTo64_10_entails_memRegion (sp + 0x450#64) spk0 spk1 spk2 spk3 sk0 sk1 sk2 sk3 sck0 sck1
    rw [show sp + 0x450#64 + 8#64 = sp + 0x458#64 from add_assoc_const _ _ _ _,
        show sp + 0x450#64 + 16#64 = sp + 0x460#64 from add_assoc_const _ _ _ _,
        show sp + 0x450#64 + 24#64 = sp + 0x468#64 from add_assoc_const _ _ _ _,
        show sp + 0x450#64 + 32#64 = sp + 0x470#64 from add_assoc_const _ _ _ _,
        show sp + 0x450#64 + 40#64 = sp + 0x478#64 from add_assoc_const _ _ _ _,
        show sp + 0x450#64 + 48#64 = sp + 0x480#64 from add_assoc_const _ _ _ _,
        show sp + 0x450#64 + 56#64 = sp + 0x488#64 from add_assoc_const _ _ _ _,
        show sp + 0x450#64 + 64#64 = sp + 0x490#64 from add_assoc_const _ _ _ _,
        show sp + 0x450#64 + 72#64 = sp + 0x498#64 from add_assoc_const _ _ _ _] at h450
    have h4c0 := pointsTo64_4_entails_memRegion (sp + 0x4c0#64) rck2 rck3 rck0 rck1
    rw [show sp + 0x4c0#64 + 8#64 = sp + 0x4c8#64 from add_assoc_const _ _ _ _,
        show sp + 0x4c0#64 + 16#64 = sp + 0x4d0#64 from add_assoc_const _ _ _ _,
        show sp + 0x4c0#64 + 24#64 = sp + 0x4d8#64 from add_assoc_const _ _ _ _] at h4c0
    have h4e0 := pointsTo64_4_entails_memRegion (sp + 0x4e0#64) sck2 sck3 sck0 sck1
    rw [show sp + 0x4e0#64 + 8#64 = sp + 0x4e8#64 from add_assoc_const _ _ _ _,
        show sp + 0x4e0#64 + 16#64 = sp + 0x4f0#64 from add_assoc_const _ _ _ _,
        show sp + 0x4e0#64 + 24#64 = sp + 0x4f8#64 from add_assoc_const _ _ _ _] at h4e0
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono h3d0 (sepConj_mono_right (sepConj_mono h400
        (sepConj_mono h420 (sepConj_mono h440 (sepConj_mono h450 (sepConj_mono_right
          (sepConj_mono h4c0 (sepConj_mono h4e0 (Entails.refl _))))))))))) ?_
    have hs1 := (memRegion_split (sp + 0x2d4#64) 252 36 (by decide)).symm
    rw [show sp + 0x2d4#64 + 252#64 = sp + 0x3d0#64 from add_assoc_const _ _ _ _,
        show (252 + 36 : Nat) = 288 from rfl] at hs1
    have hs2 := (memRegion_split (sp + 0x2d4#64) 288 12 (by decide)).symm
    rw [show sp + 0x2d4#64 + 288#64 = sp + 0x3f4#64 from add_assoc_const _ _ _ _,
        show (288 + 12 : Nat) = 300 from rfl] at hs2
    have hs3 := (memRegion_split (sp + 0x2d4#64) 300 32 (by decide)).symm
    rw [show sp + 0x2d4#64 + 300#64 = sp + 0x400#64 from add_assoc_const _ _ _ _,
        show (300 + 32 : Nat) = 332 from rfl] at hs3
    have hs4 := (memRegion_split (sp + 0x2d4#64) 332 32 (by decide)).symm
    rw [show sp + 0x2d4#64 + 332#64 = sp + 0x420#64 from add_assoc_const _ _ _ _,
        show (332 + 32 : Nat) = 364 from rfl] at hs4
    have hs5 := (memRegion_split (sp + 0x2d4#64) 364 16 (by decide)).symm
    rw [show sp + 0x2d4#64 + 364#64 = sp + 0x440#64 from add_assoc_const _ _ _ _,
        show (364 + 16 : Nat) = 380 from rfl] at hs5
    have hs6 := (memRegion_split (sp + 0x2d4#64) 380 80 (by decide)).symm
    rw [show sp + 0x2d4#64 + 380#64 = sp + 0x450#64 from add_assoc_const _ _ _ _,
        show (380 + 80 : Nat) = 460 from rfl] at hs6
    have hs7 := (memRegion_split (sp + 0x2d4#64) 460 32 (by decide)).symm
    rw [show sp + 0x2d4#64 + 460#64 = sp + 0x4a0#64 from add_assoc_const _ _ _ _,
        show (460 + 32 : Nat) = 492 from rfl] at hs7
    have hs8 := (memRegion_split (sp + 0x2d4#64) 492 32 (by decide)).symm
    rw [show sp + 0x2d4#64 + 492#64 = sp + 0x4c0#64 from add_assoc_const _ _ _ _,
        show (492 + 32 : Nat) = 524 from rfl] at hs8
    have hs9 := (memRegion_split (sp + 0x2d4#64) 524 32 (by decide)).symm
    rw [show sp + 0x2d4#64 + 524#64 = sp + 0x4e0#64 from add_assoc_const _ _ _ _,
        show (524 + 32 : Nat) = 556 from rfl] at hs9
    have hs10 := (memRegion_split (sp + 0x2d4#64) 556 96 (by decide)).symm
    rw [show sp + 0x2d4#64 + 556#64 = sp + 0x500#64 from add_assoc_const _ _ _ _,
        show (556 + 96 : Nat) = 652 from rfl] at hs10
    have hs11 := (memRegion_split (sp + 0x2d4#64) 652 32 (by decide)).symm
    rw [show sp + 0x2d4#64 + 652#64 = sp + 0x560#64 from add_assoc_const _ _ _ _,
        show (652 + 32 : Nat) = 684 from rfl] at hs11
    change (memRegion (sp + 0x2d4#64) 252 ∗ memRegion (sp + 0x3d0#64) 36 ∗
      memRegion (sp + 0x3f4#64) 12 ∗ memRegion (sp + 0x400#64) 32 ∗
      memRegion (sp + 0x420#64) 32 ∗ memRegion (sp + 0x440#64) 16 ∗
      memRegion (sp + 0x450#64) 80 ∗ memRegion (sp + 0x4a0#64) 32 ∗
      memRegion (sp + 0x4c0#64) 32 ∗ memRegion (sp + 0x4e0#64) 32 ∗
      memRegion (sp + 0x500#64) 96 ∗ memRegion (sp + 0x560#64) 32) ⊢
      memRegion (sp + 0x2d4#64) 684
    rw [← sepConj_assoc, hs1, ← sepConj_assoc, hs2, ← sepConj_assoc, hs3, ← sepConj_assoc, hs4,
        ← sepConj_assoc, hs5, ← sepConj_assoc, hs6, ← sepConj_assoc, hs7, ← sepConj_assoc, hs8,
        ← sepConj_assoc, hs9, ← sepConj_assoc, hs10, hs11]
    exact Entails.refl _
  have hmf_grouped : sf.mem ⊨
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗
       (((sp + 0x54#64) ↦₆₄ spk0) ∗ ((sp + 0x5c#64) ↦₆₄ spk1) ∗ ((sp + 0x64#64) ↦₆₄ spk2) ∗ ((sp + 0x6c#64) ↦₆₄ spk3)) ∗
       (((sp + 0x74#64) ↦₆₄ sk0) ∗ ((sp + 0x7c#64) ↦₆₄ sk1) ∗ ((sp + 0x84#64) ↦₆₄ sk2) ∗ ((sp + 0x8c#64) ↦₆₄ sk3)) ∗
       (((sp + 0x94#64) ↦₆₄ sck0) ∗ ((sp + 0x9c#64) ↦₆₄ sck1) ∗ ((sp + 0xa4#64) ↦₃₂ sck16) ∗
        ((sp + 0xa8#64) ↦₆₄ sck2) ∗ ((sp + 0xb0#64) ↦₆₄ sck3))) ∗
      (memRegion sp 8 ∗
       ((sp + 0x8#64) ↦₃₂ sck16) ∗
       memRegion (sp + 0xc#64) 4 ∗
       ((sp + 0x10#64) ↦₃₂ rck16) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW)) ∗
      (memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 104 ∗
       memRegion (sp + 0x1f8#64) 0xb8) ∗
      ((((sp + 0x2b0#64) ↦₆₄ rck2) ∗ ((sp + 0x2b8#64) ↦₆₄ rck3)) ∗
       (((sp + 0x2c0#64) ↦₆₄ rck0) ∗ ((sp + 0x2c8#64) ↦₆₄ rck1)) ∗
       ((sp + 0x2d0#64) ↦₃₂ rck16)) ∗
      (memRegion (sp + 0x2d4#64) 0xfc ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       (((sp + 0x400#64) ↦₆₄ spk0) ∗ ((sp + 0x408#64) ↦₆₄ spk1) ∗ ((sp + 0x410#64) ↦₆₄ spk2) ∗ ((sp + 0x418#64) ↦₆₄ spk3)) ∗
       (((sp + 0x420#64) ↦₆₄ sk0) ∗ ((sp + 0x428#64) ↦₆₄ sk1) ∗ ((sp + 0x430#64) ↦₆₄ sk2) ∗ ((sp + 0x438#64) ↦₆₄ sk3)) ∗
       (((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1)) ∗
       (((sp + 0x450#64) ↦₆₄ spk0) ∗ ((sp + 0x458#64) ↦₆₄ spk1) ∗ ((sp + 0x460#64) ↦₆₄ spk2) ∗ ((sp + 0x468#64) ↦₆₄ spk3) ∗
        ((sp + 0x470#64) ↦₆₄ sk0) ∗ ((sp + 0x478#64) ↦₆₄ sk1) ∗ ((sp + 0x480#64) ↦₆₄ sk2) ∗ ((sp + 0x488#64) ↦₆₄ sk3) ∗
        ((sp + 0x490#64) ↦₆₄ sck0) ∗ ((sp + 0x498#64) ↦₆₄ sck1)) ∗
       memRegion (sp + 0x4a0#64) 0x20 ∗
       (((sp + 0x4c0#64) ↦₆₄ rck2) ∗ ((sp + 0x4c8#64) ↦₆₄ rck3) ∗ ((sp + 0x4d0#64) ↦₆₄ rck0) ∗ ((sp + 0x4d8#64) ↦₆₄ rck1)) ∗
       (((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗ ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1)) ∗
       memRegion (sp + 0x500#64) 96 ∗
       memRegion (sp + 0x560#64) 0x20) ∗
      (Frame ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hmf'
    ac_rfl
  have hmf_final := Satisfies.mono
    (sepConj_mono h_sc_entails
      (sepConj_mono h_sp0_20
        (sepConj_mono h_sp140_2b0
          (sepConj_mono h_staged_entails
            (sepConj_mono_left h_sp2d4_580)))))
    hmf_grouped
  rw [sepConj_assoc ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20)] at hmf_final
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.done ⟨hpcf, hrunf, hspf, hsp_alignf, htrf,
    hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx29f, hx30f, hvregsf, hLf, hmf_final⟩

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit
