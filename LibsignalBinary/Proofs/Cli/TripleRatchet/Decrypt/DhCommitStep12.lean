/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitPack
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPack
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitWp
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvict
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# `try_decrypt_with_state` S3 Commit Sub-Segments 1 and 2

Proves `dhCommit_step1_2` (`+0x8ac → +0xa84`), committing `root_key` and `previous_counter`,
serializing `senderRatchetKey` into a `Vec<u8>`, and converting `receiverChainKey` via
`ChainKey::to_pb`.
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

/-- Steps 1 and 2 (`+0x8ac → +0xa84`): commits `root_key` and `previous_counter`, stages
`senderChainKey` pieces, calls `PublicKey::serialize`, clones the 33-byte slice into `Vec<u8>`,
and calls `ChainKey::to_pb` on `receiverChainKey`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.dhCommit_step1_2 (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hPkSer : PublicKeySerializeOkExt img.base A ext)
    (hToPb : ChainKeyToPbOkExt img.base A ext)
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s : State)
    (sp msgA : BitVec 64) (scIdx prevCtr0 : BitVec 32)
    (finalRootKey : RootKey) (senderChainKey receiverChainKey : ChainKey)
    (srk : PublicKey)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 0x8ac#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx27 : s.readReg64 .x27 = sp + 0x38#64)
    (hx28 : s.readReg64 .x28 = sp + 0x3d0#64)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (memRegion sp 12 ∗
       ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
       ((sp + 0xb8#64) ↦ₛ keyToBytes32 0) ∗
       ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x440#64) 16 ∗
       memRegion (sp + 0x4e0#64) 32 ∗
       ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
       A.pool ∗
       stackAt sp chainKeyToPbStack) ∗ (Frame ∗ R)) :
    let sckBs := chainKeyBytes senderChainKey
    let sck0 := pack64 (sckBs.take 8)
    let sck1 := pack64 ((sckBs.drop 8).take 8)
    let sck16 := pack32 ((sckBs.drop 16).take 4)
    let sck2 := pack64 ((sckBs.drop 20).take 8)
    let sck3 := pack64 (sckBs.drop 28)
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic (tripleRatchetProgAtExt img.base ext) C A ctl uuidTryParse S img x R s0 s (fun sf =>
      ∃ boxPtr srkPtr ckPtr : BitVec 64, ∃ pad : List (BitVec 8),
        srkPtr ≠ 0 ∧
        pad.length = 4 ∧
        sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 0xa84#64 ∧
        sf.status = .Running ∧
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = msgA ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = boxPtr ∧
        sf.readReg64 .x28 = srkPtr ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (tripleRatchetProgAtExt img.base ext).CodeLoaded sf.mem ∧
        (sf.mem ⊨
          ((sp ↦₆₄ boxPtr) ∗
           ((sp + 8#64) ↦₃₂ sck16) ∗
           ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
           ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
           ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
           ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
           memRegion (sp + 0x1b0#64) 40 ∗
           ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
           ((sp + 0x440#64) ↦₆₄ sck0) ∗
           ((sp + 0x448#64) ↦₆₄ sck1) ∗
           ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
           ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
           ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
           ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
           ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
           (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
           (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
           optChainKeyHeap A ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗
           A.pool ∗
           stackAt sp chainKeyToPbStack) ∗ (Frame ∗ R))) := by
  intro sckBs sck0 sck1 sck16 sck2 sck3
  have hm_440 : s.mem ⊨
      memRegion (sp + 0x440#64) 16 ∗
      (memRegion (sp + 0x4e0#64) 32 ∗
       memRegion sp 12 ∗
       ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
       ((sp + 0xb8#64) ↦ₛ keyToBytes32 0) ∗
       ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
       A.pool ∗
       stackAt sp chainKeyToPbStack ∗
       (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hmem
    ac_rfl
  obtain ⟨v440, v448, hm_440⟩ := elim_memRegion_16 hm_440
  have hm_4e0 : s.mem ⊨
      memRegion (sp + 0x4e0#64) 32 ∗
      (((sp + 0x440#64) ↦₆₄ v440) ∗ ((sp + 0x440#64 + 8#64) ↦₆₄ v448) ∗
       memRegion sp 12 ∗
       ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
       ((sp + 0xb8#64) ↦ₛ keyToBytes32 0) ∗
       ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
       A.pool ∗
       stackAt sp chainKeyToPbStack ∗
       (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm_440
    ac_rfl
  obtain ⟨v4e0, v4e8, v4f0, v4f8, hm_4e0⟩ := elim_memRegion_32 hm_4e0
  have hrk0_len : (keyToBytes32 0).length = 32 := by simp [keyToBytes32]
  have hrk_len : (keyToBytes32 finalRootKey).length = 32 := by simp [keyToBytes32]
  have hb8_cells := pointsToBytes_32_eq_4_8_8_8_4 (sp + 0xb8#64) hrk0_len
  have h194_cells := pointsToBytes_32_eq_4_8_8_8_4 (sp + 0x194#64) hrk_len
  have h1b4_cells := pointsToBytes_chainKey_eq_cells (sp + 0x1b4#64) senderChainKey
  set oldRk0 := pack32 ((keyToBytes32 0).take 4)
  set oldRk4 := pack64 (((keyToBytes32 0).drop 4).take 8)
  set oldRk12 := pack64 (((keyToBytes32 0).drop 12).take 8)
  set oldRk20 := pack64 (((keyToBytes32 0).drop 20).take 8)
  set oldRk28 := pack32 ((keyToBytes32 0).drop 28)
  set rk0 := pack32 ((keyToBytes32 finalRootKey).take 4)
  set rk4 := pack64 (((keyToBytes32 finalRootKey).drop 4).take 8)
  set rk12 := pack64 (((keyToBytes32 finalRootKey).drop 12).take 8)
  set rk20 := pack64 (((keyToBytes32 finalRootKey).drop 20).take 8)
  set rk28 := pack32 ((keyToBytes32 finalRootKey).drop 28)
  have eb1 := add_assoc_const sp 0xb8#64 4#64 0xbc#64
  have eb2 := add_assoc_const sp 0xb8#64 12#64 0xc4#64
  have eb3 := add_assoc_const sp 0xb8#64 20#64 0xcc#64
  have eb4 := add_assoc_const sp 0xb8#64 28#64 0xd4#64
  rw [eb1, eb2, eb3, eb4] at hb8_cells
  have er1 := add_assoc_const sp 0x194#64 4#64 0x198#64
  have er2 := add_assoc_const sp 0x194#64 12#64 0x1a0#64
  have er3 := add_assoc_const sp 0x194#64 20#64 0x1a8#64
  have er4 := add_assoc_const sp 0x194#64 28#64 0x1b0#64
  rw [er1, er2, er3, er4] at h194_cells
  have es1 := add_assoc_const sp 0x1b4#64 8#64 0x1bc#64
  have es2 := add_assoc_const sp 0x1b4#64 16#64 0x1c4#64
  have es3 := add_assoc_const sp 0x1b4#64 20#64 0x1c8#64
  have es4 := add_assoc_const sp 0x1b4#64 28#64 0x1d0#64
  rw [es1, es2, es3, es4] at h1b4_cells
  have h440_off := add_assoc_const sp 0x440#64 8#64 0x448#64
  have ee1 := add_assoc_const sp 0x4e0#64 8#64 0x4e8#64
  have ee2 := add_assoc_const sp 0x4e0#64 16#64 0x4f0#64
  have ee3 := add_assoc_const sp 0x4e0#64 24#64 0x4f8#64
  rw [h440_off, ee1, ee2, ee3, hb8_cells, h194_cells, h1b4_cells] at hm_4e0
  have hm_step1 : s.mem ⊨
      (((sp + 0xb4#64) ↦₃₂ scIdx) ∗
       ((sp + 0xb8#64) ↦₃₂ oldRk0) ∗
       ((sp + 0xbc#64) ↦₆₄ oldRk4) ∗
       ((sp + 0xc4#64) ↦₆₄ oldRk12) ∗
       ((sp + 0xcc#64) ↦₆₄ oldRk20) ∗
       ((sp + 0xd4#64) ↦₃₂ oldRk28) ∗
       ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗
       ((sp + 0x194#64) ↦₃₂ rk0) ∗
       ((sp + 0x198#64) ↦₆₄ rk4) ∗
       ((sp + 0x1a0#64) ↦₆₄ rk12) ∗
       ((sp + 0x1a8#64) ↦₆₄ rk20) ∗
       ((sp + 0x1b0#64) ↦₃₂ rk28) ∗
       ((sp + 0x1b4#64) ↦₆₄ sck0) ∗
       ((sp + 0x1bc#64) ↦₆₄ sck1) ∗
       ((sp + 0x1c4#64) ↦₃₂ sck16) ∗
       ((sp + 0x1c8#64) ↦₆₄ sck2) ∗
       ((sp + 0x1d0#64) ↦₆₄ sck3) ∗
       ((sp + 0x440#64) ↦₆₄ v440) ∗
       ((sp + 0x448#64) ↦₆₄ v448) ∗
       ((sp + 0x4e0#64) ↦₆₄ v4e0) ∗
       ((sp + 0x4e8#64) ↦₆₄ v4e8) ∗
       ((sp + 0x4f0#64) ↦₆₄ v4f0) ∗
       ((sp + 0x4f8#64) ↦₆₄ v4f8)) ∗
      ((memRegion sp 12 ∗
        ((sp + 0x190#64) ↦₃₂ 0#32) ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
        A.pool ∗
        stackAt sp chainKeyToPbStack ∗
        Frame) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm_4e0
    ac_rfl
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.commit_step1_wp img.base ext sp msgA scIdx
      oldRk0 oldRk28 rk0 rk28 sck16 prevCtr0
      oldRk4 oldRk12 oldRk20 rk4 rk12 rk20 sck0 sck1 sck2 sck3
      v440 v448 v4e0 v4e8 v4f0 v4f8
      s hpc hrun hsp hsp_align hx22 hx25 hx27 hx28)
    hm_step1 hL ?_
  intro s1 P1 hpc1 hrun1 _hkf1 _hsym1 hL1 hm1 hpost1
  rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1,
    hx23_1, hx24_1, hx25_1, _hx27_1, _hx28_1, hx29_1, hx30_1, hvregs_1, hP1⟩
  have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
  have hb8_final : ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) =
      ((sp + 0xb8#64) ↦₃₂ rk0) ∗ ((sp + 0xbc#64) ↦₆₄ rk4) ∗
      ((sp + 0xc4#64) ↦₆₄ rk12) ∗ ((sp + 0xcc#64) ↦₆₄ rk20) ∗
      ((sp + 0xd4#64) ↦₃₂ rk28) := by
    rw [pointsToBytes_32_eq_4_8_8_8_4 (sp + 0xb8#64) hrk_len, eb1, eb2, eb3, eb4]
  have h190_1b0_reg :
      (((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦₃₂ rk0) ∗
       ((sp + 0x198#64) ↦₆₄ rk4) ∗
       ((sp + 0x1a0#64) ↦₆₄ rk12) ∗
       ((sp + 0x1a8#64) ↦₆₄ rk20)) ⊢ memRegion (sp + 0x190#64) 32 := by
    have hsplit32 := memRegion_split (sp + 0x190#64) 8 24 (by decide)
    rw [show (8 + 24 : Nat) = 32 from rfl] at hsplit32
    have hsplit8 := memRegion_split (sp + 0x190#64) 4 4 (by decide)
    rw [show (4 + 4 : Nat) = 8 from rfl] at hsplit8
    have hsplit24 := memRegion_split (sp + 0x198#64) 8 16 (by decide)
    rw [show (8 + 16 : Nat) = 24 from rfl] at hsplit24
    have h190_4 := add_assoc_const sp 0x190#64 (BitVec.ofNat 64 4) 0x194#64
    have h190_8 := add_assoc_const sp 0x190#64 (BitVec.ofNat 64 8) 0x198#64
    have h198_8 := add_assoc_const sp 0x198#64 (BitVec.ofNat 64 8) 0x1a0#64
    rw [hsplit32, hsplit8, h190_4, h190_8, hsplit24, h198_8]
    have ha0 := cells_2_to_memRegion_16 (sp + 0x1a0#64) rk12 rk20
    have ha0_off := add_assoc_const sp 0x1a0#64 8#64 0x1a8#64
    rw [ha0_off] at ha0
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono
        (sepConj_mono (cell32_to_memRegion_4 _ 0#32) (cell32_to_memRegion_4 _ rk0))
        (sepConj_mono (cell_to_memRegion_8 _ rk4) ha0))
    ac_rfl
  have h1b0_40_reg :
      (((sp + 0x1b0#64) ↦₃₂ rk28) ∗
       ((sp + 0x1b4#64) ↦₆₄ sck0) ∗
       ((sp + 0x1bc#64) ↦₆₄ sck1) ∗
       ((sp + 0x1c4#64) ↦₃₂ sck16) ∗
       ((sp + 0x1c8#64) ↦₆₄ sck2) ∗
       ((sp + 0x1d0#64) ↦₆₄ sck3)) ⊢ memRegion (sp + 0x1b0#64) 40 := by
    have hsplit40 := memRegion_split (sp + 0x1b0#64) 4 36 (by decide)
    rw [show (4 + 36 : Nat) = 40 from rfl] at hsplit40
    have h1b0_4 := add_assoc_const sp 0x1b0#64 (BitVec.ofNat 64 4) 0x1b4#64
    rw [hsplit40, h1b0_4]
    have hsck_reg : ((sp + 0x1b4#64) ↦ₛ sckBs) ⊢ memRegion (sp + 0x1b4#64) 36 := by
      have h := pointsToBytes_entails_memRegion (sp + 0x1b4#64) sckBs
      rw [chainKeyBytes_length senderChainKey] at h
      exact h
    rw [h1b4_cells] at hsck_reg
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono (cell32_to_memRegion_4 _ rk28) hsck_reg)
    ac_rfl
  have hpc1_ser : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr publicKeySerializeName := by
    rw [hpc1, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.fnAddr_publicKeySerialize_eq]
  have hstk_ser := stackAt_split_from sp chainKeyToPbStack publicKeySerializeStack (by decide) (by decide)
  have hm_ser : s1.mem ⊨
      (publicKeySerializeSpec A).pre ⟨msgA + 0x38#64, srk⟩ s1 ∗
      ((memRegion sp 12 ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
        ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
        memRegion (sp + 0x190#64) 32 ∗
        memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗
        ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
        ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
        ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
        memRegion (sp - BitVec.ofNat 64 chainKeyToPbStack) (chainKeyToPbStack - publicKeySerializeStack) ∗
        Frame) ∗ R) := by
    dsimp only [publicKeySerializeSpec]
    rw [hsp1, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0_1, ?_⟩
    rw [hb8_final]
    have hpull_s1 : s1.mem ⊨
        (((sp + 0x190#64) ↦₃₂ 0#32) ∗
         ((sp + 0x194#64) ↦₃₂ rk0) ∗
         ((sp + 0x198#64) ↦₆₄ rk4) ∗
         ((sp + 0x1a0#64) ↦₆₄ rk12) ∗
         ((sp + 0x1a8#64) ↦₆₄ rk20)) ∗
        (((sp + 0x1b0#64) ↦₃₂ rk28) ∗
         ((sp + 0x1b4#64) ↦₆₄ sck0) ∗
         ((sp + 0x1bc#64) ↦₆₄ sck1) ∗
         ((sp + 0x1c4#64) ↦₃₂ sck16) ∗
         ((sp + 0x1c8#64) ↦₆₄ sck2) ∗
         ((sp + 0x1d0#64) ↦₆₄ sck3)) ∗
        (((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
         A.pool ∗
         stackAt sp chainKeyToPbStack ∗
         memRegion sp 12 ∗
         ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
         (((sp + 0xb8#64) ↦₃₂ rk0) ∗ ((sp + 0xbc#64) ↦₆₄ rk4) ∗
          ((sp + 0xc4#64) ↦₆₄ rk12) ∗ ((sp + 0xcc#64) ↦₆₄ rk20) ∗
          ((sp + 0xd4#64) ↦₃₂ rk28)) ∗
         ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
         ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
         ((sp + 0x440#64) ↦₆₄ sck0) ∗
         ((sp + 0x448#64) ↦₆₄ sck1) ∗
         ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
         ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
         ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
         ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
         Frame ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hm1'
      ac_rfl
    have hreg_s1 := Satisfies.mono
      (sepConj_mono h190_1b0_reg (sepConj_mono_left h1b0_40_reg))
      hpull_s1
    rw [hstk_ser] at hreg_s1
    refine Satisfies.mono (Entails.of_eq ?_) hreg_s1
    ac_rfl
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_call_alloc_panic hPkSer hpc1_ser hrun1 hsp_align1 hx30_1
    (htr1.trans htrace) hm_ser hL1 (by intro _; rfl) (by intros; rfl) ?_
  intro s2 hpc2 hrun2 hsp2 hsp_align2 hcs2 _hkf2 _hsym2 hL2 hm2
  dsimp only [publicKeySerializeSpec] at hm2
  rw [hsp1] at hm2
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
  rcases hm2 with ⟨⟨hx1_2, htr2⟩, hm2⟩
  set boxPtr := s2.readReg64 .x0
  have hser_ne_nil : srk.serialize ≠ [] := publicKey_serialize_ne_nil srk
  have hser_len : srk.serialize.length = 33 := publicKey_serialize_length srk
  have hbox_buf : boxU8Buf A boxPtr srk.serialize =
      (⌜boxPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize))) := by
    unfold boxU8Buf
    simp only [hser_ne_nil, ↓reduceIte, hser_len]
  rw [hbox_buf] at hm2
  have hm2_sp : s2.mem ⊨
      memRegion sp 12 ∗
      ((⌜boxPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize))) ∗
       ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
       A.pool ∗
       stackAt sp chainKeyToPbStack ∗
       ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
       ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
       memRegion (sp + 0x190#64) 32 ∗
       memRegion (sp + 0x1b0#64) 40 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       ((sp + 0x440#64) ↦₆₄ sck0) ∗
       ((sp + 0x448#64) ↦₆₄ sck1) ∗
       ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
       ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
       ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
       ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
       (Frame ∗ R)) := by
    rw [hstk_ser]
    refine Satisfies.mono (Entails.of_eq ?_) hm2
    ac_rfl
  have hsplit12 := memRegion_split sp 8 4 (by decide)
  rw [show (8 + 4 : Nat) = 12 from rfl] at hsplit12
  rw [hsplit12, sepConj_assoc] at hm2_sp
  obtain ⟨vSp0, hm2_sp⟩ := elim_memRegion_8 hm2_sp
  have hm2_sp8 : s2.mem ⊨
      memRegion (sp + 8#64) 4 ∗
      ((sp ↦₆₄ vSp0) ∗
       (⌜boxPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize))) ∗
       ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
       A.pool ∗
       stackAt sp chainKeyToPbStack ∗
       ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
       ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
       memRegion (sp + 0x190#64) 32 ∗
       memRegion (sp + 0x1b0#64) 40 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       ((sp + 0x440#64) ↦₆₄ sck0) ∗
       ((sp + 0x448#64) ↦₆₄ sck1) ∗
       ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
       ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
       ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
       ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
       (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm2_sp
    ac_rfl
  obtain ⟨vSp8, hm2_sp8⟩ := elim_memRegion_4 hm2_sp8
  have hm_pre_shim : s2.mem ⊨
      ((sp ↦₆₄ vSp0) ∗ ((sp + 8#64) ↦₃₂ vSp8)) ∗
      (((A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
        A.pool ∗
        stackAt sp chainKeyToPbStack ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
        ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
        memRegion (sp + 0x190#64) 32 ∗
        memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗
        ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
        ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
        ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
        Frame) ∗ R) := by
    have hdrop_pure :
        (⌜boxPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize))) ⊢
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) :=
      Entails.pure_left (fun _ => Entails.refl _)
    have hm2_sp8' := Satisfies.mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hdrop_pure))) hm2_sp8
    refine Satisfies.mono (Entails.of_eq ?_) hm2_sp8'
    ac_rfl
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.commit_step2_pre_shim_wp img.base ext sp boxPtr vSp0 vSp8 sck16
      s2 hpc2 hrun2 (by reg_chain) hsp_align2 rfl hx1_2 (by reg_chain))
    hm_pre_shim hL2 ?_
  intro s3 P3 hpc3 hrun3 _hkf3 _hsym3 hL3 hm3 hpost3
  rcases hpost3 with ⟨hsp3, hsp_align3, htr3, hx19_3, hx20_3, hx21_3, hx22_3,
    hx23_3, _hx24_3, hx25_3, hx26_3, hx27_3, _hx28_3, hx29_3, hx30_3, hvregs_3, hP3⟩
  have hm3' := Satisfies.mono (sepConj_mono_left hP3) hm3
  have hm_shim : s3.mem ⊨
      noAllocShimSpec.pre () s3 ∗
      (((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
        A.pool ∗
        stackAt sp chainKeyToPbStack ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
        ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
        memRegion (sp + 0x190#64) 32 ∗
        memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗
        ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
        ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
        ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
        Frame) ∗ R) := by
    dsimp only [noAllocShimSpec]
    rw [emp_sepConj]
    refine Satisfies.mono (Entails.of_eq ?_) hm3'
    ac_rfl
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_call_no_panic (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.shim_ok_at_0xe6a8 hA)
    hpc3 hrun3 hsp_align3 hx30_3 hm_shim hL3 (by intro _; rfl) (by intros; rfl) ?_
  intro s4 hpc4 hrun4 hsp4 hsp_align4 hcs4 _hkf4 _hsym4 hL4 hm4
  dsimp only [noAllocShimSpec] at hm4
  rw [satisfies_pure_sepConj] at hm4
  rcases hm4 with ⟨htr4, hm4⟩
  have hm_pre_alloc : s4.mem ⊨
      emp ∗
      (((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
        A.pool ∗
        stackAt sp chainKeyToPbStack ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
        ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
        memRegion (sp + 0x190#64) 32 ∗
        memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗
        ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
        ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
        ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
        Frame) ∗ R) := by
    rw [emp_sepConj]; exact hm4
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.commit_step2_pre_alloc_wp img.base ext sp
      s4 hpc4 hrun4 (by reg_chain) hsp_align4 (by reg_chain))
    hm_pre_alloc hL4 ?_
  intro s5 P5 hpc5 hrun5 _hkf5 _hsym5 hL5 hm5 hpost5
  rcases hpost5 with ⟨hsp5, hsp_align5, htr5, hx0_5, hx1_5,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, _hx24_5, hx25_5, hx26_5, _hx27_5, _hx28_5, hx29_5, hx30_5, hvregs_5, hP5⟩
  have hm5' := Satisfies.mono (sepConj_mono_left hP5) hm5
  rw [emp_sepConj] at hm5'
  have hstk_alloc := stackAt_split_from sp chainKeyToPbStack allocHookStack (by decide) (by decide)
  have hm_alloc : s5.mem ⊨
      (rustAllocSpec A).pre (33, 1) s5 ∗
      (((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
        memRegion (sp - BitVec.ofNat 64 chainKeyToPbStack) (chainKeyToPbStack - allocHookStack) ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
        ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
        memRegion (sp + 0x190#64) 32 ∗
        memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗
        ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
        ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
        ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
        Frame) ∗ R) := by
    dsimp only [rustAllocSpec]
    rw [hstk_alloc] at hm5'
    rw [hsp5, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by rw [hx0_5]; rfl, by rw [hx1_5]; rfl, by decide, ⟨0, rfl⟩, by decide⟩, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm5'
    ac_rfl
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_call_no_panic (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.alloc_ok_at_0xe6ac hA)
    hpc5 hrun5 hsp_align5 hx30_5 hm_alloc hL5 (by intro _; rfl) (by intros; rfl) ?_
  intro s6 hpc6 hrun6 hsp6 hsp_align6 hcs6 _hkf6 _hsym6 hL6 hm6
  dsimp only [rustAllocSpec] at hm6
  set srkPtr := s6.readReg64 .x0
  have htr_s5 : s5.trace = s0.trace := by reg_chain
  by_cases hsrk0 : srkPtr = 0
  · simp only [hsrk0, ↓reduceIte] at hm6
    have hm6_pull : s6.mem ⊨
        ⌜s6.trace = s5.trace ++ [allocFailedEvent]⌝ ∗
        (emp ∗
         (((A.pool ∗ stackAt s5.sp allocHookStack) ∗
           ((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗
            (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
            ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
            memRegion (sp - BitVec.ofNat 64 chainKeyToPbStack) (chainKeyToPbStack - allocHookStack) ∗
            ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
            ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
            ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
            memRegion (sp + 0x190#64) 32 ∗
            memRegion (sp + 0x1b0#64) 40 ∗
            ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
            ((sp + 0x440#64) ↦₆₄ sck0) ∗
            ((sp + 0x448#64) ↦₆₄ sck1) ∗
            ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
            ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
            ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
            ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
            Frame)) ∗ R)) := by
      rw [emp_sepConj]
      refine Satisfies.mono (Entails.of_eq ?_) hm6
      ac_rfl
    rw [satisfies_pure_sepConj] at hm6_pull
    rcases hm6_pull with ⟨htr6_fail, hm_oom⟩
    refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.commit_step2_oom_wp img.base ext sp s6 hpc6 hrun6 (hsp6.trans hsp5) hsp_align6 hsrk0)
      hm_oom hL6 ?_
    intro s7 P7 hpc7 hrun7 _hkf7 _hsym7 _hL7 hm7 ⟨htr7, _hP7⟩
    have htr7_eq : s7.trace = s0.trace ++ [allocFailedEvent] := by
      rw [htr7, htr6_fail, htr_s5]
    rcases allocFailedIn_of_eq htr7_eq with ⟨hfail7, hpfx7⟩
    rw [← sepConj_assoc] at hm7
    exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_panic_extern hrun7 (by rw [hpc7]; exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.panic_at_0xe6f4)
      hfail7 hpfx7 hm7
  · simp only [hsrk0, ↓reduceIte] at hm6
    rw [hsp5] at hm6
    have hm6_pull : s6.mem ⊨
        ⌜srkPtr.toNat % 1 = 0 ∧ s6.trace = s5.trace⌝ ∗
        ((sp ↦₆₄ boxPtr) ∗
         ((memRegion srkPtr 33 ∗
           A.live srkPtr 33 1 ∗
           A.pool ∗
           stackAt sp chainKeyToPbStack ∗
           ((sp + 8#64) ↦₃₂ sck16) ∗
           (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
           ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
           ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
           ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
           ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
           memRegion (sp + 0x190#64) 32 ∗
           memRegion (sp + 0x1b0#64) 40 ∗
           ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
           ((sp + 0x440#64) ↦₆₄ sck0) ∗
           ((sp + 0x448#64) ↦₆₄ sck1) ∗
           ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
           ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
           ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
           ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
           Frame) ∗ R)) := by
      rw [hstk_alloc]
      refine Satisfies.mono (Entails.of_eq ?_) hm6
      ac_rfl
    rw [satisfies_pure_sepConj] at hm6_pull
    rcases hm6_pull with ⟨⟨_halign, htr6⟩, hm_post_alloc⟩
    refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.commit_step2_post_alloc_wp img.base ext sp srkPtr boxPtr
        s6 hpc6 hrun6 (by reg_chain) hsp_align6 rfl hsrk0 (by reg_chain))
      hm_post_alloc hL6 ?_
    intro s7 P7 hpc7 hrun7 _hkf7 _hsym7 hL7 hm7 hpost7
    rcases hpost7 with ⟨hsp7, hsp_align7, htr7, hx0_7, hx1_7, hx2_7,
      hx19_7, hx20_7, hx21_7, hx22_7, hx23_7, _hx24_7, hx25_7, hx26_7, hx27_7, hx28_7,
      hx29_7, hx30_7, hvregs_7, hP7⟩
    have hm7' := Satisfies.mono (sepConj_mono_left hP7) hm7
    have hm_memcpy : s7.mem ⊨
        framelessMemcpySpec.pre (srkPtr, boxPtr, srk.serialize) s7 ∗
        (((sp ↦₆₄ boxPtr) ∗
          A.live srkPtr 33 1 ∗
          A.live boxPtr 33 1 ∗
          A.pool ∗
          stackAt sp chainKeyToPbStack ∗
          ((sp + 8#64) ↦₃₂ sck16) ∗
          ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
          ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
          ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
          ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
          memRegion (sp + 0x190#64) 32 ∗
          memRegion (sp + 0x1b0#64) 40 ∗
          ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
          ((sp + 0x440#64) ↦₆₄ sck0) ∗
          ((sp + 0x448#64) ↦₆₄ sck1) ∗
          ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
          ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
          ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
          ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
          Frame) ∗ R) := by
      dsimp only [framelessMemcpySpec]
      rw [hser_len]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_7, hx1_7, by rw [hx2_7]; rfl⟩, ?_⟩
      refine Satisfies.mono (Entails.of_eq ?_) hm7'
      ac_rfl
    refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_call_no_panic (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.memcpy_ok_at_0xe6d8 hA)
      hpc7 hrun7 hsp_align7 hx30_7 hm_memcpy hL7 (by intro _; rfl) (by intros; rfl) ?_
    intro s8 hpc8 hrun8 hsp8 hsp_align8 hcs8 _hkf8 _hsym8 hL8 hm8
    dsimp only [framelessMemcpySpec] at hm8
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm8
    rcases hm8 with ⟨⟨_hx0_8, htr8⟩, hm8⟩
    have hm_to_pb_wp : s8.mem ⊨
        emp ∗
        (((srkPtr ↦ₛ srk.serialize) ∗ (boxPtr ↦ₛ srk.serialize) ∗
          (sp ↦₆₄ boxPtr) ∗
          A.live srkPtr 33 1 ∗
          A.live boxPtr 33 1 ∗
          A.pool ∗
          stackAt sp chainKeyToPbStack ∗
          ((sp + 8#64) ↦₃₂ sck16) ∗
          ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
          ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
          ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
          ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
          memRegion (sp + 0x190#64) 32 ∗
          memRegion (sp + 0x1b0#64) 40 ∗
          ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
          ((sp + 0x440#64) ↦₆₄ sck0) ∗
          ((sp + 0x448#64) ↦₆₄ sck1) ∗
          ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
          ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
          ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
          ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
          Frame) ∗ R) := by
      rw [emp_sepConj]
      refine Satisfies.mono (Entails.of_eq ?_) hm8
      ac_rfl
    refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.commit_step2_to_pb_wp img.base ext sp s8 hpc8 hrun8 (by reg_chain) hsp_align8
        (by reg_chain))
      hm_to_pb_wp hL8 ?_
    intro s9 P9 hpc9 hrun9 _hkf9 _hsym9 hL9 hm9 hpost9
    rcases hpost9 with ⟨hsp9, hsp_align9, htr9, hx0_9, hx8_9,
      hx19_9, hx20_9, hx21_9, hx22_9, hx23_9, _hx24_9, hx25_9, hx26_9, hx27_9, hx28_9,
      hx29_9, hx30_9, hvregs_9, hP9⟩
    have hm9' := Satisfies.mono (sepConj_mono_left hP9) hm9
    rw [emp_sepConj] at hm9'
    have hpc9_pb : s9.pc = (tripleRatchetProgAtExt img.base ext).fnAddr chainKeyToPbName := by
      rw [hpc9, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.fnAddr_chainKeyToPb_eq]
    have hm_to_pb : s9.mem ⊨
        (chainKeyToPbSpec A).pre ⟨sp + 0x3d0#64, receiverChainKey, sp + 0x190#64⟩ s9 ∗
        (((sp ↦₆₄ boxPtr) ∗
          ((sp + 8#64) ↦₃₂ sck16) ∗
          ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
          ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
          ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
          memRegion (sp + 0x1b0#64) 40 ∗
          ((sp + 0x440#64) ↦₆₄ sck0) ∗
          ((sp + 0x448#64) ↦₆₄ sck1) ∗
          ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
          ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
          ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
          ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
          ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
          (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
          (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
          Frame) ∗ R) := by
      dsimp only [chainKeyToPbSpec]
      rw [hsp9, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_9, hx8_9⟩, ?_⟩
      refine Satisfies.mono (Entails.of_eq ?_) hm9'
      ac_rfl
    refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_call_alloc_panic hToPb hpc9_pb hrun9 hsp_align9 hx30_9
      (by reg_chain) hm_to_pb hL9 (by intro _; rfl) (by intros; rfl) ?_
    intro s10 hpc10 hrun10 hsp10 hsp_align10 hcs10 _hkf10 _hsym10 hL10 hm10
    dsimp only [chainKeyToPbSpec] at hm10
    rw [hsp9] at hm10
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm10
    rcases hm10 with ⟨htr10, hm10⟩
    have hm10_pb : s10.mem ⊨
        (∃∗ p' : BitVec 64, optChainKeyAt A ⟨32#64, p'⟩ (some receiverChainKey) (sp + 0x190#64)) ∗
        (((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
         A.pool ∗
         stackAt sp chainKeyToPbStack ∗
         ((sp ↦₆₄ boxPtr) ∗
          ((sp + 8#64) ↦₃₂ sck16) ∗
          ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
          ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
          ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
          memRegion (sp + 0x1b0#64) 40 ∗
          ((sp + 0x440#64) ↦₆₄ sck0) ∗
          ((sp + 0x448#64) ↦₆₄ sck1) ∗
          ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
          ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
          ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
          ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
          ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
          (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
          (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
          Frame) ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hm10
      ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm10_pb
    rcases hm10_pb with ⟨ckPtr, hm10_pb⟩
    rw [optChainKeyAt_eq_exists_bytes A ⟨32#64, ckPtr⟩ (some receiverChainKey) (sp + 0x190#64),
        sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm10_pb
    rcases hm10_pb with ⟨pad, hm10_pb⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm10_pb
    rcases hm10_pb with ⟨hpad, hm10_pb⟩
    have hm10_final : s10.mem ⊨
        ((sp ↦₆₄ boxPtr) ∗
         ((sp + 8#64) ↦₃₂ sck16) ∗
         ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
         ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
         ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
         ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
         memRegion (sp + 0x1b0#64) 40 ∗
         ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
         ((sp + 0x440#64) ↦₆₄ sck0) ∗
         ((sp + 0x448#64) ↦₆₄ sck1) ∗
         ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
         ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
         ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
         ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
         ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
         (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
         (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
         optChainKeyHeap A ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗
         A.pool ∗
         stackAt sp chainKeyToPbStack) ∗ (Frame ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hm10_pb
      ac_rfl
    exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.done ⟨boxPtr, srkPtr, ckPtr, pad, hsrk0, hpad, hpc10, hrun10,
      by reg_chain, hsp_align10, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, by reg_chain,
      hL10, hm10_final⟩

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit
