/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `<MessageKeyGenerator>::generate_keys`

Verifies `<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys` against
`generateKeysSpec` and `generateKeysSpecX` on both rebased images and `[LibsignalPlacement]`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Keys

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") → (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys" + 440)]

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

/-! ## `.rodata` literal `"WhisperMessageKeys"` -/

@[local simp, local arm64_norm]
theorem whisperMessageKeys_length : whisperMessageKeys.length = 18 := rfl

@[local simp, local arm64_norm]
theorem lt_32_18 : (18 : Nat) < 32 := by decide

theorem rodata_0x44ebd {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} (hro : img.RoDataLoaded m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_str% "WhisperMessageKeys")) ↦ᵣ whisperMessageKeys) ∗ P := by
  have hsec : (num% (ls_str% "WhisperMessageKeys"), 18) ∈ libsignalSessionImage.roData := by decide
  have ⟨h1, h2⟩ := rodata_readBytes_disjoint himg (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44))) rfl hsec
    (by decide) (by decide) (by decide +kernel) (by rfl_kernel) m hro
  have hbytes : (libsignalSessionImage.data.drop (num% (ls_str% "WhisperMessageKeys") - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 18 =
      whisperMessageKeys := by rfl_kernel
  rw [hbytes] at h2
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-! ## Pure and byte-splitting lemmas for `generateKeys` -/

private theorem blockToBytesLE_eq_list (b : CBC.Block) :
    CBC.blockToBytesLE b =
      [b.extractLsb' 0 8, b.extractLsb' 8 8, b.extractLsb' 16 8, b.extractLsb' 24 8,
       b.extractLsb' 32 8, b.extractLsb' 40 8, b.extractLsb' 48 8, b.extractLsb' 56 8,
       b.extractLsb' 64 8, b.extractLsb' 72 8, b.extractLsb' 80 8, b.extractLsb' 88 8,
       b.extractLsb' 96 8, b.extractLsb' 104 8, b.extractLsb' 112 8, b.extractLsb' 120 8] :=
  rfl

private theorem bytesToBlock_16_eq
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    CBC.bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] =
      b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++
      b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 := by
  have h0 (x : BitVec 8) : ((0 : BitVec 128) <<< 8) ||| x.setWidth 128 = x.setWidth 128 := by simp
  have hs {w : Nat} (x : BitVec w) (y : BitVec 8) :
      ((x.setWidth 128) <<< 8) ||| y.setWidth 128 = (x ++ y).setWidth 128 := by
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getLsbD_append]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [h8, BitVec.getLsbD_of_ge y i (by omega)]
  dsimp only [CBC.bytesToBlock, List.foldr, BitVec.zeroExtend]
  rw [h0]
  repeat rw [hs]
  exact BitVec.setWidth_eq _

theorem blockToBytesLE_bytesToBlock (bs : List (BitVec 8)) (h : bs.length = 16) :
    CBC.blockToBytesLE (CBC.bytesToBlock bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at h)
  rw [blockToBytesLE_eq_list, bytesToBlock_16_eq]
  simp only [List.cons.injEq, and_true]
  refine ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
          by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
          by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
          by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem length_hkdfExpand_80 (F : ShaCompress) (prk info : List (BitVec 8)) :
    (hkdfExpand F prk info 80).length = 80 := by
  simp [hkdfExpand, hkdfBlocks]

theorem messageKeysAt_eq_append (r : BitVec 64) (mk : MessageKeys) :
    messageKeysAt r mk =
      (r ↦ₛ (keyToBytes32 mk.cipherKey ++ keyToBytes32 mk.macKey ++ CBC.blockToBytesLE mk.iv)) ∗
        ((r + 80#64) ↦₃₂ mk.counter) := by
  simp only [messageKeysAt]
  have h1 : (keyToBytes32 mk.cipherKey).length = 32 := by simp [keyToBytes32]
  have h2 : (keyToBytes32 mk.macKey).length = 32 := by simp [keyToBytes32]
  have h12 : (keyToBytes32 mk.cipherKey ++ keyToBytes32 mk.macKey).length = 64 := by
    simp [h1, h2]
  rw [pointsToBytes_append, h12, pointsToBytes_append, h1]
  simp only [sepConj_assoc]

theorem messageKeysAt_generateKeys (r : BitVec 64) (F : ShaCompress) (seed : List (BitVec 8))
    (counter : BitVec 32) (pqrKey : Salt) :
    messageKeysAt r (MessageKeyGenerator.generateKeys F ⟨seed, counter⟩ pqrKey) =
      (r ↦ₛ (keyToBytes32 (deriveMessageKeys F pqrKey seed).1.1 ++
        keyToBytes32 (deriveMessageKeys F pqrKey seed).2 ++
        CBC.blockToBytesLE (deriveMessageKeys F pqrKey seed).1.2)) ∗
        ((r + 80#64) ↦₃₂ counter) := by
  rw [messageKeysAt_eq_append]
  rfl

theorem deriveMessageKeys_eq (F : ShaCompress) (seed : List (BitVec 8)) (pqrKey : Salt) :
    let k := deriveMessageKeys F pqrKey seed
    (keyToBytes32 k.1.1).length = 32 ∧
    (keyToBytes32 k.2).length = 32 ∧
    (CBC.blockToBytesLE k.1.2).length = 16 ∧
    hkdfExpand F (hkdfExtract F pqrKey seed) whisperMessageKeys 80 =
      keyToBytes32 k.1.1 ++ keyToBytes32 k.2 ++ CBC.blockToBytesLE k.1.2 := by
  have hlen := length_hkdfExpand_80 F (hkdfExtract F pqrKey seed) whisperMessageKeys
  dsimp only [deriveMessageKeys, hkdf]
  generalize hkdfExpand F (hkdfExtract F pqrKey seed) whisperMessageKeys 80 = okm at hlen ⊢
  have htake1 : (okm.take 32).length = 32 := by simp [hlen]
  have htake2 : ((okm.drop 32).take 32).length = 32 := by simp [hlen]
  have htake3 : ((okm.drop 64).take 16).length = 16 := by simp [hlen]
  have hdrop64 : (okm.drop 64).take 16 = okm.drop 64 := by
    rw [List.take_of_length_le (by simp [hlen])]
  refine ⟨by simp [keyToBytes32], by simp [keyToBytes32], by simp [CBC.blockToBytesLE], ?_⟩
  rw [keyToBytes32_bytesToKey32 _ htake1,
    keyToBytes32_bytesToKey32 _ htake2,
    blockToBytesLE_bytesToBlock _ htake3, hdrop64]
  have h1 := (List.take_append_drop 32 okm).symm
  have h2 := (List.take_append_drop 32 (okm.drop 32)).symm
  rw [List.drop_drop] at h2
  rw [List.append_assoc, ← h2, ← h1]

/-! ## Stack-frame, output-buffer, and `Vec<u8>` splitting lemmas -/

theorem fnFrame_split_generateKeys_pre (sp : BitVec 64) :
    stackAt sp generateKeysStack =
      stackAt (sp - 496#64) allocHookStack ∗
        cells (sp - 496#64) 10 ∗ cells (sp - 416#64) 4 ∗
        cells (sp - 384#64) 14 ∗ memRegion (sp - 272#64) 176 ∗
        cells (sp - 96#64) 12 := by
  simp only [stackAt, generateKeysStack, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 4592) (n := 4096) (k := 496)
      (b' := sp - 496#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 496#64) (n := 80) (k := 416) (b' := sp - 416#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 416#64) (n := 32) (k := 384) (b' := sp - 384#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 384#64) (n := 112) (k := 272) (b' := sp - 272#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 176) (k := 96) (b' := sp - 96#64) rfl
      (by bv_omega) (by decide),
    (memRegion_cells (sp - 496#64) 10 (by decide) :
      memRegion (sp - 496#64) 80 = cells (sp - 496#64) 10),
    (memRegion_cells (sp - 416#64) 4 (by decide) :
      memRegion (sp - 416#64) 32 = cells (sp - 416#64) 4),
    (memRegion_cells (sp - 384#64) 14 (by decide) :
      memRegion (sp - 384#64) 112 = cells (sp - 384#64) 14),
    (memRegion_cells (sp - 96#64) 12 (by decide) :
      memRegion (sp - 96#64) 96 = cells (sp - 96#64) 12)]
  have hsub : sp - 496#64 - BitVec.ofNat 64 4096 = sp - BitVec.ofNat 64 4592 := by bv_kernel
  rw [hsub]

theorem fnFrame_split_generateKeys_post (sp : BitVec 64) :
    stackAt sp generateKeysStack =
      stackAt (sp - 496#64) allocHookStack ∗
        cells (sp - 496#64) 10 ∗ cells (sp - 416#64) 8 ∗
        memRegion (sp - 352#64) 80 ∗ cells (sp - 272#64) 4 ∗
        cells (sp - 240#64) 4 ∗ cells (sp - 208#64) 14 ∗
        cells (sp - 96#64) 12 := by
  simp only [stackAt, generateKeysStack, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 4592) (n := 4096) (k := 496)
      (b' := sp - 496#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 496#64) (n := 80) (k := 416) (b' := sp - 416#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 416#64) (n := 64) (k := 352) (b' := sp - 352#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 352#64) (n := 80) (k := 272) (b' := sp - 272#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 32) (k := 240) (b' := sp - 240#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 240#64) (n := 32) (k := 208) (b' := sp - 208#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 208#64) (n := 112) (k := 96) (b' := sp - 96#64) rfl
      (by bv_omega) (by decide),
    (memRegion_cells (sp - 496#64) 10 (by decide) :
      memRegion (sp - 496#64) 80 = cells (sp - 496#64) 10),
    (memRegion_cells (sp - 416#64) 8 (by decide) :
      memRegion (sp - 416#64) 64 = cells (sp - 416#64) 8),
    (memRegion_cells (sp - 272#64) 4 (by decide) :
      memRegion (sp - 272#64) 32 = cells (sp - 272#64) 4),
    (memRegion_cells (sp - 240#64) 4 (by decide) :
      memRegion (sp - 240#64) 32 = cells (sp - 240#64) 4),
    (memRegion_cells (sp - 208#64) 14 (by decide) :
      memRegion (sp - 208#64) 112 = cells (sp - 208#64) 14),
    (memRegion_cells (sp - 96#64) 12 (by decide) :
      memRegion (sp - 96#64) 96 = cells (sp - 96#64) 12)]
  have hsub : sp - 496#64 - BitVec.ofNat 64 4096 = sp - BitVec.ofNat 64 4592 := by bv_kernel
  rw [hsub]

theorem memRegion_out_generateKeys (out : BitVec 64) :
    memRegion out 84 = cells out 10 ∗ (∃∗ v, (out + 80#64) ↦₃₂ v) := by
  rw [show (84 : Nat) = 80 + 4 from rfl, memRegion_split out 80 4 (by decide),
    (memRegion_cells out 10 (by decide) : memRegion out 80 = cells out 10),
    memRegion_four (out + 80#64)]

theorem memRegion_gen_generateKeys (genA : BitVec 64) :
    memRegion genA 40 =
      (∃∗ d0, genA ↦₃₂ d0) ∗ memRegion (genA + 4#64) 4 ∗
        cells (genA + 8#64) 3 ∗
        (∃∗ d1, (genA + 32#64) ↦₃₂ d1) ∗ memRegion (genA + 36#64) 4 := by
  rw [ProofLib.memRegion_split' (b := genA) (n := 4) (k := 36) (b' := genA + 4#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := genA + 4#64) (n := 4) (k := 32) (b' := genA + 8#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := genA + 8#64) (n := 24) (k := 8) (b' := genA + 32#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := genA + 32#64) (n := 4) (k := 4) (b' := genA + 36#64) rfl
      (by bv_omega) (by decide),
    memRegion_four genA,
    (memRegion_cells (genA + 8#64) 3 (by decide) :
      memRegion (genA + 8#64) 24 = cells (genA + 8#64) 3),
    memRegion_four (genA + 32#64)]

theorem vecU8At_split_32 (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 32) :
    vecU8At A v cap ptr bs ⊢
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 ∧ cap ≠ 0⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 32#64) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + 32#64) (cap.toNat - 32) := by
  dsimp only [vecU8At]
  simp only [hlen, BitVec.ofNat_eq_ofNat]
  rw [← sepConj_assoc, sepConj_comm (vecHeader v cap ptr 32#64), sepConj_assoc]
  refine Entails.pure_left fun ⟨hl, hs, hp⟩ => ?_
  have hc : cap ≠ 0#64 := by intro h0; subst h0; simp at hl
  simp only [hc, ↓reduceIte]
  refine Entails.pure_right ⟨hl, hs, hp, hc⟩ ?_
  dsimp only [vecHeader]
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem vecU8At_split_nil (A : RustAlloc) (v cap ptr : BitVec 64) :
    vecU8At A v cap ptr [] ⊢
      ⌜cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        (if cap = 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  dsimp only [vecU8At, List.length_nil, Nat.sub_zero, BitVec.ofNat_eq_ofNat]
  rw [← sepConj_assoc, sepConj_comm (vecHeader v cap ptr 0#64), sepConj_assoc]
  refine Entails.pure_left fun ⟨_, hs, hp⟩ => ?_
  refine Entails.pure_right ⟨hs, hp⟩ ?_
  dsimp only [vecHeader]
  simp only [pointsToBytes_nil, emp_sepConj, BitVec.add_zero, sepConj_assoc]
  exact Entails.refl _

theorem pointsToBytes_memRegion_merge_32 (ptr : BitVec 64) (bs : List (BitVec 8)) (cap : BitVec 64)
    (hlen : bs.length = 32) (hl : 32 ≤ cap.toNat) (hs : cap.toNat < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + 32#64) (cap.toNat - 32) ⊢
      memRegion ptr cap.toNat := by
  have hsplit := memRegion_split ptr 32 (cap.toNat - 32) (by omega)
  rw [show 32 + (cap.toNat - 32) = cap.toNat by omega] at hsplit
  rw [hsplit]
  have hpts := pointsToBytes_entails_memRegion ptr bs
  rw [hlen] at hpts
  exact sepConj_mono_left hpts

theorem slt_one_false_of_small {c : BitVec 64} (hs : c.toNat < 2 ^ 63) (hne : ¬c = 0)
    (h : c.slt 1#64 = true) : False := by
  rw [BitVec.slt_iff_toInt_lt, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at h
  have : c.toNat ≠ 0 := fun h0 => hne (BitVec.eq_of_toNat_eq (by simpa using h0))
  split at h <;> simp at h <;> omega

theorem slt_one_eq_false_of_small {c : BitVec 64} (hs : c.toNat < 2 ^ 63) (hne : ¬c = 0) :
    c.slt 1#64 = false :=
  Bool.eq_false_iff.mpr (slt_one_false_of_small hs hne)

private theorem generateKeys_adrp1 {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    ((b + bv% (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") + 108#64 &&& 0xfffffffffffff000#64) + bv% (ls_str% "WhisperMessageKeys" - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new" + 1768))) =
      b + bv% (ls_str% "WhisperMessageKeys") := by
  revert hb; bv_kernel

private theorem generateKeys_adrp2 {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    ((b + bv% (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") + 108#64 &&& 0xfffffffffffff000#64) + bv% (page% (ls_str% "WhisperMessageKeys") - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new" + 1768)) + bv% ((ls_str% "WhisperMessageKeys") % 4096)) =
      b + bv% (ls_str% "WhisperMessageKeys") := by
  revert hb; bv_kernel

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_sub_lit bv_sub_add_lit bv_add_neg64
attribute [local simp, local arm64_norm] hkdfExtract_length'

namespace GenerateKeysFacts

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem bv_sub_add_lit' (x a b : BitVec 64) :
    x - a + b = x - (a - b) := by bv_omega

macro "cells_pre_unfold_fast" : tactic =>
  `(tactic| (
    conv => arg 4; simp (config := { maxSteps := 200000 }) only [
      cells, sepConj_emp, bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]))

macro "wp_simp_pre_fast " "[" rules:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (conv => arg 4; simp only [$rules,*]))

theorem hmacCore_merge_sub416 (F : ShaCompress) (sp : BitVec 64) (key : List (BitVec 8))
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64}
    (hg : HmacGood F key [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
      w16, w17]) :
    (((sp - 416#64) ↦₆₄ w0) ∗ ((sp - 408#64) ↦₆₄ w1) ∗ ((sp - 400#64) ↦₆₄ w2) ∗
      ((sp - 392#64) ↦₆₄ w3) ∗ ((sp - 384#64) ↦₆₄ w4) ∗ ((sp - 376#64) ↦₆₄ w5) ∗
      ((sp - 368#64) ↦₆₄ w6) ∗ ((sp - 360#64) ↦₆₄ w7) ∗ ((sp - 352#64) ↦₆₄ w8) ∗
      ((sp - 344#64) ↦₆₄ w9) ∗ ((sp - 336#64) ↦₆₄ w10) ∗ ((sp - 328#64) ↦₆₄ w11) ∗
      ((sp - 320#64) ↦₆₄ w12) ∗ ((sp - 312#64) ↦₆₄ w13) ∗ ((sp - 304#64) ↦₆₄ w14) ∗
      ((sp - 296#64) ↦₆₄ w15) ∗ ((sp - 288#64) ↦₆₄ w16) ∗ ((sp - 280#64) ↦₆₄ w17)) ⊢
      hmacCoreAt F (sp - 416#64) key [] := by
  have hmrg := hmacCore_merge F (sp - 416#64) key hg
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hmrg
  exact hmrg

theorem generateKeys_deallocAllocStack_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr generateKeysName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys"))
      (deallocAllocStackSpec A) := by
  refine subroutine_ok_map
    (hook_ok_at_raw (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys")) rfl (by decide)
      (ls_hook% "__rustc::__rust_dealloc")
      (allocHooks_tripleRatchetExterns C ctl A abs hA).dealloc) ?_
  rintro ⟨p, size, align, sp⟩ R s0 hpre
  dsimp only [deallocAllocStackSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hsp⟩, hpre⟩
  refine ⟨(p, size, align), R, ?_, ?_⟩
  · dsimp only [rustDeallocSpec]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, hpre⟩
  · intro sf hpost
    dsimp only [rustDeallocSpec, deallocAllocStackSpec] at hpost ⊢
    subst hsp
    exact hpost

theorem cells_3_merge (a v0 v1 v2 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ⊢ cells a 3 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.refl _

theorem cells_4_merge (a v0 v1 v2 v3 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ⊢
      cells a 4 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <| Entails.refl _

theorem cells_8_merge (a v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ⊢ cells a 8 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <| Entails.refl _

theorem cells_10_merge (a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ⊢ cells a 10 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <|
    Entails.sepExists_right v8 <| Entails.sepExists_right v9 <| Entails.refl _

theorem cells_12_merge (a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗
      ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ⊢ cells a 12 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <|
    Entails.sepExists_right v8 <| Entails.sepExists_right v9 <|
    Entails.sepExists_right v10 <| Entails.sepExists_right v11 <| Entails.refl _

theorem cells_14_merge (a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗
      ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ∗ ((a + 96#64) ↦₆₄ v12) ∗
      ((a + 104#64) ↦₆₄ v13) ⊢ cells a 14 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <|
    Entails.sepExists_right v8 <| Entails.sepExists_right v9 <|
    Entails.sepExists_right v10 <| Entails.sepExists_right v11 <|
    Entails.sepExists_right v12 <| Entails.sepExists_right v13 <| Entails.refl _

theorem cells_sub496_10_merge (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    ((sp - 496#64) ↦₆₄ v0) ∗ ((sp - 488#64) ↦₆₄ v1) ∗ ((sp - 480#64) ↦₆₄ v2) ∗
      ((sp - 472#64) ↦₆₄ v3) ∗ ((sp - 464#64) ↦₆₄ v4) ∗ ((sp - 456#64) ↦₆₄ v5) ∗
      ((sp - 448#64) ↦₆₄ v6) ∗ ((sp - 440#64) ↦₆₄ v7) ∗ ((sp - 432#64) ↦₆₄ v8) ∗
      ((sp - 424#64) ↦₆₄ v9) ⊢ cells (sp - 496#64) 10 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using
    cells_10_merge (sp - 496#64) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9

theorem cells_sub416_8_merge (sp v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) :
    ((sp - 416#64) ↦₆₄ v0) ∗ ((sp - 408#64) ↦₆₄ v1) ∗ ((sp - 400#64) ↦₆₄ v2) ∗
      ((sp - 392#64) ↦₆₄ v3) ∗ ((sp - 384#64) ↦₆₄ v4) ∗ ((sp - 376#64) ↦₆₄ v5) ∗
      ((sp - 368#64) ↦₆₄ v6) ∗ ((sp - 360#64) ↦₆₄ v7) ⊢ cells (sp - 416#64) 8 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using
    cells_8_merge (sp - 416#64) v0 v1 v2 v3 v4 v5 v6 v7

theorem cells_sub272_4_merge (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 272#64) ↦₆₄ v0) ∗ ((sp - 264#64) ↦₆₄ v1) ∗ ((sp - 256#64) ↦₆₄ v2) ∗
      ((sp - 248#64) ↦₆₄ v3) ⊢ cells (sp - 272#64) 4 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using
    cells_4_merge (sp - 272#64) v0 v1 v2 v3

theorem cells_sub240_4_merge (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 240#64) ↦₆₄ v0) ∗ ((sp - 232#64) ↦₆₄ v1) ∗ ((sp - 224#64) ↦₆₄ v2) ∗
      ((sp - 216#64) ↦₆₄ v3) ⊢ cells (sp - 240#64) 4 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using
    cells_4_merge (sp - 240#64) v0 v1 v2 v3

theorem cells_sub208_14_merge (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : BitVec 64) :
    ((sp - 208#64) ↦₆₄ v0) ∗ ((sp - 200#64) ↦₆₄ v1) ∗ ((sp - 192#64) ↦₆₄ v2) ∗
      ((sp - 184#64) ↦₆₄ v3) ∗ ((sp - 176#64) ↦₆₄ v4) ∗ ((sp - 168#64) ↦₆₄ v5) ∗
      ((sp - 160#64) ↦₆₄ v6) ∗ ((sp - 152#64) ↦₆₄ v7) ∗ ((sp - 144#64) ↦₆₄ v8) ∗
      ((sp - 136#64) ↦₆₄ v9) ∗ ((sp - 128#64) ↦₆₄ v10) ∗ ((sp - 120#64) ↦₆₄ v11) ∗
      ((sp - 112#64) ↦₆₄ v12) ∗ ((sp - 104#64) ↦₆₄ v13) ⊢ cells (sp - 208#64) 14 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using
    cells_14_merge (sp - 208#64) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13

theorem cells_sub96_12_merge (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
      ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
      ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗
      ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11) ⊢
      cells (sp - 96#64) 12 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using
    cells_12_merge (sp - 96#64) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓] (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys")

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem fnOff_generateKeysName :
    libsignalSessionCode.fnOff generateKeysName = num% (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") :=
  (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys")

theorem memRegion_gen_merge (genA : BitVec 64) (d0 d1 : BitVec 32) (v0 v1 v2 : BitVec 64) :
    (genA ↦₃₂ d0) ∗ memRegion (genA + 4#64) 4 ∗
      ((genA + 8#64) ↦₆₄ v0) ∗ ((genA + 16#64) ↦₆₄ v1) ∗ ((genA + 24#64) ↦₆₄ v2) ∗
      ((genA + 32#64) ↦₃₂ d1) ∗ memRegion (genA + 36#64) 4 ⊢
      memRegion genA 40 := by
  rw [memRegion_gen_generateKeys genA]
  have hc3 : ((genA + 8#64) ↦₆₄ v0) ∗ ((genA + 16#64) ↦₆₄ v1) ∗ ((genA + 24#64) ↦₆₄ v2) ⊢
      cells (genA + 8#64) 3 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using cells_3_merge (genA + 8#64) v0 v1 v2
  rw [← sepConj_assoc ((genA + 16#64) ↦₆₄ v1), ← sepConj_assoc ((genA + 8#64) ↦₆₄ v0)]
  exact sepConj_mono (Entails.sepExists_right d0 (Entails.refl _))
    (sepConj_mono_right (sepConj_mono hc3
      (sepConj_mono_left (Entails.sepExists_right d1 (Entails.refl _)))))

theorem memRegion_24_merge (a v0 v1 v2 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ⊢ memRegion a 24 := by
  rw [(memRegion_cells a 3 (by decide) : memRegion a 24 = cells a 3)]
  exact cells_3_merge a v0 v1 v2

end GenerateKeysFacts

open GenerateKeysFacts

/-! ## Main verification theorems -/

set_option maxHeartbeats 6000000 in
/-- `<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys` (`0x1ee50`)
satisfies `(generateKeysSpec C.F A).inImage img` on `libsignalSessionCode.rebase img.base H`. -/
theorem generateKeys_ok_of_contracts {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hext : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr extractName)
      ((extractSpec C.F).inImage img))
    (hexp : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr expandMultiInfoName)
      (expandMultiInfoSpec C.F))
    (hdealloc_raw : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr generateKeysName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys"))
      (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr generateKeysName)
      ((generateKeysSpec C.F A).inImage img) := by
  have hb := base_aligned_of_loads himg
  refine subroutine_ok_inImage_rodata' (rodata_0x44ebd himg) ?_
  wp_init x s0
  have hfn : libsignalSessionCode.fnOff generateKeysName = num% (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") :=
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys")
  have hext_none := extractNoneAllocStack_ok_at_rebase hext hfn (k := 18446744073709534952) (by decide)
  have hext_empty := extractEmptyAllocStack_ok_at_rebase hext hfn (k := 18446744073709534952) (by decide)
  have hext_some := extractSomeAllocStack_ok_at_rebase hext hfn (k := 18446744073709534952) (by decide)
  have hexp' := expandCellsAllocStack_ok_at_rebase hexp hfn (k := 18446744073709533732) (by decide)
    10 (by decide)
  simp only [expandCellsAllocStackSpec, cells, sepConj_emp,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  have hdealloc := deallocAllocStack_of_rustDealloc_rebase hdealloc_raw
  have hadrp : (((libsignalSessionCode.rebase img.base H).fnAddr generateKeysName + 108#64 &&&
      0xfffffffffffff000#64) + bv% (ls_str% "WhisperMessageKeys" - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new" + 1768))) = img.base + bv% (ls_str% "WhisperMessageKeys") := by
    rw [Program.fnAddr_rebase, hfn]
    exact generateKeys_adrp1 hb
  have hadrp' : (((libsignalSessionCode.rebase img.base H).fnAddr generateKeysName + 108#64 &&&
      0xfffffffffffff000#64) + bv% (page% (ls_str% "WhisperMessageKeys") - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new" + 1768)) + bv% ((ls_str% "WhisperMessageKeys") % 4096)) = img.base + bv% (ls_str% "WhisperMessageKeys") := by
    rw [Program.fnAddr_rebase, hfn]
    exact generateKeys_adrp2 hb
  code_fetches libsignalSessionCode libsignalSessionBin img.base H hfn (num% (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys")) 444
  have hpc_eq : s0.pc = (libsignalSessionCode.rebase img.base H).fnAddr generateKeysName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  clear hpc himg hext hexp hdealloc_raw hfn hb
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr generateKeysName = entry
  examples_hide_fetches
  obtain ⟨genA, ⟨seed, counter⟩, pqrKeyA, pqrKey, out⟩ := x
  dsimp only [generateKeysSpec] at *
  have hF0 : FrozenInv img s0 := ‹_›
  have hseed_len : seed.length = 32 := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = genA› ‹s0.readReg64 (.gpr 1#5) = pqrKeyA›
    ‹s0.readReg64 (.gpr 8#5) = out›
  rw (occs := .pos [1]) [fnFrame_split_generateKeys_pre s0.sp]
  rw [memRegion_out_generateKeys (s0.readReg64 (.gpr 8#5))]
  wp_simp_pre_fast [mkgAt, vecU8, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  cells_pre_unfold_fast
  wp_extract_exists
  rename_i seed_cap seed_ptr
  apply SepWP.replace_pre
    (hPQ := vecU8At_split_32 A (s0.readReg64 (.gpr 0#5) + 8#64) seed_cap seed_ptr seed hseed_len)
    (by sep_focus)
  wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_extract_exists
  rename_i hseed
  obtain ⟨hseed_le, hseed_small, hseed_ptr, hseed_cap_ne⟩ := hseed
  have hseed_cap_beq : (seed_cap == 0#64) = false := beq_eq_false_iff_ne.mpr hseed_cap_ne
  rcases pqrKey with _ | sv
  · obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F none seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed none
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, sepConj_assoc]
    wp_extract_exists
    rename_i isNiche
    cases isNiche
    · wp_simp_pre_fast [Bool.false_eq_true, ↓reduceIte, vecU8, sepConj_assoc]
      wp_extract_exists
      rename_i pqr_cap pqr_ptr
      apply SepWP.replace_pre
        (hPQ := vecU8At_split_nil A (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr)
        (by sep_focus)
      wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_extract_exists
      rename_i hpqr
      obtain ⟨hpqr_small, hpqr_ptr⟩ := hpqr
      have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
      have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hpqr_add1_ne
      apply SepWP.of_sepWP_frozen hF0
      wp_steps
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      wp_call hext_empty (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
        (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      wp_simp_pre_fast [hadrp, hadrp']
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        img.base + bv% (ls_str% "WhisperMessageKeys"), whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit',
        BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap
          hseed_len hseed_le hseed_small)
        (by sep_focus)
      wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
      wp_extract_exists
      by_cases hpqr_cap0 : pqr_cap = 0#64
      · subst hpqr_cap0
        wp_simp_pre_fast [↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
        wp_steps
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
          (by sep_focus)
        rw [fnFrame_split_generateKeys_post s0.sp,
          messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
        wp_done
      · have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap0
        wp_simp_pre_fast [hpqr_cap0, ↓reduceIte, sepConj_assoc]
        wp_steps
        wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64)
        wp_extract_exists
        wp_steps
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
          (by sep_focus)
        rw [fnFrame_split_generateKeys_post s0.sp,
          messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
        wp_done
    · wp_simp_pre_fast [↓reduceIte, noneCap,
        (memRegion_cells (s0.readReg64 (.gpr 1#5) + 8#64) 2 (by decide) :
          memRegion (s0.readReg64 (.gpr 1#5) + 8#64) 16 = cells (s0.readReg64 (.gpr 1#5) + 8#64) 2),
        sepConj_assoc]
      cells_pre_unfold_fast
      wp_extract_exists
      apply SepWP.of_sepWP_frozen hF0
      wp_steps
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      wp_call hext_none (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
        (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      wp_simp_pre_fast [hadrp, hadrp']
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        img.base + bv% (ls_str% "WhisperMessageKeys"), whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit',
        BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap
          hseed_len hseed_le hseed_small)
        (by sep_focus)
      wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
      wp_extract_exists
      wp_steps
      apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre
        (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus)
      apply SepWP.replace_pre
        (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
        (by sep_focus)
      rw [fnFrame_split_generateKeys_post s0.sp,
        messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
      wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
      wp_done
  · obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F (some sv) seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed (some sv)
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, vecU8, sepConj_assoc]
    wp_extract_exists
    rename_i pqr_cap pqr_ptr
    have hsv_len : sv.toList.length = 32 := List.Vector.toList_length sv
    apply SepWP.replace_pre
      (hPQ := vecU8At_split_32 A (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr sv.toList hsv_len)
      (by sep_focus)
    wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_extract_exists
    rename_i hpqr
    obtain ⟨hpqr_le, hpqr_small, hpqr_ptr, hpqr_cap_ne⟩ := hpqr
    have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
    have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hpqr_add1_ne
    have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap_ne
    apply SepWP.of_sepWP_frozen hF0
    wp_steps
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF1
    wp_call hext_some (s0.sp - 272#64, pqr_ptr, sv, seed_ptr, seed, s0.sp - 496#64)
    wp_extract_exists
    rw [hprk (s0.sp - 272#64)]
    apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
      (by sep_focus)
    wp_extract_exists
    rename_i hgood
    wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_steps
    apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
    wp_simp_pre_fast [hadrp, hadrp']
    wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F (some sv) seed, s0.sp - 272#64,
      img.base + bv% (ls_str% "WhisperMessageKeys"), whisperMessageKeys, s0.sp - 496#64, s0.sp - 496#64)
    wp_extract_exists
    wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_steps
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap hseed_len hseed_le hseed_small)
      (by sep_focus)
    wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
    wp_extract_exists
    wp_steps
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 pqr_ptr sv.toList pqr_cap hsv_len hpqr_le hpqr_small)
      (by sep_focus)
    wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64)
    wp_extract_exists
    wp_steps
    apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _) (by sep_focus)
    rw [fnFrame_split_generateKeys_post s0.sp,
      messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
    wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
    wp_done

theorem generateKeys_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hext : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr extractName)
      ((extractSpec C.F).inImage img))
    (hexp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr expandMultiInfoName)
      (expandMultiInfoSpec C.F))
    (hC : AllocContracts img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr generateKeysName)
      ((generateKeysSpec C.F A).inImage img) :=
  generateKeys_ok_of_contracts himg hext hexp
    (hC.dealloc_ok_at generateKeysName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys"))
      (by rw [(ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys"), (ls_stub% "__rustc::__rust_dealloc")]))

theorem generateKeys_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hext : ExtractOk img C ctl abs)
    (hexp : ExpandMultiInfoOk img.base C ctl abs)
    (hA : AllocHooks A abs) :
    GenerateKeysOk img C A ctl abs :=
  generateKeys_ok_ext himg hext hexp
    (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA)

/-! ## `AllocContractsX` variants -/

theorem fnFrame_split_generateKeysX_pre (sp : BitVec 64) :
    stackAt sp generateKeysStackX =
      stackAt (sp - 496#64) extHookStack ∗
        cells (sp - 496#64) 10 ∗ cells (sp - 416#64) 4 ∗
        cells (sp - 384#64) 14 ∗ memRegion (sp - 272#64) 176 ∗
        cells (sp - 96#64) 12 := by
  change memRegion (sp - BitVec.ofNat 64 16880) 16880 =
    memRegion (sp - 496#64 - BitVec.ofNat 64 16384) 16384 ∗
      cells (sp - 496#64) 10 ∗ cells (sp - 416#64) 4 ∗
      cells (sp - 384#64) 14 ∗ memRegion (sp - 272#64) 176 ∗
      cells (sp - 96#64) 12
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16880) (n := 16384) (k := 496)
      (b' := sp - 496#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 496#64) (n := 80) (k := 416) (b' := sp - 416#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 416#64) (n := 32) (k := 384) (b' := sp - 384#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 384#64) (n := 112) (k := 272) (b' := sp - 272#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 176) (k := 96) (b' := sp - 96#64) rfl
      (by bv_omega) (by decide),
    (memRegion_cells (sp - 496#64) 10 (by decide) :
      memRegion (sp - 496#64) 80 = cells (sp - 496#64) 10),
    (memRegion_cells (sp - 416#64) 4 (by decide) :
      memRegion (sp - 416#64) 32 = cells (sp - 416#64) 4),
    (memRegion_cells (sp - 384#64) 14 (by decide) :
      memRegion (sp - 384#64) 112 = cells (sp - 384#64) 14),
    (memRegion_cells (sp - 96#64) 12 (by decide) :
      memRegion (sp - 96#64) 96 = cells (sp - 96#64) 12)]
  have hsub : sp - 496#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16880 := by bv_kernel
  rw [hsub]

theorem fnFrame_split_generateKeysX_post (sp : BitVec 64) :
    stackAt sp generateKeysStackX =
      stackAt (sp - 496#64) extHookStack ∗
        cells (sp - 496#64) 10 ∗ cells (sp - 416#64) 8 ∗
        memRegion (sp - 352#64) 80 ∗ cells (sp - 272#64) 4 ∗
        cells (sp - 240#64) 4 ∗ cells (sp - 208#64) 14 ∗
        cells (sp - 96#64) 12 := by
  change memRegion (sp - BitVec.ofNat 64 16880) 16880 =
    memRegion (sp - 496#64 - BitVec.ofNat 64 16384) 16384 ∗
      cells (sp - 496#64) 10 ∗ cells (sp - 416#64) 8 ∗
      memRegion (sp - 352#64) 80 ∗ cells (sp - 272#64) 4 ∗
      cells (sp - 240#64) 4 ∗ cells (sp - 208#64) 14 ∗
      cells (sp - 96#64) 12
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16880) (n := 16384) (k := 496)
      (b' := sp - 496#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 496#64) (n := 80) (k := 416) (b' := sp - 416#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 416#64) (n := 64) (k := 352) (b' := sp - 352#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 352#64) (n := 80) (k := 272) (b' := sp - 272#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 32) (k := 240) (b' := sp - 240#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 240#64) (n := 32) (k := 208) (b' := sp - 208#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 208#64) (n := 112) (k := 96) (b' := sp - 96#64) rfl
      (by bv_omega) (by decide),
    (memRegion_cells (sp - 496#64) 10 (by decide) :
      memRegion (sp - 496#64) 80 = cells (sp - 496#64) 10),
    (memRegion_cells (sp - 416#64) 8 (by decide) :
      memRegion (sp - 416#64) 64 = cells (sp - 416#64) 8),
    (memRegion_cells (sp - 272#64) 4 (by decide) :
      memRegion (sp - 272#64) 32 = cells (sp - 272#64) 4),
    (memRegion_cells (sp - 240#64) 4 (by decide) :
      memRegion (sp - 240#64) 32 = cells (sp - 240#64) 4),
    (memRegion_cells (sp - 208#64) 14 (by decide) :
      memRegion (sp - 208#64) 112 = cells (sp - 208#64) 14),
    (memRegion_cells (sp - 96#64) 12 (by decide) :
      memRegion (sp - 96#64) 96 = cells (sp - 96#64) 12)]
  have hsub : sp - 496#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16880 := by bv_kernel
  rw [hsub]

set_option maxHeartbeats 6000000 in
/-- `<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys` (`0x1ee50`)
satisfies `(generateKeysSpecX C.F A).inImage img` on `libsignalSessionCode.rebase img.base H`. -/
theorem generateKeys_ok_of_contracts_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hext : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr extractName)
      ((extractSpec C.F).inImage img))
    (hexp : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr expandMultiInfoName)
      (expandMultiInfoSpec C.F))
    (hdealloc_raw : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr generateKeysName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr generateKeysName)
      ((generateKeysSpecX C.F A).inImage img) := by
  have hb := base_aligned_of_loads himg
  refine subroutine_ok_inImage_rodata' (rodata_0x44ebd himg) ?_
  wp_init x s0
  have hfn : libsignalSessionCode.fnOff generateKeysName = num% (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") :=
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys")
  have hext_none := extractNoneExtStack_ok_at_rebase hext hfn (k := 18446744073709534952) (by decide)
  have hext_empty := extractEmptyExtStack_ok_at_rebase hext hfn (k := 18446744073709534952) (by decide)
  have hext_some := extractSomeExtStack_ok_at_rebase hext hfn (k := 18446744073709534952) (by decide)
  have hexp' := expandCellsExtStack_ok_at_rebase hexp hfn (k := 18446744073709533732) (by decide)
    10 (by decide)
  simp only [expandCellsExtStackSpec, cells, sepConj_emp,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  have hdealloc := deallocExtStack_of_rustDeallocExtern_rebase hdealloc_raw
  have hadrp : (((libsignalSessionCode.rebase img.base H).fnAddr generateKeysName + 108#64 &&&
      0xfffffffffffff000#64) + bv% (ls_str% "WhisperMessageKeys" - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new" + 1768))) = img.base + bv% (ls_str% "WhisperMessageKeys") := by
    rw [Program.fnAddr_rebase, hfn]
    exact generateKeys_adrp1 hb
  have hadrp' : (((libsignalSessionCode.rebase img.base H).fnAddr generateKeysName + 108#64 &&&
      0xfffffffffffff000#64) + bv% (page% (ls_str% "WhisperMessageKeys") - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new" + 1768)) + bv% ((ls_str% "WhisperMessageKeys") % 4096)) = img.base + bv% (ls_str% "WhisperMessageKeys") := by
    rw [Program.fnAddr_rebase, hfn]
    exact generateKeys_adrp2 hb
  code_fetches libsignalSessionCode libsignalSessionBin img.base H hfn (num% (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys")) 444
  have hpc_eq : s0.pc = (libsignalSessionCode.rebase img.base H).fnAddr generateKeysName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  clear hpc himg hext hexp hdealloc_raw hfn hb
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr generateKeysName = entry
  examples_hide_fetches
  obtain ⟨genA, ⟨seed, counter⟩, pqrKeyA, pqrKey, out⟩ := x
  dsimp only [generateKeysSpecX] at *
  have hF0 : FrozenInv img s0 := ‹_›
  have hseed_len : seed.length = 32 := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = genA› ‹s0.readReg64 (.gpr 1#5) = pqrKeyA›
    ‹s0.readReg64 (.gpr 8#5) = out›
  rw (occs := .pos [1]) [fnFrame_split_generateKeysX_pre s0.sp]
  rw [memRegion_out_generateKeys (s0.readReg64 (.gpr 8#5))]
  wp_simp_pre_fast [mkgAt, vecU8, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  cells_pre_unfold_fast
  wp_extract_exists
  rename_i seed_cap seed_ptr
  apply SepWP.replace_pre
    (hPQ := vecU8At_split_32 A (s0.readReg64 (.gpr 0#5) + 8#64) seed_cap seed_ptr seed hseed_len)
    (by sep_focus)
  wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_extract_exists
  rename_i hseed
  obtain ⟨hseed_le, hseed_small, hseed_ptr, hseed_cap_ne⟩ := hseed
  have hseed_pos : 0 < seed_cap.toNat := by omega
  have hseed_cap_beq : (seed_cap == 0#64) = false := beq_eq_false_iff_ne.mpr hseed_cap_ne
  rcases pqrKey with _ | sv
  · obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F none seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed none
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, sepConj_assoc]
    wp_extract_exists
    rename_i isNiche
    cases isNiche
    · wp_simp_pre_fast [Bool.false_eq_true, ↓reduceIte, vecU8, sepConj_assoc]
      wp_extract_exists
      rename_i pqr_cap pqr_ptr
      apply SepWP.replace_pre
        (hPQ := vecU8At_split_nil A (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr)
        (by sep_focus)
      wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_extract_exists
      rename_i hpqr
      obtain ⟨hpqr_small, hpqr_ptr⟩ := hpqr
      have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
      have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hpqr_add1_ne
      apply SepWP.of_sepWP_frozen hF0
      wp_steps
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      apply SepWP.of_sepWP_frozen hF1
      wp_call hext_empty (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
        (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      wp_simp_pre_fast [hadrp, hadrp']
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        img.base + bv% (ls_str% "WhisperMessageKeys"), whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit',
        BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap
          hseed_len hseed_le hseed_small)
        (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF2
      by_cases hpqr_cap0 : pqr_cap = 0#64
      · subst hpqr_cap0
        wp_simp_pre_fast [↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
        wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
        wp_extract_exists
        wp_steps
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
          (by sep_focus)
        rw [fnFrame_split_generateKeysX_post s0.sp,
          messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
        wp_done
      · have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap0
        have hpqr_pos : 0 < pqr_cap.toNat :=
          Nat.pos_of_ne_zero fun h0 => hpqr_cap0 (BitVec.eq_of_toNat_eq (by simpa using h0))
        wp_simp_pre_fast [hpqr_cap0, ↓reduceIte, sepConj_assoc]
        apply SepWP.of_sepWP_frozen hF2
        wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
        wp_extract_exists
        wp_steps
        apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
        intro hF3
        wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64)
        wp_extract_exists
        wp_steps
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
          (by sep_focus)
        rw [fnFrame_split_generateKeysX_post s0.sp,
          messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
        wp_done
    · wp_simp_pre_fast [↓reduceIte, noneCap,
        (memRegion_cells (s0.readReg64 (.gpr 1#5) + 8#64) 2 (by decide) :
          memRegion (s0.readReg64 (.gpr 1#5) + 8#64) 16 = cells (s0.readReg64 (.gpr 1#5) + 8#64) 2),
        sepConj_assoc]
      cells_pre_unfold_fast
      wp_extract_exists
      apply SepWP.of_sepWP_frozen hF0
      wp_steps
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      apply SepWP.of_sepWP_frozen hF1
      wp_call hext_none (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
        (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      wp_simp_pre_fast [hadrp, hadrp']
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        img.base + bv% (ls_str% "WhisperMessageKeys"), whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit',
        BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap
          hseed_len hseed_le hseed_small)
        (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF2
      wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
      wp_extract_exists
      wp_steps
      apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre
        (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus)
      apply SepWP.replace_pre
        (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
        (by sep_focus)
      rw [fnFrame_split_generateKeysX_post s0.sp,
        messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
      wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
      wp_done
  · obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F (some sv) seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed (some sv)
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, vecU8, sepConj_assoc]
    wp_extract_exists
    rename_i pqr_cap pqr_ptr
    have hsv_len : sv.toList.length = 32 := List.Vector.toList_length sv
    apply SepWP.replace_pre
      (hPQ := vecU8At_split_32 A (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr sv.toList hsv_len)
      (by sep_focus)
    wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_extract_exists
    rename_i hpqr
    obtain ⟨hpqr_le, hpqr_small, hpqr_ptr, hpqr_cap_ne⟩ := hpqr
    have hpqr_pos : 0 < pqr_cap.toNat := by omega
    have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
    have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hpqr_add1_ne
    have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap_ne
    apply SepWP.of_sepWP_frozen hF0
    wp_steps
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF1
    apply SepWP.of_sepWP_frozen hF1
    wp_call hext_some (s0.sp - 272#64, pqr_ptr, sv, seed_ptr, seed, s0.sp - 496#64)
    wp_extract_exists
    rw [hprk (s0.sp - 272#64)]
    apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
      (by sep_focus)
    wp_extract_exists
    rename_i hgood
    wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_steps
    apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
    wp_simp_pre_fast [hadrp, hadrp']
    wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F (some sv) seed, s0.sp - 272#64,
      img.base + bv% (ls_str% "WhisperMessageKeys"), whisperMessageKeys, s0.sp - 496#64, s0.sp - 496#64)
    wp_extract_exists
    wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_steps
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap hseed_len hseed_le hseed_small)
      (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF2
    apply SepWP.of_sepWP_frozen hF2
    wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
    wp_extract_exists
    wp_steps
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 pqr_ptr sv.toList pqr_cap hsv_len hpqr_le hpqr_small)
      (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF3
    wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64)
    wp_extract_exists
    wp_steps
    apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _) (by sep_focus)
    rw [fnFrame_split_generateKeysX_post s0.sp,
      messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
    wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
    wp_done

theorem generateKeys_ok_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hext : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr extractName)
      ((extractSpec C.F).inImage img))
    (hexp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr expandMultiInfoName)
      (expandMultiInfoSpec C.F))
    (hC : AllocContractsX img A ext) :
    GenerateKeysOkX img C A ext :=
  generateKeys_ok_of_contracts_x himg hext hexp
    (hC.dealloc_ok_at generateKeysName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys"))
      (by rw [(ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys"), (ls_stub% "__rustc::__rust_dealloc")]))

/-! ## Relocatable `[LibsignalPlacement]` contracts -/

set_option maxHeartbeats 6000000 in
/-- Relocatable `<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys` (Block `69`)
satisfies `withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)`. -/
theorem generateKeys_placed_ok_of_contracts [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractSpec C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfoSpec C.F)))
    (hdealloc_raw : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsρ lsRustDeallocSym)
      (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)) := by
  refine subroutine_ok_withLsCodeRoLoaded_rodata''
    (roSym := "libsignal_protocol:.rodata..Lanon.168")
    (roBytes := whisperMessageKeys) (by decide) ?_
  wp_init x s0
  have hext_none := extractNonePlacedAllocStack_ok hext
  have hext_empty := extractEmptyPlacedAllocStack_ok hext
  have hext_some := extractSomePlacedAllocStack_ok hext
  have hexp' := expandCellsPlacedAllocStack_ok hexp 10 (by decide)
  simp only [expandCellsPlacedAllocStackSpec, cells, sepConj_emp,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  have hdealloc := deallocAllocStack_of_rustDealloc_placed hdealloc_raw
  clear hext hexp hdealloc_raw
  obtain ⟨genA, ⟨seed, counter⟩, pqrKeyA, pqrKey, out⟩ := x
  dsimp only [generateKeysSpec] at *
  have hF0 : LsFrozenInv lsmpl s0 := ‹_›
  have hseed_len : seed.length = 32 := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = genA› ‹s0.readReg64 (.gpr 1#5) = pqrKeyA›
    ‹s0.readReg64 (.gpr 8#5) = out›
  rw (occs := .pos [1]) [fnFrame_split_generateKeys_pre s0.sp]
  rw [memRegion_out_generateKeys (s0.readReg64 (.gpr 8#5))]
  wp_simp_pre_fast [mkgAt, vecU8, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  cells_pre_unfold_fast
  wp_extract_exists
  rename_i seed_cap seed_ptr
  apply SepWP.replace_pre
    (hPQ := vecU8At_split_32 A (s0.readReg64 (.gpr 0#5) + 8#64) seed_cap seed_ptr seed hseed_len)
    (by sep_focus)
  wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_extract_exists
  rename_i hseed
  obtain ⟨hseed_le, hseed_small, hseed_ptr, hseed_cap_ne⟩ := hseed
  have hseed_cap_beq : (seed_cap == 0#64) = false := beq_eq_false_iff_ne.mpr hseed_cap_ne
  rcases pqrKey with _ | sv
  · obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F none seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed none
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, sepConj_assoc]
    wp_extract_exists
    rename_i isNiche
    cases isNiche
    · wp_simp_pre_fast [Bool.false_eq_true, ↓reduceIte, vecU8, sepConj_assoc]
      wp_extract_exists
      rename_i pqr_cap pqr_ptr
      apply SepWP.replace_pre
        (hPQ := vecU8At_split_nil A (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr)
        (by sep_focus)
      wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_extract_exists
      rename_i hpqr
      obtain ⟨hpqr_small, hpqr_ptr⟩ := hpqr
      have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
      have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hpqr_add1_ne
      apply SepWP.of_sepWP_lscro hF0
      wp_steps
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      apply SepWP.of_sepWP_lscro hF1
      wp_call hext_empty (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
        (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF2
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        lsmpl.ρ "libsignal_protocol:.rodata..Lanon.168", whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit',
        BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap
          hseed_len hseed_le hseed_small)
        (by sep_focus)
      wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
      wp_extract_exists
      by_cases hpqr_cap0 : pqr_cap = 0#64
      · subst hpqr_cap0
        wp_simp_pre_fast [↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
        wp_steps
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
          (by sep_focus)
        rw [fnFrame_split_generateKeys_post s0.sp,
          messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
        wp_done
      · have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap0
        wp_simp_pre_fast [hpqr_cap0, ↓reduceIte, sepConj_assoc]
        wp_steps
        wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64)
        wp_extract_exists
        wp_steps
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
          (by sep_focus)
        rw [fnFrame_split_generateKeys_post s0.sp,
          messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
        wp_done
    · wp_simp_pre_fast [↓reduceIte, noneCap,
        (memRegion_cells (s0.readReg64 (.gpr 1#5) + 8#64) 2 (by decide) :
          memRegion (s0.readReg64 (.gpr 1#5) + 8#64) 16 = cells (s0.readReg64 (.gpr 1#5) + 8#64) 2),
        sepConj_assoc]
      cells_pre_unfold_fast
      wp_extract_exists
      apply SepWP.of_sepWP_lscro hF0
      wp_steps
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      apply SepWP.of_sepWP_lscro hF1
      wp_call hext_none (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
        (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF2
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        lsmpl.ρ "libsignal_protocol:.rodata..Lanon.168", whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit',
        BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap
          hseed_len hseed_le hseed_small)
        (by sep_focus)
      wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
      wp_extract_exists
      wp_steps
      apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre
        (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus)
      apply SepWP.replace_pre
        (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
        (by sep_focus)
      rw [fnFrame_split_generateKeys_post s0.sp,
        messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
      wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
      wp_done
  · obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F (some sv) seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed (some sv)
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, vecU8, sepConj_assoc]
    wp_extract_exists
    rename_i pqr_cap pqr_ptr
    have hsv_len : sv.toList.length = 32 := List.Vector.toList_length sv
    apply SepWP.replace_pre
      (hPQ := vecU8At_split_32 A (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr sv.toList hsv_len)
      (by sep_focus)
    wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_extract_exists
    rename_i hpqr
    obtain ⟨hpqr_le, hpqr_small, hpqr_ptr, hpqr_cap_ne⟩ := hpqr
    have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
    have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hpqr_add1_ne
    have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap_ne
    apply SepWP.of_sepWP_lscro hF0
    wp_steps
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF1
    apply SepWP.of_sepWP_lscro hF1
    wp_call hext_some (s0.sp - 272#64, pqr_ptr, sv, seed_ptr, seed, s0.sp - 496#64)
    wp_extract_exists
    rw [hprk (s0.sp - 272#64)]
    apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
      (by sep_focus)
    wp_extract_exists
    rename_i hgood
    wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_steps
    apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF2
    wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F (some sv) seed, s0.sp - 272#64,
      lsmpl.ρ "libsignal_protocol:.rodata..Lanon.168", whisperMessageKeys,
      s0.sp - 496#64, s0.sp - 496#64)
    wp_extract_exists
    wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_steps
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap hseed_len hseed_le hseed_small)
      (by sep_focus)
    wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
    wp_extract_exists
    wp_steps
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 pqr_ptr sv.toList pqr_cap hsv_len hpqr_le hpqr_small)
      (by sep_focus)
    wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64)
    wp_extract_exists
    wp_steps
    apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _) (by sep_focus)
    rw [fnFrame_split_generateKeys_post s0.sp,
      messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
    wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
    wp_done

/-- Relocatable `<MessageKeyGenerator>::generate_keys` (Block `69`) from callee contracts and
`HookSat` hypotheses. -/
theorem generateKeys_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractSpec C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoSpec C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)) :=
  generateKeys_placed_ok_of_contracts
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hext)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hexp)
    (keys_ls_hook_ok_of_mem h_dealloc)

set_option maxHeartbeats 6000000 in
/-- Relocatable `<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys` (Block `69`)
satisfies `withLsCodeRoLoaded lsmpl (generateKeysSpecX C.F A)` under `rustDeallocExternSpecWithStack`. -/
theorem generateKeys_placed_ok_of_contracts_x [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractSpec C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfoSpec C.F)))
    (hdealloc_raw : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsρ lsRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack))) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl (generateKeysSpecX C.F A)) := by
  refine subroutine_ok_withLsCodeRoLoaded_rodata''
    (roSym := "libsignal_protocol:.rodata..Lanon.168")
    (roBytes := whisperMessageKeys) (by decide) ?_
  wp_init x s0
  have hext_none := extractNonePlacedExtStack_ok hext
  have hext_empty := extractEmptyPlacedExtStack_ok hext
  have hext_some := extractSomePlacedExtStack_ok hext
  have hexp' := expandCellsPlacedExtStack_ok hexp 10 (by decide)
  simp only [expandCellsPlacedExtStackSpec, cells, sepConj_emp,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  have hdealloc := deallocPlacedExtStack_of_rustDeallocExtern hdealloc_raw
  clear hext hexp hdealloc_raw
  obtain ⟨genA, ⟨seed, counter⟩, pqrKeyA, pqrKey, out⟩ := x
  dsimp only [generateKeysSpecX] at *
  have hF0 : LsFrozenInv lsmpl s0 := ‹_›
  have hseed_len : seed.length = 32 := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = genA› ‹s0.readReg64 (.gpr 1#5) = pqrKeyA›
    ‹s0.readReg64 (.gpr 8#5) = out›
  rw (occs := .pos [1]) [fnFrame_split_generateKeysX_pre s0.sp]
  rw [memRegion_out_generateKeys (s0.readReg64 (.gpr 8#5))]
  wp_simp_pre_fast [mkgAt, vecU8, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  cells_pre_unfold_fast
  wp_extract_exists
  rename_i seed_cap seed_ptr
  apply SepWP.replace_pre
    (hPQ := vecU8At_split_32 A (s0.readReg64 (.gpr 0#5) + 8#64) seed_cap seed_ptr seed hseed_len)
    (by sep_focus)
  wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_extract_exists
  rename_i hseed
  obtain ⟨hseed_le, hseed_small, hseed_ptr, hseed_cap_ne⟩ := hseed
  have hseed_pos : 0 < seed_cap.toNat := by omega
  have hseed_cap_beq : (seed_cap == 0#64) = false := beq_eq_false_iff_ne.mpr hseed_cap_ne
  rcases pqrKey with _ | sv
  · obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F none seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed none
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, sepConj_assoc]
    wp_extract_exists
    rename_i isNiche
    cases isNiche
    · wp_simp_pre_fast [Bool.false_eq_true, ↓reduceIte, vecU8, sepConj_assoc]
      wp_extract_exists
      rename_i pqr_cap pqr_ptr
      apply SepWP.replace_pre
        (hPQ := vecU8At_split_nil A (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr)
        (by sep_focus)
      wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_extract_exists
      rename_i hpqr
      obtain ⟨hpqr_small, hpqr_ptr⟩ := hpqr
      have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
      have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hpqr_add1_ne
      apply SepWP.of_sepWP_lscro hF0
      wp_steps
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      apply SepWP.of_sepWP_lscro hF1
      wp_call hext_empty (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
        (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF2
      apply SepWP.of_sepWP_lscro hF2
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        lsmpl.ρ "libsignal_protocol:.rodata..Lanon.168", whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit',
        BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap
          hseed_len hseed_le hseed_small)
        (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF3
      by_cases hpqr_cap0 : pqr_cap = 0#64
      · subst hpqr_cap0
        wp_simp_pre_fast [↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
        wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
        wp_extract_exists
        wp_steps
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
          (by sep_focus)
        rw [fnFrame_split_generateKeysX_post s0.sp,
          messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
        wp_done
      · have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap0
        have hpqr_pos : 0 < pqr_cap.toNat :=
          Nat.pos_of_ne_zero fun h0 => hpqr_cap0 (BitVec.eq_of_toNat_eq (by simpa using h0))
        wp_simp_pre_fast [hpqr_cap0, ↓reduceIte, sepConj_assoc]
        apply SepWP.of_sepWP_lscro hF3
        wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
        wp_extract_exists
        wp_steps
        apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
        intro hF4
        wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64)
        wp_extract_exists
        wp_steps
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
          (by sep_focus)
        rw [fnFrame_split_generateKeysX_post s0.sp,
          messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
        wp_done
    · wp_simp_pre_fast [↓reduceIte, noneCap,
        (memRegion_cells (s0.readReg64 (.gpr 1#5) + 8#64) 2 (by decide) :
          memRegion (s0.readReg64 (.gpr 1#5) + 8#64) 16 = cells (s0.readReg64 (.gpr 1#5) + 8#64) 2),
        sepConj_assoc]
      cells_pre_unfold_fast
      wp_extract_exists
      apply SepWP.of_sepWP_lscro hF0
      wp_steps
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      apply SepWP.of_sepWP_lscro hF1
      wp_call hext_none (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
        (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF2
      apply SepWP.of_sepWP_lscro hF2
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        lsmpl.ρ "libsignal_protocol:.rodata..Lanon.168", whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit',
        BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap
          hseed_len hseed_le hseed_small)
        (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF3
      wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
      wp_extract_exists
      wp_steps
      apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre
        (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus)
      apply SepWP.replace_pre
        (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
        (by sep_focus)
      rw [fnFrame_split_generateKeysX_post s0.sp,
        messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
      wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
      wp_done
  · obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F (some sv) seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed (some sv)
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, vecU8, sepConj_assoc]
    wp_extract_exists
    rename_i pqr_cap pqr_ptr
    have hsv_len : sv.toList.length = 32 := List.Vector.toList_length sv
    apply SepWP.replace_pre
      (hPQ := vecU8At_split_32 A (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr sv.toList hsv_len)
      (by sep_focus)
    wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_extract_exists
    rename_i hpqr
    obtain ⟨hpqr_le, hpqr_small, hpqr_ptr, hpqr_cap_ne⟩ := hpqr
    have hpqr_pos : 0 < pqr_cap.toNat := by omega
    have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
    have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hpqr_add1_ne
    have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap_ne
    apply SepWP.of_sepWP_lscro hF0
    wp_steps
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF1
    apply SepWP.of_sepWP_lscro hF1
    wp_call hext_some (s0.sp - 272#64, pqr_ptr, sv, seed_ptr, seed, s0.sp - 496#64)
    wp_extract_exists
    rw [hprk (s0.sp - 272#64)]
    apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
      (by sep_focus)
    wp_extract_exists
    rename_i hgood
    wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_steps
    apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF2
    apply SepWP.of_sepWP_lscro hF2
    wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F (some sv) seed, s0.sp - 272#64,
      lsmpl.ρ "libsignal_protocol:.rodata..Lanon.168", whisperMessageKeys,
      s0.sp - 496#64, s0.sp - 496#64)
    wp_extract_exists
    wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_steps
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap hseed_len hseed_le hseed_small)
      (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF3
    apply SepWP.of_sepWP_lscro hF3
    wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
    wp_extract_exists
    wp_steps
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 pqr_ptr sv.toList pqr_cap hsv_len hpqr_le hpqr_small)
      (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF4
    wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64)
    wp_extract_exists
    wp_steps
    apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _) (by sep_focus)
    rw [fnFrame_split_generateKeysX_post s0.sp,
      messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
    wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
    wp_done

theorem subroutine_ok_generateKeysSpecX_of_generateKeysSpec {prog : Program}
    {entry : BitVec 64} {pl : Obj.MultiPlacement} {F : ShaCompress} {A : RustAlloc}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded pl (generateKeysSpec F A))) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl (generateKeysSpecX F A)) := by
  refine subroutine_ok_map h ?_
  intro x R s0 hpre
  have hstk : stackAt s0.sp generateKeysStackX =
      stackAt s0.sp generateKeysStack ∗ memRegion (s0.sp - 16880#64) 12288 := by
    change memRegion (s0.sp - BitVec.ofNat 64 16880) 16880 =
      memRegion (s0.sp - BitVec.ofNat 64 4592) 4592 ∗ memRegion (s0.sp - 16880#64) 12288
    rw [sepConj_comm]
    exact ProofLib.memRegion_split' (b := s0.sp - 16880#64) (n := 12288) (k := 4592)
      (b' := s0.sp - 4592#64) rfl (by bv_omega) (by decide)
  refine ⟨x, memRegion (s0.sp - 16880#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded, generateKeysSpecX, generateKeysSpec] at hpre ⊢
    rw [hstk] at hpre
    ac_nf at hpre ⊢
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, generateKeysSpecX, generateKeysSpec] at hpost ⊢
    rw [hstk]
    ac_nf at hpost ⊢

theorem generateKeys_placed_ok_x [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractSpec C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoSpec C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl (generateKeysSpecX C.F A)) :=
  subroutine_ok_generateKeysSpecX_of_generateKeysSpec
    (generateKeys_placed_ok hext hexp h_dealloc)

end CryptoVerification.LibsignalTripleRatchet.Keys
