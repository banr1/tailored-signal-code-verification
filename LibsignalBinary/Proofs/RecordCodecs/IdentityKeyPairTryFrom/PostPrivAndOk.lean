/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp

/-!
# `IdentityKeyPair::try_from` Private-Key Validation, Clamping, and `Ok` Packing

32-byte cell decompositions, inline scalar clamping (`bfxil`), private-key length check
(`BadKeyLength(Djb, len)`), and `Ok` output packing (`+396 .. +568` → `+812`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section PostPrivStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_ikp (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_ikp (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPState_ikp (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_advancePC_ikp (s : State) : s.advancePC.sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_gpr_ikp (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg32_gpr_ikp (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg_gpr_ikp (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_ikp (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_ikp (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPState_ikp (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_ikp (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_ikp (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPState_ikp (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_ikp (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_ikp (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPState_ikp (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓]
theorem bfm32_clamp_ikp1 : ∀ b : BitVec 8,
    (Arm64.evalBitfield .W32 .BFM 64#64 (b.zeroExtend 64) 0 5).setWidth 8 =
      (b &&& 0x7f#8) ||| 0x40#8 := by decide

@[local arm64_norm ↓]
theorem bfm32_clamp_ikp2 : ∀ b : BitVec 8,
    (Arm64.evalBitfield .W32 .BFM 64#64 ((b.zeroExtend 32).zeroExtend 64) 0 5).setWidth 8 =
      (b &&& 0x7f#8) ||| 0x40#8 := by decide

end PostPrivStateSimp

/-! ## 32-byte cell decompositions for `PublicKey` (7 cells) and `PrivateKey` / `clampScalar` (9 cells) -/

def pkCells (w0 : BitVec 64) (b8 : BitVec 8) (w9 : BitVec 32) (h13 : BitVec 16)
    (w15 w23 : BitVec 64) (b31 : BitVec 8) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ b8) ∗ ((a + 9#64) ↦₃₂ w9) ∗ ((a + 13#64) ↦₁₆ h13) ∗
  ((a + 15#64) ↦₆₄ w15) ∗ ((a + 23#64) ↦₆₄ w23) ∗ ((a + 31#64) ↦₈ b31)

def skCells (b0 : BitVec 8) (w1 : BitVec 32) (h5 h7 : BitVec 16) (w9 : BitVec 32)
    (h13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) (a : BitVec 64) : SepProp :=
  (a ↦₈ b0) ∗ ((a + 1#64) ↦₃₂ w1) ∗ ((a + 5#64) ↦₁₆ h5) ∗ ((a + 7#64) ↦₁₆ h7) ∗
  ((a + 9#64) ↦₃₂ w9) ∗ ((a + 13#64) ↦₁₆ h13) ∗ ((a + 15#64) ↦₆₄ w15) ∗
  ((a + 23#64) ↦₆₄ w23) ∗ ((a + 31#64) ↦₈ b31)

theorem pointsToBytes8_exists (l : List (BitVec 8)) (h : l.length = 8) :
    ∃ w : BitVec 64, ∀ a : BitVec 64, (a ↦ₛ l) = (a ↦₆₄ w) := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try simp at h
  exact ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0, fun a => pointsToBytes8_eq_pointsTo64 a ..⟩

theorem pointsToBytes4_exists (l : List (BitVec 8)) (h : l.length = 4) :
    ∃ w : BitVec 32, ∀ a : BitVec 64, (a ↦ₛ l) = (a ↦₃₂ w) := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try simp at h
  exact ⟨b3 ++ b2 ++ b1 ++ b0, fun a => pointsToBytes4_eq_pointsTo32 a ..⟩

theorem pointsToBytes2_exists (l : List (BitVec 8)) (h : l.length = 2) :
    ∃ w : BitVec 16, ∀ a : BitVec 64, (a ↦ₛ l) = (a ↦₁₆ w) := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | _⟩⟩ <;> try simp at h
  exact ⟨b1 ++ b0, fun a => pointsToBytes2_eq_pointsTo16 a ..⟩

theorem pointsToBytes1_exists (l : List (BitVec 8)) (h : l.length = 1) :
    ∃ b : BitVec 8, ∀ a : BitVec 64, (a ↦ₛ l) = (a ↦₈ b) := by
  rcases l with _ | ⟨b0, _ | _⟩ <;> try simp at h
  exact ⟨b0, fun a => by rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]⟩

theorem pointsToBytes32_exists_pkCells (bs : List (BitVec 8)) (h : bs.length = 32) :
    ∃ (w0 : BitVec 64) (b8 : BitVec 8) (w9 : BitVec 32) (h13 : BitVec 16)
      (w15 w23 : BitVec 64) (b31 : BitVec 8),
      ∀ a : BitVec 64, (a ↦ₛ bs) = pkCells w0 b8 w9 h13 w15 w23 b31 a := by
  obtain ⟨w0, hw0⟩ := pointsToBytes8_exists (bs.take 8) (by simp [h])
  obtain ⟨b8, hb8⟩ := pointsToBytes1_exists ((bs.drop 8).take 1) (by simp [h])
  obtain ⟨w9, hw9⟩ := pointsToBytes4_exists ((bs.drop 9).take 4) (by simp [h])
  obtain ⟨h13, hh13⟩ := pointsToBytes2_exists ((bs.drop 13).take 2) (by simp [h])
  obtain ⟨w15, hw15⟩ := pointsToBytes8_exists ((bs.drop 15).take 8) (by simp [h])
  obtain ⟨w23, hw23⟩ := pointsToBytes8_exists ((bs.drop 23).take 8) (by simp [h])
  obtain ⟨b31, hb31⟩ := pointsToBytes1_exists (bs.drop 31) (by simp [h])
  refine ⟨w0, b8, w9, h13, w15, w23, b31, fun a => ?_⟩
  have s1 := pointsToBytes_take_drop a bs 8 (by omega)
  have s2 := pointsToBytes_take_drop (a + 8#64) (bs.drop 8) 1 (by simp [h])
  have s3 := pointsToBytes_take_drop (a + 9#64) (bs.drop 9) 4 (by simp [h])
  have s4 := pointsToBytes_take_drop (a + 13#64) (bs.drop 13) 2 (by simp [h])
  have s5 := pointsToBytes_take_drop (a + 15#64) (bs.drop 15) 8 (by simp [h])
  have s6 := pointsToBytes_take_drop (a + 23#64) (bs.drop 23) 8 (by simp [h])
  simp only [List.drop_drop, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at s1 s2 s3 s4 s5 s6
  rw [← s1, ← s2, ← s3, ← s4, ← s5, ← s6,
    hw0, hb8, hw9, hh13, hw15, hw23, hb31]
  unfold pkCells
  ac_rfl

theorem pointsToBytes32_decomp9 {l : List (BitVec 8)} (hl : l.length = 32)
    {b0 : BitVec 8} {w1 : BitVec 32} {h5 h7 : BitVec 16} {w9 : BitVec 32}
    {h13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    (hb0 : l.take 1 = [b0])
    (hw1 : ∀ a, (a ↦ₛ (l.drop 1).take 4) = (a ↦₃₂ w1))
    (hh5 : ∀ a, (a ↦ₛ (l.drop 5).take 2) = (a ↦₁₆ h5))
    (hh7 : ∀ a, (a ↦ₛ (l.drop 7).take 2) = (a ↦₁₆ h7))
    (hw9 : ∀ a, (a ↦ₛ (l.drop 9).take 4) = (a ↦₃₂ w9))
    (hh13 : ∀ a, (a ↦ₛ (l.drop 13).take 2) = (a ↦₁₆ h13))
    (hw15 : ∀ a, (a ↦ₛ (l.drop 15).take 8) = (a ↦₆₄ w15))
    (hw23 : ∀ a, (a ↦ₛ (l.drop 23).take 8) = (a ↦₆₄ w23))
    (hb31 : l.drop 31 = [b31]) (a : BitVec 64) :
    (a ↦ₛ l) = skCells b0 w1 h5 h7 w9 h13 w15 w23 b31 a := by
  have s0 := pointsToBytes_take_drop a l 1 (by omega)
  have s1 := pointsToBytes_take_drop (a + 1#64) (l.drop 1) 4 (by simp [hl])
  have s2 := pointsToBytes_take_drop (a + 5#64) (l.drop 5) 2 (by simp [hl])
  have s3 := pointsToBytes_take_drop (a + 7#64) (l.drop 7) 2 (by simp [hl])
  have s4 := pointsToBytes_take_drop (a + 9#64) (l.drop 9) 4 (by simp [hl])
  have s5 := pointsToBytes_take_drop (a + 13#64) (l.drop 13) 2 (by simp [hl])
  have s6 := pointsToBytes_take_drop (a + 15#64) (l.drop 15) 8 (by simp [hl])
  have s7 := pointsToBytes_take_drop (a + 23#64) (l.drop 23) 8 (by simp [hl])
  simp only [List.drop_drop, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at s0 s1 s2 s3 s4 s5 s6 s7
  rw [← s0, ← s1, ← s2, ← s3, ← s4, ← s5, ← s6, ← s7,
    hb0, hw1, hh5, hh7, hw9, hh13, hw15, hw23, hb31,
    pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  unfold skCells
  ac_rfl

theorem vector32_exists_skCells (sk : List.Vector (BitVec 8) 32) :
    ∃ (b0 : BitVec 8) (w1 : BitVec 32) (h5 h7 : BitVec 16) (w9 : BitVec 32)
      (h13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8),
      (∀ a : BitVec 64, (a ↦ₛ sk.1) =
        skCells b0 w1 h5 h7 w9 h13 w15 w23 b31 a) ∧
      (∀ a : BitVec 64, (a ↦ₛ (Ratchet.clampScalar sk).1) =
        skCells (b0 &&& 0xf8#8) w1 h5 h7 w9 h13 w15 w23 ((b31 &&& 0x7f#8) ||| 0x40#8) a) := by
  rcases sk with ⟨l, hl⟩
  set cl := (Ratchet.clampScalar ⟨l, hl⟩).1
  have hcl : cl.length = 32 := (Ratchet.clampScalar ⟨l, hl⟩).2
  have hmid : ∀ i : Nat, 1 ≤ i → i < 31 → cl[i]? = l[i]? := by
    intro i hi1 hi2
    simp only [cl, Ratchet.clampScalar, List.Vector.set, List.Vector.get]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hdrop_take : ∀ k n : Nat, k + n ≤ 30 →
      (cl.drop (k + 1)).take n = (l.drop (k + 1)).take n := by
    intro k n hkn
    ext i
    by_cases hi : i < n
    · simp only [List.getElem?_take_of_lt hi, List.getElem?_drop]
      rw [hmid (k + 1 + i) (by omega) (by omega)]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  obtain ⟨w1, hw1⟩ := pointsToBytes4_exists ((l.drop 1).take 4) (by simp [hl])
  obtain ⟨h5, hh5⟩ := pointsToBytes2_exists ((l.drop 5).take 2) (by simp [hl])
  obtain ⟨h7, hh7⟩ := pointsToBytes2_exists ((l.drop 7).take 2) (by simp [hl])
  obtain ⟨w9, hw9⟩ := pointsToBytes4_exists ((l.drop 9).take 4) (by simp [hl])
  obtain ⟨h13, hh13⟩ := pointsToBytes2_exists ((l.drop 13).take 2) (by simp [hl])
  obtain ⟨w15, hw15⟩ := pointsToBytes8_exists ((l.drop 15).take 8) (by simp [hl])
  obtain ⟨w23, hw23⟩ := pointsToBytes8_exists ((l.drop 23).take 8) (by simp [hl])
  refine ⟨l[0]'(by omega), w1, h5, h7, w9, h13, w15, w23, l[31]'(by omega), ?_, ?_⟩
  · intro a
    refine pointsToBytes32_decomp9 hl ?_ hw1 hh5 hh7 hw9 hh13 hw15 hw23 ?_ a
    · rcases l with _ | ⟨x0, xs⟩; · simp at hl
      rfl
    · rw [List.drop_eq_getElem_cons (by omega),
        List.drop_eq_nil_of_le (show l.length ≤ 32 by omega)]
  · intro a
    refine pointsToBytes32_decomp9 hcl ?_
      (fun p => by rw [hdrop_take 0 4 (by decide)]; exact hw1 p)
      (fun p => by rw [hdrop_take 4 2 (by decide)]; exact hh5 p)
      (fun p => by rw [hdrop_take 6 2 (by decide)]; exact hh7 p)
      (fun p => by rw [hdrop_take 8 4 (by decide)]; exact hw9 p)
      (fun p => by rw [hdrop_take 12 2 (by decide)]; exact hh13 p)
      (fun p => by rw [hdrop_take 14 8 (by decide)]; exact hw15 p)
      (fun p => by rw [hdrop_take 22 8 (by decide)]; exact hw23 p)
      ?_ a
    · rw [List.take_one]
      rcases l with _ | ⟨x0, _ | ⟨x1, xs⟩⟩ <;> try simp at hl
      rfl
    · rw [List.drop_eq_getElem_cons (by omega),
        List.drop_eq_nil_of_le (show cl.length ≤ 32 by omega)]
      congr 1
      have hset31 : ∀ (xs : List (BitVec 8)) (hxs : xs.length = 32) (v0 v31 : BitVec 8),
          ((xs.set 0 v0).set 31 v31)[31]'(by simp [hxs]) = v31 := by
        intro xs hxs v0 v31
        rw [List.getElem_set_self]
      exact hset31 l hl _ _

/-! ## Stack scratch `[sp' .. sp' + 32)` & output `Ok` buffer splitting/folding helpers -/

def ikpScratch32 (sw8 : BitVec 64) (sb16 : BitVec 8) (sw24 : BitVec 32) (sh28 : BitVec 16)
    (sp' : BitVec 64) : SepProp :=
  memRegion sp' 8 ∗ ((sp' + 8#64) ↦₆₄ sw8) ∗ ((sp' + 16#64) ↦₈ sb16) ∗
  memRegion (sp' + 17#64) 7 ∗ ((sp' + 24#64) ↦₃₂ sw24) ∗ ((sp' + 28#64) ↦₁₆ sh28) ∗
  memRegion (sp' + 30#64) 2

theorem memRegion32_split_scratch (sp' : BitVec 64) :
    memRegion sp' 32 ⊢
      ∃∗ sh28 : BitVec 16, ∃∗ sw24 : BitVec 32, ∃∗ sb16 : BitVec 8, ∃∗ sw8 : BitVec 64,
        ikpScratch32 sw8 sb16 sw24 sh28 sp' := by
  have hm2 : ∀ a : BitVec 64, memRegion a 2 ⊢ ∃∗ v : BitVec 16, a ↦₁₆ v := by
    intro a
    rw [memRegion_eq_exists_bytes a 2 (by decide)]
    refine Entails.sepExists_elim fun bs => Entails.pure_left fun hlen => ?_
    obtain ⟨v, hv⟩ := pointsToBytes2_exists bs hlen
    rw [hv a]
    exact sepExists_intro _ v
  rw [Prost.memRegion_split sp' 8 24 (by decide),
    Prost.memRegion_split (sp' + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64) 1 15 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64 + 1#64) 7 8 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64 + 1#64 + 7#64) 4 4 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64 + 1#64 + 7#64 + 4#64) 2 2 (by decide),
    ProofLib.memRegion_eight (sp' + 8#64), memRegion_one]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (memRegion_four_entails (sp' + 24#64))
        (sepConj_mono_left (hm2 (sp' + 28#64)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, ikpScratch32]
  exact Entails.refl _

theorem ikpScratch32_entails_memRegion32 (sw8 : BitVec 64) (sb16 : BitVec 8)
    (sw24 : BitVec 32) (sh28 : BitVec 16) (sp' : BitVec 64) :
    ikpScratch32 sw8 sb16 sw24 sh28 sp' ⊢ memRegion sp' 32 := by
  unfold ikpScratch32
  have hm4 : ((sp' + 24#64) ↦₃₂ sw24) ⊢ memRegion (sp' + 24#64) 4 := by
    rw [pointsTo32_eq_pointsToBytes]
    exact pointsToBytes_entails_memRegion (sp' + 24#64) (unpack32 sw24)
  have hm2 : ((sp' + 28#64) ↦₁₆ sh28) ⊢ memRegion (sp' + 28#64) 2 := by
    rw [pointsTo16_eq_pointsToBytes]
    exact pointsToBytes_entails_memRegion (sp' + 28#64) (unpack16 sh28)
  have hm1 : ((sp' + 16#64) ↦₈ sb16) ⊢ memRegion (sp' + 16#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ sb16
  rw [Prost.memRegion_split sp' 8 24 (by decide),
    Prost.memRegion_split (sp' + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64) 1 15 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64 + 1#64) 7 8 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64 + 1#64 + 7#64) 4 4 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64 + 1#64 + 7#64 + 4#64) 2 2 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion (sp' + 8#64) sw8)
      (sepConj_mono hm1
        (sepConj_mono_right (sepConj_mono hm4 (sepConj_mono_left hm2)))))

theorem memRegion72_split_ok (r : BitVec 64) :
    memRegion r 72 ⊢
      ∃∗ sb0 : BitVec 8, ∃∗ sw1 : BitVec 32, ∃∗ sh5 : BitVec 16, ∃∗ sh7 : BitVec 16,
      ∃∗ sw9 : BitVec 32, ∃∗ sh13 : BitVec 16, ∃∗ sw15 : BitVec 64, ∃∗ sw23 : BitVec 64,
      ∃∗ sb31 : BitVec 8,
      ∃∗ dw0 : BitVec 64, ∃∗ db8 : BitVec 8, ∃∗ dw9 : BitVec 32, ∃∗ dh13 : BitVec 16,
      ∃∗ dw15 : BitVec 64, ∃∗ dw23 : BitVec 64, ∃∗ db31 : BitVec 8,
      ∃∗ b_tag : BitVec 8,
        (r ↦₈ b_tag) ∗
        pkCells dw0 db8 dw9 dh13 dw15 dw23 db31 (r + 1#64) ∗
        skCells sb0 sw1 sh5 sh7 sw9 sh13 sw15 sw23 sb31 (r + 0x21#64) ∗
        memRegion (r + 0x41#64) 7 := by
  have hm32_pk : memRegion (r + 1#64) 32 ⊢
      ∃∗ dw0 : BitVec 64, ∃∗ db8 : BitVec 8, ∃∗ dw9 : BitVec 32, ∃∗ dh13 : BitVec 16,
      ∃∗ dw15 : BitVec 64, ∃∗ dw23 : BitVec 64, ∃∗ db31 : BitVec 8,
        pkCells dw0 db8 dw9 dh13 dw15 dw23 db31 (r + 1#64) := by
    rw [memRegion_eq_exists_bytes (r + 1#64) 32 (by decide)]
    refine Entails.sepExists_elim fun bs => Entails.pure_left fun hlen => ?_
    obtain ⟨dw0', db8', dw9', dh13', dw15', dw23', db31', heq⟩ := pointsToBytes32_exists_pkCells bs hlen
    rw [heq (r + 1#64)]
    refine Entails.trans ?_ (sepExists_intro _ dw0')
    refine Entails.trans ?_ (sepExists_intro _ db8')
    refine Entails.trans ?_ (sepExists_intro _ dw9')
    refine Entails.trans ?_ (sepExists_intro _ dh13')
    refine Entails.trans ?_ (sepExists_intro _ dw15')
    refine Entails.trans ?_ (sepExists_intro _ dw23')
    exact sepExists_intro (fun db31 => pkCells dw0' db8' dw9' dh13' dw15' dw23' db31 (r + 1#64)) db31'
  have hm32_sk : memRegion (r + 0x21#64) 32 ⊢
      ∃∗ sb0 : BitVec 8, ∃∗ sw1 : BitVec 32, ∃∗ sh5 : BitVec 16, ∃∗ sh7 : BitVec 16,
      ∃∗ sw9 : BitVec 32, ∃∗ sh13 : BitVec 16, ∃∗ sw15 : BitVec 64, ∃∗ sw23 : BitVec 64,
      ∃∗ sb31 : BitVec 8,
        skCells sb0 sw1 sh5 sh7 sw9 sh13 sw15 sw23 sb31 (r + 0x21#64) := by
    rw [memRegion_eq_exists_bytes (r + 0x21#64) 32 (by decide)]
    refine Entails.sepExists_elim fun bs => Entails.pure_left fun hlen => ?_
    obtain ⟨sb0', sw1', sh5', sh7', sw9', sh13', sw15', sw23', sb31', hsrc, _⟩ :=
      vector32_exists_skCells ⟨bs, hlen⟩
    rw [hsrc (r + 0x21#64)]
    refine Entails.trans ?_ (sepExists_intro _ sb0')
    refine Entails.trans ?_ (sepExists_intro _ sw1')
    refine Entails.trans ?_ (sepExists_intro _ sh5')
    refine Entails.trans ?_ (sepExists_intro _ sh7')
    refine Entails.trans ?_ (sepExists_intro _ sw9')
    refine Entails.trans ?_ (sepExists_intro _ sh13')
    refine Entails.trans ?_ (sepExists_intro _ sw15')
    refine Entails.trans ?_ (sepExists_intro _ sw23')
    exact sepExists_intro
      (fun sb31 => skCells sb0' sw1' sh5' sh7' sw9' sh13' sw15' sw23' sb31 (r + 0x21#64)) sb31'
  rw [Prost.memRegion_split r 1 71 (by decide),
    Prost.memRegion_split (r + 1#64) 32 39 (by decide),
    Prost.memRegion_split (r + 1#64 + 32#64) 32 7 (by decide),
    memRegion_one]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono hm32_pk (sepConj_mono_left hm32_sk))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

/-! ## Error tail `+760 .. +772 -> +812` and post-PK `Ok(pk)` path `+396 .. +568 -> +812` -/

theorem err_store_760_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    {x : DecodeGhost} {s0 s : State}
    {sp' pkCap pkPtr skCap skPtr w24 w25 : BitVec 64}
    {pkBs skBs : List (BitVec 8)}
    (hst : IkpBaseState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 760#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx24 : s.readReg64 .x24 = w24) (hx25 : s.readReg64 .x25 = w25)
    (hx22 : s.readReg64 .x22 = pkCap) (hx20 : s.readReg64 .x20 = pkPtr)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr)
    (herr : (x.ret ↦₈ 1#8) ∗ memRegion (x.ret + 1#64) 7 ∗
      ((x.ret + 8#64) ↦₆₄ w24) ∗ ((x.ret + 16#64) ↦₆₄ w25) ∗
      memRegion (x.ret + 24#64) 48 ⊢
      identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes)) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (memRegion x.ret 72 ∗ vecU8Buf A pkCap pkPtr pkBs ∗ vecU8Buf A skCap skPtr skBs ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseState img s0 sp' sf ∧
        (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (memRegion72_split_err x.ret)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun w2 => Wire.SepWPp.exists_pre fun w1 =>
    Wire.SepWPp.exists_pre fun b0 => ?_
  let H := Rust.withPanics ext
  have hcleanup := @cleanup_pk_sk_772_wp img C A encFn decFn ext hC s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    760 12
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hst.sp
  refine Wire.SepWPp.of_sepWP_frozen hst.frozen hst.symtab (mid := entry + bv% (772)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre
    (P' := (vecU8Buf A pkCap pkPtr pkBs ∗ vecU8Buf A skCap skPtr skBs ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
      identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes))
    (by
      try rw [hx19]
      try rw [hx24]
      try rw [hx25]
      simp only [arm64_norm]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right herr))))
      apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.frame_tryFrom
    (hcleanup
      (hst.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq])
        (by simp [*, hst.trace, arm64_norm]) (by simp [*, hst.x26, arm64_norm])
        (by simp [*, hst.x27, arm64_norm]) (by simp [*, hst.x28, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm]))
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  apply entails_of_eq; ac_rfl

private theorem clamp_b0_post (b : BitVec 8) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 b &&& 1065151889656#64) = b &&& 248#8 := by
  revert b; decide

private theorem clamp_b31_post (b : BitVec 8) :
    BitVec.zeroExtend 8 (64#64 ||| BitVec.zeroExtend 64 b >>> 0 &&& 63#64) =
      (b &&& 127#8) ||| 64#8 := by
  revert b; decide

theorem post_pk_ok_396_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    {x : DecodeGhost} {s0 s : State}
    {sp' pkCap pkPtr skCap skPtr : BitVec 64}
    {m : IdentityKeyPairStructure} {pk : PublicKey}
    (hdec : IdentityKeyPairStructure.decode x.bytes = some m)
    (hpk : PublicKey.deserialize m.publicKey = .ok pk)
    (hsk_lt : m.privateKey.length < 2 ^ 64)
    (hst : IkpBaseState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 396#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx29 : s.readReg64 .x29 = sp' + 144#64)
    (hx24 : s.readReg64 .x24 = speWord 9)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 m.privateKey.length)
    (hx22 : s.readReg64 .x22 = pkCap) (hx20 : s.readReg64 .x20 = pkPtr)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr)
    {w0 : BitVec 64} {b8 : BitVec 8} {w9 : BitVec 32} {h13 : BitVec 16}
    {w15 w23 : BitVec 64} {b31 : BitVec 8}
    (hpk_cells : ∀ a : BitVec 64, (a ↦ₛ pk.bytes.toList) = pkCells w0 b8 w9 h13 w15 w23 b31 a)
    (hx8 : s.readReg64 .x8 = b8.zeroExtend 64) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (memRegion sp' 32 ∗
        ((sp' + 96#64) ↦₈ 0#8) ∗ pkCells w0 b8 w9 h13 w15 w23 b31 (sp' + 97#64) ∗
        memRegion (sp' + 129#64) 15 ∗
        memRegion x.ret 72 ∗
        vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseState img s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  have hfold96 : ((sp' + 96#64) ↦₈ 0#8) ∗ pkCells w0 b8 w9 h13 w15 w23 b31 (sp' + 97#64) ∗
      memRegion (sp' + 129#64) 15 ⊢ memRegion (sp' + 96#64) 48 := by
    rw [← hpk_cells (sp' + 97#64)]
    have hm1 : ((sp' + 96#64) ↦₈ 0#8) ⊢ memRegion (sp' + 96#64) 1 := by
      rw [memRegion_one]; exact sepExists_intro _ 0#8
    have hm32 : ((sp' + 97#64) ↦ₛ pk.bytes.toList) ⊢ memRegion (sp' + 97#64) 32 := by
      simpa [pk.bytes.2] using pointsToBytes_entails_memRegion (sp' + 97#64) pk.bytes.toList
    rw [show (48 : Nat) = 1 + (32 + 15) by decide,
      Prost.memRegion_split (sp' + 96#64) 1 47 (by decide),
      Prost.memRegion_split (sp' + 96#64 + 1#64) 32 15 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono hm1 (sepConj_mono_left hm32)
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (memRegion32_split_scratch sp')) ?_
  simp only [sepExists_sepConj_left, ikpScratch32, pkCells, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun sh28 => Wire.SepWPp.exists_pre fun sw24 =>
    Wire.SepWPp.exists_pre fun sb16 => Wire.SepWPp.exists_pre fun sw8 => ?_
  let H := Rust.withPanics ext
  by_cases hlen32 : m.privateKey.length = 32
  · have htry_ok : IdentityKeyPair.tryFrom x.bytes =
        .ok ⟨⟨pk⟩, ⟨Ratchet.clampScalar ⟨m.privateKey, hlen32⟩⟩⟩ := by
      unfold IdentityKeyPair.tryFrom decodeIdentityKey deserializePrivateKey
      simp [hdec, hpk, hlen32, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map]
    obtain ⟨b0_s, w1_s, h5_s, h7_s, w9_s, h13_s, w15_s, w23_s, b31_s, hsk_src, hsk_dst⟩ :=
      vector32_exists_skCells ⟨m.privateKey, hlen32⟩
    have hpre_unpack :
        memRegion sp' 8 ∗ ((sp' + 8#64) ↦₆₄ sw8) ∗ ((sp' + 16#64) ↦₈ sb16) ∗
        memRegion (sp' + 17#64) 7 ∗ ((sp' + 24#64) ↦₃₂ sw24) ∗ ((sp' + 28#64) ↦₁₆ sh28) ∗
        memRegion (sp' + 30#64) 2 ∗ ((sp' + 96#64) ↦₈ 0#8) ∗
        ((sp' + 97#64) ↦₆₄ w0) ∗ ((sp' + 97#64 + 8#64) ↦₈ b8) ∗
        ((sp' + 97#64 + 9#64) ↦₃₂ w9) ∗ ((sp' + 97#64 + 13#64) ↦₁₆ h13) ∗
        ((sp' + 97#64 + 15#64) ↦₆₄ w15) ∗ ((sp' + 97#64 + 23#64) ↦₆₄ w23) ∗
        ((sp' + 97#64 + 31#64) ↦₈ b31) ∗ memRegion (sp' + 129#64) 15 ∗
        memRegion x.ret 72 ∗ vecU8Buf A pkCap pkPtr m.publicKey ∗
        vecU8Buf A skCap skPtr m.privateKey ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) ⊢
        ∃∗ sb0 : BitVec 8, ∃∗ sw1 : BitVec 32, ∃∗ sh5 : BitVec 16, ∃∗ sh7 : BitVec 16,
        ∃∗ sw9 : BitVec 32, ∃∗ sh13 : BitVec 16, ∃∗ sw15 : BitVec 64, ∃∗ sw23 : BitVec 64,
        ∃∗ sb31 : BitVec 8,
        ∃∗ dw0 : BitVec 64, ∃∗ db8 : BitVec 8, ∃∗ dw9 : BitVec 32, ∃∗ dh13 : BitVec 16,
        ∃∗ dw15 : BitVec 64, ∃∗ dw23 : BitVec 64, ∃∗ db31 : BitVec 8,
        ∃∗ b_tag : BitVec 8,
          memRegion sp' 8 ∗ ((sp' + 8#64) ↦₆₄ sw8) ∗ ((sp' + 16#64) ↦₈ sb16) ∗
          memRegion (sp' + 17#64) 7 ∗ ((sp' + 24#64) ↦₃₂ sw24) ∗ ((sp' + 28#64) ↦₁₆ sh28) ∗
          memRegion (sp' + 30#64) 2 ∗ ((sp' + 96#64) ↦₈ 0#8) ∗
          ((sp' + 97#64) ↦₆₄ w0) ∗ ((sp' + 97#64 + 8#64) ↦₈ b8) ∗
          ((sp' + 97#64 + 9#64) ↦₃₂ w9) ∗ ((sp' + 97#64 + 13#64) ↦₁₆ h13) ∗
          ((sp' + 97#64 + 15#64) ↦₆₄ w15) ∗ ((sp' + 97#64 + 23#64) ↦₆₄ w23) ∗
          ((sp' + 97#64 + 31#64) ↦₈ b31) ∗ memRegion (sp' + 129#64) 15 ∗
          (x.ret ↦₈ b_tag) ∗
          pkCells dw0 db8 dw9 dh13 dw15 dw23 db31 (x.ret + 1#64) ∗
          skCells sb0 sw1 sh5 sh7 sw9 sh13 sw15 sw23 sb31 (x.ret + 0x21#64) ∗
          memRegion (x.ret + 0x41#64) 7 ∗
          vecU8Buf A pkCap pkPtr m.publicKey ∗
          skCells b0_s w1_s h5_s h7_s w9_s h13_s w15_s w23_s b31_s skPtr ∗
          vecU8BufRest A skCap skPtr m.privateKey ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) := by
      have hsk_ent : vecU8Buf A skCap skPtr m.privateKey ⊢
          skCells b0_s w1_s h5_s h7_s w9_s h13_s w15_s w23_s b31_s skPtr ∗
            vecU8BufRest A skCap skPtr m.privateKey := by
        refine Entails.trans (vecU8Buf_entails_slice_rest A skCap skPtr m.privateKey) ?_
        refine Entails.pure_left fun _ => ?_
        rw [hsk_src skPtr]
        exact Entails.refl _
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono (memRegion72_split_ok x.ret)
                  (sepConj_mono_right (sepConj_mono_left hsk_ent))))))))))))))))))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      exact Entails.refl _
    refine Wire.SepWPp.mono_pre hpre_unpack ?_
    clear hpre_unpack
    refine Wire.SepWPp.exists_pre fun sb0 => Wire.SepWPp.exists_pre fun sw1 =>
      Wire.SepWPp.exists_pre fun sh5 => Wire.SepWPp.exists_pre fun sh7 =>
      Wire.SepWPp.exists_pre fun sw9 => Wire.SepWPp.exists_pre fun sh13 =>
      Wire.SepWPp.exists_pre fun sw15 => Wire.SepWPp.exists_pre fun sw23 =>
      Wire.SepWPp.exists_pre fun sb31 =>
      Wire.SepWPp.exists_pre fun dw0 => Wire.SepWPp.exists_pre fun db8 =>
      Wire.SepWPp.exists_pre fun dw9 => Wire.SepWPp.exists_pre fun dh13 =>
      Wire.SepWPp.exists_pre fun dw15 => Wire.SepWPp.exists_pre fun dw23 =>
      Wire.SepWPp.exists_pre fun db31 =>
      Wire.SepWPp.exists_pre fun b_tag => ?_
    simp only [pkCells, skCells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hcleanup792 := @cleanup_sk_792_wp img C A encFn decFn ext hC s0
    have hcall := ikp_dealloc_ok hC
    code_fetches_from CryptoVerification.libsignalSessionCode
      ikpTryFromBin img.base H
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
      (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
      396 176
    code_fetches_from CryptoVerification.libsignalSessionCode
      ikpTryFromBin img.base H
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
      (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
      776 16
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
    examples_hide_fetches
    try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
    have hsp_subst := hst.sp
    subst hsp_subst
    have _hsp_align := hst.spAligned
    have hsp_eq : s.sp = s.sp := rfl
    refine Wire.SepWPp.of_sepWP_frozen hst.frozen hst.symtab (mid := entry + bv% (564)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.mono_pre
      (P' := (vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
        A.pool ∗ stackAt s.sp (skipFieldStackX 100)) ∗
        (memRegion s.sp 32 ∗ memRegion (s.sp + 96#64) 48 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes)))
      (by
        have hok_res :
            (x.ret ↦₈ 0#8) ∗ pkCells w0 b8 w9 h13 w15 w23 b31 (x.ret + 1#64) ∗
              skCells (b0_s &&& 0xf8#8) w1_s h5_s h7_s w9_s h13_s w15_s w23_s
                ((b31_s &&& 0x7f#8) ||| 0x40#8) (x.ret + 0x21#64) ∗
              memRegion (x.ret + 0x41#64) 7 ⊢
            identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) := by
          rw [htry_ok, ← hpk_cells (x.ret + 1#64), ← hsk_dst (x.ret + 0x21#64)]
          dsimp only [identityKeyPairResultAt]
          apply entails_of_eq; ac_rfl
        have hsk_fold :
            skCells b0_s w1_s h5_s h7_s w9_s h13_s w15_s w23_s b31_s skPtr ∗
              vecU8BufRest A skCap skPtr m.privateKey ⊢
            vecU8Buf A skCap skPtr m.privateKey := by
          rw [← hsk_src skPtr]
          exact slice_rest_entails_vecU8Buf A skCap skPtr m.privateKey
        have hscr_fold := ikpScratch32_entails_memRegion32 w23 b31 w9 h13 s.sp
        dsimp only [pkCells, skCells, ikpScratch32] at hok_res hsk_fold hscr_fold hfold96
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hok_res hsk_fold hscr_fold hfold96
        refine Entails.trans ?_
          (sepConj_mono
            (sepConj_mono_right (sepConj_mono_left hsk_fold))
            (sepConj_mono hscr_fold (sepConj_mono hfold96 hok_res)))
        apply entails_of_eq
        simp only [arm64_norm]
        rw [clamp_b0_post, clamp_b31_post]
        ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (Q' := fun sf Pf => IkpBaseState img s0 s.sp sf ∧
        (Pf ⊢ A.pool ∗ stackAt s.sp (skipFieldStackX 100)))
      ?_ fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    · by_cases hcap : pkCap = 0#64
      · subst hcap
        rw [vecU8Buf_zero]
        refine Wire.SepWPp.pure_pre fun _ => ?_
        refine Wire.SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + bv% (792)) ?_
        wp_steps
        refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
        intro hF2 hsym2
        exact hcleanup792
          (hst.of_steps hF2 hsym2 (by tryFromPost_sp [hsp_eq])
            (by simp [*, hst.trace, arm64_norm])
            (by simp [*, hst.x26, arm64_norm])
            (by simp [*, hst.x27, arm64_norm])
            (by simp [*, hst.x28, arm64_norm]))
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
      · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A pkCap pkPtr m.publicKey hcap)) ?_
        simp only [sepConj_assoc]
        refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
        have hstack := stackAt_sub_split s.sp extHookStack (skipFieldStackX 100)
        have _hne1 : (pkCap == 0#64) = false := beq_false_of_ne hcap
        have _hne2 : (pkCap != 0#64) = true := bne_iff_ne.mpr hcap
        refine Wire.SepWPp.of_sepWP_frozen hF1 hsym1
          (mid := entry + bv% ((ls_off% "__rustc::__rust_dealloc") -
            (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
        wp_steps
        refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
        intro hF2 hsym2
        refine Wire.SepWPp.call_noPanic_tryFrom (pkPtr, pkCap.toNat, 1) hcall
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by tryFromPost_sp_align hst.spAligned) hF2 hsym2
          (ret_pc := entry + bv% (792))
          (by simp [*, arm64_norm])
          (T := A.pool ∗ A.live pkPtr pkCap.toNat 1 ∗ memRegion pkPtr pkCap.toNat ∗ stackAt s.sp extHookStack)
          (φ := pkPtr = pkPtr ∧ pkCap.toNat = pkCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk pkCap.toNat 1)
          (by simp [*, rustDeallocExternSpecWithStack, arm64_norm])
          ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
          (by rw [hstack]; sep_focus)
          ?_
        clear hcall
        intro s3 hpc3 hrun3 hsp3 hsp3_align hF3 hsym3 hcs3
        dsimp only [rustDeallocExternSpecWithStack]
        rw [sepConj_assoc]
        refine Wire.SepWPp.pure_pre fun htr3 => ?_
        have hst1 : IkpBaseState img s0 s.sp _ :=
          hst.of_steps hF2 hsym2 (by tryFromPost_sp [hsp_eq])
            (by simp [*, hst.trace, arm64_norm])
            (by simp [*, hst.x26, arm64_norm])
            (by simp [*, hst.x27, arm64_norm])
            (by simp [*, hst.x28, arm64_norm])
        have hst3 : IkpBaseState img s0 s.sp s3 :=
          hst1.of_calleeSaved hsp3 hsp3_align hF3 hsym3
            (htr3.trans hst1.trace) hcs3
        have hx21_3 : s3.readReg64 .x21 = skCap :=
          hcs3.2.2.1.trans (by simp [*, arm64_norm])
        have hx23_3 : s3.readReg64 .x23 = skPtr :=
          hcs3.2.2.2.2.1.trans (by simp [*, arm64_norm])
        refine Wire.SepWPp.mono_pre
          (P' := vecU8Buf A skCap skPtr m.privateKey ∗ A.pool ∗ stackAt s.sp (skipFieldStackX 100))
          (by
            apply entails_of_eq
            try simp only [arm64_norm]
            try rw [hsp_eq]
            rw [hstack]
            ac_rfl) ?_
        exact hcleanup792 hst3 hpc3 hrun3 hx21_3 hx23_3
    · refine Entails.trans (sepConj_mono_left hentf) ?_
      apply entails_of_eq; ac_rfl
  · have hbv_ne : BitVec.ofNat 64 m.privateKey.length ≠ 32#64 := by
      intro heq
      have hnat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsk_lt] at hnat
      exact hlen32 hnat
    have htry_err : IdentityKeyPair.tryFrom x.bytes = .error (.badKeyLength m.privateKey.length) := by
      unfold IdentityKeyPair.tryFrom decodeIdentityKey deserializePrivateKey
      simp [hdec, hpk, hlen32, Bind.bind, Except.bind, Except.map]
    have herr := @err_store_760_wp img C A encFn decFn ext hC x s0
    code_fetches_from CryptoVerification.libsignalSessionCode
      ikpTryFromBin img.base H
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
      (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
      396 44
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
    examples_hide_fetches
    try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
    have hsp_subst := hst.sp
    subst hsp_subst
    have _hsp_align := hst.spAligned
    have hsp_eq : s.sp = s.sp := rfl
    refine Wire.SepWPp.of_sepWP_frozen hst.frozen hst.symtab (mid := entry + bv% (760)) ?_
    wp_steps
    wp_if hne
    · refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre
        (P' := (memRegion x.ret 72 ∗ vecU8Buf A pkCap pkPtr m.publicKey ∗
          vecU8Buf A skCap skPtr m.privateKey ∗ A.pool ∗ stackAt s.sp (skipFieldStackX 100)) ∗
          (memRegion s.sp 32 ∗ memRegion (s.sp + 96#64) 48))
        (by
          have hscr_fold := ikpScratch32_entails_memRegion32 w23 b31 w9 h13 s.sp
          dsimp only [pkCells, ikpScratch32] at hscr_fold hfold96
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at hscr_fold hfold96
          refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono hscr_fold hfold96))
          apply entails_of_eq
          simp only [arm64_norm]
          ac_rfl) ?_
      refine Wire.SepWPp.frame_tryFrom
        (Q' := fun sf Pf => IkpBaseState img s0 s.sp sf ∧
          (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
            A.pool ∗ stackAt s.sp (skipFieldStackX 100)))
        (herr
          (hst.of_steps hF1 hsym1 rfl
            (by simp [*, hst.trace, arm64_norm])
            (by simp [*, hst.x26, arm64_norm])
            (by simp [*, hst.x27, arm64_norm])
            (by simp [*, hst.x28, arm64_norm]))
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (ikpResult_err_spe9 A x.ret m.privateKey.length htry_err))
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hentf) ?_
      apply entails_of_eq; ac_rfl
    · exfalso
      apply hbv_ne
      revert hne
      try simp only [hx25, arm64_norm]
      exact id

section Placed

open CryptoVerification.RecordCodecs.Placed

theorem err_store_760_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State}
    {sp' pkCap pkPtr skCap skPtr w24 w25 : BitVec 64} {pkBs skBs : List (BitVec 8)}
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (760)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx24 : s.readReg64 .x24 = w24) (hx25 : s.readReg64 .x25 = w25)
    (hx22 : s.readReg64 .x22 = pkCap) (hx20 : s.readReg64 .x20 = pkPtr)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr)
    (herr : (x.ret ↦₈ 1#8) ∗ memRegion (x.ret + 1#64) 7 ∗
      ((x.ret + 8#64) ↦₆₄ w24) ∗ ((x.ret + 16#64) ↦₆₄ w25) ∗
      memRegion (x.ret + 24#64) 48 ⊢
      identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes)) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (memRegion x.ret 72 ∗ vecU8Buf A pkCap pkPtr pkBs ∗ vecU8Buf A skCap skPtr skBs ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (memRegion72_split_err x.ret)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun w2 => Wire.SepWPp.exists_pre fun w1 =>
    Wire.SepWPp.exists_pre fun b0 => ?_
  have hcleanup := @cleanup_pk_sk_772_placed_wp _ A H d s0
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hst.sp
  refine sepWPp_of_sepWP_lscro hst.crl (mid := (blkPl_84).base + bv% (772)) ?_; wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  refine Wire.SepWPp.mono_pre
    (P' := (vecU8Buf A pkCap pkPtr pkBs ∗ vecU8Buf A skCap skPtr skBs ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
      identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes))
    (by try simp only [arm64_norm]
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right herr))))
        apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.frame_tryFrom
    (hcleanup
      (hst.of_steps hcrl1 (by tryFromPost_sp [hsp_eq])
        (by simp [*, hst.trace, arm64_norm]) (by simp [*, hst.x26, arm64_norm])
        (by simp [*, hst.x27, arm64_norm]) (by simp [*, hst.x28, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm]))
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  apply entails_of_eq; ac_rfl

theorem post_pk_ok_396_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State}
    {sp' pkCap pkPtr skCap skPtr : BitVec 64} {m : IdentityKeyPairStructure} {pk : PublicKey}
    (hdec : IdentityKeyPairStructure.decode x.bytes = some m)
    (hpk : PublicKey.deserialize m.publicKey = .ok pk) (hsk_lt : m.privateKey.length < 2 ^ 64)
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (396)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret) (hx29 : s.readReg64 .x29 = sp' + 144#64)
    (hx24 : s.readReg64 .x24 = speWord 9)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 m.privateKey.length)
    (hx22 : s.readReg64 .x22 = pkCap) (hx20 : s.readReg64 .x20 = pkPtr)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr)
    {w0 : BitVec 64} {b8 : BitVec 8} {w9 : BitVec 32} {h13 : BitVec 16}
    {w15 w23 : BitVec 64} {b31 : BitVec 8}
    (hpk_cells : ∀ a : BitVec 64, (a ↦ₛ pk.bytes.toList) = pkCells w0 b8 w9 h13 w15 w23 b31 a)
    (hx8 : s.readReg64 .x8 = b8.zeroExtend 64) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (memRegion sp' 32 ∗ ((sp' + 96#64) ↦₈ 0#8) ∗
        pkCells w0 b8 w9 h13 w15 w23 b31 (sp' + 97#64) ∗
        memRegion (sp' + 129#64) 15 ∗ memRegion x.ret 72 ∗
        vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  have hfold96 : ((sp' + 96#64) ↦₈ 0#8) ∗ pkCells w0 b8 w9 h13 w15 w23 b31 (sp' + 97#64) ∗
      memRegion (sp' + 129#64) 15 ⊢ memRegion (sp' + 96#64) 48 := by
    rw [← hpk_cells (sp' + 97#64)]
    have hm1 : ((sp' + 96#64) ↦₈ 0#8) ⊢ memRegion (sp' + 96#64) 1 := by
      rw [memRegion_one]; exact sepExists_intro _ 0#8
    have hm32 : ((sp' + 97#64) ↦ₛ pk.bytes.toList) ⊢ memRegion (sp' + 97#64) 32 := by
      simpa [pk.bytes.2] using pointsToBytes_entails_memRegion (sp' + 97#64) pk.bytes.toList
    rw [show (48 : Nat) = 1 + (32 + 15) by decide,
      Prost.memRegion_split (sp' + 96#64) 1 47 (by decide),
      Prost.memRegion_split (sp' + 96#64 + 1#64) 32 15 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono hm1 (sepConj_mono_left hm32)
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (memRegion32_split_scratch sp')) ?_
  simp only [sepExists_sepConj_left, ikpScratch32, pkCells, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun sh28 => Wire.SepWPp.exists_pre fun sw24 =>
    Wire.SepWPp.exists_pre fun sb16 => Wire.SepWPp.exists_pre fun sw8 => ?_
  by_cases hlen32 : m.privateKey.length = 32
  · have htry_ok : IdentityKeyPair.tryFrom x.bytes =
        .ok ⟨⟨pk⟩, ⟨Ratchet.clampScalar ⟨m.privateKey, hlen32⟩⟩⟩ := by
      unfold IdentityKeyPair.tryFrom decodeIdentityKey deserializePrivateKey
      simp [hdec, hpk, hlen32, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map]
    obtain ⟨b0_s, w1_s, h5_s, h7_s, w9_s, h13_s, w15_s, w23_s, b31_s, hsk_src, hsk_dst⟩ :=
      vector32_exists_skCells ⟨m.privateKey, hlen32⟩
    have hpre_unpack :
        memRegion sp' 8 ∗ ((sp' + 8#64) ↦₆₄ sw8) ∗ ((sp' + 16#64) ↦₈ sb16) ∗
        memRegion (sp' + 17#64) 7 ∗ ((sp' + 24#64) ↦₃₂ sw24) ∗ ((sp' + 28#64) ↦₁₆ sh28) ∗
        memRegion (sp' + 30#64) 2 ∗ ((sp' + 96#64) ↦₈ 0#8) ∗
        ((sp' + 97#64) ↦₆₄ w0) ∗ ((sp' + 97#64 + 8#64) ↦₈ b8) ∗
        ((sp' + 97#64 + 9#64) ↦₃₂ w9) ∗ ((sp' + 97#64 + 13#64) ↦₁₆ h13) ∗
        ((sp' + 97#64 + 15#64) ↦₆₄ w15) ∗ ((sp' + 97#64 + 23#64) ↦₆₄ w23) ∗
        ((sp' + 97#64 + 31#64) ↦₈ b31) ∗ memRegion (sp' + 129#64) 15 ∗
        memRegion x.ret 72 ∗ vecU8Buf A pkCap pkPtr m.publicKey ∗
        vecU8Buf A skCap skPtr m.privateKey ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) ⊢
        ∃∗ sb0 : BitVec 8, ∃∗ sw1 : BitVec 32, ∃∗ sh5 : BitVec 16, ∃∗ sh7 : BitVec 16,
        ∃∗ sw9 : BitVec 32, ∃∗ sh13 : BitVec 16, ∃∗ sw15 : BitVec 64, ∃∗ sw23 : BitVec 64,
        ∃∗ sb31 : BitVec 8,
        ∃∗ dw0 : BitVec 64, ∃∗ db8 : BitVec 8, ∃∗ dw9 : BitVec 32, ∃∗ dh13 : BitVec 16,
        ∃∗ dw15 : BitVec 64, ∃∗ dw23 : BitVec 64, ∃∗ db31 : BitVec 8,
        ∃∗ b_tag : BitVec 8,
          memRegion sp' 8 ∗ ((sp' + 8#64) ↦₆₄ sw8) ∗ ((sp' + 16#64) ↦₈ sb16) ∗
          memRegion (sp' + 17#64) 7 ∗ ((sp' + 24#64) ↦₃₂ sw24) ∗ ((sp' + 28#64) ↦₁₆ sh28) ∗
          memRegion (sp' + 30#64) 2 ∗ ((sp' + 96#64) ↦₈ 0#8) ∗
          ((sp' + 97#64) ↦₆₄ w0) ∗ ((sp' + 97#64 + 8#64) ↦₈ b8) ∗
          ((sp' + 97#64 + 9#64) ↦₃₂ w9) ∗ ((sp' + 97#64 + 13#64) ↦₁₆ h13) ∗
          ((sp' + 97#64 + 15#64) ↦₆₄ w15) ∗ ((sp' + 97#64 + 23#64) ↦₆₄ w23) ∗
          ((sp' + 97#64 + 31#64) ↦₈ b31) ∗ memRegion (sp' + 129#64) 15 ∗
          (x.ret ↦₈ b_tag) ∗ pkCells dw0 db8 dw9 dh13 dw15 dw23 db31 (x.ret + 1#64) ∗
          skCells sb0 sw1 sh5 sh7 sw9 sh13 sw15 sw23 sb31 (x.ret + 0x21#64) ∗
          memRegion (x.ret + 0x41#64) 7 ∗ vecU8Buf A pkCap pkPtr m.publicKey ∗
          skCells b0_s w1_s h5_s h7_s w9_s h13_s w15_s w23_s b31_s skPtr ∗
          vecU8BufRest A skCap skPtr m.privateKey ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) := by
      have hsk_ent : vecU8Buf A skCap skPtr m.privateKey ⊢
          skCells b0_s w1_s h5_s h7_s w9_s h13_s w15_s w23_s b31_s skPtr ∗
            vecU8BufRest A skCap skPtr m.privateKey := by
        refine Entails.trans (vecU8Buf_entails_slice_rest A skCap skPtr m.privateKey) ?_
        refine Entails.pure_left fun _ => ?_; rw [hsk_src skPtr]; exact Entails.refl _
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono (memRegion72_split_ok x.ret)
                  (sepConj_mono_right (sepConj_mono_left hsk_ent))))))))))))))))))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      exact Entails.refl _
    refine Wire.SepWPp.mono_pre hpre_unpack ?_; clear hpre_unpack
    refine Wire.SepWPp.exists_pre fun sb0 => Wire.SepWPp.exists_pre fun sw1 =>
      Wire.SepWPp.exists_pre fun sh5 => Wire.SepWPp.exists_pre fun sh7 =>
      Wire.SepWPp.exists_pre fun sw9 => Wire.SepWPp.exists_pre fun sh13 =>
      Wire.SepWPp.exists_pre fun sw15 => Wire.SepWPp.exists_pre fun sw23 =>
      Wire.SepWPp.exists_pre fun sb31 =>
      Wire.SepWPp.exists_pre fun dw0 => Wire.SepWPp.exists_pre fun db8 =>
      Wire.SepWPp.exists_pre fun dw9 => Wire.SepWPp.exists_pre fun dh13 =>
      Wire.SepWPp.exists_pre fun dw15 => Wire.SepWPp.exists_pre fun dw23 =>
      Wire.SepWPp.exists_pre fun db31 => Wire.SepWPp.exists_pre fun b_tag => ?_
    simp only [pkCells, skCells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hcleanup792 := @cleanup_sk_792_placed_wp _ A H d s0
    have hcall := ikp_dealloc_placed_ok d
    try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
    have hsp_subst := hst.sp; subst hsp_subst
    have _hsp_align := hst.spAligned
    have hsp_eq : s.sp = s.sp := rfl
    refine sepWPp_of_sepWP_lscro hst.crl (mid := (blkPl_84).base + bv% (564)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    refine Wire.SepWPp.mono_pre
      (P' := (vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
        A.pool ∗ stackAt s.sp (skipFieldStackX 100)) ∗
        (memRegion s.sp 32 ∗ memRegion (s.sp + 96#64) 48 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes)))
      (by
        have hok_res :
            (x.ret ↦₈ 0#8) ∗ pkCells w0 b8 w9 h13 w15 w23 b31 (x.ret + 1#64) ∗
              skCells (b0_s &&& 0xf8#8) w1_s h5_s h7_s w9_s h13_s w15_s w23_s
                ((b31_s &&& 0x7f#8) ||| 0x40#8) (x.ret + 0x21#64) ∗
              memRegion (x.ret + 0x41#64) 7 ⊢
            identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) := by
          rw [htry_ok, ← hpk_cells (x.ret + 1#64), ← hsk_dst (x.ret + 0x21#64)]
          dsimp only [identityKeyPairResultAt]; apply entails_of_eq; ac_rfl
        have hsk_fold :
            skCells b0_s w1_s h5_s h7_s w9_s h13_s w15_s w23_s b31_s skPtr ∗
              vecU8BufRest A skCap skPtr m.privateKey ⊢
            vecU8Buf A skCap skPtr m.privateKey := by
          rw [← hsk_src skPtr]; exact slice_rest_entails_vecU8Buf A skCap skPtr m.privateKey
        have hscr_fold := ikpScratch32_entails_memRegion32 w23 b31 w9 h13 s.sp
        dsimp only [pkCells, skCells, ikpScratch32] at hok_res hsk_fold hscr_fold hfold96
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hok_res hsk_fold hscr_fold hfold96
        refine Entails.trans ?_
          (sepConj_mono (sepConj_mono_right (sepConj_mono_left hsk_fold))
            (sepConj_mono hscr_fold (sepConj_mono hfold96 hok_res)))
        apply entails_of_eq; simp only [arm64_norm]; rw [clamp_b0_post, clamp_b31_post]; ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (Q' := fun sf Pf => IkpBaseStatePlaced s0 s.sp sf ∧
        (Pf ⊢ A.pool ∗ stackAt s.sp (skipFieldStackX 100)))
      ?_ fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    · by_cases hcap : pkCap = 0#64
      · subst hcap; rw [vecU8Buf_zero]; refine Wire.SepWPp.pure_pre fun _ => ?_
        refine sepWPp_of_sepWP_lscro hcrl1 (mid := (blkPl_84).base + bv% (792)) ?_; wp_steps
        refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl2
        exact hcleanup792
          (hst.of_steps hcrl2 (by tryFromPost_sp [hsp_eq])
            (by simp [*, hst.trace, arm64_norm]) (by simp [*, hst.x26, arm64_norm])
            (by simp [*, hst.x27, arm64_norm]) (by simp [*, hst.x28, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A pkCap pkPtr m.publicKey hcap)) ?_
        simp only [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
        have hstack := stackAt_sub_split s.sp extHookStack (skipFieldStackX 100)
        have _hne1 : (pkCap == 0#64) = false := beq_false_of_ne hcap
        have _hne2 : (pkCap != 0#64) = true := bne_iff_ne.mpr hcap
        refine sepWPp_of_sepWP_lscro hcrl1 (mid := lsρ lsRustDeallocSym) ?_; wp_steps
        refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl2
        refine sepWPp_call_noPanic_lscro (pkPtr, pkCap.toNat, 1) hcall
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by tryFromPost_sp_align hst.spAligned) hcrl2
          (by simp [*, arm64_norm] : _ = (blkPl_84).base + bv% (792))
          (by simp [*, hst.trace, arm64_norm])
          (T := A.pool ∗ A.live pkPtr pkCap.toNat 1 ∗ memRegion pkPtr pkCap.toNat ∗ stackAt s.sp extHookStack)
          (φ := pkPtr = pkPtr ∧ pkCap.toNat = pkCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk pkCap.toNat 1)
          (by simp [*, rustDeallocExternSpecWithStack, arm64_norm])
          ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩ (by rw [hstack]; sep_focus) ?_
        clear hcall
        intro s3 hpc3 hrun3 hsp3 hsp3_align hcrl3 hcs3
        dsimp only [rustDeallocExternSpecWithStack]; rw [sepConj_assoc]
        refine Wire.SepWPp.pure_pre fun htr3 => ?_
        have hst1 := hst.of_steps hcrl2 (by tryFromPost_sp [hsp_eq])
          (by simp [*, hst.trace, arm64_norm]) (by simp [*, hst.x26, arm64_norm])
          (by simp [*, hst.x27, arm64_norm]) (by simp [*, hst.x28, arm64_norm])
        have hst3 := hst1.of_calleeSaved hsp3 hsp3_align hcrl3 (htr3.trans hst1.trace) hcs3
        have hx21_3 : s3.readReg64 .x21 = skCap := hcs3.2.2.1.trans (by simp [*, arm64_norm])
        have hx23_3 : s3.readReg64 .x23 = skPtr := hcs3.2.2.2.2.1.trans (by simp [*, arm64_norm])
        refine Wire.SepWPp.mono_pre
          (P' := vecU8Buf A skCap skPtr m.privateKey ∗ A.pool ∗ stackAt s.sp (skipFieldStackX 100))
          (by apply entails_of_eq; simp only [arm64_norm]; rw [hstack]; ac_rfl) ?_
        exact hcleanup792 hst3 hpc3 hrun3 hx21_3 hx23_3
    · refine Entails.trans (sepConj_mono_left hentf) ?_; apply entails_of_eq; ac_rfl
  · have hbv_ne : BitVec.ofNat 64 m.privateKey.length ≠ 32#64 := by
      intro heq; have hnat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsk_lt] at hnat; exact hlen32 hnat
    have _hbv_bne : (BitVec.ofNat 64 m.privateKey.length != 32#64) = true := bne_iff_ne.mpr hbv_ne
    have _hbv_beq : (BitVec.ofNat 64 m.privateKey.length == 32#64) = false := beq_false_of_ne hbv_ne
    have htry_err : IdentityKeyPair.tryFrom x.bytes = .error (.badKeyLength m.privateKey.length) := by
      unfold IdentityKeyPair.tryFrom decodeIdentityKey deserializePrivateKey
      simp [hdec, hpk, hlen32, Bind.bind, Except.bind, Except.map]
    have herr := @err_store_760_placed_wp _ A H d x s0
    try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
    have hsp_subst := hst.sp; subst hsp_subst
    have _hsp_align := hst.spAligned
    refine sepWPp_of_sepWP_lscro hst.crl (mid := (blkPl_84).base + bv% (760)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    refine Wire.SepWPp.mono_pre
      (P' := (memRegion x.ret 72 ∗ vecU8Buf A pkCap pkPtr m.publicKey ∗
        vecU8Buf A skCap skPtr m.privateKey ∗ A.pool ∗ stackAt s.sp (skipFieldStackX 100)) ∗
        (memRegion s.sp 32 ∗ memRegion (s.sp + 96#64) 48))
      (by
        have hscr_fold := ikpScratch32_entails_memRegion32 w23 b31 w9 h13 s.sp
        dsimp only [pkCells, ikpScratch32] at hscr_fold hfold96
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hscr_fold hfold96
        refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono hscr_fold hfold96))
        apply entails_of_eq; simp only [arm64_norm]; ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (Q' := fun sf Pf => IkpBaseStatePlaced s0 s.sp sf ∧
        (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt s.sp (skipFieldStackX 100)))
      (herr
        (hst.of_steps hcrl1 rfl
          (by simp [*, hst.trace, arm64_norm]) (by simp [*, hst.x26, arm64_norm])
          (by simp [*, hst.x27, arm64_norm]) (by simp [*, hst.x28, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm])
        (ikpResult_err_spe9 A x.ret m.privateKey.length htry_err))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_; apply entails_of_eq; ac_rfl

end Placed

end CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers
