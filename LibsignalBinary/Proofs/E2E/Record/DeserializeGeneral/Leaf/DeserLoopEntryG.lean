/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.BodyDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.LoopEntry
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp

/-!
# Entry Segment Leaf (`deserLoopEntryG_ok`) for General `SessionRecord::deserialize`

Proves `deserLoopEntryG_ok` (`+0x000 → +0x254`, `k = 0`) for `SessionRecord::deserialize` (`0x16ed4`),
covering `previous_sessions` initialization, outer key `0x0a`, 1-byte and multi-byte
(`decode_varint_slice`) session length varints, and `SessionStructure::default()`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopEntryG

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? sessionImg0
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[irreducible] private def deserEntry_loopEntryG : BitVec 64 := bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")

private theorem fnAddr_deser_eq_loopEntryG (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase sessionImg0.base H).fnAddr recDeserializeName = deserEntry_loopEntryG := by
  unfold deserEntry_loopEntryG
  rw [Program.fnAddr_rebase, EntryAux.sessionImg0_base, (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize")]
  rfl

private theorem decodeVarintSlice_fnAddr_eq_loopEntryG (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)} :
    deserEntry_loopEntryG + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") =
      (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr Prost.decodeVarintSliceName := by
  unfold deserEntry_loopEntryG
  rw [tripleRatchetProgAt, Program.fnAddr_rebase, EntryAux.sessionImg0_base, (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")]
  rfl

/-! ## Pure Codec and Varint Helpers -/

private theorem encodeKey_1_ld_loopEntryG : encodeKey 1 .lengthDelimited = [0x0a#8] := rfl

private theorem encodeVarint_length_pos_loopEntryG (v : BitVec 64) :
    0 < (encodeVarint v).length :=
  List.length_pos_iff.mpr (encodeVarint_ne_nil v)

private theorem encodeVarint_of_lt_128_loopEntryG {n : Nat} (hn : n < 128) :
    encodeVarint (BitVec.ofNat 64 n) = [BitVec.ofNat 8 n] := by
  have h1 : (BitVec.ofNat 64 n).toNat < 0x80 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  unfold encodeVarint encodeVarintAux
  simp only [h1, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

private theorem encodeVarint_cons_of_ge_128_loopEntryG {n : Nat} (hge : 128 ≤ n) (hlt : n < 2 ^ 20) :
    encodeVarint (BitVec.ofNat 64 n) =
      BitVec.ofNat 8 (n % 128 + 128) :: encodeVarintAux 9 (BitVec.ofNat 64 n >>> 7) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : ¬ ((BitVec.ofNat 64 n).toNat < 0x80) := by omega
  unfold encodeVarint encodeVarintAux
  simp only [h1, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := n % 128) (by omega) 1
  simp only [Nat.reducePow, Nat.reduceMul] at hor
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and, hn,
    show (0x7F : BitVec 64).toNat = 127 from rfl,
    Nat.and_two_pow_sub_one_eq_mod n 7,
    show (0x80 : BitVec 64).toNat = 128 from rfl,
    Nat.or_comm, ← hor, BitVec.toNat_ofNat]
  omega

private theorem signExtend64_bit63_eq_false_iff_loopEntryG (b0 : BitVec 8) :
    ((b0.signExtend 64).getLsbD 63 == true) = false ↔ b0.toNat ≤ 0x7F := by
  revert b0; decide

private theorem signExtend64_bit63_eq_true_iff_loopEntryG (b0 : BitVec 8) :
    ((b0.signExtend 64).getLsbD 63 == true) = true ↔ 0x7F < b0.toNat := by
  revert b0; decide

private theorem signExtend64_eq_zeroExtend64_of_le_loopEntryG (b0 : BitVec 8) (h : b0.toNat ≤ 0x7F) :
    b0.signExtend 64 = b0.zeroExtend 64 := by
  revert b0 h; decide

private theorem signExtend64_ofNat8_lt_128_loopEntryG {n : Nat} (hn : n < 128) :
    (BitVec.ofNat 8 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hle : (BitVec.ofNat 8 n).toNat ≤ 0x7F := by rw [BitVec.toNat_ofNat]; omega
  rw [signExtend64_eq_zeroExtend64_of_le_loopEntryG _ hle]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

/-! ## `prostSSGAt` Initialization and Stack Splitting Helpers -/

private theorem sp_sub_1904_aligned_loopEntryG {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0x770#64) &&& 15#64 = 0#64 ∧ (sp0 - 0x770#64 + 1808#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h; rw [e] at h'
  have hlt := sp0.isLt
  have hsub : sp0 - 0x770#64 + 1808#64 = sp0 - 96#64 := by bv_omega
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢; omega
  · rw [hsub]; apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢; omega

private theorem empty_vecU8_intro_loopEntryG (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢ vecU8 A0 v [] := by
  dsimp only [vecU8, vecU8At, vecHeader]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [↓reduceIte, sepConj_emp, sepConj_assoc]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧
      (1#64 : BitVec 64) ≠ 0#64 := by decide
  have heq :
      (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧
          (1#64 : BitVec 64) ≠ 0#64⌝ =
      ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧
        (1#64 : BitVec 64) ≠ 0#64⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) := by ac_rfl
  rw [heq]; exact Entails.pure_right hp (Entails.refl _)

private theorem empty_vecChainG_intro_loopEntryG (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecOf A0 104 8 (fun c a => prostChainGAt A0 a c) v [] := by
  dsimp only [vecOf, vecAt, vecHeader, vecBuf]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 8#64)
  have hite : (if (0#64 : BitVec 64) = 0 then emp
    else A0.live (8#64) ((0#64 : BitVec 64).toNat * 104) 8 ∗
      arrayAt (fun c a => prostChainGAt A0 a c) 104 8#64 [] ∗
      memRegion (8#64 + BitVec.ofNat 64 (([] : List ChainG).length * 104))
        (((0#64 : BitVec 64).toNat - ([] : List ChainG).length) * 104)) = emp := rfl
  rw [hite]; simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_emp]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0 := by decide
  exact Entails.pure_right hp (Entails.refl _)

private theorem pointsTo64_zero_split32_loopEntryG (a : BitVec 64) :
    (a ↦₆₄ 0#64) = (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  simpa using pointsTo64_split32 a 0#64

private def ssRawCells_loopEntryG (L : BitVec 64) : SepProp :=
  (((L + 0x420#64) ↦₆₄ 0#64) ∗ ((L + 0x428#64) ↦₆₄ 1#64) ∗ ((L + 0x430#64) ↦₆₄ 0#64)) ∗
  (((L + 0x438#64) ↦₆₄ 0#64) ∗ ((L + 0x440#64) ↦₆₄ 1#64) ∗ ((L + 0x448#64) ↦₆₄ 0#64)) ∗
  (((L + 0x450#64) ↦₆₄ 0#64) ∗ ((L + 0x458#64) ↦₆₄ 1#64) ∗ ((L + 0x460#64) ↦₆₄ 0#64)) ∗
  (((L + 0x468#64) ↦₆₄ 0#64) ∗ ((L + 0x470#64) ↦₆₄ 8#64) ∗ ((L + 0x478#64) ↦₆₄ 0#64)) ∗
  (((L + 0x480#64) ↦₆₄ 0#64) ∗ ((L + 0x488#64) ↦₆₄ 1#64) ∗ ((L + 0x490#64) ↦₆₄ 0#64)) ∗
  (((L + 0x498#64) ↦₆₄ 0#64) ∗ ((L + 0x4a0#64) ↦₆₄ 1#64) ∗ ((L + 0x4a8#64) ↦₆₄ 0#64)) ∗
  ((L + 0x4b0#64) ↦₆₄ noneCap) ∗ ((L + 0x518#64) ↦₆₄ noneCap) ∗
  ((L + 0x548#64) ↦₆₄ noneCap) ∗ ((L + 0x568#64) ↦₆₄ 0#64) ∗ ((L + 0x570#64) ↦₆₄ 0#64)

private theorem prostSSGAt_empty_intro_loopEntryG (L : BitVec 64) :
    ssRawCells_loopEntryG L ∗ memRegion (L + 0x4b8#64) 96 ∗
      memRegion (L + 0x520#64) 40 ∗ memRegion (L + 0x550#64) 24 ⊢
      prostSSGAt A0 (L + 0x420#64) SSG.empty := by
  unfold ssRawCells_loopEntryG prostSSGAt SSG.empty; dsimp only
  have h1 := empty_vecU8_intro_loopEntryG (L + 0x420#64)
  have h2 := empty_vecU8_intro_loopEntryG (L + 0x420#64 + 0x18#64)
  have h3 := empty_vecU8_intro_loopEntryG (L + 0x420#64 + 0x30#64)
  have h4 := empty_vecChainG_intro_loopEntryG (L + 0x420#64 + 0x48#64)
  have h5 := empty_vecU8_intro_loopEntryG (L + 0x420#64 + 0x60#64)
  have h6 := empty_vecU8_intro_loopEntryG (L + 0x420#64 + 0x78#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3 h4 h5 h6 ⊢
  rw [pointsTo64_zero_split32_loopEntryG (L + 0x568#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans ?_
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
      (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono h6 (Entails.refl _)))))))
  exact Entails.of_eq (by ac_rfl)

/-! ## Address Normalization for `L = s0.sp - 0x770` -/

@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1904_sub_96_loopEntryG (L : BitVec 64) :
    L + 1904#64 + bv% (2 ^ 64 - 96) = L + 1808#64 := by rw [BitVec.add_assoc]; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1808_sub_1808_loopEntryG (L : BitVec 64) :
    L + 1808#64 - 1808#64 = L := by bv_omega

@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1808_sub_40_loopEntryG (L : BitVec 64) :
    L + 1808#64 + bv% (2 ^ 64 - 40) = L + 1768#64 := by rw [BitVec.add_assoc]; rfl

private def deserSavedAt_loopEntryG (L : BitVec 64) (s0 : State) : SepProp :=
  ((L + 1808#64) ↦₆₄ s0.readReg64 .x29) ∗ ((L + 1816#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((L + 1824#64) ↦₆₄ s0.readReg64 .x28) ∗ ((L + 1832#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((L + 1840#64) ↦₆₄ s0.readReg64 .x26) ∗ ((L + 1848#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((L + 1856#64) ↦₆₄ s0.readReg64 .x24) ∗ ((L + 1864#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((L + 1872#64) ↦₆₄ s0.readReg64 .x22) ∗ ((L + 1880#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((L + 1888#64) ↦₆₄ s0.readReg64 .x20) ∗ ((L + 1896#64) ↦₆₄ s0.readReg64 .x19)

private theorem deserSavedAt_eq_loopEntryG (s0 : State) :
    deserSavedAt_loopEntryG (deserSpL s0.sp) s0 = deserSaved s0 := by
  unfold deserSavedAt_loopEntryG deserSaved deserSpL; dsimp only
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

/-! ## `SessionStructure::default()` Writes (`+0x104 → +0x15c`) -/

private def ssUninitCells_loopEntryG (L : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 : BitVec 64) :
    SepProp :=
  ((L + 1056#64) ↦₆₄ noneCap) ∗
  ((L + 1064#64) ↦₆₄ c1) ∗ ((L + 1072#64) ↦₆₄ c2) ∗ ((L + 1080#64) ↦₆₄ c3) ∗
  ((L + 1088#64) ↦₆₄ c4) ∗ ((L + 1096#64) ↦₆₄ c5) ∗ ((L + 1104#64) ↦₆₄ c6) ∗
  ((L + 1112#64) ↦₆₄ c7) ∗ ((L + 1120#64) ↦₆₄ c8) ∗ ((L + 1128#64) ↦₆₄ c9) ∗
  ((L + 1136#64) ↦₆₄ c10) ∗ ((L + 1144#64) ↦₆₄ c11) ∗ ((L + 1152#64) ↦₆₄ c12) ∗
  ((L + 1160#64) ↦₆₄ c13) ∗ ((L + 1168#64) ↦₆₄ c14) ∗ ((L + 1176#64) ↦₆₄ c15) ∗
  ((L + 1184#64) ↦₆₄ c16) ∗ ((L + 1192#64) ↦₆₄ c17) ∗ ((L + 1200#64) ↦₆₄ c18) ∗
  ((L + 1304#64) ↦₆₄ c19) ∗ ((L + 1352#64) ↦₆₄ c20) ∗
  ((L + 1384#64) ↦₆₄ c21) ∗ ((L + 1392#64) ↦₆₄ c22)

private theorem step_1b_loopEntryG (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)} (L : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 : BitVec 64)
    {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = deserEntry_loopEntryG + 260#64) (hrun : s.status = .Running)
    (hsp : s.sp = L) (halign : L &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = 2#64) (hx21 : s.readReg64 .x21 = noneCap)
    (hx23 : s.readReg64 .x23 = L + 1032#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx26 : s.readReg64 .x26 = 8#64)
    (hnext : ∀ s' : State, s'.pc = deserEntry_loopEntryG + 348#64 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) → s'.readReg64 .x19 = s.readReg64 .x19 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = s.readReg64 .x29 →
      post s' (ssRawCells_loopEntryG L)) :
    SepWP (libsignalSessionCode.rebase sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)))
      (deserEntry_loopEntryG + 348#64) s
      (ssUninitCells_loopEntryG L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22)
      post := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  d0_fetches_1b sessionImg0.base H
  rw [fnAddr_deser_eq_loopEntryG H] at *
  examples_hide_fetches; unfold ssUninitCells_loopEntryG
  have hnone : noneCap = bv% (2 ^ 64 - 1) := rfl
  rw [hnone] at hx21 ⊢
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩ (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold ssRawCells_loopEntryG; rw [hnone]; ac_rfl

/-! ## Prologue and Outer Key `0x0a` (`+0x000 → +0x104`) -/

private def step1aPre_loopEntryG (L p : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64) : SepProp :=
  ((L + 1808#64) ↦₆₄ w0) ∗ ((L + 1816#64) ↦₆₄ w1) ∗
  ((L + 1824#64) ↦₆₄ w2) ∗ ((L + 1832#64) ↦₆₄ w3) ∗
  ((L + 1840#64) ↦₆₄ w4) ∗ ((L + 1848#64) ↦₆₄ w5) ∗
  ((L + 1856#64) ↦₆₄ w6) ∗ ((L + 1864#64) ↦₆₄ w7) ∗
  ((L + 1872#64) ↦₆₄ w8) ∗ ((L + 1880#64) ↦₆₄ w9) ∗
  ((L + 1888#64) ↦₆₄ w10) ∗ ((L + 1896#64) ↦₆₄ w11) ∗
  (L ↦₆₄ u0) ∗ ((L + 1016#64) ↦₆₄ u1) ∗ ((L + 1024#64) ↦₆₄ u2) ∗
  ((L + 1032#64) ↦₆₄ u3) ∗ ((L + 1040#64) ↦₆₄ u4) ∗
  ((L + 1048#64) ↦₆₄ u5) ∗ ((L + 1056#64) ↦₆₄ u6) ∗
  ((L + 1768#64) ↦₆₄ u7) ∗ (p ↦₈ 10#8)

private def step1aPost_loopEntryG (L p : BitVec 64) (len1 : Nat) (s0 : State) : SepProp :=
  deserSavedAt_loopEntryG L s0 ∗ (L ↦₆₄ 0#64) ∗
  ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗
  ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗
  ((L + 1048#64) ↦₆₄ 0#64) ∗ ((L + 1056#64) ↦₆₄ noneCap) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 10#8)

private theorem step_1a_loopEntryG (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (L p out : BitVec 64) (len1 : Nat)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = deserEntry_loopEntryG) (hrun : s0.status = .Running)
    (hsp : s0.sp = L + 1904#64) (halignL : L &&& 15#64 = 0#64)
    (halign1808 : (L + 1808#64) &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + len1))
    (hx8 : s0.readReg64 .x8 = out) (hlen1_pos : 0 < len1) (hlen1_lt : len1 < 2 ^ 20)
    (hnext : ∀ s1 : State, s1.pc = deserEntry_loopEntryG + 260#64 → s1.status = .Running →
      s1.sp = L → (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) → s1.readReg64 .x0 = 2#64 →
      s1.readReg64 .x19 = out → s1.readReg64 .x21 = noneCap →
      s1.readReg64 .x23 = L + 1032#64 → s1.readReg64 .x24 = 1#64 →
      s1.readReg64 .x26 = 8#64 → s1.readReg64 .x29 = L + 1808#64 →
      post s1 (step1aPost_loopEntryG L p len1 s0)) :
    SepWP (libsignalSessionCode.rebase sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)))
      (deserEntry_loopEntryG + 260#64) s0
      (step1aPre_loopEntryG L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7)
      post := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  d0_fetches_1a sessionImg0.base H
  rw [fnAddr_deser_eq_loopEntryG H] at *
  examples_hide_fetches; unfold step1aPre_loopEntryG
  have hcbz : (BitVec.ofNat 64 (1 + len1) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change 1 + len1 = 0 at hnat; omega
  have hsub1 : BitVec.ofNat 64 (1 + len1) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 len1 := by
    rw [Nat.add_comm 1 len1, BitVec.ofNat_add]; bv_omega
  have hsub1' : BitVec.ofNat 64 (1 + len1) - 1#64 = BitVec.ofNat 64 len1 := by
    rw [Nat.add_comm 1 len1, BitVec.ofNat_add]; bv_omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  have hnone : noneCap = bv% (2 ^ 64 - 1) := rfl
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩ (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by rw [hnone]; simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])) ?_
  unfold step1aPost_loopEntryG deserSavedAt_loopEntryG; rw [hnone]
  simp only [Reg.x29, Reg.x30, Reg.x28, Reg.x27, Reg.x26, Reg.x25, Reg.x24, Reg.x23,
    Reg.x22, Reg.x21, Reg.x20, Reg.x19]
  ac_rfl

/-! ## Single-Byte Length Fast Path (`+0x15c → +0x254`, `N < 128`) -/

private def step2aPre_loopEntryG (L p : BitVec 64) (N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (1 + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)

private def step2aPost_loopEntryG (L p : BitVec 64) (N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 2#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)

private theorem step_2a_loopEntryG (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (L p out : BitVec 64) (N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = deserEntry_loopEntryG + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64)
    (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_lt : N < 128)
    (hnext : ∀ s' : State, s'.pc = deserEntry_loopEntryG + 596#64 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) → s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 →
      post s' (step2aPost_loopEntryG L p N)) :
    SepWP (libsignalSessionCode.rebase sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)))
      (deserEntry_loopEntryG + 596#64) s (step2aPre_loopEntryG L p N) post := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  d0_fetches_2a sessionImg0.base H
  rw [fnAddr_deser_eq_loopEntryG H] at *
  examples_hide_fetches; unfold step2aPre_loopEntryG
  have hcbz : (BitVec.ofNat 64 (1 + N) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change 1 + N = 0 at hnat; omega
  have hse := signExtend64_ofNat8_lt_128_loopEntryG hN_lt
  have hbit63 : (((BitVec.ofNat 8 N).signExtend 64).getLsbD 63 == true) = false :=
    (signExtend64_bit63_eq_false_iff_loopEntryG (BitVec.ofNat 8 N)).mpr (by rw [BitVec.toNat_ofNat]; omega)
  have hsub1 : BitVec.ofNat 64 (1 + N) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 N := by
    rw [Nat.add_comm 1 N, BitVec.ofNat_add]; bv_omega
  have hsub1' : BitVec.ofNat 64 (1 + N) - 1#64 = BitVec.ofNat 64 N := by
    rw [Nat.add_comm 1 N, BitVec.ofNat_add]; bv_omega
  have hult_self : (BitVec.ofNat 64 N).ult (BitVec.ofNat 64 N) = false := by simp [BitVec.ult]
  have hsub_self : BitVec.ofNat 64 N - BitVec.ofNat 64 N = 0#64 := by bv_omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩ (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step2aPost_loopEntryG; ac_rfl

/-! ## Multi-Byte Length Path (`+0x15c → +0x254`, `128 ≤ N < 2 ^ 20`) -/

private def step2bPre_loopEntryG (L p : BitVec 64) (vlen N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128))

private theorem step_2b_pre_loopEntryG (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (L p out : BitVec 64) (vlen N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = deserEntry_loopEntryG + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64)
    (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_ge : 128 ≤ N) (hVN_lt : vlen + N < 2 ^ 20)
    (hnext : ∀ s' : State, s'.pc = deserEntry_loopEntryG + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) → s'.readReg64 .lr = deserEntry_loopEntryG + 540#64 →
      s'.readReg64 .x0 = L + 1400#64 → s'.readReg64 .x1 = p + 1#64 →
      s'.readReg64 .x2 = BitVec.ofNat 64 (vlen + N) → s'.readReg64 .x19 = out →
      s'.readReg64 .x20 = L + 1016#64 → s'.readReg64 .x23 = L + 1032#64 →
      s'.readReg64 .x29 = L + 1808#64 → post s' (step2bPre_loopEntryG L p vlen N)) :
    SepWP (libsignalSessionCode.rebase sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)))
      (deserEntry_loopEntryG + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) s (step2bPre_loopEntryG L p vlen N) post := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  d0_fetches_2b_pre sessionImg0.base H
  rw [fnAddr_deser_eq_loopEntryG H] at *
  examples_hide_fetches; unfold step2bPre_loopEntryG
  have hcbz : (BitVec.ofNat 64 (vlen + N) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change vlen + N = 0 at hnat; omega
  have hbit63 :
      (((BitVec.ofNat 8 (N % 128 + 128)).signExtend 64).getLsbD 63 == true) = true :=
    (signExtend64_bit63_eq_true_iff_loopEntryG (BitVec.ofNat 8 (N % 128 + 128))).mpr
      (by rw [BitVec.toNat_ofNat]; omega)
  have hhi10 : (10#64).ult (BitVec.ofNat 64 (vlen + N)) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega),
      decide_eq_true_eq]; omega
  have hule10 : (BitVec.ofNat 64 (vlen + N)).ule 10#64 = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega),
      decide_eq_false_iff_not]; omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩ (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])) ?_
  unfold step2bPre_loopEntryG; ac_rfl

private def step2bPostPre_loopEntryG (L p : BitVec 64) (vlen N : Nat) : SepProp :=
  ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
  ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ BitVec.ofNat 64 vlen) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N))

private def step2bPostPost_loopEntryG (L p : BitVec 64) (vlen N : Nat) : SepProp :=
  ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
  ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ BitVec.ofNat 64 vlen) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N)

private theorem step_2b_post_loopEntryG (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (L p out : BitVec 64) (vlen N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = deserEntry_loopEntryG + 540#64) (hrun : s.status = .Running)
    (hsp : s.sp = L) (halignL : L &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = L + 1016#64)
    (hx23 : s.readReg64 .x23 = L + 1032#64) (hx29 : s.readReg64 .x29 = L + 1808#64)
    (hVN_lt : vlen + N < 2 ^ 20)
    (hnext : ∀ s' : State, s'.pc = deserEntry_loopEntryG + 596#64 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) → s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 →
      post s' (step2bPostPost_loopEntryG L p vlen N)) :
    SepWP (libsignalSessionCode.rebase sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)))
      (deserEntry_loopEntryG + 596#64) s (step2bPostPre_loopEntryG L p vlen N) post := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  d0_fetches_2b_post sessionImg0.base H
  rw [fnAddr_deser_eq_loopEntryG H] at *
  examples_hide_fetches; unfold step2bPostPre_loopEntryG
  have hsub2 : BitVec.ofNat 64 (vlen + N) - BitVec.ofNat 64 vlen = BitVec.ofNat 64 N := by
    rw [BitVec.ofNat_add]; bv_omega
  have hult2 : (BitVec.ofNat 64 (vlen + N)).ult (BitVec.ofNat 64 vlen) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show vlen < 2 ^ 64 by omega),
      decide_eq_false_iff_not]; omega
  have hult_self : (BitVec.ofNat 64 N).ult (BitVec.ofNat 64 N) = false := by simp [BitVec.ult]
  have hsub_self : BitVec.ofNat 64 N - BitVec.ofNat 64 N = 0#64 := by bv_omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩ (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step2bPostPost_loopEntryG; ac_rfl

/-! ## Memory Framing and `deserLoopEntryG_ok` -/

private theorem memRegion_succ8_loopEntryG (a : BitVec 64) (n : Nat) (hn : n < 2000) :
    memRegion a (n + 8) =
      (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) n := by
  rw [Nat.add_comm n 8, memRegion_split a 8 n (by omega), ProofLib.memRegion_eight]

private theorem memRegion_1064_336_cells_loopEntryG (L : BitVec 64) :
    ((L + 1056#64) ↦₆₄ noneCap) ∗ memRegion (L + 1064#64) 336 =
      ∃∗ c22 : BitVec 64, ∃∗ c21 : BitVec 64, ∃∗ c20 : BitVec 64, ∃∗ c19 : BitVec 64,
      ∃∗ c18 : BitVec 64, ∃∗ c17 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c15 : BitVec 64,
      ∃∗ c14 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c12 : BitVec 64, ∃∗ c11 : BitVec 64,
      ∃∗ c10 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c7 : BitVec 64,
      ∃∗ c6 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c2 : BitVec 64, ∃∗ c1 : BitVec 64,
        ssUninitCells_loopEntryG L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 ∗
        memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 := by
  rw [memRegion_split (L + 1064#64) 144 192 (by decide),
    memRegion_split (L + 1064#64 + 144#64) 96 96 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64) 8 88 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64) 40 48 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64 + 40#64) 8 40 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64 + 40#64 + 8#64) 24 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 2; arg 1
    simp (discharger := decide) only [memRegion_succ8_loopEntryG, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight (L + 1304#64), ProofLib.memRegion_eight (L + 1352#64)]
  conv_lhs =>
    arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2
    simp (discharger := decide) only [memRegion_succ8_loopEntryG, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  unfold ssUninitCells_loopEntryG
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply congrArg sepExists; funext _)
  ac_rfl

private theorem memRegion_1904_split_loopEntryG (L p : BitVec 64) :
    memRegion L 1904 ∗ (p ↦₈ 0x0a#8) =
      ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ u7 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u4 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        step1aPre_loopEntryG L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1064#64) 336 ∗
        memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 := by
  rw [memRegion_split L 1808 96 (by decide),
    memRegion_split L 8 1800 (by decide),
    memRegion_split (L + 8#64) 1008 792 (by decide),
    memRegion_split (L + 8#64 + 1008#64) 48 744 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64) 336 408 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64) 368 40 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64 + 368#64) 8 32 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight L, ProofLib.memRegion_eight (L + 1768#64)]
  conv_lhs =>
    arg 1; arg 2
    simp (discharger := decide) only [memRegion_succ8_loopEntryG, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 1; arg 1; arg 2; arg 2; arg 1
    simp (discharger := decide) only [memRegion_succ8_loopEntryG, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  unfold step1aPre_loopEntryG
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply congrArg sepExists; funext _)
  ac_rfl

private theorem stackAt_recDeserialize_split_loopEntryG (sp0 : BitVec 64) :
    stackAt sp0 recDeserializeStack =
      stackAt (deserSpL sp0) deserCalleeStack ∗ memRegion (deserSpL sp0) 1904 := by
  change memRegion (sp0 - 65536#64) 65536 =
    memRegion (sp0 - 0x770#64 - 63632#64) 63632 ∗ memRegion (sp0 - 0x770#64) 1904
  rw [memRegion_split (sp0 - 65536#64) 63632 1904 (by decide)]
  have h1 : sp0 - 65536#64 = sp0 - 0x770#64 - 63632#64 := by bv_omega
  have h2 : sp0 - 65536#64 + 63632#64 = sp0 - 0x770#64 := by bv_omega
  rw [h2, h1]

private theorem memRegion_0_1016_intro_loopEntryG (L : BitVec 64) :
    (L ↦₆₄ 0#64) ∗ memRegion (L + 8#64) 1008 ⊢ memRegion L 0x3f8 := by
  rw [show (0x3f8 : Nat) = 1016 by decide, memRegion_split L 8 1008 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion L 0#64)

private def deserFixedLocalsG_loopEntryG (L : BitVec 64) : SepProp :=
  memRegion L 0x3f8 ∗
    ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
    prostSSGAt A0 (L + 0x420#64) SSG.empty ∗ memRegion (L + 0x6f0#64) 0x20

private theorem step1b_post_entails_loopEntryG (L p : BitVec 64) (len1 : Nat) (s0 : State)
    (hL : L = deserSpL s0.sp) :
    ssRawCells_loopEntryG L ∗ memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗
      memRegion (L + 1360#64) 24 ∗ deserSavedAt_loopEntryG L s0 ∗ (L ↦₆₄ 0#64) ∗
      ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗
      ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
      ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 0x0a#8) ∗ memRegion (L + 8#64) 1008 ∗
      memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ⊢
    ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
      ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopEntryG L ∗ deserSaved s0 := by
  have hss := prostSSGAt_empty_intro_loopEntryG L
  have hm0 := memRegion_0_1016_intro_loopEntryG L
  have hds : deserSavedAt_loopEntryG L s0 = deserSaved s0 := hL ▸ deserSavedAt_eq_loopEntryG s0
  unfold deserFixedLocalsG_loopEntryG; rw [hds]
  rw [show (0x408#64 : BitVec 64) = 1032#64 from rfl,
    show (0x410#64 : BitVec 64) = 1040#64 from rfl,
    show (0x418#64 : BitVec 64) = 1048#64 from rfl,
    show (0x6f0#64 : BitVec 64) = 1776#64 from rfl,
    show (0x20 : Nat) = 32 from rfl]
  refine Entails.trans ?_
    (Entails.trans
      (sepConj_mono (sepConj_mono hss hm0)
        (Entails.refl (((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
          ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ (p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗
          ((L + 1048#64) ↦₆₄ 0#64) ∗ memRegion (L + 1776#64) 32 ∗ deserSaved s0))) ?_)
  · exact Entails.of_eq (by ac_rfl)
  · exact Entails.of_eq (by ac_rfl)

private theorem scratch24_368_fold_loopEntryG (L v w : BitVec 64) :
    ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
      ((L + 1408#64) ↦₆₄ v) ∗ ((L + 1416#64) ↦₆₄ w) ∗ memRegion (L + 1424#64) 344 ⊢
      memRegion (L + 1400#64) 368 := by
  have h0 : ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) =
      ((L + 1400#64) ↦₆₄ 0#64) := by
    have hs := (pointsTo64_zero_split32_loopEntryG (L + 1400#64)).symm
    rw [show L + 1400#64 + 4#64 = L + 1404#64 by bv_omega] at hs; exact hs
  rw [← sepConj_assoc, h0,
    memRegion_split (L + 1400#64) 24 344 (by decide),
    memRegion_split (L + 1400#64) 8 16 (by decide),
    memRegion_split (L + 1400#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans ?_
    (sepConj_mono
      (sepConj_mono (pointsTo64_entails_memRegion (L + 1400#64) 0#64)
        (sepConj_mono (pointsTo64_entails_memRegion (L + 1408#64) v)
          (pointsTo64_entails_memRegion (L + 1416#64) w)))
      (Entails.refl _))
  exact Entails.of_eq (by ac_rfl)

private theorem deserLocalsG_of_2a_loopEntryG (L p : BitVec 64) (r : SessionRecord (List (BitVec 8)))
    (heq : encodeRecord r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFields r).flatMap GenField.enc).length) ++
      (recFields r).flatMap GenField.enc)
    (hN : ((recFields r).flatMap GenField.enc).length < 128) :
    let body := (recFields r).flatMap GenField.enc
    step2aPost_loopEntryG L p body.length ∗
      ((p + 1#64 + 1#64) ↦ₛ body) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopEntryG L =
    deserLocalsG L p (encodeRecord r) body SSG.empty := by
  intro body
  have hpfx : encodeRecord r =
      0x0a#8 :: BitVec.ofNat 8 body.length :: body := by
    rw [heq, encodeKey_1_ld_loopEntryG, encodeVarint_of_lt_128_loopEntryG hN]; rfl
  have hsub : (encodeRecord r).length - body.length = 2 := by
    rw [hpfx, List.length_cons, List.length_cons]; omega
  have hbytes : (p ↦ₛ encodeRecord r) =
      (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 body.length) ∗
        ((p + 1#64 + 1#64) ↦ₛ body) := by
    rw [hpfx, pointsToBytes_cons, pointsToBytes_cons]
  unfold deserLocalsG Prost.sliceCursorAfter deserFixedLocalsG_loopEntryG step2aPost_loopEntryG
  rw [hsub, hbytes,
    show (0x3f8#64 : BitVec 64) = 1016#64 from rfl,
    show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (BitVec.ofNat 64 2 : BitVec 64) = 2#64 from rfl,
    show (0x578#64 : BitVec 64) = 1400#64 from rfl,
    show (0x170 : Nat) = 368 from rfl,
    show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]; ac_rfl

private theorem step2bPostPost_entails_loopEntryG (L p : BitVec 64) (vlen N : Nat) :
    step2bPostPost_loopEntryG L p vlen N ∗ memRegion (L + 1424#64) 344 ⊢
      memRegion (L + 1400#64) 368 ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
        ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N) := by
  unfold step2bPostPost_loopEntryG
  refine Entails.trans ?_
    (sepConj_mono_left (Q := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
      ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗
      ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N))
      (scratch24_368_fold_loopEntryG L (BitVec.ofNat 64 N) (BitVec.ofNat 64 vlen)))
  exact Entails.of_eq (by ac_rfl)

private theorem deserLocalsG_of_2b_loopEntryG (L p : BitVec 64) (r : SessionRecord (List (BitVec 8)))
    (heq : encodeRecord r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFields r).flatMap GenField.enc).length) ++
      (recFields r).flatMap GenField.enc) :
    let body := (recFields r).flatMap GenField.enc
    let vlen := (encodeVarint (BitVec.ofNat 64 body.length)).length
    (step2bPostPost_loopEntryG L p vlen body.length ∗ memRegion (L + 1424#64) 344) ∗
      ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) ∗
      (p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_loopEntryG L ⊢
    deserLocalsG L p (encodeRecord r) body SSG.empty := by
  intro body vlen
  refine Entails.trans
    (sepConj_mono_left (step2bPostPost_entails_loopEntryG L p vlen body.length)) ?_
  have hpfx : encodeRecord r =
      0x0a#8 :: (encodeVarint (BitVec.ofNat 64 body.length) ++ body) := by
    rw [heq, encodeKey_1_ld_loopEntryG]; rfl
  have hsub : (encodeRecord r).length - body.length = 1 + vlen := by
    rw [hpfx, List.length_cons, List.length_append]; omega
  have hptr : p + 1#64 + BitVec.ofNat 64 vlen = p + BitVec.ofNat 64 (1 + vlen) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  have hbytes : (p ↦ₛ encodeRecord r) =
      (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) := by
    rw [hpfx, pointsToBytes_cons]
  unfold deserLocalsG Prost.sliceCursorAfter deserFixedLocalsG_loopEntryG
  rw [hsub, hptr, hbytes,
    show (0x3f8#64 : BitVec 64) = 1016#64 from rfl,
    show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (0x578#64 : BitVec 64) = 1400#64 from rfl,
    show (0x170 : Nat) = 368 from rfl,
    show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]
  exact Entails.of_eq (by ac_rfl)

private theorem stackAt_deserCallee_split_varint_loopEntryG (L : BitVec 64) :
    stackAt L deserCalleeStack =
      stackAt L Prost.decodeVarintSliceStack ∗ memRegion (L - 63632#64) 55360 := by
  change memRegion (L - 63632#64) 63632 =
    memRegion (L - 8272#64) 8272 ∗ memRegion (L - 63632#64) 55360
  rw [memRegion_split (L - 63632#64) 55360 8272 (by decide)]
  have h1 : L - 63632#64 + 55360#64 = L - 8272#64 := by bv_omega
  rw [h1, sepConj_comm]

private theorem allocFailedIn_of_trace_eq_loopEntryG {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢; rwa [htr] at h

private theorem allowPanic_frame_trace_loopEntryG {s0 sm sf : State} {F R : SepProp}
    (htr : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (allocFailedIn_of_trace_eq_loopEntryG htr) h

private theorem step_1_combined_loopEntryG (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (recordProg C ctl abs).fnAddr recDeserializeName) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.p)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length)
    (hx8 : s0.readReg64 .x8 = x.out)
    (heq : encodeRecord x.r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFields x.r).flatMap GenField.enc).length) ++
      (recFields x.r).flatMap GenField.enc)
    (hrec_lt : (encodeRecord x.r).length < 2 ^ 20)
    (hal : s0.spAligned = true)
    (hm0 : s0.mem ⊨ (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗ stackAt s0.sp recDeserializeStack ∗ R)
    (hL : (recordProg C ctl abs).CodeLoaded s0.mem) :
    let L := deserSpL s0.sp
    let body := (recFields x.r).flatMap GenField.enc
    let rest1 := encodeVarint (BitVec.ofNat 64 body.length) ++ body
    ∃ s2, Steps (recordProg C ctl abs) s0 s2 ∧ s2.pc = deserEntry_loopEntryG + 348#64 ∧
      s2.status = .Running ∧ s2.sp = L ∧ (s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
      s2.readReg64 .x19 = x.out ∧ s2.readReg64 .x23 = L + 1032#64 ∧
      s2.readReg64 .x29 = L + 1808#64 ∧
      (s2.mem ⊨
        (((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
          ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ (x.p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopEntryG L ∗ deserSaved s0) ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
  intro L body rest1
  have hsp0 : s0.sp = L + 1904#64 := by change s0.sp = s0.sp - 0x770#64 + 1904#64; bv_omega
  obtain ⟨halignL, halign1808⟩ := sp_sub_1904_aligned_loopEntryG (decide_eq_true_iff.mp hal)
  have hbs_cons : encodeRecord x.r = 0x0a#8 :: rest1 := by
    rw [heq, encodeKey_1_ld_loopEntryG]; rfl
  have hv_pos := encodeVarint_length_pos_loopEntryG (BitVec.ofNat 64 body.length)
  have hlen1_pos : 0 < rest1.length := by simp only [rest1, List.length_append]; omega
  have hlen1_lt : rest1.length < 2 ^ 20 := by
    rw [hbs_cons, List.length_cons] at hrec_lt; omega
  have hx1' : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + rest1.length) := by
    rw [hx1, hbs_cons, List.length_cons, Nat.add_comm]
  have hpc0 : s0.pc = deserEntry_loopEntryG := by rw [hpc]; exact fnAddr_deser_eq_loopEntryG _
  have hm0a : s0.mem ⊨ (memRegion L 1904 ∗ (x.p ↦₈ 0x0a#8)) ∗
      (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
    rw [hbs_cons, pointsToBytes_cons, stackAt_recDeserialize_split_loopEntryG s0.sp] at hm0
    dsimp only [L]; convert hm0 using 1; ac_rfl
  rw [memRegion_1904_split_loopEntryG L x.p] at hm0a
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm0a
  rcases hm0a with ⟨w11, w10, w9, w8, w7, w6, w5, w4, w3, w2, w1, w0, u7, u6, u5, u4, u3, u2, u1, u0, hm0b⟩
  have hm0c : s0.mem ⊨
      step1aPre_loopEntryG L x.p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
      (memRegion (L + 8#64) 1008 ∗ memRegion (L + 1064#64) 336 ∗
        memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    convert hm0b using 1; ac_rfl
  rcases (step_1a_loopEntryG C ctl L x.p x.out rest1.length
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7
      (post := fun s' P => P = step1aPost_loopEntryG L x.p rest1.length s0 ∧
        s'.sp = L ∧ (s'.trace = s0.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s0) ∧ s'.readReg64 .x0 = 2#64 ∧
        s'.readReg64 .x19 = x.out ∧ s'.readReg64 .x21 = noneCap ∧
        s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x24 = 1#64 ∧
        s'.readReg64 .x26 = 8#64 ∧ s'.readReg64 .x29 = L + 1808#64)
      hpc0 hrun hsp0 halignL halign1808 hx0 hx1' hx8 hlen1_pos hlen1_lt
      (fun s' _ _ hsp' htr' hx0' hx19' hx21' hx23' hx24' hx26' hx29' =>
        ⟨rfl, hsp', htr', hx0', hx19', hx21', hx23', hx24', hx26', hx29'⟩)).elim hm0c hL with
    ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, rfl,
      hsp1, htr1, hx0_1, hx19_1, hx21_1, hx23_1, hx24_1, hx26_1, hx29_1⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hm1a : s1.mem ⊨ (((L + 1056#64) ↦₆₄ noneCap) ∗ memRegion (L + 1064#64) 336) ∗
      (deserSavedAt_loopEntryG L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗
        ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
        ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (x.p ↦₈ 0x0a#8) ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold step1aPost_loopEntryG at hm1; convert hm1 using 1; ac_rfl
  rw [memRegion_1064_336_cells_loopEntryG L] at hm1a
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1a
  rcases hm1a with ⟨c22, c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11,
    c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, hm1b⟩
  have hm1c : s1.mem ⊨
      ssUninitCells_loopEntryG L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 ∗
      ((memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 ∗
        deserSavedAt_loopEntryG L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗
        ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
        ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (x.p ↦₈ 0x0a#8) ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32) ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold ssUninitCells_loopEntryG at hm1b ⊢; convert hm1b using 1; ac_rfl
  rcases (step_1b_loopEntryG C ctl L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
      c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      (post := fun s' P => P = ssRawCells_loopEntryG L ∧
        s'.sp = L ∧ (s'.trace = s1.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s1) ∧ s'.readReg64 .x19 = s1.readReg64 .x19 ∧
        s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = s1.readReg64 .x29)
      hpc1 hrun1 hsp1 halignL hx0_1 hx21_1 hx23_1 hx24_1 hx26_1
      (fun s' _ _ hsp' htr' hx19' hx23' hx29' =>
        ⟨rfl, hsp', htr', hx19', hx23', hx29'⟩)).elim hm1c (hst1.codeLoaded hL) with
    ⟨s2, hst2, ⟨hpc2, hrun2, P2, hm2, rfl, hsp2, htr2, hx19_2, hx23_2, hx29_2⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  refine ⟨s2, hst1.trans hst2, hpc2, hrun2, hsp2, ⟨htr2.1.trans htr1.1, htr2.2.trans htr1.2⟩,
    hx19_2.trans hx19_1, hx23_2, hx29_2.trans hx29_1, ?_⟩
  rw [← sepConj_assoc] at hm2
  exact Satisfies.mono (sepConj_mono_left (step1b_post_entails_loopEntryG L x.p rest1.length s0 rfl)) hm2

set_option maxHeartbeats 1600000 in
theorem deserLoopEntryG_ok_of_fields (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (recordProg C ctl abs).fnAddr recDeserializeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ deserializeGenSpec.pre x s0 ∗ R) (hal : s0.spAligned = true)
    (heq : DeserializeScope x.r → encodeRecord x.r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFields x.r).flatMap GenField.enc).length) ++
      (recFields x.r).flatMap GenField.enc)
    (hlt : DeserializeScope x.r → (encodeRecord x.r).length < 2 ^ 20) :
    DeserStepG C ctl x R s0 s0 (DeserLoopG C ctl x R s0 0) abs := by
  intro hL0
  unfold deserializeGenSpec at hpre; dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hr, hF0, hsym0⟩, hm0⟩
  rw [sepConj_assoc, sepConj_assoc] at hm0
  have heq' := heq hr
  have hrec_lt := hlt hr
  obtain ⟨halignL, _halign1808⟩ := sp_sub_1904_aligned_loopEntryG (decide_eq_true_iff.mp hal)
  obtain ⟨s2, hst2, hpc2, hrun2, hsp2, htr2, hx19_2, hx23_2, hx29_2, hm2⟩ :=
    step_1_combined_loopEntryG C ctl x R s0 hpc hrun hx0 hx1 hx8 heq' hrec_lt hal hm0 hL0
  set L := deserSpL s0.sp
  set body := (recFields x.r).flatMap GenField.enc
  set N := body.length
  set rest1 := encodeVarint (BitVec.ofNat 64 N) ++ body
  have hbs_cons : encodeRecord x.r = 0x0a#8 :: rest1 := by
    rw [heq', encodeKey_1_ld_loopEntryG]; rfl
  have hrest1_lt : rest1.length < 2 ^ 20 := by
    rw [hbs_cons, List.length_cons] at hrec_lt; omega
  by_cases hN : N < 128
  · have hr1 : rest1 = BitVec.ofNat 8 N :: body := by
      simp only [rest1, encodeVarint_of_lt_128_loopEntryG hN, List.singleton_append]
    have hlen1 : rest1.length = 1 + N := by rw [hr1, List.length_cons, Nat.add_comm]
    have hm2a : s2.mem ⊨ step2aPre_loopEntryG L x.p N ∗
        (((x.p + 1#64 + 1#64) ↦ₛ body) ∗ (x.p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopEntryG L ∗ deserSaved s0 ∗
          memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
      rw [hlen1, hr1, pointsToBytes_cons] at hm2
      unfold step2aPre_loopEntryG; convert hm2 using 1; ac_rfl
    rcases (step_2a_loopEntryG C ctl L x.p x.out N
        (post := fun s' P => P = step2aPost_loopEntryG L x.p N ∧
          s'.sp = L ∧ (s'.trace = s2.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s2) ∧ s'.readReg64 .x19 = x.out ∧
          s'.readReg64 .x20 = 0#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧
          s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 hN
        (fun s' _ _ hsp' htr' hx19' hx20' hx23' hx29' =>
          ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim hm2a (hst2.codeLoaded hL0) with
      ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, rfl, hsp3, htr3, hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    refine ⟨s3, hst2.trans hst3, Or.inl ?_⟩
    refine ⟨?_, hrun3, ⟨htr3.1.trans htr2.1, htr3.2.trans htr2.2⟩, ?_, (hst2.trans hst3).frozenLoaded hF0,
      hsp3, ?_, hx29_3, hx19_3, hx20_3, hx23_3, ?_⟩
    · unfold deserPC; rw [hpc3, fnAddr_deser_eq_loopEntryG]
    · rw [(hst2.trans hst3).symtab_eq, hsym0]
    · rw [State.spAligned, hsp3]; exact decide_eq_true halignL
    · have hloc := deserLocalsG_of_2a_loopEntryG L x.p x.r heq' hN
      have hdrop : (((recFields x.r).drop 0).flatMap GenField.enc) = body := by
        rw [List.drop_zero]
      have hss0 : ssgAfter x.r 0 = SSG.empty := rfl
      change s3.mem ⊨ deserLocalsG L x.p (encodeRecord x.r)
          (((recFields x.r).drop 0).flatMap GenField.enc) (ssgAfter x.r 0) ∗
        memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
      rw [hdrop, hss0, ← hloc]
      convert hm3 using 1; ac_rfl
  · have hN_ge : 128 ≤ N := by omega
    set vlen := (encodeVarint (BitVec.ofNat 64 N)).length
    set vtail := encodeVarintAux 9 (BitVec.ofNat 64 N >>> 7)
    have hlen1 : rest1.length = vlen + N := List.length_append
    have hVN_lt : vlen + N < 2 ^ 20 := by rw [← hlen1]; exact hrest1_lt
    have hN_lt : N < 2 ^ 20 := by omega
    have hr1 : rest1 = BitVec.ofNat 8 (N % 128 + 128) :: (vtail ++ body) := by
      simp only [rest1, vtail, encodeVarint_cons_of_ge_128_loopEntryG hN_ge hN_lt, List.cons_append]
    have hm2_bytes : ((x.p + 1#64) ↦ₛ rest1) =
        ((x.p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128)) ∗
          ((x.p + 1#64 + 1#64) ↦ₛ (vtail ++ body)) := by
      rw [hr1, pointsToBytes_cons]
    have hm2c : s2.mem ⊨ step2bPre_loopEntryG L x.p vlen N ∗
        (((x.p + 1#64 + 1#64) ↦ₛ (vtail ++ body)) ∗
          (x.p ↦₈ 0x0a#8) ∗ memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopEntryG L ∗
          deserSaved s0 ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
      rw [hlen1, hm2_bytes] at hm2
      unfold step2bPre_loopEntryG; convert hm2 using 1; ac_rfl
    rcases (step_2b_pre_loopEntryG C ctl L x.p x.out vlen N
        (post := fun s' P => P = step2bPre_loopEntryG L x.p vlen N ∧
          s'.sp = L ∧ (s'.trace = s2.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s2) ∧ s'.readReg64 .lr = deserEntry_loopEntryG + 540#64 ∧
          s'.readReg64 .x0 = L + 1400#64 ∧ s'.readReg64 .x1 = x.p + 1#64 ∧
          s'.readReg64 .x2 = BitVec.ofNat 64 (vlen + N) ∧ s'.readReg64 .x19 = x.out ∧
          s'.readReg64 .x20 = L + 1016#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧
          s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 hN_ge hVN_lt
        (fun s' _ _ hsp' htr' hlr' hx0' hx1' hx2' hx19' hx20' hx23' hx29' =>
          ⟨rfl, hsp', htr', hlr', hx0', hx1', hx2', hx19', hx20', hx23', hx29'⟩)).elim
        hm2c (hst2.codeLoaded hL0) with
      ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, rfl,
        hsp3, htr3, hlr_3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    have hpc3' : s3.pc = (recordProg C ctl abs).fnAddr Prost.decodeVarintSliceName := by
      rw [hpc3]; exact decodeVarintSlice_fnAddr_eq_loopEntryG C ctl
    have hal3 : s3.spAligned = true := by rw [State.spAligned, hsp3]; exact decide_eq_true halignL
    have hx2_3_nat : (s3.readReg64 .x2).toNat = rest1.length := by
      rw [hx2_3, hlen1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen1_lt32 : rest1.length < 4294967296 := by omega
    have hpre_slice : Prost.VarintSlicePre rest1 := Or.inl (by omega)
    let gvar : Prost.DecodeVarintSliceGhost := ⟨L + 1400#64, x.p + 1#64, rest1⟩
    let F_call : SepProp :=
      ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N)) ∗
        memRegion (L - 63632#64) 55360 ∗ memRegion (L + 1424#64) 344 ∗
        (x.p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_loopEntryG L ∗ deserSaved s0 ∗ memRegion x.out 368
    have hm3_call : s3.mem ⊨ (Prost.decodeVarintSliceSpec A0).pre gvar s3 ∗ (F_call ∗ R) := by
      unfold Prost.decodeVarintSliceSpec; dsimp only [gvar]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_3, hx1_3, hx2_3_nat, Nat.lt_of_lt_of_le hlen1_lt32 (by decide), hpre_slice⟩, ?_⟩
      unfold step2bPre_loopEntryG at hm3
      rw [memRegion_split (L + 1400#64) 24 344 (by decide),
        stackAt_deserCallee_split_varint_loopEntryG L] at hm3
      have h1424 : L + 1400#64 + 24#64 = L + 1424#64 := by bv_omega
      have hpool : A0.pool = emp := rfl
      rw [h1424] at hm3
      dsimp only [F_call]
      rw [hsp3, hpool, hm2_bytes]
      convert hm3 using 1; ac_rfl
    obtain ⟨s4, hst4, hpost4, -⟩ :=
      subroutine_ok.no_fault_before_outcome hC.1 gvar (F_call ∗ R) s3 hpc3' hrun3 hm3_call hal3
        ((hst2.trans hst3).codeLoaded hL0)
    rcases hpost4 with ⟨⟨hpc4, _, hrun4⟩, ⟨hsp4, hcs4⟩, hm4⟩ | ⟨hpan4, hm4_pan⟩ | ⟨code, _, hm4_ex⟩ | ⟨_, hm4_oom⟩
    · have hpc4' : s4.pc = deserEntry_loopEntryG + 540#64 := by rw [hpc4, hlr_3]
      have hsp4' : s4.sp = L := by rw [hsp4, hsp3]
      have hx19_4 : s4.readReg64 .x19 = x.out := by rw [hcs4.1, hx19_3]
      have hx20_4 : s4.readReg64 .x20 = L + 1016#64 := by rw [hcs4.2.1, hx20_3]
      have hx23_4 : s4.readReg64 .x23 = L + 1032#64 := by rw [hcs4.2.2.2.2.1, hx23_3]
      have hx29_4 : s4.readReg64 .x29 = L + 1808#64 := by rw [hcs4.2.2.2.2.2.2.2.2.2.2.1, hx29_3]
      have hv4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 :=
        hcs4.2.2.2.2.2.2.2.2.2.2.2.trans (htr3.2.trans htr2.2)
      have hdec : decodeVarint rest1 = some (BitVec.ofNat 64 N, body) :=
        decodeVarint_encodeVarint (BitVec.ofNat 64 N) body
      have hsub1 : rest1.length - body.length = vlen := by
        rw [hlen1]; change (vlen + N) - N = vlen; omega
      unfold Prost.decodeVarintSliceSpec at hm4; dsimp only [gvar] at hm4
      rw [hdec] at hm4; dsimp only [Prost.varintSliceResultAt] at hm4
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm4
      rcases hm4 with ⟨htr4, hm4⟩
      have hm4a : s4.mem ⊨ step2bPostPre_loopEntryG L x.p vlen N ∗
          (memRegion (L + 1424#64) 344 ∗ ((x.p + 1#64) ↦ₛ rest1) ∗ (x.p ↦₈ 0x0a#8) ∗
            deserFixedLocalsG_loopEntryG L ∗ deserSaved s0 ∗ memRegion x.out 368 ∗
            stackAt L deserCalleeStack ∗ R) := by
        dsimp only [F_call] at hm4; unfold step2bPostPre_loopEntryG
        have hpool : A0.pool = emp := rfl
        rw [hsp3, hpool, pointsTo64_zero_split32_loopEntryG (L + 1400#64), hsub1] at hm4
        rw [stackAt_deserCallee_split_varint_loopEntryG L]
        have ha1 : L + 1400#64 + 4#64 = L + 1404#64 := by bv_omega
        have ha2 : L + 1400#64 + 8#64 = L + 1408#64 := by bv_omega
        have ha3 : L + 1400#64 + 16#64 = L + 1416#64 := by bv_omega
        rw [ha1, ha2, ha3] at hm4
        convert hm4 using 1; ac_rfl
      rcases (step_2b_post_loopEntryG C ctl L x.p x.out vlen N
          (post := fun s' P => P = step2bPostPost_loopEntryG L x.p vlen N ∧
            s'.sp = L ∧ (s'.trace = s4.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s4) ∧ s'.readReg64 .x19 = x.out ∧
            s'.readReg64 .x20 = 0#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧
            s'.readReg64 .x29 = L + 1808#64)
          hpc4' hrun4 hsp4' halignL hx19_4 hx20_4 hx23_4 hx29_4 hVN_lt
          (fun s' _ _ hsp' htr' hx19' hx20' hx23' hx29' =>
            ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim
          hm4a ((hst2.trans (hst3.trans hst4)).codeLoaded hL0) with
        ⟨s5, hst5, ⟨hpc5, hrun5, P5, hm5, rfl, hsp5, htr5, hx19_5, hx20_5, hx23_5, hx29_5⟩ | ⟨_, hoom⟩⟩
      swap; · exact (not_satisfies_false_sepConj hoom).elim
      refine ⟨s5, (hst2.trans (hst3.trans hst4)).trans hst5, Or.inl ?_⟩
      refine ⟨?_, hrun5, ⟨(htr5.1.trans htr4).trans (htr3.1.trans htr2.1), htr5.2.trans hv4⟩, ?_,
        ((hst2.trans (hst3.trans hst4)).trans hst5).frozenLoaded hF0,
        hsp5, ?_, hx29_5, hx19_5, hx20_5, hx23_5, ?_⟩
      · unfold deserPC; rw [hpc5, fnAddr_deser_eq_loopEntryG]
      · rw [((hst2.trans (hst3.trans hst4)).trans hst5).symtab_eq, hsym0]
      · rw [State.spAligned, hsp5]; exact decide_eq_true halignL
      · have hloc := deserLocalsG_of_2b_loopEntryG L x.p x.r heq'
        have hdrop : (((recFields x.r).drop 0).flatMap GenField.enc) = body := by
          rw [List.drop_zero]
        have hss0 : ssgAfter x.r 0 = SSG.empty := rfl
        change s5.mem ⊨ deserLocalsG L x.p (encodeRecord x.r)
            (((recFields x.r).drop 0).flatMap GenField.enc) (ssgAfter x.r 0) ∗
          memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
        rw [hdrop, hss0]
        have hm5a : s5.mem ⊨
            ((step2bPostPost_loopEntryG L x.p vlen N ∗ memRegion (L + 1424#64) 344) ∗
              ((x.p + 1#64) ↦ₛ rest1) ∗ (x.p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_loopEntryG L) ∗
            (memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R) := by
          convert hm5 using 1; ac_rfl
        exact Satisfies.mono (sepConj_mono_left hloc) hm5a
    · refine ⟨s4, (hst2.trans hst3).trans hst4, Or.inr ⟨hpan4, ?_⟩⟩
      unfold Prost.decodeVarintSliceSpec at hm4_pan; dsimp only at hm4_pan
      have hm4_pan' : s4.mem ⊨
          ((⌜allocFailedIn s3 s4 ∧ s3.trace <+: s4.trace⌝ ∗ anyHeap) ∗ F_call) ∗ R := by
        convert hm4_pan using 1; ac_rfl
      exact allowPanic_frame_trace_loopEntryG (htr3.1.trans htr2.1) hm4_pan'
    · exact False.elim (not_satisfies_false_sepConj hm4_ex)
    · exact False.elim (not_satisfies_false_sepConj hm4_oom)

theorem deserLoopEntryG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (recordProg C ctl abs).fnAddr recDeserializeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ deserializeGenSpec.pre x s0 ∗ R) (hal : s0.spAligned = true) :
    DeserStepG C ctl x R s0 s0 (DeserLoopG C ctl x R s0 0) abs :=
  deserLoopEntryG_ok_of_fields C ctl hC x R s0 hpc hrun hpre hal
    (encodeRecord_eq_recFields x.r) encodeRecord_length_lt

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopEntryG
