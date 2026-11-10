/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.BodyDefs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Fields
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Seed `SessionRecord::deserialize` Entry Segment (`+0x000 → +0x254`)

Proves `deserLoopEntry_ok` and `deserLoopEntry_placed_ok`, stepping `SessionRecord::deserialize`
(`0x16ed4`, block `46`) from function entry on `seedRecord f = [0x0a] ++ len ++ seedSession f`
through `RecordStructure` and `SessionStructure::default()` initialization and the 1- or 2-byte
outer length varint to the field-loop head `+0x254` (`DeserLoop … 0`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? sessionImg0
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace LoopEntryStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pre_loopEntry (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_pre_loopEntry (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pre_loopEntry (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_pre_loopEntry (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pre_loopEntry (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_pre_loopEntry (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pre_loopEntry (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_pre_loopEntry (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

section Fetch

open Lean Meta Elab Command Tactic

gen_decodes libsignalSessionCode_tree d0 [(ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") → (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize" + 140), (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize" + 208) → (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize" + 380), (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize" + 512) → (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize" + 516),
    (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize" + 532) → (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize" + 592)]

private meta def addFetchesRange_loopEntry (b H : Syntax.Term) (ranges : List (Nat × Nat)) : TacticM Unit := do
  let off := num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn ← `(ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize")
  for (start, len) in ranges do
    for i in [0 : len / 4] do
      let k := start + 4 * i
      let dec := mkIdent (.str `CryptoVerification.E2E.Record.DeserializeSeed.LoopEntryStateSimp
        s!"d0_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
      let kq := Syntax.mkNumLit (toString k)
      if k == 0 then
        evalTactic (← `(tactic|
          have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
      else
        evalTactic (← `(tactic|
          have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

elab "d0_fetches_1a " b:term:max H:term:max : tactic =>
  addFetchesRange_loopEntry b H [(0, 144), (208, 52)]

elab "d0_fetches_1b " b:term:max H:term:max : tactic =>
  addFetchesRange_loopEntry b H [(260, 88)]

elab "d0_fetches_2a " b:term:max H:term:max : tactic =>
  addFetchesRange_loopEntry b H [(348, 36), (576, 20)]

elab "d0_fetches_2b_pre " b:term:max H:term:max : tactic =>
  addFetchesRange_loopEntry b H [(348, 24), (512, 8), (532, 8)]

elab "d0_fetches_2b_post " b:term:max H:term:max : tactic =>
  addFetchesRange_loopEntry b H [(540, 56)]

end Fetch

@[irreducible] private def deserEntry_loopEntry : BitVec 64 := bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")

private theorem fnAddr_deser_eq_loopEntry (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase sessionImg0.base H).fnAddr recDeserializeName = deserEntry_loopEntry := by
  unfold deserEntry_loopEntry
  rw [Program.fnAddr_rebase, EntryAux.sessionImg0_base, (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize")]
  rfl

private theorem decodeVarintSlice_fnAddr_eq_loopEntry (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)} :
    deserEntry_loopEntry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") =
      (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr Prost.decodeVarintSliceName := by
  unfold deserEntry_loopEntry
  rw [tripleRatchetProgAt, Program.fnAddr_rebase, EntryAux.sessionImg0_base, (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")]
  rfl

/-! ## Pure Codec and Length Bounds -/

private theorem pbVarintBody_length_bounds_loopEntry :
    ∀ (fuel x : Nat), 1 ≤ (pbVarintBody fuel x).length ∧ (pbVarintBody fuel x).length ≤ fuel + 1
  | 0, _ => by simp [pbVarintBody]
  | fuel + 1, x => by
    unfold pbVarintBody
    split_ifs with h
    · simp
    · have ih := pbVarintBody_length_bounds_loopEntry fuel (x / 128)
      simp only [List.length_cons]
      omega

private theorem seedSlice_length_le_loopEntry (f : List (BitVec 8)) (off n : Nat) :
    (seedSlice f off n).length ≤ n := by
  unfold seedSlice
  exact List.length_take_le n (f.drop off)

private theorem pbChain_length_le_loopEntry (pub : List (BitVec 8)) (priv : Option (List (BitVec 8)))
    (key : List (BitVec 8)) (index : Nat)
    (hpub : pub.length ≤ 32) (hpriv : ∀ p, priv = some p → p.length ≤ 32) (hkey : key.length ≤ 32) :
    (pbChain pub priv key index).length ≤ 120 := by
  have hv := pbVarintBody_length_bounds_loopEntry 5 index
  unfold pbChain pbBytes pbVarint pbPubkey pbKey
  cases priv with
  | none =>
    split_ifs <;> simp only [List.length_append, List.length_cons, List.length_nil] <;> omega
  | some p =>
    have hp := hpriv p rfl
    split_ifs <;> simp only [List.length_append, List.length_cons, List.length_nil] <;> omega

private theorem seedSession_length_bounds_loopEntry {f : List (BitVec 8)} (hf : SeedOk f) :
    106 ≤ (seedSession f).length ∧ (seedSession f).length < 1000 := by
  have hlen := hf.1
  have hs0 : (seedSlice f 0 32).length = 32 := seedSlice_length (by omega)
  have hs32 : (seedSlice f 32 32).length = 32 := seedSlice_length (by omega)
  have hs64 : (seedSlice f 64 32).length = 32 := seedSlice_length (by omega)
  have hc1 := pbChain_length_le_loopEntry (seedSlice f 97 32) (some (seedSlice f 129 32))
    (seedSlice f 161 32) (seedU32 f 193)
    (seedSlice_length_le_loopEntry f 97 32)
    (by rintro p ⟨⟩; exact seedSlice_length_le_loopEntry f 129 32)
    (seedSlice_length_le_loopEntry f 161 32)
  have hc2 := pbChain_length_le_loopEntry (seedSlice f 198 32) none
    (seedSlice f 230 32) (seedU32 f 262)
    (seedSlice_length_le_loopEntry f 198 32)
    (by rintro p ⟨⟩)
    (seedSlice_length_le_loopEntry f 230 32)
  have hpv1 : (pbVarint 1 4).length = 2 := rfl
  unfold seedSession
  split_ifs <;>
    simp only [pbBytes, pbPubkey, pbKey, List.length_append, List.length_cons, List.length_nil,
      List.length_replicate, hs0, hs32, hs64, hpv1] <;>
    omega

private theorem pbVarintBody_of_lt_128_loopEntry {n : Nat} (hn : n < 128) :
    pbVarintBody 5 n = [BitVec.ofNat 8 n] := by
  unfold pbVarintBody
  simp [hn]

private theorem pbVarintBody_of_ge_128_loopEntry {n : Nat} (hge : 128 ≤ n) (hlt : n < 1000) :
    pbVarintBody 5 n = [BitVec.ofNat 8 (n % 128 + 128), BitVec.ofNat 8 (n / 128)] := by
  have h1 : ¬ (n < 128) := by omega
  have h2 : n / 128 < 128 := by omega
  conv_lhs => unfold pbVarintBody
  simp only [h1, ↓reduceIte]
  conv_lhs => rhs; unfold pbVarintBody
  simp only [h2, ↓reduceIte]

private theorem decodeVarint_two_bytes_loopEntry {n : Nat} (rest : List (BitVec 8))
    (hge : 128 ≤ n) (hlt : n < 1000) :
    decodeVarint (BitVec.ofNat 8 (n % 128 + 128) :: BitVec.ofNat 8 (n / 128) :: rest) =
      some (BitVec.ofNat 64 n, rest) := by
  set b0 := BitVec.ofNat 8 (n % 128 + 128)
  set b1 := BitVec.ofNat 8 (n / 128)
  have hb0_nat : b0.toNat = n % 128 + 128 := by
    dsimp [b0]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb1_nat : b1.toNat = n / 128 := by
    dsimp [b1]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb0_gt : ¬ (b0.toNat ≤ 0x7F) := by omega
  have hb1_le : b1.toNat ≤ 0x7F := by omega
  have h19 : ¬ (0 + 1 = 9 ∧ 0x02 ≤ b1.toNat) := fun ⟨h, _⟩ => by cases h
  unfold decodeVarint decodeVarintAux
  simp only [hb0_gt, ↓reduceIte, show (0 : Nat) = 9 ↔ False by decide]
  unfold decodeVarintAux
  simp only [hb1_le, h19, ↓reduceIte]
  congr 1; congr 1
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := n % 128) (by omega) (n / 128)
  simp only [Nat.reducePow] at hor
  have hand0 : (b0 &&& 127).toNat = n % 128 := by
    rw [BitVec.toNat_and, hb0_nat, show (127 : BitVec 8).toNat = 127 from rfl,
      Nat.and_two_pow_sub_one_eq_mod _ 7]
    omega
  have hand1 : (b1 &&& 127).toNat = n / 128 := by
    rw [BitVec.toNat_and, hb1_nat, show (127 : BitVec 8).toNat = 127 from rfl,
      Nat.and_two_pow_sub_one_eq_mod _ 7]
    omega
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_or, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mul_zero, Nat.shiftLeft_eq, Nat.reducePow]
  rw [hand0, hand1]
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  have hp : 2 ^ (7 * (0 + 1)) = 128 := rfl
  rw [hz, hp, Nat.zero_or, Nat.mul_one,
    Nat.mod_eq_of_lt (show n % 128 < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show n % 128 < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show n / 128 < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show n / 128 * 128 < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show n < 18446744073709551616 by omega),
    Nat.mul_comm (n / 128) 128, Nat.or_comm, ← hor]
  omega

private theorem signExtend64_bit63_eq_false_iff_loopEntry (b0 : BitVec 8) :
    ((b0.signExtend 64).getLsbD 63 == true) = false ↔ b0.toNat ≤ 0x7F := by
  revert b0; decide

private theorem signExtend64_bit63_eq_true_iff_loopEntry (b0 : BitVec 8) :
    ((b0.signExtend 64).getLsbD 63 == true) = true ↔ 0x7F < b0.toNat := by
  revert b0; decide

private theorem signExtend64_eq_zeroExtend64_of_le_loopEntry (b0 : BitVec 8) (h : b0.toNat ≤ 0x7F) :
    b0.signExtend 64 = b0.zeroExtend 64 := by
  revert b0 h; decide

private theorem signExtend64_ofNat8_lt_128_loopEntry {n : Nat} (hn : n < 128) :
    (BitVec.ofNat 8 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hle : (BitVec.ofNat 8 n).toNat ≤ 0x7F := by rw [BitVec.toNat_ofNat]; omega
  rw [signExtend64_eq_zeroExtend64_of_le_loopEntry _ hle]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

/-! ## `prostSSAt` Default Initialization and Stack Splitting -/

private theorem sp_sub_1904_aligned_loopEntry {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0x770#64) &&& 15#64 = 0#64 ∧ (sp0 - 0x770#64 + 1808#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h; rw [e] at h'
  have hlt := sp0.isLt
  have hsub : sp0 - 0x770#64 + 1808#64 = sp0 - 96#64 := by bv_omega
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢; omega
  · rw [hsub]; apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢; omega

private theorem empty_vecU8_intro_loopEntry (v : BitVec 64) :
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

private theorem empty_vecChain_intro_loopEntry (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecOf A0 104 8 (fun c a => prostChainAt A0 a c) v [] := by
  dsimp only [vecOf, vecAt, vecHeader, vecBuf]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 8#64)
  have hite : (if (0#64 : BitVec 64) = 0 then emp
    else A0.live (8#64) ((0#64 : BitVec 64).toNat * 104) 8 ∗
      arrayAt (fun c a => prostChainAt A0 a c) 104 8#64 [] ∗
      memRegion (8#64 + BitVec.ofNat 64 (([] : List ChainV).length * 104))
        (((0#64 : BitVec 64).toNat - ([] : List ChainV).length) * 104)) = emp := rfl
  rw [hite]; simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_emp]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0 := by decide
  exact Entails.pure_right hp (Entails.refl _)

private theorem pointsTo64_zero_split32_loopEntry (a : BitVec 64) :
    (a ↦₆₄ 0#64) = (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  simpa using pointsTo64_split32 a 0#64

private def ssRawCells_loopEntry (L : BitVec 64) : SepProp :=
  (((L + 0x420#64) ↦₆₄ 0#64) ∗ ((L + 0x428#64) ↦₆₄ 1#64) ∗ ((L + 0x430#64) ↦₆₄ 0#64)) ∗
  (((L + 0x438#64) ↦₆₄ 0#64) ∗ ((L + 0x440#64) ↦₆₄ 1#64) ∗ ((L + 0x448#64) ↦₆₄ 0#64)) ∗
  (((L + 0x450#64) ↦₆₄ 0#64) ∗ ((L + 0x458#64) ↦₆₄ 1#64) ∗ ((L + 0x460#64) ↦₆₄ 0#64)) ∗
  (((L + 0x468#64) ↦₆₄ 0#64) ∗ ((L + 0x470#64) ↦₆₄ 8#64) ∗ ((L + 0x478#64) ↦₆₄ 0#64)) ∗
  (((L + 0x480#64) ↦₆₄ 0#64) ∗ ((L + 0x488#64) ↦₆₄ 1#64) ∗ ((L + 0x490#64) ↦₆₄ 0#64)) ∗
  (((L + 0x498#64) ↦₆₄ 0#64) ∗ ((L + 0x4a0#64) ↦₆₄ 1#64) ∗ ((L + 0x4a8#64) ↦₆₄ 0#64)) ∗
  ((L + 0x4b0#64) ↦₆₄ noneCap) ∗ ((L + 0x518#64) ↦₆₄ noneCap) ∗
  ((L + 0x548#64) ↦₆₄ noneCap) ∗ ((L + 0x568#64) ↦₆₄ 0#64) ∗ ((L + 0x570#64) ↦₆₄ 0#64)

private theorem prostSSAt_empty_intro_loopEntry (L : BitVec 64) :
    ssRawCells_loopEntry L ∗ memRegion (L + 0x4b8#64) 96 ∗
      memRegion (L + 0x520#64) 40 ∗ memRegion (L + 0x550#64) 24 ⊢
      prostSSAt A0 (L + 0x420#64) SSV.empty := by
  unfold ssRawCells_loopEntry prostSSAt SSV.empty; dsimp only
  have h1 := empty_vecU8_intro_loopEntry (L + 0x420#64)
  have h2 := empty_vecU8_intro_loopEntry (L + 0x420#64 + 0x18#64)
  have h3 := empty_vecU8_intro_loopEntry (L + 0x420#64 + 0x30#64)
  have h4 := empty_vecChain_intro_loopEntry (L + 0x420#64 + 0x48#64)
  have h5 := empty_vecU8_intro_loopEntry (L + 0x420#64 + 0x60#64)
  have h6 := empty_vecU8_intro_loopEntry (L + 0x420#64 + 0x78#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3 h4 h5 h6 ⊢
  rw [pointsTo64_zero_split32_loopEntry (L + 0x568#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans ?_
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
      (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono h6 (Entails.refl _)))))))
  exact Entails.of_eq (by ac_rfl)

/-! ## Frame Address Normalization -/

@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1904_sub_96_loopEntry (L : BitVec 64) :
    L + 1904#64 + bv% (2 ^ 64 - 96) = L + 1808#64 := by rw [BitVec.add_assoc]; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1808_sub_1808_loopEntry (L : BitVec 64) :
    L + 1808#64 - 1808#64 = L := by bv_omega

@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1808_sub_40_loopEntry (L : BitVec 64) :
    L + 1808#64 + bv% (2 ^ 64 - 40) = L + 1768#64 := by rw [BitVec.add_assoc]; rfl

private def deserSavedAt_loopEntry (L : BitVec 64) (s0 : State) : SepProp :=
  ((L + 1808#64) ↦₆₄ s0.readReg64 .x29) ∗ ((L + 1816#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((L + 1824#64) ↦₆₄ s0.readReg64 .x28) ∗ ((L + 1832#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((L + 1840#64) ↦₆₄ s0.readReg64 .x26) ∗ ((L + 1848#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((L + 1856#64) ↦₆₄ s0.readReg64 .x24) ∗ ((L + 1864#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((L + 1872#64) ↦₆₄ s0.readReg64 .x22) ∗ ((L + 1880#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((L + 1888#64) ↦₆₄ s0.readReg64 .x20) ∗ ((L + 1896#64) ↦₆₄ s0.readReg64 .x19)

private theorem deserSavedAt_eq_loopEntry (s0 : State) :
    deserSavedAt_loopEntry (deserSpL s0.sp) s0 = deserSaved s0 := by
  unfold deserSavedAt_loopEntry deserSaved deserSpL; dsimp only
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

/-! ## `SessionStructure::default()` Writes (`+0x104 → +0x15c`) -/

private def ssUninitCells_loopEntry (L : BitVec 64)
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

private theorem step_1b_loopEntry (C : Crypto) (ctl : BitVec 64) (L : BitVec 64)
    {abs : String → Option (State → State)}
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 : BitVec 64)
    {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = deserEntry_loopEntry + 260#64) (hrun : s.status = .Running)
    (hsp : s.sp = L) (halign : L &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = 2#64) (hx21 : s.readReg64 .x21 = noneCap)
    (hx23 : s.readReg64 .x23 = L + 1032#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx26 : s.readReg64 .x26 = 8#64)
    (hnext : ∀ s' : State, s'.pc = deserEntry_loopEntry + 348#64 → s'.status = .Running →
      s'.sp = L → s'.trace = s.trace → s'.readReg64 .x19 = s.readReg64 .x19 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = s.readReg64 .x29 →
      post s' (ssRawCells_loopEntry L)) :
    SepWP (libsignalSessionCode.rebase sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)))
      (deserEntry_loopEntry + 348#64) s
      (ssUninitCells_loopEntry L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22)
      post := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  d0_fetches_1b sessionImg0.base H
  rw [fnAddr_deser_eq_loopEntry H] at *
  examples_hide_fetches; unfold ssUninitCells_loopEntry
  have hnone : noneCap = bv% (2 ^ 64 - 1) := rfl
  rw [hnone] at hx21 ⊢
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold ssRawCells_loopEntry; rw [hnone]; ac_rfl

/-! ## Prologue, `RecordStructure` Init, and Outer Key `0x0a` (`+0x000 → +0x104`) -/

private def step1aPre_loopEntry (L p : BitVec 64)
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

private def step1aPost_loopEntry (L p : BitVec 64) (len1 : Nat) (s0 : State) : SepProp :=
  deserSavedAt_loopEntry L s0 ∗ (L ↦₆₄ 0#64) ∗
  ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗
  ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗
  ((L + 1048#64) ↦₆₄ 0#64) ∗ ((L + 1056#64) ↦₆₄ noneCap) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 10#8)

private theorem step_1a_loopEntry (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (L p out : BitVec 64) (len1 : Nat)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = deserEntry_loopEntry) (hrun : s0.status = .Running)
    (hsp : s0.sp = L + 1904#64) (halignL : L &&& 15#64 = 0#64)
    (halign1808 : (L + 1808#64) &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + len1))
    (hx8 : s0.readReg64 .x8 = out) (hlen1_pos : 0 < len1) (hlen1_lt : len1 < 2000)
    (hnext : ∀ s1 : State, s1.pc = deserEntry_loopEntry + 260#64 → s1.status = .Running →
      s1.sp = L → s1.trace = s0.trace → s1.readReg64 .x0 = 2#64 →
      s1.readReg64 .x19 = out → s1.readReg64 .x21 = noneCap →
      s1.readReg64 .x23 = L + 1032#64 → s1.readReg64 .x24 = 1#64 →
      s1.readReg64 .x26 = 8#64 → s1.readReg64 .x29 = L + 1808#64 →
      post s1 (step1aPost_loopEntry L p len1 s0)) :
    SepWP (libsignalSessionCode.rebase sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)))
      (deserEntry_loopEntry + 260#64) s0
      (step1aPre_loopEntry L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7)
      post := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  d0_fetches_1a sessionImg0.base H
  rw [fnAddr_deser_eq_loopEntry H] at *
  examples_hide_fetches; unfold step1aPre_loopEntry
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
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by rw [hnone]; simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])) ?_
  unfold step1aPost_loopEntry deserSavedAt_loopEntry; rw [hnone]
  simp only [Reg.x29, Reg.x30, Reg.x28, Reg.x27, Reg.x26, Reg.x25, Reg.x24, Reg.x23,
    Reg.x22, Reg.x21, Reg.x20, Reg.x19]
  ac_rfl

/-! ## 1-Byte Outer Length Varint Fast Path (`+0x15c → +0x254`, `N < 128`) -/

private def step2aPre_loopEntry (L p : BitVec 64) (N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (1 + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)

private def step2aPost_loopEntry (L p : BitVec 64) (N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 2#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)

private theorem step_2a_loopEntry (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (L p out : BitVec 64) (N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = deserEntry_loopEntry + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64)
    (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_pos : 0 < N) (hN_lt : N < 128)
    (hnext : ∀ s' : State, s'.pc = deserEntry_loopEntry + 596#64 → s'.status = .Running →
      s'.sp = L → s'.trace = s.trace → s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 →
      post s' (step2aPost_loopEntry L p N)) :
    SepWP (libsignalSessionCode.rebase sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)))
      (deserEntry_loopEntry + 596#64) s (step2aPre_loopEntry L p N) post := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  d0_fetches_2a sessionImg0.base H
  rw [fnAddr_deser_eq_loopEntry H] at *
  examples_hide_fetches; unfold step2aPre_loopEntry
  have hcbz : (BitVec.ofNat 64 (1 + N) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change 1 + N = 0 at hnat; omega
  have hse := signExtend64_ofNat8_lt_128_loopEntry hN_lt
  have hbit63 : (((BitVec.ofNat 8 N).signExtend 64).getLsbD 63 == true) = false :=
    (signExtend64_bit63_eq_false_iff_loopEntry (BitVec.ofNat 8 N)).mpr (by rw [BitVec.toNat_ofNat]; omega)
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
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step2aPost_loopEntry; ac_rfl

/-! ## 2-Byte Outer Length Varint via `decode_varint_slice` (`+0x15c → +0x254`, `128 ≤ N < 1000`) -/

private def step2bPre_loopEntry (L p : BitVec 64) (N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (2 + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128))

private theorem step_2b_pre_loopEntry (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (L p out : BitVec 64) (N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = deserEntry_loopEntry + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64)
    (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_ge : 128 ≤ N) (hN_lt : N < 1000)
    (hnext : ∀ s' : State, s'.pc = deserEntry_loopEntry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") → s'.status = .Running →
      s'.sp = L → s'.trace = s.trace → s'.readReg64 .lr = deserEntry_loopEntry + 540#64 →
      s'.readReg64 .x0 = L + 1400#64 → s'.readReg64 .x1 = p + 1#64 →
      s'.readReg64 .x2 = BitVec.ofNat 64 (2 + N) → s'.readReg64 .x19 = out →
      s'.readReg64 .x20 = L + 1016#64 → s'.readReg64 .x23 = L + 1032#64 →
      s'.readReg64 .x29 = L + 1808#64 → post s' (step2bPre_loopEntry L p N)) :
    SepWP (libsignalSessionCode.rebase sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)))
      (deserEntry_loopEntry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) s (step2bPre_loopEntry L p N) post := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  d0_fetches_2b_pre sessionImg0.base H
  rw [fnAddr_deser_eq_loopEntry H] at *
  examples_hide_fetches; unfold step2bPre_loopEntry
  have hcbz : (BitVec.ofNat 64 (2 + N) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change 2 + N = 0 at hnat; omega
  have hbit63 :
      (((BitVec.ofNat 8 (N % 128 + 128)).signExtend 64).getLsbD 63 == true) = true :=
    (signExtend64_bit63_eq_true_iff_loopEntry (BitVec.ofNat 8 (N % 128 + 128))).mpr
      (by rw [BitVec.toNat_ofNat]; omega)
  have hhi10 : (10#64).ult (BitVec.ofNat 64 (2 + N)) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 + N < 2 ^ 64 by omega),
      decide_eq_true_eq]; omega
  have hule10 : (BitVec.ofNat 64 (2 + N)).ule 10#64 = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 + N < 2 ^ 64 by omega),
      decide_eq_false_iff_not]; omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])) ?_
  unfold step2bPre_loopEntry; ac_rfl

private def step2bPostPre_loopEntry (L p : BitVec 64) (N : Nat) : SepProp :=
  ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
  ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ 2#64) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (2 + N))

private def step2bPostPost_loopEntry (L p : BitVec 64) (N : Nat) : SepProp :=
  ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
  ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ 2#64) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 3#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N)

private theorem step_2b_post_loopEntry (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (L p out : BitVec 64) (N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = deserEntry_loopEntry + 540#64) (hrun : s.status = .Running)
    (hsp : s.sp = L) (halignL : L &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = L + 1016#64)
    (hx23 : s.readReg64 .x23 = L + 1032#64) (hx29 : s.readReg64 .x29 = L + 1808#64)
    (hN_ge : 128 ≤ N) (hN_lt : N < 1000)
    (hnext : ∀ s' : State, s'.pc = deserEntry_loopEntry + 596#64 → s'.status = .Running →
      s'.sp = L → s'.trace = s.trace → s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 →
      post s' (step2bPostPost_loopEntry L p N)) :
    SepWP (libsignalSessionCode.rebase sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)))
      (deserEntry_loopEntry + 596#64) s (step2bPostPre_loopEntry L p N) post := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  d0_fetches_2b_post sessionImg0.base H
  rw [fnAddr_deser_eq_loopEntry H] at *
  examples_hide_fetches; unfold step2bPostPre_loopEntry
  have hsub2 : BitVec.ofNat 64 (2 + N) - 2#64 = BitVec.ofNat 64 N := by
    rw [Nat.add_comm 2 N, BitVec.ofNat_add]; bv_omega
  have hsub2' : BitVec.ofNat 64 (2 + N) + bv% (2 ^ 64 - 2) = BitVec.ofNat 64 N := by
    rw [Nat.add_comm 2 N, BitVec.ofNat_add]; bv_omega
  have hult2 : (BitVec.ofNat 64 (2 + N)).ult 2#64 = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 + N < 2 ^ 64 by omega),
      decide_eq_false_iff_not]; omega
  have hult_self : (BitVec.ofNat 64 N).ult (BitVec.ofNat 64 N) = false := by simp [BitVec.ult]
  have hsub_self : BitVec.ofNat 64 N - BitVec.ofNat 64 N = 0#64 := by bv_omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step2bPostPost_loopEntry; ac_rfl

/-! ## Memory Splitting and Folding Helpers -/

private theorem memRegion_succ8_loopEntry (a : BitVec 64) (n : Nat) (hn : n < 2000) :
    memRegion a (n + 8) =
      (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) n := by
  rw [Nat.add_comm n 8, memRegion_split a 8 n (by omega), ProofLib.memRegion_eight]

private theorem memRegion_1064_336_cells_loopEntry (L : BitVec 64) :
    ((L + 1056#64) ↦₆₄ noneCap) ∗ memRegion (L + 1064#64) 336 =
      ∃∗ c22 : BitVec 64, ∃∗ c21 : BitVec 64, ∃∗ c20 : BitVec 64, ∃∗ c19 : BitVec 64,
      ∃∗ c18 : BitVec 64, ∃∗ c17 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c15 : BitVec 64,
      ∃∗ c14 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c12 : BitVec 64, ∃∗ c11 : BitVec 64,
      ∃∗ c10 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c7 : BitVec 64,
      ∃∗ c6 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c2 : BitVec 64, ∃∗ c1 : BitVec 64,
        ssUninitCells_loopEntry L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 ∗
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
    simp (discharger := decide) only [memRegion_succ8_loopEntry, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight (L + 1304#64), ProofLib.memRegion_eight (L + 1352#64)]
  conv_lhs =>
    arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2
    simp (discharger := decide) only [memRegion_succ8_loopEntry, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  unfold ssUninitCells_loopEntry
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply congrArg sepExists; funext _)
  ac_rfl

private theorem memRegion_1904_split_loopEntry (L p : BitVec 64) :
    memRegion L 1904 ∗ (p ↦₈ 0x0a#8) =
      ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ u7 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u4 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        step1aPre_loopEntry L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
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
    simp (discharger := decide) only [memRegion_succ8_loopEntry, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 1; arg 1; arg 2; arg 2; arg 1
    simp (discharger := decide) only [memRegion_succ8_loopEntry, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  unfold step1aPre_loopEntry
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply congrArg sepExists; funext _)
  ac_rfl

private theorem stackAt_recDeserialize_split_loopEntry (sp0 : BitVec 64) :
    stackAt sp0 recDeserializeStack =
      stackAt (deserSpL sp0) deserCalleeStack ∗ memRegion (deserSpL sp0) 1904 := by
  change memRegion (sp0 - 65536#64) 65536 =
    memRegion (sp0 - 0x770#64 - 63632#64) 63632 ∗ memRegion (sp0 - 0x770#64) 1904
  rw [memRegion_split (sp0 - 65536#64) 63632 1904 (by decide)]
  have h1 : sp0 - 65536#64 = sp0 - 0x770#64 - 63632#64 := by bv_omega
  have h2 : sp0 - 65536#64 + 63632#64 = sp0 - 0x770#64 := by bv_omega
  rw [h2, h1]

private theorem memRegion_0_1016_intro_loopEntry (L : BitVec 64) :
    (L ↦₆₄ 0#64) ∗ memRegion (L + 8#64) 1008 ⊢ memRegion L 0x3f8 := by
  rw [show (0x3f8 : Nat) = 1016 by decide, memRegion_split L 8 1008 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion L 0#64)

private def deserFixedLocals_loopEntry (L : BitVec 64) : SepProp :=
  memRegion L 0x3f8 ∗
    ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
    prostSSAt A0 (L + 0x420#64) SSV.empty ∗ memRegion (L + 0x6f0#64) 0x20

private theorem step1b_post_entails_loopEntry (L p : BitVec 64) (len1 : Nat) (s0 : State)
    (hL : L = deserSpL s0.sp) :
    ssRawCells_loopEntry L ∗ memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗
      memRegion (L + 1360#64) 24 ∗ deserSavedAt_loopEntry L s0 ∗ (L ↦₆₄ 0#64) ∗
      ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗
      ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
      ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 0x0a#8) ∗ memRegion (L + 8#64) 1008 ∗
      memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ⊢
    ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
      ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ deserFixedLocals_loopEntry L ∗ deserSaved s0 := by
  have hss := prostSSAt_empty_intro_loopEntry L
  have hm0 := memRegion_0_1016_intro_loopEntry L
  have hds : deserSavedAt_loopEntry L s0 = deserSaved s0 := hL ▸ deserSavedAt_eq_loopEntry s0
  unfold deserFixedLocals_loopEntry; rw [hds]
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

private theorem scratch24_368_fold_loopEntry (L v w : BitVec 64) :
    ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
      ((L + 1408#64) ↦₆₄ v) ∗ ((L + 1416#64) ↦₆₄ w) ∗ memRegion (L + 1424#64) 344 ⊢
      memRegion (L + 1400#64) 368 := by
  have h0 : ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) =
      ((L + 1400#64) ↦₆₄ 0#64) := by
    have hs := (pointsTo64_zero_split32_loopEntry (L + 1400#64)).symm
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

private theorem deserLocals_of_2a_loopEntry (L p : BitVec 64) (f : List (BitVec 8))
    (hN : (seedSession f).length < 128) :
    step2aPost_loopEntry L p (seedSession f).length ∗
      ((p + 1#64 + 1#64) ↦ₛ seedSession f) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ deserFixedLocals_loopEntry L =
    deserLocals L p (seedRecord f) (seedSession f) SSV.empty := by
  have hpfx : seedRecord f =
      0x0a#8 :: BitVec.ofNat 8 (seedSession f).length :: seedSession f := by
    unfold seedRecord; rw [pbVarintBody_of_lt_128_loopEntry hN]; rfl
  have hsub : (seedRecord f).length - (seedSession f).length = 2 := by
    rw [hpfx, List.length_cons, List.length_cons]; omega
  have hbytes : (p ↦ₛ seedRecord f) =
      (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 (seedSession f).length) ∗
        ((p + 1#64 + 1#64) ↦ₛ seedSession f) := by
    rw [hpfx, pointsToBytes_cons, pointsToBytes_cons]
  unfold deserLocals Prost.sliceCursorAfter deserFixedLocals_loopEntry step2aPost_loopEntry
  rw [hsub, hbytes,
    show (0x3f8#64 : BitVec 64) = 1016#64 from rfl,
    show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (BitVec.ofNat 64 2 : BitVec 64) = 2#64 from rfl,
    show (0x578#64 : BitVec 64) = 1400#64 from rfl,
    show (0x170 : Nat) = 368 from rfl,
    show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]; ac_rfl

private theorem step2bPostPost_entails_loopEntry (L p : BitVec 64) (N : Nat) :
    step2bPostPost_loopEntry L p N ∗ memRegion (L + 1424#64) 344 ⊢
      memRegion (L + 1400#64) 368 ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
        ((L + 1016#64) ↦₆₄ (p + 3#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N) := by
  unfold step2bPostPost_loopEntry
  refine Entails.trans ?_
    (sepConj_mono_left (Q := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
      ((L + 1016#64) ↦₆₄ (p + 3#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N))
      (scratch24_368_fold_loopEntry L (BitVec.ofNat 64 N) 2#64))
  exact Entails.of_eq (by ac_rfl)

private theorem deserLocals_of_2b_loopEntry (L p : BitVec 64) (f : List (BitVec 8))
    (hN_ge : 128 ≤ (seedSession f).length) (hN_lt : (seedSession f).length < 1000) :
    (step2bPostPost_loopEntry L p (seedSession f).length ∗ memRegion (L + 1424#64) 344) ∗
      ((p + 1#64) ↦ₛ (pbVarintBody 5 (seedSession f).length ++ seedSession f)) ∗
      (p ↦₈ 0x0a#8) ∗ deserFixedLocals_loopEntry L ⊢
    deserLocals L p (seedRecord f) (seedSession f) SSV.empty := by
  refine Entails.trans
    (sepConj_mono_left (step2bPostPost_entails_loopEntry L p (seedSession f).length)) ?_
  have hpfx : seedRecord f =
      0x0a#8 :: (pbVarintBody 5 (seedSession f).length ++ seedSession f) := rfl
  have hvar := pbVarintBody_of_ge_128_loopEntry hN_ge hN_lt
  have hsub : (seedRecord f).length - (seedSession f).length = 3 := by
    rw [hpfx, hvar]; simp only [List.cons_append, List.nil_append, List.length_cons]; omega
  have hbytes : (p ↦ₛ seedRecord f) =
      (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦ₛ (pbVarintBody 5 (seedSession f).length ++ seedSession f)) := by
    rw [hpfx, pointsToBytes_cons]
  unfold deserLocals Prost.sliceCursorAfter deserFixedLocals_loopEntry
  rw [hsub, hbytes,
    show (0x3f8#64 : BitVec 64) = 1016#64 from rfl,
    show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (BitVec.ofNat 64 3 : BitVec 64) = 3#64 from rfl,
    show (0x578#64 : BitVec 64) = 1400#64 from rfl,
    show (0x170 : Nat) = 368 from rfl,
    show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]
  exact Entails.of_eq (by ac_rfl)

private theorem stackAt_deserCallee_split_varint_loopEntry (L : BitVec 64) :
    stackAt L deserCalleeStack =
      stackAt L Prost.decodeVarintSliceStack ∗ memRegion (L - 63632#64) 55360 := by
  change memRegion (L - 63632#64) 63632 =
    memRegion (L - 8272#64) 8272 ∗ memRegion (L - 63632#64) 55360
  rw [memRegion_split (L - 63632#64) 55360 8272 (by decide)]
  have h1 : L - 63632#64 + 55360#64 = L - 8272#64 := by bv_omega
  rw [h1, sepConj_comm]

private theorem allocFailedIn_of_trace_eq_loopEntry {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢; rwa [htr] at h

private theorem allowPanic_frame_trace_loopEntry {s0 sm sf : State} {F R : SepProp}
    (htr : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (allocFailedIn_of_trace_eq_loopEntry htr) h

private theorem step_1_combined_loopEntry (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (x : DeserializeSeedGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (recordProg C ctl abs).fnAddr recDeserializeName) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bs.length)
    (hx8 : s0.readReg64 .x8 = x.out) (hseed : SeedOk x.f) (hbs : x.bs = seedRecord x.f)
    (hal : s0.spAligned = true)
    (hm0 : s0.mem ⊨ (x.p ↦ₛ x.bs) ∗ memRegion x.out 368 ∗ stackAt s0.sp recDeserializeStack ∗ R)
    (hL : (recordProg C ctl abs).CodeLoaded s0.mem) :
    let L := deserSpL s0.sp
    let rest1 := pbVarintBody 5 (seedSession x.f).length ++ seedSession x.f
    ∃ s2, Steps (recordProg C ctl abs) s0 s2 ∧ s2.pc = deserEntry_loopEntry + 348#64 ∧
      s2.status = .Running ∧ s2.sp = L ∧ s2.trace = s0.trace ∧
      s2.readReg64 .x19 = x.out ∧ s2.readReg64 .x23 = L + 1032#64 ∧
      s2.readReg64 .x29 = L + 1808#64 ∧
      (s2.mem ⊨
        (((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
          ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ (x.p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ deserFixedLocals_loopEntry L ∗ deserSaved s0) ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
  intro L rest1
  have hsp0 : s0.sp = L + 1904#64 := by change s0.sp = s0.sp - 0x770#64 + 1904#64; bv_omega
  obtain ⟨halignL, halign1808⟩ := sp_sub_1904_aligned_loopEntry (decide_eq_true_iff.mp hal)
  obtain ⟨hN_lo, hN_hi⟩ := seedSession_length_bounds_loopEntry hseed
  obtain ⟨hvb_lo, hvb_hi⟩ := pbVarintBody_length_bounds_loopEntry 5 (seedSession x.f).length
  have hlen1_pos : 0 < rest1.length := by simp only [rest1, List.length_append]; omega
  have hlen1_lt : rest1.length < 2000 := by simp only [rest1, List.length_append]; omega
  have hbs_cons : x.bs = 0x0a#8 :: rest1 := hbs
  have hx1' : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + rest1.length) := by
    rw [hx1, hbs_cons, List.length_cons, Nat.add_comm]
  have hpc0 : s0.pc = deserEntry_loopEntry := by rw [hpc]; exact fnAddr_deser_eq_loopEntry _
  have hm0a : s0.mem ⊨ (memRegion L 1904 ∗ (x.p ↦₈ 0x0a#8)) ∗
      (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
    rw [hbs_cons, pointsToBytes_cons, stackAt_recDeserialize_split_loopEntry s0.sp] at hm0
    dsimp only [L]; convert hm0 using 1; ac_rfl
  rw [memRegion_1904_split_loopEntry L x.p] at hm0a
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm0a
  rcases hm0a with ⟨w11, w10, w9, w8, w7, w6, w5, w4, w3, w2, w1, w0, u7, u6, u5, u4, u3, u2, u1, u0, hm0b⟩
  have hm0c : s0.mem ⊨
      step1aPre_loopEntry L x.p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
      (memRegion (L + 8#64) 1008 ∗ memRegion (L + 1064#64) 336 ∗
        memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    convert hm0b using 1; ac_rfl
  rcases (step_1a_loopEntry C ctl L x.p x.out rest1.length
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7
      (post := fun s' P => P = step1aPost_loopEntry L x.p rest1.length s0 ∧
        s'.sp = L ∧ s'.trace = s0.trace ∧ s'.readReg64 .x0 = 2#64 ∧
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
      (deserSavedAt_loopEntry L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗
        ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
        ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (x.p ↦₈ 0x0a#8) ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold step1aPost_loopEntry at hm1; convert hm1 using 1; ac_rfl
  rw [memRegion_1064_336_cells_loopEntry L] at hm1a
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1a
  rcases hm1a with ⟨c22, c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11,
    c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, hm1b⟩
  have hm1c : s1.mem ⊨
      ssUninitCells_loopEntry L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 ∗
      ((memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 ∗
        deserSavedAt_loopEntry L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗
        ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
        ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (x.p ↦₈ 0x0a#8) ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32) ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold ssUninitCells_loopEntry at hm1b ⊢; convert hm1b using 1; ac_rfl
  rcases (step_1b_loopEntry C ctl L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
      c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      (post := fun s' P => P = ssRawCells_loopEntry L ∧
        s'.sp = L ∧ s'.trace = s1.trace ∧ s'.readReg64 .x19 = s1.readReg64 .x19 ∧
        s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = s1.readReg64 .x29)
      hpc1 hrun1 hsp1 halignL hx0_1 hx21_1 hx23_1 hx24_1 hx26_1
      (fun s' _ _ hsp' htr' hx19' hx23' hx29' =>
        ⟨rfl, hsp', htr', hx19', hx23', hx29'⟩)).elim hm1c (hst1.codeLoaded hL) with
    ⟨s2, hst2, ⟨hpc2, hrun2, P2, hm2, rfl, hsp2, htr2, hx19_2, hx23_2, hx29_2⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  refine ⟨s2, hst1.trans hst2, hpc2, hrun2, hsp2, htr2.trans htr1,
    hx19_2.trans hx19_1, hx23_2, hx29_2.trans hx29_1, ?_⟩
  rw [← sepConj_assoc] at hm2
  exact Satisfies.mono (sepConj_mono_left (step1b_post_entails_loopEntry L x.p rest1.length s0 rfl)) hm2

end LoopEntryStateSimp

open LoopEntryStateSimp

set_option maxHeartbeats 1600000 in
/-- Steps `SessionRecord::deserialize` (`0x16ed4`) from `deserializeSeedSpec.pre` to `DeserLoop … 0`
at `+0x254`, initializing `RecordStructure` and `prostSSAt A0 (L + 0x420) SSV.empty` and decoding
the outer tag `0x0a` and length varint of `seedRecord f`. -/
theorem deserLoopEntry_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (x : DeserializeSeedGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (recordProg C ctl abs).fnAddr recDeserializeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ deserializeSeedSpec.pre x s0 ∗ R) (hal : s0.spAligned = true) :
    DeserStep C ctl x R s0 s0 (DeserLoop C ctl x R s0 0) abs := by
  intro hL0
  unfold deserializeSeedSpec at hpre; dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hseed, hbs, hF0, hsym0⟩, hm0⟩
  rw [sepConj_assoc, sepConj_assoc] at hm0
  obtain ⟨halignL, _halign1808⟩ := sp_sub_1904_aligned_loopEntry (decide_eq_true_iff.mp hal)
  obtain ⟨hN_lo, hN_hi⟩ := seedSession_length_bounds_loopEntry hseed
  obtain ⟨s2, hst2, hpc2, hrun2, hsp2, htr2, hx19_2, hx23_2, hx29_2, hm2⟩ :=
    step_1_combined_loopEntry C ctl x R s0 hpc hrun hx0 hx1 hx8 hseed hbs hal hm0 hL0
  set L := deserSpL s0.sp
  set N := (seedSession x.f).length
  set rest1 := pbVarintBody 5 N ++ seedSession x.f
  by_cases hN : N < 128
  · have hr1 : rest1 = BitVec.ofNat 8 N :: seedSession x.f := by
      simp only [rest1, pbVarintBody_of_lt_128_loopEntry hN, List.singleton_append]
    have hlen1 : rest1.length = 1 + N := by rw [hr1, List.length_cons, Nat.add_comm]
    have hm2a : s2.mem ⊨ step2aPre_loopEntry L x.p N ∗
        (((x.p + 1#64 + 1#64) ↦ₛ seedSession x.f) ∗ (x.p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ deserFixedLocals_loopEntry L ∗ deserSaved s0 ∗
          memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
      rw [hlen1, hr1, pointsToBytes_cons] at hm2
      unfold step2aPre_loopEntry; convert hm2 using 1; ac_rfl
    rcases (step_2a_loopEntry C ctl L x.p x.out N
        (post := fun s' P => P = step2aPost_loopEntry L x.p N ∧
          s'.sp = L ∧ s'.trace = s2.trace ∧ s'.readReg64 .x19 = x.out ∧
          s'.readReg64 .x20 = 0#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧
          s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 (by omega) hN
        (fun s' _ _ hsp' htr' hx19' hx20' hx23' hx29' =>
          ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim hm2a (hst2.codeLoaded hL0) with
      ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, rfl, hsp3, htr3, hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    refine ⟨s3, hst2.trans hst3, Or.inl ?_⟩
    refine ⟨?_, hrun3, htr3.trans htr2, ?_, (hst2.trans hst3).frozenLoaded hF0,
      hsp3, ?_, hx29_3, hx19_3, hx20_3, hx23_3, ?_⟩
    · unfold deserPC; rw [hpc3, fnAddr_deser_eq_loopEntry]
    · rw [(hst2.trans hst3).symtab_eq, hsym0]
    · rw [State.spAligned, hsp3]; exact decide_eq_true halignL
    · have hloc := deserLocals_of_2a_loopEntry L x.p x.f hN
      have hdrop : (((seedFields x.f).drop 0).flatMap SeedField.enc) = seedSession x.f := by
        rw [List.drop_zero, ← seedSession_eq_fields hseed]
      change s3.mem ⊨ deserLocals L x.p x.bs
          (((seedFields x.f).drop 0).flatMap SeedField.enc) SSV.empty ∗
        memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
      rw [hdrop, hbs, ← hloc]
      convert hm3 using 1; ac_rfl
  · have hN_ge : 128 ≤ N := by omega
    have hr1 : rest1 = BitVec.ofNat 8 (N % 128 + 128) :: BitVec.ofNat 8 (N / 128) :: seedSession x.f := by
      simp only [rest1, pbVarintBody_of_ge_128_loopEntry hN_ge hN_hi, List.cons_append, List.nil_append]
    have hlen1 : rest1.length = 2 + N := by
      rw [hr1, List.length_cons, List.length_cons]; omega
    have hm2_bytes : ((x.p + 1#64) ↦ₛ rest1) =
        ((x.p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128)) ∗
          ((x.p + 1#64 + 1#64) ↦ₛ (BitVec.ofNat 8 (N / 128) :: seedSession x.f)) := by
      rw [hr1, pointsToBytes_cons]
    have hm2c : s2.mem ⊨ step2bPre_loopEntry L x.p N ∗
        (((x.p + 1#64 + 1#64) ↦ₛ (BitVec.ofNat 8 (N / 128) :: seedSession x.f)) ∗
          (x.p ↦₈ 0x0a#8) ∗ memRegion (L + 1400#64) 368 ∗ deserFixedLocals_loopEntry L ∗
          deserSaved s0 ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
      rw [hlen1, hm2_bytes] at hm2
      unfold step2bPre_loopEntry; convert hm2 using 1; ac_rfl
    rcases (step_2b_pre_loopEntry C ctl L x.p x.out N
        (post := fun s' P => P = step2bPre_loopEntry L x.p N ∧
          s'.sp = L ∧ s'.trace = s2.trace ∧ s'.readReg64 .lr = deserEntry_loopEntry + 540#64 ∧
          s'.readReg64 .x0 = L + 1400#64 ∧ s'.readReg64 .x1 = x.p + 1#64 ∧
          s'.readReg64 .x2 = BitVec.ofNat 64 (2 + N) ∧ s'.readReg64 .x19 = x.out ∧
          s'.readReg64 .x20 = L + 1016#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧
          s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 hN_ge hN_hi
        (fun s' _ _ hsp' htr' hlr' hx0' hx1' hx2' hx19' hx20' hx23' hx29' =>
          ⟨rfl, hsp', htr', hlr', hx0', hx1', hx2', hx19', hx20', hx23', hx29'⟩)).elim
        hm2c (hst2.codeLoaded hL0) with
      ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, rfl,
        hsp3, htr3, hlr_3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    have hpc3' : s3.pc = (recordProg C ctl abs).fnAddr Prost.decodeVarintSliceName := by
      rw [hpc3]; exact decodeVarintSlice_fnAddr_eq_loopEntry C ctl
    have hal3 : s3.spAligned = true := by rw [State.spAligned, hsp3]; exact decide_eq_true halignL
    have hx2_3_nat : (s3.readReg64 .x2).toNat = rest1.length := by
      rw [hx2_3, hlen1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen1_lt32 : rest1.length < 4294967296 := by omega
    have hpre_slice : Prost.VarintSlicePre rest1 := Or.inl (by omega)
    let gvar : Prost.DecodeVarintSliceGhost := ⟨L + 1400#64, x.p + 1#64, rest1⟩
    let F_call : SepProp :=
      ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (2 + N)) ∗
        memRegion (L - 63632#64) 55360 ∗ memRegion (L + 1424#64) 344 ∗
        (x.p ↦₈ 0x0a#8) ∗ deserFixedLocals_loopEntry L ∗ deserSaved s0 ∗ memRegion x.out 368
    have hm3_call : s3.mem ⊨ (Prost.decodeVarintSliceSpec A0).pre gvar s3 ∗ (F_call ∗ R) := by
      unfold Prost.decodeVarintSliceSpec; dsimp only [gvar]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_3, hx1_3, hx2_3_nat, Nat.lt_of_lt_of_le hlen1_lt32 (by decide), hpre_slice⟩, ?_⟩
      unfold step2bPre_loopEntry at hm3
      rw [memRegion_split (L + 1400#64) 24 344 (by decide),
        stackAt_deserCallee_split_varint_loopEntry L] at hm3
      have h1424 : L + 1400#64 + 24#64 = L + 1424#64 := by bv_omega
      have hpool : A0.pool = emp := rfl
      rw [h1424] at hm3
      dsimp only [F_call]
      rw [hsp3, hpool, hm2_bytes]
      convert hm3 using 1; ac_rfl
    obtain ⟨s4, hst4, hpost4, -⟩ :=
      hC.1.no_fault_before_outcome gvar (F_call ∗ R) s3 hpc3' hrun3 hm3_call hal3
        ((hst2.trans hst3).codeLoaded hL0)
    rcases hpost4 with ⟨⟨hpc4, _, hrun4⟩, ⟨hsp4, hcs4⟩, hm4⟩ | ⟨hpan4, hm4_pan⟩ | ⟨code, _, hm4_ex⟩ | ⟨_, hm4_oom⟩
    · have hpc4' : s4.pc = deserEntry_loopEntry + 540#64 := by reg_chain
      have hsp4' : s4.sp = L := by reg_chain
      have hx19_4 : s4.readReg64 .x19 = x.out := by reg_chain
      have hx20_4 : s4.readReg64 .x20 = L + 1016#64 := by reg_chain
      have hx23_4 : s4.readReg64 .x23 = L + 1032#64 := by reg_chain
      have hx29_4 : s4.readReg64 .x29 = L + 1808#64 := by reg_chain
      have hdec : decodeVarint rest1 = some (BitVec.ofNat 64 N, seedSession x.f) := by
        rw [hr1]; exact decodeVarint_two_bytes_loopEntry (seedSession x.f) hN_ge hN_hi
      have hsub1 : rest1.length - (seedSession x.f).length = 2 := by
        rw [hlen1]; change (2 + N) - N = 2; omega
      unfold Prost.decodeVarintSliceSpec at hm4; dsimp only [gvar] at hm4
      rw [hdec] at hm4; dsimp only [Prost.varintSliceResultAt] at hm4
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm4
      rcases hm4 with ⟨htr4, hm4⟩
      have hm4a : s4.mem ⊨ step2bPostPre_loopEntry L x.p N ∗
          (memRegion (L + 1424#64) 344 ∗ ((x.p + 1#64) ↦ₛ rest1) ∗ (x.p ↦₈ 0x0a#8) ∗
            deserFixedLocals_loopEntry L ∗ deserSaved s0 ∗ memRegion x.out 368 ∗
            stackAt L deserCalleeStack ∗ R) := by
        dsimp only [F_call] at hm4; unfold step2bPostPre_loopEntry
        have hpool : A0.pool = emp := rfl
        rw [hsp3, hpool, pointsTo64_zero_split32_loopEntry (L + 1400#64), hsub1] at hm4
        rw [stackAt_deserCallee_split_varint_loopEntry L]
        have ha1 : L + 1400#64 + 4#64 = L + 1404#64 := by bv_omega
        have ha2 : L + 1400#64 + 8#64 = L + 1408#64 := by bv_omega
        have ha3 : L + 1400#64 + 16#64 = L + 1416#64 := by bv_omega
        have ha4 : (BitVec.ofNat 64 2 : BitVec 64) = 2#64 := rfl
        rw [ha1, ha2, ha3, ha4] at hm4
        convert hm4 using 1; ac_rfl
      rcases (step_2b_post_loopEntry C ctl L x.p x.out N
          (post := fun s' P => P = step2bPostPost_loopEntry L x.p N ∧
            s'.sp = L ∧ s'.trace = s4.trace ∧ s'.readReg64 .x19 = x.out ∧
            s'.readReg64 .x20 = 0#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧
            s'.readReg64 .x29 = L + 1808#64)
          hpc4' hrun4 hsp4' halignL hx19_4 hx20_4 hx23_4 hx29_4 hN_ge hN_hi
          (fun s' _ _ hsp' htr' hx19' hx20' hx23' hx29' =>
            ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim
          hm4a ((hst2.trans (hst3.trans hst4)).codeLoaded hL0) with
        ⟨s5, hst5, ⟨hpc5, hrun5, P5, hm5, rfl, hsp5, htr5, hx19_5, hx20_5, hx23_5, hx29_5⟩ | ⟨_, hoom⟩⟩
      swap; · exact (not_satisfies_false_sepConj hoom).elim
      refine ⟨s5, (hst2.trans (hst3.trans hst4)).trans hst5, Or.inl ?_⟩
      refine ⟨?_, hrun5, by reg_chain, ?_,
        ((hst2.trans (hst3.trans hst4)).trans hst5).frozenLoaded hF0,
        hsp5, ?_, hx29_5, hx19_5, hx20_5, hx23_5, ?_⟩
      · unfold deserPC; rw [hpc5, fnAddr_deser_eq_loopEntry]
      · rw [((hst2.trans (hst3.trans hst4)).trans hst5).symtab_eq, hsym0]
      · rw [State.spAligned, hsp5]; exact decide_eq_true halignL
      · have hloc := deserLocals_of_2b_loopEntry L x.p x.f hN_ge hN_hi
        have hdrop : (((seedFields x.f).drop 0).flatMap SeedField.enc) = seedSession x.f := by
          rw [List.drop_zero, ← seedSession_eq_fields hseed]
        change s5.mem ⊨ deserLocals L x.p x.bs
            (((seedFields x.f).drop 0).flatMap SeedField.enc) SSV.empty ∗
          memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
        rw [hdrop, hbs]
        have hm5a : s5.mem ⊨
            ((step2bPostPost_loopEntry L x.p N ∗ memRegion (L + 1424#64) 344) ∗
              ((x.p + 1#64) ↦ₛ rest1) ∗ (x.p ↦₈ 0x0a#8) ∗ deserFixedLocals_loopEntry L) ∗
            (memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R) := by
          convert hm5 using 1; ac_rfl
        exact Satisfies.mono (sepConj_mono_left hloc) hm5a
    · refine ⟨s4, (hst2.trans hst3).trans hst4, Or.inr ⟨hpan4, ?_⟩⟩
      unfold Prost.decodeVarintSliceSpec at hm4_pan; dsimp only at hm4_pan
      have hm4_pan' : s4.mem ⊨
          ((⌜allocFailedIn s3 s4 ∧ s3.trace <+: s4.trace⌝ ∗ anyHeap) ∗ F_call) ∗ R := by
        convert hm4_pan using 1; ac_rfl
      exact allowPanic_frame_trace_loopEntry (htr3.trans htr2) hm4_pan'
    · exact False.elim (not_satisfies_false_sepConj hm4_ex)
    · exact False.elim (not_satisfies_false_sepConj hm4_oom)

/-! ## Relocatable `[LibsignalPlacement]` Loop-Entry Proof -/

namespace LoopEntryStateSimp

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_loopEntry sp_setMem_setPC_pre_loopEntry
  readReg64_setPC_pre_loopEntry readReg64_setMem_setPC_pre_loopEntry
  readReg32_setPC_pre_loopEntry readReg32_setMem_setPC_pre_loopEntry
  readReg_setPC_pre_loopEntry readReg_setMem_setPC_pre_loopEntry
  add_1904_sub_96_loopEntry add_1808_sub_1808_loopEntry add_1808_sub_40_loopEntry

private theorem step_1b_placed_loopEntry [LibsignalPlacement] (L : BitVec 64)
    {H : String → Option (State → State)}
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 : BitVec 64)
    {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 260#64) (hrun : s.status = .Running)
    (hsp : s.sp = L) (halign : L &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = 2#64) (hx21 : s.readReg64 .x21 = noneCap)
    (hx23 : s.readReg64 .x23 = L + 1032#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx26 : s.readReg64 .x26 = 8#64)
    (hnext : ∀ s' : State, s'.pc = (blkPl_46).base + 348#64 → s'.status = .Running →
      s'.sp = L → s'.trace = s.trace → s'.readReg64 .x19 = s.readReg64 .x19 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = s.readReg64 .x29 →
      post s' (ssRawCells_loopEntry L)) :
    SepWP (lsProg_46 H)
      ((blkPl_46).base + 348#64) s
      (ssUninitCells_loopEntry L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22)
      post := by
  unfold ssUninitCells_loopEntry
  have hnone : noneCap = bv% (2 ^ 64 - 1) := rfl
  rw [hnone] at hx21 ⊢
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold ssRawCells_loopEntry; rw [hnone]; ac_rfl

private theorem step_1a_placed_loopEntry [LibsignalPlacement]
    {H : String → Option (State → State)}
    (L p out : BitVec 64) (len1 : Nat)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_46).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = L + 1904#64) (halignL : L &&& 15#64 = 0#64)
    (halign1808 : (L + 1808#64) &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + len1))
    (hx8 : s0.readReg64 .x8 = out) (hlen1_pos : 0 < len1) (hlen1_lt : len1 < 2000)
    (hnext : ∀ s1 : State, s1.pc = (blkPl_46).base + 260#64 → s1.status = .Running →
      s1.sp = L → s1.trace = s0.trace → s1.readReg64 .x0 = 2#64 →
      s1.readReg64 .x19 = out → s1.readReg64 .x21 = noneCap →
      s1.readReg64 .x23 = L + 1032#64 → s1.readReg64 .x24 = 1#64 →
      s1.readReg64 .x26 = 8#64 → s1.readReg64 .x29 = L + 1808#64 →
      post s1 (step1aPost_loopEntry L p len1 s0)) :
    SepWP (lsProg_46 H)
      ((blkPl_46).base + 260#64) s0
      (step1aPre_loopEntry L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7)
      post := by
  unfold step1aPre_loopEntry
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
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by rw [hnone]; simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])) ?_
  unfold step1aPost_loopEntry deserSavedAt_loopEntry; rw [hnone]
  simp only [Reg.x29, Reg.x30, Reg.x28, Reg.x27, Reg.x26, Reg.x25, Reg.x24, Reg.x23,
    Reg.x22, Reg.x21, Reg.x20, Reg.x19]
  ac_rfl

private theorem step_2a_placed_loopEntry [LibsignalPlacement]
    {H : String → Option (State → State)}
    (L p out : BitVec 64) (N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64)
    (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_pos : 0 < N) (hN_lt : N < 128)
    (hnext : ∀ s' : State, s'.pc = (blkPl_46).base + 596#64 → s'.status = .Running →
      s'.sp = L → s'.trace = s.trace → s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 →
      post s' (step2aPost_loopEntry L p N)) :
    SepWP (lsProg_46 H)
      ((blkPl_46).base + 596#64) s (step2aPre_loopEntry L p N) post := by
  unfold step2aPre_loopEntry
  have hcbz : (BitVec.ofNat 64 (1 + N) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change 1 + N = 0 at hnat; omega
  have hse := signExtend64_ofNat8_lt_128_loopEntry hN_lt
  have hbit63 : (((BitVec.ofNat 8 N).signExtend 64).getLsbD 63 == true) = false :=
    (signExtend64_bit63_eq_false_iff_loopEntry (BitVec.ofNat 8 N)).mpr (by rw [BitVec.toNat_ofNat]; omega)
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
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step2aPost_loopEntry; ac_rfl

private theorem step_2b_pre_placed_loopEntry [LibsignalPlacement]
    {H : String → Option (State → State)}
    (L p out : BitVec 64) (N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64)
    (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_ge : 128 ≤ N) (hN_lt : N < 1000)
    (hnext : ∀ s' : State, s'.pc = lsmpl.base 76 → s'.status = .Running →
      s'.sp = L → s'.trace = s.trace → s'.readReg64 .lr = (blkPl_46).base + 540#64 →
      s'.readReg64 .x0 = L + 1400#64 → s'.readReg64 .x1 = p + 1#64 →
      s'.readReg64 .x2 = BitVec.ofNat 64 (2 + N) → s'.readReg64 .x19 = out →
      s'.readReg64 .x20 = L + 1016#64 → s'.readReg64 .x23 = L + 1032#64 →
      s'.readReg64 .x29 = L + 1808#64 → post s' (step2bPre_loopEntry L p N)) :
    SepWP (lsProg_46 H) (lsmpl.base 76) s (step2bPre_loopEntry L p N) post := by
  unfold step2bPre_loopEntry
  have hcbz : (BitVec.ofNat 64 (2 + N) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change 2 + N = 0 at hnat; omega
  have hbit63 :
      (((BitVec.ofNat 8 (N % 128 + 128)).signExtend 64).getLsbD 63 == true) = true :=
    (signExtend64_bit63_eq_true_iff_loopEntry (BitVec.ofNat 8 (N % 128 + 128))).mpr
      (by rw [BitVec.toNat_ofNat]; omega)
  have hhi10 : (10#64).ult (BitVec.ofNat 64 (2 + N)) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 + N < 2 ^ 64 by omega),
      decide_eq_true_eq]; omega
  have hule10 : (BitVec.ofNat 64 (2 + N)).ule 10#64 = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 + N < 2 ^ 64 by omega),
      decide_eq_false_iff_not]; omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])) ?_
  unfold step2bPre_loopEntry; ac_rfl

private theorem step_2b_post_placed_loopEntry [LibsignalPlacement]
    {H : String → Option (State → State)}
    (L p out : BitVec 64) (N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 540#64) (hrun : s.status = .Running)
    (hsp : s.sp = L) (halignL : L &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = L + 1016#64)
    (hx23 : s.readReg64 .x23 = L + 1032#64) (hx29 : s.readReg64 .x29 = L + 1808#64)
    (hN_ge : 128 ≤ N) (hN_lt : N < 1000)
    (hnext : ∀ s' : State, s'.pc = (blkPl_46).base + 596#64 → s'.status = .Running →
      s'.sp = L → s'.trace = s.trace → s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 →
      post s' (step2bPostPost_loopEntry L p N)) :
    SepWP (lsProg_46 H)
      ((blkPl_46).base + 596#64) s (step2bPostPre_loopEntry L p N) post := by
  unfold step2bPostPre_loopEntry
  have hsub2 : BitVec.ofNat 64 (2 + N) - 2#64 = BitVec.ofNat 64 N := by
    rw [Nat.add_comm 2 N, BitVec.ofNat_add]; bv_omega
  have hsub2' : BitVec.ofNat 64 (2 + N) + bv% (2 ^ 64 - 2) = BitVec.ofNat 64 N := by
    rw [Nat.add_comm 2 N, BitVec.ofNat_add]; bv_omega
  have hult2 : (BitVec.ofNat 64 (2 + N)).ult 2#64 = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 + N < 2 ^ 64 by omega),
      decide_eq_false_iff_not]; omega
  have hult_self : (BitVec.ofNat 64 N).ult (BitVec.ofNat 64 N) = false := by simp [BitVec.ult]
  have hsub_self : BitVec.ofNat 64 N - BitVec.ofNat 64 N = 0#64 := by bv_omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step2bPostPost_loopEntry; ac_rfl

private theorem step_1_combined_placed_loopEntry [LibsignalPlacement]
    {H : String → Option (State → State)}
    (x : DeserializeSeedGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (blkPl_46).base) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bs.length)
    (hx8 : s0.readReg64 .x8 = x.out) (hseed : SeedOk x.f) (hbs : x.bs = seedRecord x.f)
    (hal : s0.spAligned = true)
    (hm0 : s0.mem ⊨ (x.p ↦ₛ x.bs) ∗ memRegion x.out 368 ∗ stackAt s0.sp recDeserializeStack ∗ R)
    (hL : (lsProg_46 H).CodeLoaded s0.mem) :
    let L := deserSpL s0.sp
    let rest1 := pbVarintBody 5 (seedSession x.f).length ++ seedSession x.f
    ∃ s2, Steps (lsProg_46 H) s0 s2 ∧ s2.pc = (blkPl_46).base + 348#64 ∧
      s2.status = .Running ∧ s2.sp = L ∧ s2.trace = s0.trace ∧
      s2.readReg64 .x19 = x.out ∧ s2.readReg64 .x23 = L + 1032#64 ∧
      s2.readReg64 .x29 = L + 1808#64 ∧
      (s2.mem ⊨
        (((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
          ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ (x.p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ deserFixedLocals_loopEntry L ∗ deserSaved s0) ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
  intro L rest1
  have hsp0 : s0.sp = L + 1904#64 := by change s0.sp = s0.sp - 0x770#64 + 1904#64; bv_omega
  obtain ⟨halignL, halign1808⟩ := sp_sub_1904_aligned_loopEntry (decide_eq_true_iff.mp hal)
  obtain ⟨hN_lo, hN_hi⟩ := seedSession_length_bounds_loopEntry hseed
  obtain ⟨hvb_lo, hvb_hi⟩ := pbVarintBody_length_bounds_loopEntry 5 (seedSession x.f).length
  have hlen1_pos : 0 < rest1.length := by simp only [rest1, List.length_append]; omega
  have hlen1_lt : rest1.length < 2000 := by simp only [rest1, List.length_append]; omega
  have hbs_cons : x.bs = 0x0a#8 :: rest1 := hbs
  have hx1' : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + rest1.length) := by
    rw [hx1, hbs_cons, List.length_cons, Nat.add_comm]
  have hm0a : s0.mem ⊨ (memRegion L 1904 ∗ (x.p ↦₈ 0x0a#8)) ∗
      (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
    rw [hbs_cons, pointsToBytes_cons, stackAt_recDeserialize_split_loopEntry s0.sp] at hm0
    dsimp only [L]; convert hm0 using 1; ac_rfl
  rw [memRegion_1904_split_loopEntry L x.p] at hm0a
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm0a
  rcases hm0a with ⟨w11, w10, w9, w8, w7, w6, w5, w4, w3, w2, w1, w0, u7, u6, u5, u4, u3, u2, u1, u0, hm0b⟩
  have hm0c : s0.mem ⊨
      step1aPre_loopEntry L x.p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
      (memRegion (L + 8#64) 1008 ∗ memRegion (L + 1064#64) 336 ∗
        memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    convert hm0b using 1; ac_rfl
  rcases (step_1a_placed_loopEntry L x.p x.out rest1.length
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7
      (post := fun s' P => P = step1aPost_loopEntry L x.p rest1.length s0 ∧
        s'.sp = L ∧ s'.trace = s0.trace ∧ s'.readReg64 .x0 = 2#64 ∧
        s'.readReg64 .x19 = x.out ∧ s'.readReg64 .x21 = noneCap ∧
        s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x24 = 1#64 ∧
        s'.readReg64 .x26 = 8#64 ∧ s'.readReg64 .x29 = L + 1808#64)
      hpc hrun hsp0 halignL halign1808 hx0 hx1' hx8 hlen1_pos hlen1_lt
      (fun s' _ _ hsp' htr' hx0' hx19' hx21' hx23' hx24' hx26' hx29' =>
        ⟨rfl, hsp', htr', hx0', hx19', hx21', hx23', hx24', hx26', hx29'⟩)).elim hm0c hL with
    ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, rfl,
      hsp1, htr1, hx0_1, hx19_1, hx21_1, hx23_1, hx24_1, hx26_1, hx29_1⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hm1a : s1.mem ⊨ (((L + 1056#64) ↦₆₄ noneCap) ∗ memRegion (L + 1064#64) 336) ∗
      (deserSavedAt_loopEntry L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗
        ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
        ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (x.p ↦₈ 0x0a#8) ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold step1aPost_loopEntry at hm1; convert hm1 using 1; ac_rfl
  rw [memRegion_1064_336_cells_loopEntry L] at hm1a
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1a
  rcases hm1a with ⟨c22, c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11,
    c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, hm1b⟩
  have hm1c : s1.mem ⊨
      ssUninitCells_loopEntry L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 ∗
      ((memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 ∗
        deserSavedAt_loopEntry L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗
        ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
        ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (x.p ↦₈ 0x0a#8) ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32) ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold ssUninitCells_loopEntry at hm1b ⊢; convert hm1b using 1; ac_rfl
  rcases (step_1b_placed_loopEntry L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
      c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      (post := fun s' P => P = ssRawCells_loopEntry L ∧
        s'.sp = L ∧ s'.trace = s1.trace ∧ s'.readReg64 .x19 = s1.readReg64 .x19 ∧
        s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = s1.readReg64 .x29)
      hpc1 hrun1 hsp1 halignL hx0_1 hx21_1 hx23_1 hx24_1 hx26_1
      (fun s' _ _ hsp' htr' hx19' hx23' hx29' =>
        ⟨rfl, hsp', htr', hx19', hx23', hx29'⟩)).elim hm1c (hst1.codeLoaded hL) with
    ⟨s2, hst2, ⟨hpc2, hrun2, P2, hm2, rfl, hsp2, htr2, hx19_2, hx23_2, hx29_2⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  refine ⟨s2, hst1.trans hst2, hpc2, hrun2, hsp2, htr2.trans htr1,
    hx19_2.trans hx19_1, hx23_2, hx29_2.trans hx29_1, ?_⟩
  rw [← sepConj_assoc] at hm2
  exact Satisfies.mono (sepConj_mono_left (step1b_post_entails_loopEntry L x.p rest1.length s0 rfl)) hm2

end LoopEntryStateSimp

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed LoopEntryStateSimp in
set_option maxHeartbeats 1600000 in
/-- Relocatable `SessionRecord::deserialize` (block `46`, `lsProg_46 H`) steps from function entry
to `DeserLoopPlaced … 0` at `(blkPl_46).base + 0x254`. -/
theorem deserLoopEntry_placed_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hC : DeserializeCalleesPlaced H) (x : DeserializeSeedGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (blkPl_46).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ deserializeSeedPlacedSpec.pre x s0 ∗ R) (hal : s0.spAligned = true) :
    DeserStepPlaced x R s0 s0 (DeserLoopPlaced x R s0 0) H := by
  intro hL0
  obtain ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [deserializeSeedRawSpec] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx8, hseed, hbs⟩, hm0⟩
  rw [sepConj_assoc, sepConj_assoc] at hm0
  obtain ⟨halignL, _halign1808⟩ := sp_sub_1904_aligned_loopEntry (decide_eq_true_iff.mp hal)
  obtain ⟨hN_lo, hN_hi⟩ := seedSession_length_bounds_loopEntry hseed
  obtain ⟨s2, hst2, hpc2, hrun2, hsp2, htr2, hx19_2, hx23_2, hx29_2, hm2⟩ :=
    step_1_combined_placed_loopEntry x R s0 hpc hrun hx0 hx1 hx8 hseed hbs hal hm0 hL0
  set L := deserSpL s0.sp
  set N := (seedSession x.f).length
  set rest1 := pbVarintBody 5 N ++ seedSession x.f
  by_cases hN : N < 128
  · have hr1 : rest1 = BitVec.ofNat 8 N :: seedSession x.f := by
      simp only [rest1, pbVarintBody_of_lt_128_loopEntry hN, List.singleton_append]
    have hlen1 : rest1.length = 1 + N := by rw [hr1, List.length_cons, Nat.add_comm]
    have hm2a : s2.mem ⊨ step2aPre_loopEntry L x.p N ∗
        (((x.p + 1#64 + 1#64) ↦ₛ seedSession x.f) ∗ (x.p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ deserFixedLocals_loopEntry L ∗ deserSaved s0 ∗
          memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
      rw [hlen1, hr1, pointsToBytes_cons] at hm2
      unfold step2aPre_loopEntry; convert hm2 using 1; ac_rfl
    rcases (step_2a_placed_loopEntry L x.p x.out N
        (post := fun s' P => P = step2aPost_loopEntry L x.p N ∧
          s'.sp = L ∧ s'.trace = s2.trace ∧ s'.readReg64 .x19 = x.out ∧
          s'.readReg64 .x20 = 0#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧
          s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 (by omega) hN
        (fun s' _ _ hsp' htr' hx19' hx20' hx23' hx29' =>
          ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim hm2a (hst2.codeLoaded hL0) with
      ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, rfl, hsp3, htr3, hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    refine ⟨s3, hst2.trans hst3, Or.inl ?_⟩
    refine ⟨hpc3, hrun3, htr3.trans htr2, hcrl0.of_keepsFrozen (hst2.trans hst3).keepsFrozen,
      hsp3, ?_, hx29_3, hx19_3, hx20_3, hx23_3, ?_⟩
    · rw [State.spAligned, hsp3]; exact decide_eq_true halignL
    · have hloc := deserLocals_of_2a_loopEntry L x.p x.f hN
      have hdrop : (((seedFields x.f).drop 0).flatMap SeedField.enc) = seedSession x.f := by
        rw [List.drop_zero, ← seedSession_eq_fields hseed]
      change s3.mem ⊨ deserLocals L x.p x.bs
          (((seedFields x.f).drop 0).flatMap SeedField.enc) SSV.empty ∗
        memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
      rw [hdrop, hbs, ← hloc]
      convert hm3 using 1; ac_rfl
  · have hN_ge : 128 ≤ N := by omega
    have hr1 : rest1 = BitVec.ofNat 8 (N % 128 + 128) :: BitVec.ofNat 8 (N / 128) :: seedSession x.f := by
      simp only [rest1, pbVarintBody_of_ge_128_loopEntry hN_ge hN_hi, List.cons_append, List.nil_append]
    have hlen1 : rest1.length = 2 + N := by
      rw [hr1, List.length_cons, List.length_cons]; omega
    have hm2_bytes : ((x.p + 1#64) ↦ₛ rest1) =
        ((x.p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128)) ∗
          ((x.p + 1#64 + 1#64) ↦ₛ (BitVec.ofNat 8 (N / 128) :: seedSession x.f)) := by
      rw [hr1, pointsToBytes_cons]
    have hm2c : s2.mem ⊨ step2bPre_loopEntry L x.p N ∗
        (((x.p + 1#64 + 1#64) ↦ₛ (BitVec.ofNat 8 (N / 128) :: seedSession x.f)) ∗
          (x.p ↦₈ 0x0a#8) ∗ memRegion (L + 1400#64) 368 ∗ deserFixedLocals_loopEntry L ∗
          deserSaved s0 ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
      rw [hlen1, hm2_bytes] at hm2
      unfold step2bPre_loopEntry; convert hm2 using 1; ac_rfl
    rcases (step_2b_pre_placed_loopEntry L x.p x.out N
        (post := fun s' P => P = step2bPre_loopEntry L x.p N ∧
          s'.sp = L ∧ s'.trace = s2.trace ∧ s'.readReg64 .lr = (blkPl_46).base + 540#64 ∧
          s'.readReg64 .x0 = L + 1400#64 ∧ s'.readReg64 .x1 = x.p + 1#64 ∧
          s'.readReg64 .x2 = BitVec.ofNat 64 (2 + N) ∧ s'.readReg64 .x19 = x.out ∧
          s'.readReg64 .x20 = L + 1016#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧
          s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 hN_ge hN_hi
        (fun s' _ _ hsp' htr' hlr' hx0' hx1' hx2' hx19' hx20' hx23' hx29' =>
          ⟨rfl, hsp', htr', hlr', hx0', hx1', hx2', hx19', hx20', hx23', hx29'⟩)).elim
        hm2c (hst2.codeLoaded hL0) with
      ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, rfl,
        hsp3, htr3, hlr_3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    have hal3 : s3.spAligned = true := by rw [State.spAligned, hsp3]; exact decide_eq_true halignL
    have hx2_3_nat : (s3.readReg64 .x2).toNat = rest1.length := by
      rw [hx2_3, hlen1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen1_lt32 : rest1.length < 4294967296 := by omega
    have hpre_slice : Prost.VarintSlicePre rest1 := Or.inl (by omega)
    have hcrl3 : LibsignalCodeRoLoaded lsmpl s3.mem := hcrl0.of_keepsFrozen (hst2.trans hst3).keepsFrozen
    have hcall : subroutine_ok (lsProg_46 H) (lsmpl.base 76)
        (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.decodeVarintSliceSpec A0)) :=
      ls_call_ro_of_cl (callerProg := lsProg_46 H) hC.1
    let gvar : Prost.DecodeVarintSliceGhost := ⟨L + 1400#64, x.p + 1#64, rest1⟩
    let F_call : SepProp :=
      ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (2 + N)) ∗
        memRegion (L - 63632#64) 55360 ∗ memRegion (L + 1424#64) 344 ∗
        (x.p ↦₈ 0x0a#8) ∗ deserFixedLocals_loopEntry L ∗ deserSaved s0 ∗ memRegion x.out 368
    have hm3_call : s3.mem ⊨
        (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.decodeVarintSliceSpec A0)).pre
          gvar s3 ∗ (F_call ∗ R) := by
      dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcrl3, ?_⟩
      unfold Prost.decodeVarintSliceSpec; dsimp only [gvar]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_3, hx1_3, hx2_3_nat, Nat.lt_of_lt_of_le hlen1_lt32 (by decide), hpre_slice⟩, ?_⟩
      unfold step2bPre_loopEntry at hm3
      rw [memRegion_split (L + 1400#64) 24 344 (by decide),
        stackAt_deserCallee_split_varint_loopEntry L] at hm3
      have h1424 : L + 1400#64 + 24#64 = L + 1424#64 := by bv_omega
      have hpool : A0.pool = emp := rfl
      rw [h1424] at hm3
      dsimp only [F_call]
      rw [hsp3, hpool, hm2_bytes]
      convert hm3 using 1; ac_rfl
    obtain ⟨s4, hst4, hpost4, -⟩ :=
      hcall.no_fault_before_outcome gvar (F_call ∗ R) s3 hpc3 hrun3 hm3_call hal3
        ((hst2.trans hst3).codeLoaded hL0)
    rcases hpost4 with ⟨⟨hpc4, _, hrun4⟩, ⟨hsp4, hcs4⟩, hm4⟩ | ⟨hpan4, hm4_pan⟩ | ⟨code, _, hm4_ex⟩ | ⟨_, hm4_oom⟩
    · have hpc4' : s4.pc = (blkPl_46).base + 540#64 := by reg_chain
      have hsp4' : s4.sp = L := by reg_chain
      have hx19_4 : s4.readReg64 .x19 = x.out := by reg_chain
      have hx20_4 : s4.readReg64 .x20 = L + 1016#64 := by reg_chain
      have hx23_4 : s4.readReg64 .x23 = L + 1032#64 := by reg_chain
      have hx29_4 : s4.readReg64 .x29 = L + 1808#64 := by reg_chain
      have hdec : decodeVarint rest1 = some (BitVec.ofNat 64 N, seedSession x.f) := by
        rw [hr1]; exact decodeVarint_two_bytes_loopEntry (seedSession x.f) hN_ge hN_hi
      have hsub1 : rest1.length - (seedSession x.f).length = 2 := by
        rw [hlen1]; change (2 + N) - N = 2; omega
      dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hm4
      unfold Prost.decodeVarintSliceSpec at hm4; dsimp only [gvar] at hm4
      rw [hdec] at hm4; dsimp only [Prost.varintSliceResultAt] at hm4
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm4
      rcases hm4 with ⟨htr4, hm4⟩
      have hm4a : s4.mem ⊨ step2bPostPre_loopEntry L x.p N ∗
          (memRegion (L + 1424#64) 344 ∗ ((x.p + 1#64) ↦ₛ rest1) ∗ (x.p ↦₈ 0x0a#8) ∗
            deserFixedLocals_loopEntry L ∗ deserSaved s0 ∗ memRegion x.out 368 ∗
            stackAt L deserCalleeStack ∗ R) := by
        dsimp only [F_call] at hm4; unfold step2bPostPre_loopEntry
        have hpool : A0.pool = emp := rfl
        rw [hsp3, hpool, pointsTo64_zero_split32_loopEntry (L + 1400#64), hsub1] at hm4
        rw [stackAt_deserCallee_split_varint_loopEntry L]
        have ha1 : L + 1400#64 + 4#64 = L + 1404#64 := by bv_omega
        have ha2 : L + 1400#64 + 8#64 = L + 1408#64 := by bv_omega
        have ha3 : L + 1400#64 + 16#64 = L + 1416#64 := by bv_omega
        have ha4 : (BitVec.ofNat 64 2 : BitVec 64) = 2#64 := rfl
        rw [ha1, ha2, ha3, ha4] at hm4
        convert hm4 using 1; ac_rfl
      rcases (step_2b_post_placed_loopEntry L x.p x.out N
          (post := fun s' P => P = step2bPostPost_loopEntry L x.p N ∧
            s'.sp = L ∧ s'.trace = s4.trace ∧ s'.readReg64 .x19 = x.out ∧
            s'.readReg64 .x20 = 0#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧
            s'.readReg64 .x29 = L + 1808#64)
          hpc4' hrun4 hsp4' halignL hx19_4 hx20_4 hx23_4 hx29_4 hN_ge hN_hi
          (fun s' _ _ hsp' htr' hx19' hx20' hx23' hx29' =>
            ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim
          hm4a ((hst2.trans (hst3.trans hst4)).codeLoaded hL0) with
        ⟨s5, hst5, ⟨hpc5, hrun5, P5, hm5, rfl, hsp5, htr5, hx19_5, hx20_5, hx23_5, hx29_5⟩ | ⟨_, hoom⟩⟩
      swap; · exact (not_satisfies_false_sepConj hoom).elim
      have hsteps_all := (hst2.trans (hst3.trans hst4)).trans hst5
      refine ⟨s5, hsteps_all, Or.inl ?_⟩
      refine ⟨hpc5, hrun5, by reg_chain, hcrl0.of_keepsFrozen hsteps_all.keepsFrozen,
        hsp5, ?_, hx29_5, hx19_5, hx20_5, hx23_5, ?_⟩
      · rw [State.spAligned, hsp5]; exact decide_eq_true halignL
      · have hloc := deserLocals_of_2b_loopEntry L x.p x.f hN_ge hN_hi
        have hdrop : (((seedFields x.f).drop 0).flatMap SeedField.enc) = seedSession x.f := by
          rw [List.drop_zero, ← seedSession_eq_fields hseed]
        change s5.mem ⊨ deserLocals L x.p x.bs
            (((seedFields x.f).drop 0).flatMap SeedField.enc) SSV.empty ∗
          memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
        rw [hdrop, hbs]
        have hm5a : s5.mem ⊨
            ((step2bPostPost_loopEntry L x.p N ∗ memRegion (L + 1424#64) 344) ∗
              ((x.p + 1#64) ↦ₛ rest1) ∗ (x.p ↦₈ 0x0a#8) ∗ deserFixedLocals_loopEntry L) ∗
            (memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R) := by
          convert hm5 using 1; ac_rfl
        exact Satisfies.mono (sepConj_mono_left hloc) hm5a
    · refine ⟨s4, (hst2.trans hst3).trans hst4, Or.inr ⟨hpan4, ?_⟩⟩
      dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hm4_pan
      unfold Prost.decodeVarintSliceSpec at hm4_pan; dsimp only at hm4_pan
      have hm4_pan' : s4.mem ⊨
          ((⌜allocFailedIn s3 s4 ∧ s3.trace <+: s4.trace⌝ ∗ anyHeap) ∗ F_call) ∗ R := by
        convert hm4_pan using 1; ac_rfl
      exact allowPanic_frame_trace_loopEntry (htr3.trans htr2) hm4_pan'
    · exact False.elim (not_satisfies_false_sepConj hm4_ex)
    · exact False.elim (not_satisfies_false_sepConj hm4_oom)

end CryptoVerification.E2E.Record.DeserializeSeed
