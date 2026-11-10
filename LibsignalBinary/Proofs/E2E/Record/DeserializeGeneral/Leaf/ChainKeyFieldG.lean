/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.BodyDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.ChainKeyEpilogue
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Tag-3 Field Leaf (`chainKeyFieldG_ok`) for General `message::merge<Chain>`

Proves `chainKeyFieldG_ok` (`+0x120 → +0x120`, `k → k + 1`) for nested `ChainKey` messages (tag `3`,
with optional varint `index` tag `1` and 32-byte `key` tag `2` written into `Option<ChainKey>` at
`a + 0x48`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter BytesMergeOk Int32MergeOk)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? sessionImg0
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.sp_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain

attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## Pure `ChainG`, `ChainField.ck`, and Cursor Helpers -/

theorem chainG_enc_eq_fields_local (c : ChainG) : c.enc = c.fields.flatMap ChainField.enc := by
  unfold ChainG.enc ChainG.fields
  have h4 : (c.keys.map ChainField.key).flatMap ChainField.enc =
      (c.keys.map fun m => lenField 4 (encMessageKey m)).flatten := by
    induction c.keys with
    | nil => rfl
    | cons m ms ih => simp [ChainField.enc, ih]
  simp only [List.flatMap_append, h4, List.append_assoc]
  by_cases hsrk : c.srk = [] <;> by_cases hpriv : c.priv = [] <;>
    rcases hck : c.ck with _ | ⟨i, k⟩ <;>
    simp [hsrk, hpriv, bytesField, msgField, ChainField.enc]

private theorem map_key_getElem_tag_ne_three (keys : List MessageKeyGenerator) (j : Nat)
    (hj : j < (keys.map ChainField.key).length) :
    ((keys.map ChainField.key)[j]'hj).tag ≠ 3 := by
  simp [ChainField.tag]

theorem chainField_tag_three_info (c : ChainG) (k : Nat)
    (hk : k < c.fields.length) (htag : (c.fields[k]'hk).tag = 3) :
    (∃ i key, c.ck = some (i, key) ∧ c.fields[k]'hk = ChainField.ck i key) ∧
    (chainGAfter c k).ck = none := by
  rcases c with ⟨srk, priv, _ | ⟨i, key⟩, keys⟩ <;>
    unfold chainGAfter <;>
    unfold ChainG.fields at hk htag ⊢ <;>
    by_cases hsrk : srk = [] <;> by_cases hpriv : priv = [] <;>
    simp only [hsrk, hpriv, ↓reduceIte, List.nil_append, List.cons_append] at hk htag ⊢
  · exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | k
    · simp [ChainField.tag] at htag
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | k
    · simp [ChainField.tag] at htag
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | _ | k
    · simp [ChainField.tag] at htag
    · simp [ChainField.tag] at htag
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | k
    · exact ⟨⟨i, key, rfl, rfl⟩, rfl⟩
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | _ | k
    · simp [ChainField.tag] at htag
    · exact ⟨⟨i, key, rfl, rfl⟩, rfl⟩
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | _ | k
    · simp [ChainField.tag] at htag
    · exact ⟨⟨i, key, rfl, rfl⟩, rfl⟩
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | _ | _ | k
    · simp [ChainField.tag] at htag
    · simp [ChainField.tag] at htag
    · exact ⟨⟨i, key, rfl, rfl⟩, rfl⟩
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim

theorem chainGAfter_succ (c : ChainG) (k : Nat) (hk : k < c.fields.length) :
    chainGAfter c (k + 1) = (chainGAfter c k).apply (c.fields[k]'hk) := by
  unfold chainGAfter
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem uint32Field_one_eq_pbVarint (i : BitVec 32) :
    uint32Field 1 i = pbVarint 1 i.toNat := by
  unfold uint32Field pbVarint
  by_cases hi : i = 0
  · subst hi; rfl
  · have hi_nat : i.toNat ≠ 0 := by
      intro h; apply hi; apply BitVec.eq_of_toNat_eq; simpa using h
    simp only [hi, hi_nat, ↓reduceIte]
    have hkey : encodeKey 1 .varint = pbKey 1 0 := rfl
    have hbody : encodeVarint (i.setWidth 64) = pbVarintBody 5 i.toNat :=
      (pbVarintBody_u32_eq_encodeVarint_seedChain i).symm
    rw [hkey, hbody]

theorem bytesField_two_eq_pbBytes {key : List (BitVec 8)} (hkey : key.length = 32) :
    bytesField 2 key = pbBytes 2 key := by
  have hne : key ≠ [] := by intro h; subst h; simp at hkey
  have hlt : key.length < 128 := by omega
  unfold bytesField lenField pbBytes pbKey encodeKey WireType.toNat
  simp only [hne, ↓reduceIte]
  rw [encodeVarint_lt128_seedChain key.length hlt]
  rfl

theorem chainField_ck_enc_eq (i : BitVec 32) {key : List (BitVec 8)} (hkey : key.length = 32) :
    let ck_body := pbVarint 1 i.toNat ++ pbBytes 2 key
    (ChainField.ck i key).enc =
      [0x1a#8, BitVec.ofNat 8 ck_body.length] ++ (pbVarint 1 i.toNat ++ pbBytes 2 key) := by
  intro ck_body
  have hck_bounds := ckEnc_length_bounds_seedChain i hkey
  have hck_lt : ck_body.length < 128 := by dsimp [ck_body]; omega
  dsimp only [ChainField.enc]
  rw [uint32Field_one_eq_pbVarint i, bytesField_two_eq_pbBytes hkey]
  change lenField 3 ck_body = [0x1a#8, BitVec.ofNat 8 ck_body.length] ++ ck_body
  unfold lenField encodeKey WireType.toNat
  rw [encodeVarint_lt128_seedChain ck_body.length hck_lt]
  rfl

theorem prostChainGAt_ck_none_eq (a : BitVec 64) (c0 : ChainG) (hck : c0.ck = none) :
    prostChainGAt A0 a c0 =
      vecU8 A0 a c0.srk ∗ vecU8 A0 (a + 0x18#64) c0.priv ∗
      vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (a + 0x30#64) c0.keys ∗
      ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 := by
  unfold prostChainGAt
  rw [hck]

theorem prostChainGAt_apply_ck_eq (a : BitVec 64) (c0 : ChainG) (i : BitVec 32) (key : List (BitVec 8)) :
    prostChainGAt A0 a (c0.apply (ChainField.ck i key)) =
      vecU8 A0 a c0.srk ∗ vecU8 A0 (a + 0x18#64) c0.priv ∗
      vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (a + 0x30#64) c0.keys ∗
      vecU8 A0 (a + 0x48#64) key ∗ ((a + 0x60#64) ↦₃₂ i) ∗ memRegion (a + 0x64#64) 4 := by
  unfold prostChainGAt ChainG.apply
  rfl

/-- Prefix of `c.payload ++ tail` consumed before field `k`. -/
def pfx_k (c : ChainG) (k : Nat) : List (BitVec 8) :=
  encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.fields.take k).flatMap ChainField.enc

/-- Suffix of `c.payload ++ tail` remaining from field `k` onward. -/
def rem_k (c : ChainG) (k : Nat) (tail : List (BitVec 8)) : List (BitVec 8) :=
  ((c.fields.drop k).flatMap ChainField.enc) ++ tail

theorem payload_append_eq_pfx_rem (c : ChainG) (k : Nat) (tail : List (BitVec 8)) :
    c.payload ++ tail = pfx_k c k ++ rem_k c k tail := by
  unfold ChainG.payload pfx_k rem_k
  rw [chainG_enc_eq_fields_local c]
  have htd : c.fields.flatMap ChainField.enc =
      (c.fields.take k).flatMap ChainField.enc ++ (c.fields.drop k).flatMap ChainField.enc := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [htd]
  simp only [List.append_assoc]

theorem rem_k_eq_cons (c : ChainG) (k : Nat) (tail : List (BitVec 8)) (hk : k < c.fields.length) :
    rem_k c k tail = (c.fields[k]'hk).enc ++ rem_k c (k + 1) tail := by
  unfold rem_k
  rw [List.drop_eq_getElem_cons hk, List.flatMap_cons, List.append_assoc]

theorem pfx_k_succ (c : ChainG) (k : Nat) (hk : k < c.fields.length) :
    pfx_k c (k + 1) = pfx_k c k ++ (c.fields[k]'hk).enc := by
  unfold pfx_k
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem combine_tag3_cursor (slot ptr : BitVec 64)
    (pfx b3a b3b b3c afterCk : List (BitVec 8))
    (hb3a_len : b3a.length = 2) :
    let ptr3a := ptr + BitVec.ofNat 64 pfx.length
    let ptr3b := ptr3a + 2#64
    let ptr3c := ptr3b + BitVec.ofNat 64 b3b.length
    let ptrEnd := ptr3c + BitVec.ofNat 64 b3c.length
    (ptr ↦ₛ pfx) ∗
      (ptr3a ↦ₛ b3a) ∗
      (ptr3b ↦ₛ b3b) ∗
      (ptr3c ↦ₛ b3c) ∗
      sliceCursorAt slot ptrEnd afterCk =
    sliceCursorAfter slot ptr
      ((pfx ++ (b3a ++ (b3b ++ b3c))) ++ afterCk) afterCk := by
  intro ptr3a ptr3b ptr3c ptrEnd
  rw [sliceCursorAfter_append_eq_seedChain slot ptr (pfx ++ (b3a ++ (b3b ++ b3c))) afterCk]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  have hp3a : ptr + BitVec.ofNat 64 pfx.length = ptr3a := rfl
  have hp3b : ptr3a + BitVec.ofNat 64 b3a.length = ptr3b := by dsimp [ptr3b]; rw [hb3a_len]
  have hp3c : ptr3b + BitVec.ofNat 64 b3b.length = ptr3c := rfl
  have hpEnd : ptr + BitVec.ofNat 64 (pfx ++ (b3a ++ (b3b ++ b3c))).length = ptrEnd := by
    dsimp [ptrEnd, ptr3c, ptr3b, ptr3a]
    simp only [List.length_append, hb3a_len]
    bv_omega
  rw [hp3a, hp3b, hp3c, hpEnd]
  ac_rfl

theorem sp0_aligned_of_sub_256_aligned {sp0 : BitVec 64} (h : (sp0 - 256#64) &&& 15#64 = 0#64) :
    sp0 &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

/-! ## Segment Steps for Tag 3 (`+0x120 → +0x4c8 → +0x120`) -/

/-- Reg bundle preserved across the inner `ChainKey` loop (`+0x4c8`). -/
def InnerLoopRegs (sp0 bufRef a : BitVec 64) (outerTailLen innerTailLen : Nat) (s : State) : Prop :=
  s.sp = sp0 - 256#64 ∧
  s.readReg64 .x29 = sp0 - 0x60#64 ∧
  s.readReg64 .x19 = bufRef ∧
  s.readReg64 .x20 = a ∧
  s.readReg64 .x21 = 98#64 ∧
  s.readReg64 .x22 = 97#64 ∧
  s.readReg64 .x23 = BitVec.ofNat 64 innerTailLen ∧
  s.readReg64 .x24 = BitVec.ofNat 64 outerTailLen ∧
  s.readReg64 .x25 = sp0 - 0xf8#64 ∧
  s.readReg64 .x26 = 1#64

theorem InnerLoopRegs.of_calleeSaved {sp0 bufRef a : BitVec 64} {outerTailLen innerTailLen : Nat}
    {s1 s2 : State} (h1 : InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s1)
    (hsp2 : s2.sp = sp0 - 256#64) (hcs : CalleeSavedPreserved s1 s2) :
    InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s2 :=
  ⟨hsp2,
   hcs.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.1,
   hcs.1.trans h1.2.2.1,
   hcs.2.1.trans h1.2.2.2.1,
   hcs.2.2.1.trans h1.2.2.2.2.1,
   hcs.2.2.2.1.trans h1.2.2.2.2.2.1,
   hcs.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2⟩

/-- Dummy seed ghost to reuse `step_chainMerge_int32Merge_seedChain` / `step_chainMerge_bytesMerge_seedChain`,
since `chainMergeSeedSpec.onPanic` and `chainMergeGenSpec.onPanic` are both `Serialization.allocPanic`. -/
def dummySeedGhost : ChainMergeGhost :=
  ⟨0#64, ⟨[], [], none⟩, 0#64, 0#64, 0#64, [], []⟩

/-- Outer field 3 header (`[0x1a#8, len]`, `+0x120 → +0x4c8`) with general `afterCk` and `outerTailLen`. -/
theorem step_chainMerge_seg3a_G (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64)
    (ck_body afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hck_lt : ck_body.length < 128)
    (houter_le : outerTailLen ≤ afterCk.length)
    (hlen_lt : (2 + (ck_body.length + afterCk.length)) < 2 ^ 32)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 outerTailLen)
    (hx25 : s0.readReg64 .x25 = sp0 - 0xf8#64)
    (hx26 : s0.readReg64 .x26 = 1#64)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x4c8#64 →
      sm.status = .Running →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x48#64) [] ∗
          ((a + 0x60#64) ↦₃₂ 0#32) ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 ck_body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (ck_body ++ afterCk) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q Qp) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (a + 0x50#64) 24 ∗
        sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q Qp := by
  have hlen_gt : outerTailLen < (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length := by
    simp only [List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 32 := by
    simp only [List.length_cons, List.length_append]; omega
  have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x1a#8 (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk))
  have hrem1_lt : (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 32 := by
    simp only [List.length_cons, List.length_append]; omega
  have hcbz2 := cbz_len_cons_false_seedChain (b0 := BitVec.ofNat 8 ck_body.length)
    (bs1 := ck_body ++ afterCk) hrem1_lt
  have hse0 := signExtend64_ofNat8_lt128_seedChain hck_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hck_lt
  have hsub2 := len_cons_sub_one_seedChain (BitVec.ofNat 8 ck_body.length) (ck_body ++ afterCk)
  have hlen_ck_append : (ck_body ++ afterCk).length = ck_body.length + afterCk.length := List.length_append
  have hule_ck_sub := ule_ofNat_add_right_true_seedChain (m := ck_body.length) (k := afterCk.length) (by omega)
  have hsub_ck_tail := bv_ofNat_add_sub_left_seedChain ck_body.length afterCk.length
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x120 0x144
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x188 0x1ac
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x1d8 0x1dc
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x268 0x2a8
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x49c 0x4ac
  dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25
  have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (1224)) hF hsym ?_
  rw [memRegion24_split_ck_seedChain a]
  unfold sliceCursorAt noneCap
  rw [pointsToBytes_cons, pointsToBytes_cons]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w50
  apply SepWP.exists_elim; intro w58
  apply SepWP.exists_elim; intro w60
  iterate 44 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
    ⟨by simp only [hsp, arm64_norm],
     by simp only [h29, arm64_norm],
     by simp only [h19, arm64_norm],
     by simp only [h20, arm64_norm],
     by simp only [h21, arm64_norm],
     by simp only [h22, arm64_norm],
     by simp only [arm64_norm],
     by simp only [h24, arm64_norm],
     by simp only [h25, arm64_norm],
     by simp only [h26, arm64_norm]⟩)
  unfold sliceCursorAt
  rw [← hlen_ck_append, ← ck_hdr_pointsTo_combine_seedChain ptr ck_body.length]
  have hvec := emptyVec_entails_vecU8_seedChain (a + 0x48#64)
  have h48_8 : (a + 0x48#64) + 8#64 = a + 0x50#64 := by bv_omega
  have h48_16 : (a + 0x48#64) + 16#64 = a + 0x58#64 := by bv_omega
  have hptr2 : ptr + 1#64 + 1#64 = ptr + 2#64 := by bv_omega
  rw [h48_8, h48_16] at hvec
  rw [hptr2]
  have hEq1 :
      bufRef ↦₆₄ slot ∗
        (a + 72#64) ↦₆₄ 0#64 ∗
          (a + 80#64) ↦₆₄ 1#64 ∗
            (a + 88#64) ↦₆₄ 0#64 ∗
              (a + 96#64) ↦₃₂ 0#32 ∗
                memRegion (a + 100#64) 4 ∗
                  slot ↦₆₄ (ptr + 2#64) ∗
                    (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ afterCk).length ∗
                      ptr ↦₈ 26#8 ∗
                        (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length ∗
                          (ptr + 2#64) ↦ₛ (ck_body ++ afterCk) ∗
                            stackAt (sp0 - 256#64) chainMergeSubStack ∗ F =
      (((a + 0x48#64) ↦₆₄ 0#64) ∗ ((a + 0x50#64) ↦₆₄ 1#64) ∗ ((a + 0x58#64) ↦₆₄ 0#64)) ∗
        (bufRef ↦₆₄ slot ∗
          (a + 0x60#64) ↦₃₂ 0#32 ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
          (slot ↦₆₄ (ptr + 2#64) ∗
            (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ afterCk).length ∗
            (ptr + 2#64) ↦ₛ (ck_body ++ afterCk)) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack ∗ F) := by ac_rfl
  have hEq2 :
      vecU8 A0 (a + 0x48#64) [] ∗
        (bufRef ↦₆₄ slot ∗
          (a + 0x60#64) ↦₃₂ 0#32 ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
          (slot ↦₆₄ (ptr + 2#64) ∗
            (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ afterCk).length ∗
            (ptr + 2#64) ↦ₛ (ck_body ++ afterCk)) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack ∗ F) =
      (bufRef ↦₆₄ slot ∗
        vecU8 A0 (a + 0x48#64) [] ∗
        (a + 0x60#64) ↦₃₂ 0#32 ∗
        memRegion (a + 0x64#64) 4 ∗
        (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
        (slot ↦₆₄ (ptr + 2#64) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ afterCk).length ∗
          (ptr + 2#64) ↦ₛ (ck_body ++ afterCk)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F := by ac_rfl
  rw [hEq1, ← hEq2]
  exact sepConj_mono_left hvec

/-- Inner field 1 (`pbVarint 1 i.toNat`, `+0x4c8 → +0x4c8`) preserving `InnerLoopRegs`. -/
theorem step_chainMerge_seg3b_G (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hIM : Prost.Int32MergeOk sessionImg0.base C A0 ctl abs)
    (a bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) (rest afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hlen_lt : (pbVarint 1 i.toNat ++ rest ++ afterCk).length < 2 ^ 32)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x4c8#64)
    (hrun : s0.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s0)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x4c8#64 →
      sm.status = .Running →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest ++ afterCk) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s_init sf ∗ R))) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest ++ afterCk)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s_init sf ∗ R)) := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩
  by_cases hi0 : i = 0#32
  · subst hi0
    have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    rw [hpb0] at hnext ⊢
    simp only [List.nil_append, List.length_nil,
      BitVec.add_zero, pointsToBytes_nil] at hnext ⊢
    refine SepWPp.mono_pre_seedChain ?_ (hnext s0 hpc hrun hF hsym htr hvregs
      ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩)
    exact sep_ac_seedChain (by ac_rfl)
  · have hi_pos : i.toNat ≠ 0 := by
      intro h; apply hi0; apply BitVec.eq_of_toNat_eq; simpa using h
    have hpb : pbVarint 1 i.toNat = 0x08#8 :: pbVarintBody 5 i.toNat := by
      unfold pbVarint; simp [hi_pos]; rfl
    let rem1 : List (BitVec 8) := pbVarintBody 5 i.toNat ++ (rest ++ afterCk)
    have hcons_eq : pbVarint 1 i.toNat ++ (rest ++ afterCk) = 0x08#8 :: rem1 := by
      rw [hpb]; simp [rem1, List.cons_append]
    have hlen_gt : afterCk.length < (0x08#8 :: rem1).length := by
      simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x08#8 :: rem1).length < 2 ^ 32 := by
      rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
    have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
    have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
    have hsub1 := len_cons_sub_one_seedChain 0x08#8 rem1
    refine (?_ :
      (∀ (s1 : State),
        s1.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName +
          bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) →
        s1.status = .Running →
        sessionImg0.FrozenLoaded s1 →
        s1.symtab = sessionImg0.symtab →
        s1.trace = s_init.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s_init →
        s1.readReg64 .lr = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x588#64 →
        (s1.readReg64 .x0).setWidth 8 = 0#8 →
        s1.readReg64 .x1 = a + 0x60#64 →
        s1.readReg64 .x2 = bufRef →
        InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s1 →
        SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s1
          ((((a + 0x60#64) ↦₃₂ 0#32) ∗
            (bufRef ↦₆₄ slot) ∗
            sliceCursorAt slot (ptr + 1#64) rem1 ∗
            stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x08#8) ∗ F))
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
    · intro hnext1
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x4c8 0x4ec
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x530 0x554
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x578 0x584
      dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext1 ⊢
      generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
      examples_hide_fetches
      have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
      have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
      have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
      have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
      have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
      have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23
      have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
      have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25
      have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))) hF hsym ?_
      rw [hcons_eq]
      unfold sliceCursorAt
      rw [pointsToBytes_cons]
      simp only [sepConj_assoc]
      iterate 24 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ⟨by simp only [hsp, arm64_norm],
         by simp only [h29, arm64_norm],
         by simp only [h19, arm64_norm],
         by simp only [h20, arm64_norm],
         by simp only [h21, arm64_norm],
         by simp only [h22, arm64_norm],
         by simp only [h23, arm64_norm],
         by simp only [h24, arm64_norm],
         by simp only [h25, arm64_norm],
         by simp only [h26, arm64_norm]⟩)
      unfold sliceCursorAt
      exact sep_ac_seedChain (by ac_rfl)
    · intro s1 hpc1 hrun1 hF1 hsym1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
      have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest ++ afterCk)).length < 2 ^ 32 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chainMerge_int32Merge_seedChain C ctl hIM
        (a + 0x60#64) bufRef slot (ptr + 1#64) sp0
        ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x588#64)
        0#32 i (rest ++ afterCk) hrem1_lt
        hpc1 hrun1 hregs1.1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
      intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
      have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      have hregs2 := hregs1.of_calleeSaved hsp2 hcs2
      rcases hregs2 with ⟨hsp2, hx29_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2⟩
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x588 0x588
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x4c4 0x4c4
      dsimp only [tripleRatchetProgAt, chainMergeName] at hpc2 hnext ⊢
      generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
      examples_hide_fetches
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29_2
      have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hx19_2
      have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hx20_2
      have h21_2 : s2.readReg64 (Reg.gpr 21#5) = 98#64 := hx21_2
      have h22_2 : s2.readReg64 (Reg.gpr 22#5) = 97#64 := hx22_2
      have h23_2 : s2.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23_2
      have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24_2
      have h25_2 : s2.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25_2
      have h26_2 : s2.readReg64 (Reg.gpr 26#5) = 1#64 := hx26_2
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (1224)) hF2 hsym2 ?_
      iterate 2 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        hF3 hsym3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs2, arm64_norm])
        ⟨by simp only [hsp2, arm64_norm],
         by simp only [h29_2, arm64_norm],
         by simp only [h19_2, arm64_norm],
         by simp only [h20_2, arm64_norm],
         by simp only [h21_2, arm64_norm],
         by simp only [h22_2, arm64_norm],
         by simp only [h23_2, arm64_norm],
         by simp only [h24_2, arm64_norm],
         by simp only [h25_2, arm64_norm],
         by simp only [h26_2, arm64_norm]⟩)
      rw [pbVarint1_ptr_advance_seedChain ptr i.toNat hi_pos,
        ← pbVarint1_pointsTo_combine_seedChain ptr i.toNat hi_pos]
      exact sep_ac_seedChain (by ac_rfl)

/-- Inner field 2 (`pbBytes 2 k`, `+0x4c8 → +0x4c8`) preserving `InnerLoopRegs`. -/
theorem step_chainMerge_seg3c_G (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hBM : Prost.BytesMergeOk sessionImg0 C A0 ctl abs)
    (a bufRef slot ptr sp0 : BitVec 64)
    (k afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hk_lt : k.length < 128)
    (hlen_lt : (pbBytes 2 k ++ afterCk).length < 2 ^ 32)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x4c8#64)
    (hrun : s0.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s0)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x4c8#64 →
      sm.status = .Running →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x48#64) k ∗
          (ptr ↦ₛ pbBytes 2 k) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 k).length) afterCk ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s_init sf ∗ R))) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x48#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 k ++ afterCk) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s_init sf ∗ R)) := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩
  have hpb : pbBytes 2 k = 0x12#8 :: BitVec.ofNat 8 k.length :: k :=
    pbBytes_lt128_eq_seedChain 2 (by decide) k hk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 k.length] ++ k ++ afterCk
  have hcons_eq : pbBytes 2 k ++ afterCk = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : afterCk.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 32 := by
    rw [← hcons_eq]; exact hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x12#8 rem1
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) →
      s1.status = .Running →
      sessionImg0.FrozenLoaded s1 →
      s1.symtab = sessionImg0.symtab →
      s1.trace = s_init.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x570#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a + 0x48#64 →
      s1.readReg64 .x2 = bufRef →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s1 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s1
        ((vecU8 A0 (a + 0x48#64) [] ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x12#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
  · intro hnext1
    chainMerge_fetches_range sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x4c8 0x4ec
    chainMerge_fetches_range sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x530 0x56c
    dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext1 ⊢
    generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
    have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
    have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
    have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23
    have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
    have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25
    have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))) hF hsym ?_
    rw [hcons_eq]
    unfold sliceCursorAt
    rw [pointsToBytes_cons]
    simp only [sepConj_assoc]
    iterate 26 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      ⟨by simp only [hsp, arm64_norm],
       by simp only [h29, arm64_norm],
       by simp only [h19, arm64_norm],
       by simp only [h20, arm64_norm],
       by simp only [h21, arm64_norm],
       by simp only [h22, arm64_norm],
       by simp only [h23, arm64_norm],
       by simp only [h24, arm64_norm],
       by simp only [h25, arm64_norm],
       by simp only [h26, arm64_norm]⟩)
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hF1 hsym1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
    have hrem1_lt : ([BitVec.ofNat 8 k.length] ++ k ++ afterCk).length < 2 ^ 32 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_seedChain C ctl hBM
      (a + 0x48#64) bufRef slot (ptr + 1#64) sp0
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x570#64)
      [] k afterCk hk_lt hrem1_lt
      hpc1 hrun1 hregs1.1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    have hregs2 := hregs1.of_calleeSaved hsp2 hcs2
    rcases hregs2 with ⟨hsp2, hx29_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2⟩
    chainMerge_fetches_range sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x570 0x570
    chainMerge_fetches_range sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x4c4 0x4c4
    dsimp only [tripleRatchetProgAt, chainMergeName] at hpc2 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29_2
    have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hx19_2
    have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hx20_2
    have h21_2 : s2.readReg64 (Reg.gpr 21#5) = 98#64 := hx21_2
    have h22_2 : s2.readReg64 (Reg.gpr 22#5) = 97#64 := hx22_2
    have h23_2 : s2.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23_2
    have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24_2
    have h25_2 : s2.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25_2
    have h26_2 : s2.readReg64 (Reg.gpr 26#5) = 1#64 := hx26_2
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (1224)) hF2 hsym2 ?_
    iterate 2 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      hF3 hsym3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs2, arm64_norm])
      ⟨by simp only [hsp2, arm64_norm],
       by simp only [h29_2, arm64_norm],
       by simp only [h19_2, arm64_norm],
       by simp only [h20_2, arm64_norm],
       by simp only [h21_2, arm64_norm],
       by simp only [h22_2, arm64_norm],
       by simp only [h23_2, arm64_norm],
       by simp only [h24_2, arm64_norm],
       by simp only [h25_2, arm64_norm],
       by simp only [h26_2, arm64_norm]⟩)
    rw [pbBytes_ptr_advance_seedChain 2 (by decide) ptr k hk_lt,
      ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr k hk_lt]
    exact sep_ac_seedChain (by ac_rfl)

/-- Inner loop exit (`+0x4c8 → +0x120`) when remaining slice is `afterCk`. -/
theorem step_chainMerge_seg3d_G (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64)
    (afterCk : List (BitVec 8)) (outerTailLen : Nat)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x4c8#64)
    (hrun : s0.status = .Running)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s0)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr afterCk ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q Qp) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr afterCk ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q Qp := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x4c8 0x4d4
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x5a8 0x5b0
  dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23
  have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25
  have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (288)) hF hsym ?_
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 7 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm])
    hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
    ⟨by simp only [hsp, arm64_norm],
     by simp only [h29, arm64_norm],
     by simp only [h19, arm64_norm],
     by simp only [h20, arm64_norm],
     by simp only [h21, arm64_norm],
     by simp only [h22, arm64_norm],
     by simp only [h23, arm64_norm],
     by simp only [h24, arm64_norm],
     by simp only [h25, arm64_norm],
     by simp only [h26, arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

/-! ## Main Leaf Theorem (`chainKeyFieldG_ok`) -/

theorem chainKeyFieldG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length) (htag : (x.c.fields[k]'hk).tag = 3)
    (hs : ChainLoopG C ctl x R s0 k s) :
    ChainStepG C ctl x R s0 s (ChainLoopG C ctl x R s0 (k + 1)) abs := by
  obtain ⟨_, hIM, hBM, _⟩ := hC
  rcases hs with ⟨hpc, hrun, htr, hvregs, hsym, hF, hsp, hal, hx29, hx19, hx20, hx24,
    hx21, hx22, hx25, hx26, hcOk, hlen_lt, hmem⟩
  intro hL
  have hsp_sub_align : (s0.sp - 256#64) &&& 15#64 = 0#64 := by
    have : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    simpa [hsp] using this
  have hsp0_align : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sub_256_aligned hsp_sub_align
  obtain ⟨⟨i, key, hck_some, hfl_eq⟩, hck_none⟩ := chainField_tag_three_info x.c k hk htag
  have hkey_len : key.length = 32 := hcOk.2.2.1 (i, key) hck_some
  have hkey_lt : key.length < 128 := by omega
  have hck_bounds := ckEnc_length_bounds_seedChain i hkey_len
  let b3b : List (BitVec 8) := pbVarint 1 i.toNat
  let b3c : List (BitVec 8) := pbBytes 2 key
  let ck_body : List (BitVec 8) := b3b ++ b3c
  have hck_lt : ck_body.length < 128 := by dsimp [ck_body, b3b, b3c]; omega
  let b3a : List (BitVec 8) := [0x1a#8, BitVec.ofNat 8 ck_body.length]
  let pfx : List (BitVec 8) := pfx_k x.c k
  let afterCk : List (BitVec 8) := rem_k x.c (k + 1) x.tail
  have hfl_enc : (x.c.fields[k]'hk).enc = b3a ++ (b3b ++ b3c) := by
    rw [hfl_eq]
    exact chainField_ck_enc_eq i hkey_len
  have hrem_k : rem_k x.c k x.tail = 0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk) := by
    rw [rem_k_eq_cons x.c k x.tail hk, hfl_enc]
    dsimp [b3a, ck_body]
  have hpay_eq : x.c.payload ++ x.tail = pfx ++ rem_k x.c k x.tail :=
    payload_append_eq_pfx_rem x.c k x.tail
  have houter_le : x.tail.length ≤ afterCk.length := by
    dsimp [afterCk, rem_k]
    simp only [List.length_append]
    omega
  have hlen_lt3a : (2 + (ck_body.length + afterCk.length)) < 2 ^ 32 := by
    have h1 := hlen_lt
    rw [hpay_eq, hrem_k] at h1
    simp only [List.length_append, List.length_cons] at h1
    omega
  have hlen_lt3b : (b3b ++ b3c ++ afterCk).length < 2 ^ 32 := by
    have h1 : (b3b ++ b3c ++ afterCk).length = ck_body.length + afterCk.length :=
      List.length_append
    omega
  have hlen_lt3c : (b3c ++ afterCk).length < 2 ^ 32 := by
    simp only [List.length_append] at hlen_lt3b ⊢
    omega
  let c0 : ChainG := chainGAfter x.c k
  let ptr3a : BitVec 64 := x.ptr + BitVec.ofNat 64 pfx.length
  let ptr3b : BitVec 64 := ptr3a + 2#64
  let ptr3c : BitVec 64 := ptr3b + BitVec.ofNat 64 b3b.length
  let ptrEnd : BitVec 64 := ptr3c + BitVec.ofNat 64 b3c.length
  have hcur_init :
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) =
      (x.ptr ↦ₛ pfx) ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) := by
    change sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rem_k x.c k x.tail) = _
    rw [hpay_eq, sliceCursorAfter_append_eq_seedChain x.slot x.ptr pfx (rem_k x.c k x.tail), hrem_k]
  have hmem_init : s.mem ⊨
      (((x.bufRef ↦₆₄ x.slot) ∗
        ((x.a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (x.a + 0x50#64) 24 ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        (vecU8 A0 x.a c0.srk ∗ vecU8 A0 (x.a + 0x18#64) c0.priv ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chainMergeSavedRegs s0.sp s0)) ∗ R := by
    change s.mem ⊨
      prostChainGAt A0 x.a c0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      stackAt (s0.sp - 256#64) chainMergeSubStack ∗ chainMergeSavedRegs s0.sp s0 ∗ R at hmem
    rw [prostChainGAt_ck_none_eq x.a c0 hck_none, hcur_init] at hmem
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  have hfull : SepWPp (recordProg C ctl abs) (chainPC C ctl 0x120#64) s
      (((x.bufRef ↦₆₄ x.slot) ∗
        ((x.a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (x.a + 0x50#64) 24 ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        (vecU8 A0 x.a c0.srk ∗ vecU8 A0 (x.a + 0x18#64) c0.priv ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chainMergeSavedRegs s0.sp s0))
      (fun sf Pf =>
        sessionImg0.FrozenLoaded sf ∧ sf.symtab = sessionImg0.symtab ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        InnerLoopRegs s0.sp x.bufRef x.a x.tail.length afterCk.length sf ∧
        (Pf ⊢ prostChainGAt A0 x.a (chainGAfter x.c (k + 1)) ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
            (((x.c.fields.drop (k + 1)).flatMap ChainField.enc) ++ x.tail) ∗
          stackAt (s0.sp - 0x100#64) chainMergeSubStack ∗ chainMergeSavedRegs s0.sp s0))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s0 sf ∗ R)) := by
    have hpc' : s.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64 := hpc
    refine step_chainMerge_seg3a_G C ctl x.a x.bufRef x.slot ptr3a s0.sp
      ck_body afterCk x.tail.length hck_lt houter_le hlen_lt3a
      hpc' hrun hsp hF hsym htr hvregs hx29 hx19 hx20 hx21 hx22 hx24 hx25 hx26 ?_
    intro s4 hpc4 hrun4 hF4 hsym4 htr4 hvregs4 hregs4
    refine SepWPp.mono_pre_seedChain
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        ((x.a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt x.slot ptr3b (b3b ++ (b3c ++ afterCk)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        ((ptr3a ↦ₛ b3a) ∗
          vecU8 A0 (x.a + 0x48#64) [] ∗
          memRegion (x.a + 0x64#64) 4 ∗
          vecU8 A0 x.a c0.srk ∗ vecU8 A0 (x.a + 0x18#64) c0.priv ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chainMergeSavedRegs s0.sp s0)))
      (by
        have hck_eq : ck_body ++ afterCk = b3b ++ (b3c ++ afterCk) := by
          simp [ck_body, b3b, b3c, List.append_assoc]
        dsimp only [ptr3b, b3a]
        rw [hck_eq]
        exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3b_G C ctl hIM x.a x.bufRef x.slot ptr3b s0.sp
      i b3c afterCk x.tail.length hlen_lt3b
      hpc4 hrun4 hsp0_align hF4 hsym4 htr4 hvregs4 hregs4 ?_
    intro s5 hpc5 hrun5 hF5 hsym5 htr5 hvregs5 hregs5
    refine SepWPp.mono_pre_seedChain
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        vecU8 A0 (x.a + 0x48#64) [] ∗
        sliceCursorAt x.slot ptr3c (b3c ++ afterCk) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        ((ptr3a ↦ₛ b3a) ∗
          (ptr3b ↦ₛ b3b) ∗
          ((x.a + 0x60#64) ↦₃₂ i) ∗
          memRegion (x.a + 0x64#64) 4 ∗
          vecU8 A0 x.a c0.srk ∗ vecU8 A0 (x.a + 0x18#64) c0.priv ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chainMergeSavedRegs s0.sp s0)))
      (by dsimp only [ptr3c, b3b]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3c_G C ctl hBM x.a x.bufRef x.slot ptr3c s0.sp
      key afterCk x.tail.length hkey_lt hlen_lt3c
      hpc5 hrun5 hsp0_align hF5 hsym5 htr5 hvregs5 hregs5 ?_
    intro s6 hpc6 hrun6 hF6 hsym6 htr6 hvregs6 hregs6
    refine SepWPp.mono_pre_seedChain
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd afterCk ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        ((ptr3a ↦ₛ b3a) ∗
          (ptr3b ↦ₛ b3b) ∗
          (ptr3c ↦ₛ b3c) ∗
          vecU8 A0 (x.a + 0x48#64) key ∗
          ((x.a + 0x60#64) ↦₃₂ i) ∗
          memRegion (x.a + 0x64#64) 4 ∗
          vecU8 A0 x.a c0.srk ∗ vecU8 A0 (x.a + 0x18#64) c0.priv ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chainMergeSavedRegs s0.sp s0)))
      (by dsimp only [ptrEnd, b3c]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3d_G C ctl x.a x.bufRef x.slot ptrEnd s0.sp
      afterCk x.tail.length hpc6 hrun6 hF6 hsym6 htr6 hvregs6 hregs6 ?_
    intro sf hpcf hrunf hFf hsymf htrf hvregsf hregsf
    refine SepWPp.done hpcf hrunf ⟨hFf, hsymf, htrf, hvregsf, hregsf, ?_⟩
    have hc_succ : chainGAfter x.c (k + 1) = c0.apply (ChainField.ck i key) := by
      rw [chainGAfter_succ x.c k hk, hfl_eq]
    rw [hc_succ, prostChainGAt_apply_ck_eq x.a c0 i key]
    have hcur_end := combine_tag3_cursor x.slot x.ptr pfx b3a b3b b3c afterCk rfl
    dsimp only at hcur_end
    have htotal_end : (pfx ++ (b3a ++ (b3b ++ b3c))) ++ afterCk = x.c.payload ++ x.tail := by
      rw [← hfl_enc, ← pfx_k_succ x.c k hk]
      exact (payload_append_eq_pfx_rem x.c (k + 1) x.tail).symm
    rw [htotal_end] at hcur_end
    change _ ⊢
      (vecU8 A0 x.a c0.srk ∗ vecU8 A0 (x.a + 0x18#64) c0.priv ∗
        vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 0x30#64) c0.keys ∗
        vecU8 A0 (x.a + 0x48#64) key ∗ ((x.a + 0x60#64) ↦₃₂ i) ∗ memRegion (x.a + 0x64#64) 4) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) afterCk ∗
      stackAt (s0.sp - 256#64) chainMergeSubStack ∗ chainMergeSavedRegs s0.sp s0
    rw [← hcur_end]
    dsimp only [ptr3a, ptr3b, ptr3c, ptrEnd]
    exact sep_ac_seedChain (by ac_rfl)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem_init hL
  rcases hex with ⟨hpcf, hrunf, Pf, hmf, hFf, hsymf, htrf, hvregsf, hregsf, hentf⟩ | ⟨hpan, Pf, hmf, htrf⟩ | ⟨_, hoom⟩
  · rcases hregsf with ⟨hspf, hx29f, hx19f, hx20f, hx21f, hx22f, _, hx24f, hx25f, hx26f⟩
    have half : sf.spAligned = true := by
      rw [State.spAligned, hspf, ← hsp]
      exact hal
    have hmemf := Satisfies.mono (sepConj_mono_left hentf) hmf
    simp only [sepConj_assoc] at hmemf
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, htrf, hvregsf, hsymf, hFf, hspf, half, hx29f, hx19f, hx20f,
      hx24f, hx21f, hx22f, hx25f, hx26f, hcOk, hlen_lt, hmemf⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan, htrf hmf⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG
