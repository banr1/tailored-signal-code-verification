/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.BodyDefs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Fields
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Seed `SessionRecord::deserialize` Field-Loop Iteration (`+0x254 → +0x254`)

Proves `deserLoopIter_ok` and `deserLoopIter_placed_ok`, stepping `SessionRecord::deserialize`
(`0x16ed4`, block `46`) across one field `(seedFields f)[k]` at loop head `+0x254` via the single-byte
key fast path and `SessionStructure::merge_field` (`0x581c`) to `DeserLoop … (k + 1)`.
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

namespace LoopIterStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pre_loopIter (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_pre_loopIter (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pre_loopIter (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_pre_loopIter (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pre_loopIter (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_pre_loopIter (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pre_loopIter (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_pre_loopIter (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setPC_pre_loopIter (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_setPC_pre_loopIter (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by
  cases s; rfl

section Fetch

open Lean Meta Elab Command Tactic

gen_decodes libsignalSessionCode_tree diter [(ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize" + 596) → (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize" + 632), (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize" + 700) → (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize" + 748)]

elab "diter_fetches " b:term:max H:term:max : tactic => do
  let off := num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")
  let ranges := [(596, 40), (700, 52)]
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn ← `(ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize")
  for (start, len) in ranges do
    for i in [0 : len / 4] do
      let k := start + 4 * i
      let dec := mkIdent (.str `CryptoVerification.E2E.Record.DeserializeSeed.LoopIterStateSimp
        s!"diter_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
      let kq := Syntax.mkNumLit (toString k)
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

end Fetch

/-! ## Entry and Callee Address Normalization -/

@[irreducible] def deserEntry_loopIter : BitVec 64 := bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")

theorem fnAddr_recDeserialize_eq_deserEntry_loopIter (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase sessionImg0.base H).fnAddr recDeserializeName =
      deserEntry_loopIter := by
  unfold deserEntry_loopIter
  rw [Program.fnAddr_rebase, EntryAux.sessionImg0_base, (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize")]
  rfl

theorem deserPC_eq_deserEntry_loopIter (C : Crypto) (ctl : BitVec 64)
    (off : BitVec 64) :
    deserPC C ctl off = deserEntry_loopIter + off := by
  unfold deserPC recordProg tripleRatchetProgAt
  rw [fnAddr_recDeserialize_eq_deserEntry_loopIter]

theorem mergeField_fnAddr_eq_loopIter (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)} :
    deserEntry_loopIter + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) =
      (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName := by
  unfold deserEntry_loopIter
  rw [tripleRatchetProgAt, Program.fnAddr_rebase, EntryAux.sessionImg0_base, (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")]
  rfl

/-! ## Pure `SeedField` and `ssvAfter` Helpers -/

def keyByte_loopIter (fl : SeedField) : BitVec 8 :=
  BitVec.ofNat 8 (fl.tag * 8 + if fl.wt = .varint then 0 else 2)

theorem enc_eq_keyByte_cons_loopIter (fl : SeedField) :
    fl.enc = keyByte_loopIter fl :: fl.payload := by
  unfold SeedField.enc pbKey keyByte_loopIter
  rfl

theorem drop_flatMap_enc_loopIter {f : List (BitVec 8)} {k : Nat}
    (hk : k < (seedFields f).length) :
    ((seedFields f).drop k).flatMap SeedField.enc =
      (seedFields f)[k].enc ++ ((seedFields f).drop (k + 1)).flatMap SeedField.enc := by
  rw [List.drop_eq_getElem_cons hk, List.flatMap_cons]

theorem ssvAfter_succ_loopIter {f : List (BitVec 8)} {k : Nat}
    (hk : k < (seedFields f).length) :
    ssvAfter f (k + 1) = (ssvAfter f k).apply (seedFields f)[k] := by
  simp only [ssvAfter, List.take_succ_eq_append_getElem hk, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem seedFields_fresh_loopIter (f : List (BitVec 8)) (k : Nat)
    (hk : k < (seedFields f).length) :
    ((seedFields f)[k] matches .sender _ → (ssvAfter f k).sender = none) ∧
      ((seedFields f)[k] matches .pending _ → (ssvAfter f k).pending = none) ∧
      ((seedFields f)[k] matches .recv _ → (ssvAfter f k).recv = []) := by
  by_cases h96 : f.getD 96 0 = 1 <;>
    by_cases h197 : f.getD 197 0 = 1 <;>
    by_cases h266 : f.getD 266 0 = 1 <;>
    (simp only [seedFields, h96, h197, h266, ite_true, ite_false, List.length_append,
       List.length_cons, List.length_nil] at hk
     have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
     rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
       (try omega) <;>
       (simp only [ssvAfter, seedFields, h96, h197, h266, ite_true, ite_false]
        refine ⟨?_, ?_, ?_⟩ <;> (intro h; first | rfl | nomatch h)))

theorem rem_length_lt_loopIter {f : List (BitVec 8)} (hf : SeedOk f) (k : Nat) :
    (((seedFields f).drop k).flatMap SeedField.enc).length < 16384 := by
  have h1 := (SeedLengthFacts.seedSession_length_bounds f).2
  rw [seedSession_eq_fields hf, ← List.take_append_drop k (seedFields f),
    List.flatMap_append, List.length_append] at h1
  omega

theorem payload_rest_length_lt_loopIter {f : List (BitVec 8)} (hf : SeedOk f) {k : Nat}
    (hk : k < (seedFields f).length) :
    ((seedFields f)[k].payload ++ ((seedFields f).drop (k + 1)).flatMap SeedField.enc).length <
      16384 := by
  have h := rem_length_lt_loopIter hf k
  rw [drop_flatMap_enc_loopIter hk, enc_eq_keyByte_cons_loopIter, List.cons_append,
    List.length_cons] at h
  omega

/-! ## Spatial Cursor and Stack Helpers -/

def preBytes_loopIter (f : List (BitVec 8)) (k : Nat) : List (BitVec 8) :=
  pbKey 1 2 ++ pbVarintBody 5 (seedSession f).length ++
    ((seedFields f).take k).flatMap SeedField.enc

def curPtr_loopIter (p : BitVec 64) (f : List (BitVec 8)) (k : Nat) : BitVec 64 :=
  p + BitVec.ofNat 64 (preBytes_loopIter f k).length

theorem bs_eq_preBytes_append_loopIter {bs f : List (BitVec 8)} (hf : SeedOk f)
    (hbs : bs = seedRecord f) (k : Nat) :
    bs = preBytes_loopIter f k ++ ((seedFields f).drop k).flatMap SeedField.enc := by
  have hs : seedSession f =
      ((seedFields f).take k).flatMap SeedField.enc ++
        ((seedFields f).drop k).flatMap SeedField.enc := by
    rw [← List.flatMap_append, List.take_append_drop]
    exact seedSession_eq_fields hf
  rw [hbs, seedRecord, preBytes_loopIter, List.append_assoc, List.append_assoc, ← hs,
    ← List.append_assoc]

theorem bs_sub_rem_length_loopIter {bs f : List (BitVec 8)} (hf : SeedOk f)
    (hbs : bs = seedRecord f) (k : Nat) :
    bs.length - (((seedFields f).drop k).flatMap SeedField.enc).length =
      (preBytes_loopIter f k).length := by
  rw [bs_eq_preBytes_append_loopIter hf hbs k, List.length_append]
  omega

theorem sliceCursorAfter_split_key_loopIter (L p : BitVec 64) {bs f : List (BitVec 8)}
    (hf : SeedOk f) (hbs : bs = seedRecord f) {k : Nat} (hk : k < (seedFields f).length) :
    Prost.sliceCursorAfter (L + 0x3f8#64) p bs
      (((seedFields f).drop k).flatMap SeedField.enc) =
      ((L + 0x3f8#64) ↦₆₄ curPtr_loopIter p f k) ∗
        ((L + 0x400#64) ↦₆₄ BitVec.ofNat 64
          (((seedFields f)[k].payload ++
            ((seedFields f).drop (k + 1)).flatMap SeedField.enc).length + 1)) ∗
        (curPtr_loopIter p f k ↦₈ keyByte_loopIter (seedFields f)[k]) ∗
        ((curPtr_loopIter p f k + 1#64) ↦ₛ
          ((seedFields f)[k].payload ++ ((seedFields f).drop (k + 1)).flatMap SeedField.enc)) ∗
        (p ↦ₛ preBytes_loopIter f k) := by
  unfold Prost.sliceCursorAfter
  have hsub := bs_sub_rem_length_loopIter hf hbs k
  have hrem : ((seedFields f).drop k).flatMap SeedField.enc =
      keyByte_loopIter (seedFields f)[k] ::
        ((seedFields f)[k].payload ++ ((seedFields f).drop (k + 1)).flatMap SeedField.enc) := by
    rw [drop_flatMap_enc_loopIter hk, enc_eq_keyByte_cons_loopIter, List.cons_append]
  have hbs_split : (p ↦ₛ bs) =
      (p ↦ₛ preBytes_loopIter f k) ∗
        (curPtr_loopIter p f k ↦₈ keyByte_loopIter (seedFields f)[k]) ∗
        ((curPtr_loopIter p f k + 1#64) ↦ₛ
          ((seedFields f)[k].payload ++ ((seedFields f).drop (k + 1)).flatMap SeedField.enc)) := by
    conv_lhs => rw [bs_eq_preBytes_append_loopIter hf hbs k, hrem]
    rw [pointsToBytes_append, ← curPtr_loopIter, pointsToBytes_cons]
  have ha : L + 0x3f8#64 + 8#64 = L + 0x400#64 := by bv_omega
  rw [hsub, ← curPtr_loopIter, ha, hbs_split, hrem, List.length_cons]
  ac_rfl

theorem sliceCursorAfter_unsplit_key_loopIter (L p : BitVec 64) {bs f : List (BitVec 8)}
    (hf : SeedOk f) (hbs : bs = seedRecord f) {k : Nat} (hk : k < (seedFields f).length) :
    Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr_loopIter p f k + 1#64)
      ((seedFields f)[k].payload ++ ((seedFields f).drop (k + 1)).flatMap SeedField.enc)
      (((seedFields f).drop (k + 1)).flatMap SeedField.enc) ∗
      (curPtr_loopIter p f k ↦₈ keyByte_loopIter (seedFields f)[k]) ∗
      (p ↦ₛ preBytes_loopIter f k) =
    Prost.sliceCursorAfter (L + 0x3f8#64) p bs
      (((seedFields f).drop (k + 1)).flatMap SeedField.enc) := by
  let fl := (seedFields f)[k]
  let rest := ((seedFields f).drop (k + 1)).flatMap SeedField.enc
  have hrem : ((seedFields f).drop k).flatMap SeedField.enc =
      keyByte_loopIter fl :: (fl.payload ++ rest) := by
    rw [drop_flatMap_enc_loopIter hk, enc_eq_keyByte_cons_loopIter, List.cons_append]
  have hbs_eq : bs = preBytes_loopIter f k ++ (keyByte_loopIter fl :: (fl.payload ++ rest)) := by
    rw [bs_eq_preBytes_append_loopIter hf hbs k, hrem]
  have hpay_sub : (fl.payload ++ rest).length - rest.length = fl.payload.length := by
    rw [List.length_append]; omega
  have hbs_sub : bs.length - rest.length =
      (preBytes_loopIter f k).length + 1 + fl.payload.length := by
    rw [hbs_eq, List.length_append, List.length_cons, List.length_append]; omega
  have hptr : curPtr_loopIter p f k + 1#64 +
      BitVec.ofNat 64 ((fl.payload ++ rest).length - rest.length) =
      p + BitVec.ofNat 64 (bs.length - rest.length) := by
    rw [hpay_sub, hbs_sub, curPtr_loopIter]
    have hadd : BitVec.ofNat 64 ((preBytes_loopIter f k).length + 1 + fl.payload.length) =
        BitVec.ofNat 64 (preBytes_loopIter f k).length + 1#64 + BitVec.ofNat 64 fl.payload.length := by
      rw [BitVec.ofNat_add, BitVec.ofNat_add]
    rw [hadd]
    bv_omega
  have hbs_pts : (p ↦ₛ bs) =
      (p ↦ₛ preBytes_loopIter f k) ∗
        (curPtr_loopIter p f k ↦₈ keyByte_loopIter fl) ∗
        ((curPtr_loopIter p f k + 1#64) ↦ₛ (fl.payload ++ rest)) := by
    conv_lhs => rw [hbs_eq]
    rw [pointsToBytes_append, ← curPtr_loopIter, pointsToBytes_cons]
  unfold Prost.sliceCursorAfter
  rw [hptr, hbs_pts]
  ac_rfl

@[irreducible] def deserCalleeUnused_loopIter (L : BitVec 64) : SepProp :=
  memRegion (L - 63632#64) 47248

theorem stackAt_deserCallee_split_loopIter (L : BitVec 64) :
    stackAt L deserCalleeStack =
      deserCalleeUnused_loopIter L ∗ stackAt L mergeFieldStack := by
  unfold stackAt deserCalleeUnused_loopIter deserCalleeStack recDeserializeStack mergeFieldStack
  have hsplit := memRegion_split (L - 63632#64) 47248 16384 (by decide)
  have ha : L - 63632#64 + 47248#64 = L - 16384#64 := by bv_omega
  rw [show (65536 - 0x770 : Nat) = 47248 + 16384 by rfl,
    show BitVec.ofNat 64 (47248 + 16384) = 63632#64 by rfl, hsplit, ha]

@[irreducible] def deserFixed_loopIter (L : BitVec 64) : SepProp :=
  memRegion L 0x3f8 ∗
    ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
    memRegion (L + 0x578#64) 0x170 ∗ memRegion (L + 0x6f0#64) 0x20

@[irreducible] def deserOutRegion_loopIter (out : BitVec 64) : SepProp :=
  memRegion out 368

theorem deserOutRegion_eq_loopIter (out : BitVec 64) :
    memRegion out 368 = deserOutRegion_loopIter out := by
  unfold deserOutRegion_loopIter; rfl

theorem deserLocals_decomp_loopIter (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSV) :
    deserLocals L p bs rest v =
      Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗
      prostSSAt A0 (L + 0x420#64) v ∗
      ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
      deserFixed_loopIter L := by
  unfold deserLocals deserFixed_loopIter
  generalize memRegion L 0x3f8 = m1
  generalize memRegion (L + 0x578#64) 0x170 = m2
  generalize memRegion (L + 0x6f0#64) 0x20 = m3
  ac_rfl

def stepPre_loopIter (L curPtr : BitVec 64) (kb : BitVec 8) (n : Nat) : SepProp :=
  ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
    ((L + 0x3f8#64) ↦₆₄ curPtr) ∗
    ((L + 0x400#64) ↦₆₄ BitVec.ofNat 64 (n + 1)) ∗
    (curPtr ↦₈ kb)

theorem ule_zero_ofNat_succ_loopIter {n : Nat} (hn : n < 16384) :
    (BitVec.ofNat 64 (n + 1)).ule 0#64 = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_zero,
    Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 64)]
  omega

@[local arm64_norm]
theorem ofNat_succ_sub_one_loopIter (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add]; bv_omega

@[local arm64_norm]
theorem keyByte_signExtend_lsb63_loopIter (fl : SeedField) :
    (BitVec.signExtend 64 (keyByte_loopIter fl)).getLsbD 63 = false := by
  cases fl <;> simp [keyByte_loopIter, SeedField.tag, SeedField.wt]

@[local arm64_norm]
theorem keyByte_signExtend_lsr32_loopIter (fl : SeedField) :
    (BitVec.signExtend 64 (keyByte_loopIter fl)) >>> 32 = 0#64 := by
  cases fl <;> simp [keyByte_loopIter, SeedField.tag, SeedField.wt]

@[local arm64_norm]
theorem keyByte_signExtend_and7_ule6_loopIter (fl : SeedField) :
    (6#64).ule (BitVec.signExtend 64 (keyByte_loopIter fl) &&& 7#64) = false := by
  cases fl <;> simp [keyByte_loopIter, SeedField.tag, SeedField.wt]

@[local arm64_norm]
theorem keyByte_signExtend_tag_w1_loopIter (fl : SeedField) :
    BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (keyByte_loopIter fl))) >>> 3)) =
      BitVec.ofNat 64 fl.tag := by
  cases fl <;> simp [keyByte_loopIter, SeedField.tag, SeedField.wt]

@[local arm64_norm]
theorem tag_zeroExtend_ofNat32_loopIter (fl : SeedField) :
    BitVec.zeroExtend 64 (BitVec.ofNat 32 fl.tag) = BitVec.ofNat 64 fl.tag := by
  cases fl <;> simp [SeedField.tag]

@[local arm64_norm]
theorem tag_ofNat64_beq0_loopIter (fl : SeedField) :
    (BitVec.ofNat 64 fl.tag == 0#64) = false := by
  cases fl <;> simp [SeedField.tag]

@[local arm64_norm]
theorem tag_ofNat64_setWidth32_loopIter (fl : SeedField) :
    (BitVec.ofNat 64 fl.tag).setWidth 32 = BitVec.ofNat 32 fl.tag := by
  cases fl <;> simp [SeedField.tag]

def stepPost_loopIter (L curPtr : BitVec 64) (kb : BitVec 8) (n : Nat) : SepProp :=
  ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
    ((L + 0x3f8#64) ↦₆₄ (curPtr + 1#64)) ∗
    ((L + 0x400#64) ↦₆₄ BitVec.ofNat 64 n) ∗
    (curPtr ↦₈ kb)

theorem step_254_to_2e8_loopIter (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (L curPtr : BitVec 64) (fl : SeedField) (n : Nat) (s : State)
    {post : State → SepProp → Prop}
    (hpc : s.pc = deserEntry_loopIter + 596#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = L + 0x710#64)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hx23 : s.readReg64 .x23 = L + 0x408#64)
    (hn : n < 16384)
    (hnext : ∀ sm : State,
      sm.pc = deserEntry_loopIter + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .lr = deserEntry_loopIter + 748#64 →
      sm.readReg64 .x0 = L + 0x420#64 →
      (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 fl.tag →
      (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 fl.wt.toNat →
      sm.readReg64 .x3 = L + 0x6e8#64 →
      (sm.readReg64 .x4).setWidth 32 = 99#32 →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = 0#64 →
      sm.readReg64 .x23 = L + 0x408#64 →
      sm.readReg64 .x29 = L + 0x710#64 →
      post sm (stepPost_loopIter L curPtr (keyByte_loopIter fl) n)) :
    SepWP (recordProg C ctl abs) (deserEntry_loopIter + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))) s
      (stepPre_loopIter L curPtr (keyByte_loopIter fl) n) post := by
  have hule := ule_zero_ofNat_succ_loopIter hn
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  diter_fetches sessionImg0.base H
  change SepWP (libsignalSessionCode.rebase sessionImg0.base H)
    (deserEntry_loopIter + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))) s
    (stepPre_loopIter L curPtr (keyByte_loopIter fl) n) post
  rw [fnAddr_recDeserialize_eq_deserEntry_loopIter H] at *
  examples_hide_fetches
  unfold stepPre_loopIter
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  exact hnext _
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]; cases fl <;> simp [keyByte_loopIter, SeedField.tag, SeedField.wt, WireType.toNat])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])

theorem step_2ec_loopIter (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (s2 : State) {P : SepProp} {post : State → SepProp → Prop}
    (hpc2 : s2.pc = deserEntry_loopIter + 748#64)
    (hrun2 : s2.status = .Running)
    (hx0_2 : s2.readReg64 .x0 = 0#64)
    (hnext : ∀ sf : State,
      sf.pc = deserEntry_loopIter + 596#64 →
      sf.status = .Running →
      sf.sp = s2.sp →
      (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) →
      sf.readReg64 .x19 = s2.readReg64 .x19 →
      sf.readReg64 .x20 = s2.readReg64 .x20 →
      sf.readReg64 .x23 = s2.readReg64 .x23 →
      sf.readReg64 .x29 = s2.readReg64 .x29 →
      post sf P) :
    SepWP (recordProg C ctl abs) (deserEntry_loopIter + 596#64) s2 P post := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  diter_fetches sessionImg0.base H
  change SepWP (libsignalSessionCode.rebase sessionImg0.base H)
    (deserEntry_loopIter + 596#64) s2 P post
  rw [fnAddr_recDeserialize_eq_deserEntry_loopIter H] at *
  examples_hide_fetches
  wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  exact hnext _
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])

theorem sep_perm1_loopIter (m0 m1 m2 m3 m4 m5 ss fix out un stk sav R : SepProp) :
    ((m1 ∗ m2 ∗ m3 ∗ m4 ∗ m5) ∗ ss ∗ m0 ∗ fix) ∗ out ∗ (un ∗ stk) ∗ sav ∗ R =
      (m0 ∗ m1 ∗ m2 ∗ m3) ∗ (m5 ∗ ss ∗ m4 ∗ fix ∗ out ∗ un ∗ stk ∗ sav ∗ R) := by
  ac_rfl

theorem sep_perm2_loopIter (m0 m1 m2 m3 m4 m5 ss fix out un stk sav R : SepProp) :
    (m0 ∗ m1 ∗ m2 ∗ m3) ∗ (m5 ∗ ss ∗ m4 ∗ fix ∗ out ∗ un ∗ stk ∗ sav ∗ R) =
      (ss ∗ m0 ∗ (m1 ∗ m2 ∗ m4) ∗ stk) ∗ ((m3 ∗ m5 ∗ fix ∗ out ∗ un ∗ sav) ∗ R) := by
  ac_rfl

theorem sep_perm3_loopIter (m0 cur m3 m5 ss fix out un stk sav R : SepProp) :
    (ss ∗ m0 ∗ cur ∗ stk) ∗ ((m3 ∗ m5 ∗ fix ∗ out ∗ un ∗ sav) ∗ R) =
      ((cur ∗ m3 ∗ m5) ∗ ss ∗ m0 ∗ fix) ∗ out ∗ (un ∗ stk) ∗ sav ∗ R := by
  ac_rfl

end LoopIterStateSimp

open LoopIterStateSimp in
/-- Advances `DeserLoop` from `k` to `k + 1` (`k < (seedFields f).length`) across one field key byte
and one `SessionStructure::merge_field` call at `+0x2e8`. -/
theorem deserLoopIter_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hMF : MergeFieldSeedOk C ctl (fun _ => True) abs) (x : DeserializeSeedGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hf : SeedOk x.f) (hbs : x.bs = seedRecord x.f)
    (hk : k < (seedFields x.f).length) (hs : DeserLoop C ctl x R s0 k s) :
    DeserStep C ctl x R s0 s (DeserLoop C ctl x R s0 (k + 1)) abs := by
  obtain ⟨hpc, hrun, htr, hsym, hF, hsp, hal, hx29, hx19, hx20, hx23, hmem⟩ := hs
  let L := deserSpL s0.sp
  let fl := (seedFields x.f)[k]
  let rest := ((seedFields x.f).drop (k + 1)).flatMap SeedField.enc
  let payRest := fl.payload ++ rest
  let curPtr := curPtr_loopIter x.p x.f k
  have hpc_entry : s.pc = deserEntry_loopIter + 596#64 := by
    rw [hpc, deserPC_eq_deserEntry_loopIter]
  have hn_lt : payRest.length < 16384 := payload_rest_length_lt_loopIter hf hk
  set F_loop : SepProp :=
    (x.p ↦ₛ preBytes_loopIter x.f k) ∗
      prostSSAt A0 (L + 0x420#64) (ssvAfter x.f k) ∗
      ((curPtr + 1#64) ↦ₛ payRest) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIter L ∗ stackAt L mergeFieldStack ∗
      deserSaved s0 ∗ R
  have hmem1 : s.mem ⊨ stepPre_loopIter L curPtr (keyByte_loopIter fl) payRest.length ∗ F_loop := by
    change s.mem ⊨ deserLocals L x.p x.bs (((seedFields x.f).drop k).flatMap SeedField.enc)
        (ssvAfter x.f k) ∗
      memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R at hmem
    rw [deserLocals_decomp_loopIter, deserOutRegion_eq_loopIter,
      sliceCursorAfter_split_key_loopIter L x.p hf hbs hk,
      stackAt_deserCallee_split_loopIter L, sep_perm1_loopIter] at hmem
    exact hmem
  intro hL
  rcases (step_254_to_2e8_loopIter C ctl L curPtr fl payRest.length s
      (post := fun sm Pm =>
        sm.pc = deserEntry_loopIter + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) ∧
        sm.status = .Running ∧
        sm.sp = s.sp ∧
        sm.trace = s.trace ∧
        sm.readReg64 .lr = deserEntry_loopIter + 748#64 ∧
        sm.readReg64 .x0 = L + 0x420#64 ∧
        (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 fl.tag ∧
        (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 fl.wt.toNat ∧
        sm.readReg64 .x3 = L + 0x6e8#64 ∧
        (sm.readReg64 .x4).setWidth 32 = 99#32 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = 0#64 ∧
        sm.readReg64 .x23 = L + 0x408#64 ∧
        sm.readReg64 .x29 = L + 0x710#64 ∧
        Pm = stepPost_loopIter L curPtr (keyByte_loopIter fl) payRest.length)
      hpc_entry hrun hx29 hx20 hx23 hn_lt
      (fun _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 =>
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, rfl⟩)).elim hmem1 hL with
    ⟨sm, hsteps1, ⟨-, -, Pm, hmm, hpcm, hrunm, hspm, htrm, hlrm,
      hx0m, hx1m, hx2m, hx3m, hx4m, hx19m, hx20m, hx23m, hx29m, hPm⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  subst hPm
  have hFm : sessionImg0.FrozenLoaded sm := hsteps1.frozenLoaded hF
  have hsymm : sm.symtab = sessionImg0.symtab := hsteps1.symtab_eq.trans hsym
  have hLm : (recordProg C ctl abs).CodeLoaded sm.mem := hsteps1.codeLoaded hL
  have hspm_L : sm.sp = L := hspm.trans hsp
  have hal_m : sm.spAligned = true := by
    simp only [State.spAligned] at hal ⊢
    rwa [hspm]
  have hcall : subroutine_ok (recordProg C ctl abs)
      (deserEntry_loopIter + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))) (mergeFieldSeedSpec (fun _ => True)) := by
    rw [mergeField_fnAddr_eq_loopIter C ctl]
    exact hMF
  let g : MergeFieldGhost :=
    ⟨L + 0x420#64, ssvAfter x.f k, fl, L + 0x6e8#64, L + 0x3f8#64, curPtr + 1#64, rest, x.f⟩
  set F_mf : SepProp :=
    (curPtr ↦₈ keyByte_loopIter fl) ∗
      (x.p ↦ₛ preBytes_loopIter x.f k) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIter L ∗ deserSaved s0
  have hfresh := seedFields_fresh_loopIter x.f k hk
  have hpay_lt32 : (fl.payload ++ rest).length < 2 ^ 32 :=
    Nat.lt_trans hn_lt (by decide)
  have hpre_mf : sm.mem ⊨ (mergeFieldSeedSpec (fun _ => True)).pre g sm ∗ (F_mf ∗ R) := by
    dsimp only [mergeFieldSeedSpec, g]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hx1m, hx2m, hx3m, hx4m, trivial, hf, List.getElem_mem hk,
      hfresh.1, hfresh.2.1, hfresh.2.2, hpay_lt32, hFm, hsymm⟩, ?_⟩
    rw [hspm_L]
    unfold Prost.sliceCursorAt
    have ha : L + 0x3f8#64 + 8#64 = L + 0x400#64 := by bv_omega
    rw [ha]
    dsimp only [stepPost_loopIter, F_loop] at hmm
    dsimp only [F_mf]
    rw [← sep_perm2_loopIter]
    exact hmm
  obtain ⟨s2, hsteps2, hout, -⟩ :=
    hcall.no_fault_before_outcome g (F_mf ∗ R) sm hpcm hrunm hpre_mf hal_m hLm
  rcases hout with ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hpost2⟩ | ⟨hpan2, hpost2⟩ | ⟨code, _, hpost2⟩ | ⟨_, hpost2⟩
  · rw [hlrm] at hpc2
    dsimp only [mergeFieldSeedSpec, g] at hpost2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost2
    obtain ⟨⟨htr2, hx0_2⟩, hmem2⟩ := hpost2
    have hL2 : (recordProg C ctl abs).CodeLoaded s2.mem := hsteps2.codeLoaded hLm
    rcases (step_2ec_loopIter C ctl s2
        (P := prostSSAt A0 (L + 0x420#64) ((ssvAfter x.f k).apply fl) ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
          stackAt sm.sp mergeFieldStack)
        (post := fun sf P_f =>
          sf.pc = deserEntry_loopIter + 596#64 ∧
          sf.status = .Running ∧
          sf.sp = s2.sp ∧
          (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) ∧
          sf.readReg64 .x19 = s2.readReg64 .x19 ∧
          sf.readReg64 .x20 = s2.readReg64 .x20 ∧
          sf.readReg64 .x23 = s2.readReg64 .x23 ∧
          sf.readReg64 .x29 = s2.readReg64 .x29 ∧
          P_f = (prostSSAt A0 (L + 0x420#64) ((ssvAfter x.f k).apply fl) ∗
            ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
            Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
            stackAt sm.sp mergeFieldStack))
        hpc2 hrun2 hx0_2
        (fun _ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩)).elim hmem2 hL2 with
      ⟨sf, hsteps3, ⟨-, -, P_f, hmf, hpcf, hrunf, hspf, ⟨htrf, _⟩,
        hx19f, hx20f, hx23f, hx29f, hPf⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    subst hPf
    have hsteps_all : Steps (recordProg C ctl abs) s sf := (hsteps1.trans hsteps2).trans hsteps3
    have hsp_sf : sf.sp = L := by reg_chain
    have hsp_s : sf.sp = s.sp := by reg_chain
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned] at hal ⊢
      rwa [hsp_s]
    refine ⟨sf, hsteps_all, Or.inl ?_⟩
    refine ⟨?_, hrunf, by reg_chain, hsteps_all.symtab_eq.trans hsym, hsteps_all.frozenLoaded hF,
      hsp_sf, hal_sf, by reg_chain, by reg_chain, by reg_chain, by reg_chain, ?_⟩
    · rw [deserPC_eq_deserEntry_loopIter]; exact hpcf
    · change sf.mem ⊨ deserLocals L x.p x.bs
          (((seedFields x.f).drop (k + 1)).flatMap SeedField.enc) (ssvAfter x.f (k + 1)) ∗
        memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
      rw [deserLocals_decomp_loopIter, deserOutRegion_eq_loopIter,
        ssvAfter_succ_loopIter hk, ← sliceCursorAfter_unsplit_key_loopIter L x.p hf hbs hk,
        stackAt_deserCallee_split_loopIter L, ← sep_perm3_loopIter]
      rw [hspm_L] at hmf
      exact hmf
  · have hsteps_all : Steps (recordProg C ctl abs) s s2 := hsteps1.trans hsteps2
    refine ⟨s2, hsteps_all, Or.inr ⟨hpan2, ?_⟩⟩
    dsimp only [mergeFieldSeedSpec, deserializeSeedSpec, Serialization.allocPanic] at hpost2 ⊢
    rw [← sepConj_assoc] at hpost2
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hpost2
    rw [allocFailedIn, htrm, htr] at ha
    rw [htrm, htr] at hp
    exact ⟨ha, hp⟩
  · exact (not_satisfies_false_sepConj hpost2).elim
  · exact (not_satisfies_false_sepConj hpost2).elim

/-! ## Relocatable `[LibsignalPlacement]` Loop-Iteration Proof -/

namespace LoopIterStateSimp

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_loopIter sp_setMem_setPC_pre_loopIter
  readReg64_setPC_pre_loopIter readReg64_setMem_setPC_pre_loopIter
  readReg32_setPC_pre_loopIter readReg32_setMem_setPC_pre_loopIter
  readReg_setPC_pre_loopIter readReg_setMem_setPC_pre_loopIter
  calleeSavedVRegs_setPC_pre_loopIter calleeSavedVRegs_setMem_setPC_pre_loopIter

attribute [local arm64_norm]
  ofNat_succ_sub_one_loopIter keyByte_signExtend_lsb63_loopIter
  keyByte_signExtend_lsr32_loopIter keyByte_signExtend_and7_ule6_loopIter
  keyByte_signExtend_tag_w1_loopIter tag_zeroExtend_ofNat32_loopIter
  tag_ofNat64_beq0_loopIter tag_ofNat64_setWidth32_loopIter

theorem step_254_to_2e8_placed_loopIter [LibsignalPlacement]
    {H : String → Option (State → State)}
    (L curPtr : BitVec 64) (fl : SeedField) (n : Nat) (s : State)
    {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 596#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = L + 0x710#64)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hx23 : s.readReg64 .x23 = L + 0x408#64)
    (hn : n < 16384)
    (hnext : ∀ sm : State,
      sm.pc = lsmpl.base 15 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .lr = (blkPl_46).base + 748#64 →
      sm.readReg64 .x0 = L + 0x420#64 →
      (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 fl.tag →
      (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 fl.wt.toNat →
      sm.readReg64 .x3 = L + 0x6e8#64 →
      (sm.readReg64 .x4).setWidth 32 = 99#32 →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = 0#64 →
      sm.readReg64 .x23 = L + 0x408#64 →
      sm.readReg64 .x29 = L + 0x710#64 →
      post sm (stepPost_loopIter L curPtr (keyByte_loopIter fl) n)) :
    SepWP (lsProg_46 H) (lsmpl.base 15) s
      (stepPre_loopIter L curPtr (keyByte_loopIter fl) n) post := by
  have hule := ule_zero_ofNat_succ_loopIter hn
  unfold stepPre_loopIter
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  exact hnext _
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]; cases fl <;> simp [keyByte_loopIter, SeedField.tag, SeedField.wt, WireType.toNat])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])

theorem step_2ec_placed_loopIter [LibsignalPlacement]
    {H : String → Option (State → State)}
    (s2 : State) {P : SepProp} {post : State → SepProp → Prop}
    (hpc2 : s2.pc = (blkPl_46).base + 748#64)
    (hrun2 : s2.status = .Running)
    (hx0_2 : s2.readReg64 .x0 = 0#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_46).base + 596#64 →
      sf.status = .Running →
      sf.sp = s2.sp →
      (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) →
      sf.readReg64 .x19 = s2.readReg64 .x19 →
      sf.readReg64 .x20 = s2.readReg64 .x20 →
      sf.readReg64 .x23 = s2.readReg64 .x23 →
      sf.readReg64 .x29 = s2.readReg64 .x29 →
      post sf P) :
    SepWP (lsProg_46 H) ((blkPl_46).base + 596#64) s2 P post := by
  wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  exact hnext _
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])

end LoopIterStateSimp

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed LoopIterStateSimp in
/-- Relocatable `[LibsignalPlacement]` proof of one field iteration of `SessionRecord::deserialize`
(block `46`, `lsProg_46 H`). -/
theorem deserLoopIter_placed_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hMF : MergeFieldSeedPlacedOk (fun _ => True) H) (x : DeserializeSeedGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hf : SeedOk x.f) (hbs : x.bs = seedRecord x.f)
    (hk : k < (seedFields x.f).length) (hs : DeserLoopPlaced x R s0 k s) :
    DeserStepPlaced x R s0 s (DeserLoopPlaced x R s0 (k + 1)) H := by
  obtain ⟨hpc, hrun, htr, hcrl, hsp, hal, hx29, hx19, hx20, hx23, hmem⟩ := hs
  let L := deserSpL s0.sp
  let fl := (seedFields x.f)[k]
  let rest := ((seedFields x.f).drop (k + 1)).flatMap SeedField.enc
  let payRest := fl.payload ++ rest
  let curPtr := curPtr_loopIter x.p x.f k
  have hpc_entry : s.pc = (blkPl_46).base + 596#64 := hpc
  have hn_lt : payRest.length < 16384 := payload_rest_length_lt_loopIter hf hk
  set F_loop : SepProp :=
    (x.p ↦ₛ preBytes_loopIter x.f k) ∗
      prostSSAt A0 (L + 0x420#64) (ssvAfter x.f k) ∗
      ((curPtr + 1#64) ↦ₛ payRest) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIter L ∗ stackAt L mergeFieldStack ∗
      deserSaved s0 ∗ R
  have hmem1 : s.mem ⊨ stepPre_loopIter L curPtr (keyByte_loopIter fl) payRest.length ∗ F_loop := by
    change s.mem ⊨ deserLocals L x.p x.bs (((seedFields x.f).drop k).flatMap SeedField.enc)
        (ssvAfter x.f k) ∗
      memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R at hmem
    rw [deserLocals_decomp_loopIter, deserOutRegion_eq_loopIter,
      sliceCursorAfter_split_key_loopIter L x.p hf hbs hk,
      stackAt_deserCallee_split_loopIter L, sep_perm1_loopIter] at hmem
    exact hmem
  intro hL
  rcases (step_254_to_2e8_placed_loopIter L curPtr fl payRest.length s
      (post := fun sm Pm =>
        sm.pc = lsmpl.base 15 ∧
        sm.status = .Running ∧
        sm.sp = s.sp ∧
        sm.trace = s.trace ∧
        sm.readReg64 .lr = (blkPl_46).base + 748#64 ∧
        sm.readReg64 .x0 = L + 0x420#64 ∧
        (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 fl.tag ∧
        (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 fl.wt.toNat ∧
        sm.readReg64 .x3 = L + 0x6e8#64 ∧
        (sm.readReg64 .x4).setWidth 32 = 99#32 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = 0#64 ∧
        sm.readReg64 .x23 = L + 0x408#64 ∧
        sm.readReg64 .x29 = L + 0x710#64 ∧
        Pm = stepPost_loopIter L curPtr (keyByte_loopIter fl) payRest.length)
      hpc_entry hrun hx29 hx20 hx23 hn_lt
      (fun _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 =>
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, rfl⟩)).elim hmem1 hL with
    ⟨sm, hsteps1, ⟨-, -, Pm, hmm, hpcm, hrunm, hspm, htrm, hlrm,
      hx0m, hx1m, hx2m, hx3m, hx4m, hx19m, hx20m, hx23m, hx29m, hPm⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  subst hPm
  have hcrl_m : LibsignalCodeRoLoaded lsmpl sm.mem := hcrl.of_keepsFrozen hsteps1.keepsFrozen
  have hLm : (lsProg_46 H).CodeLoaded sm.mem := hsteps1.codeLoaded hL
  have hspm_L : sm.sp = L := hspm.trans hsp
  have hal_m : sm.spAligned = true := by
    simp only [State.spAligned] at hal ⊢
    rwa [hspm]
  have hcall : subroutine_ok (lsProg_46 H) (lsmpl.base 15)
      (mergeFieldSeedPlacedSpec (fun _ => True)) :=
    ls_call_ro_of_block (callerProg := lsProg_46 H) hMF
  let g : MergeFieldGhost :=
    ⟨L + 0x420#64, ssvAfter x.f k, fl, L + 0x6e8#64, L + 0x3f8#64, curPtr + 1#64, rest, x.f⟩
  set F_mf : SepProp :=
    (curPtr ↦₈ keyByte_loopIter fl) ∗
      (x.p ↦ₛ preBytes_loopIter x.f k) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIter L ∗ deserSaved s0
  have hfresh := seedFields_fresh_loopIter x.f k hk
  have hpay_lt32 : (fl.payload ++ rest).length < 2 ^ 32 :=
    Nat.lt_trans hn_lt (by decide)
  have hpre_mf : sm.mem ⊨ (mergeFieldSeedPlacedSpec (fun _ => True)).pre g sm ∗ (F_mf ∗ R) := by
    dsimp only [mergeFieldSeedPlacedSpec, LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl_m, ?_⟩
    dsimp only [mergeFieldSeedRawSpec, g]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hx1m, hx2m, hx3m, hx4m, trivial, hf, List.getElem_mem hk,
      hfresh.1, hfresh.2.1, hfresh.2.2, hpay_lt32⟩, ?_⟩
    rw [hspm_L]
    unfold Prost.sliceCursorAt
    have ha : L + 0x3f8#64 + 8#64 = L + 0x400#64 := by bv_omega
    rw [ha]
    dsimp only [stepPost_loopIter, F_loop] at hmm
    dsimp only [F_mf]
    rw [← sep_perm2_loopIter]
    exact hmm
  obtain ⟨s2, hsteps2, hout, -⟩ :=
    hcall.no_fault_before_outcome g (F_mf ∗ R) sm hpcm hrunm hpre_mf hal_m hLm
  rcases hout with ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hpost2⟩ | ⟨hpan2, hpost2⟩ | ⟨code, _, hpost2⟩ | ⟨_, hpost2⟩
  · rw [hlrm] at hpc2
    dsimp only [mergeFieldSeedPlacedSpec, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeFieldSeedRawSpec, g] at hpost2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost2
    obtain ⟨⟨htr2, hx0_2⟩, hmem2⟩ := hpost2
    have hL2 : (lsProg_46 H).CodeLoaded s2.mem := hsteps2.codeLoaded hLm
    rcases (step_2ec_placed_loopIter s2
        (P := prostSSAt A0 (L + 0x420#64) ((ssvAfter x.f k).apply fl) ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
          stackAt sm.sp mergeFieldStack)
        (post := fun sf P_f =>
          sf.pc = (blkPl_46).base + 596#64 ∧
          sf.status = .Running ∧
          sf.sp = s2.sp ∧
          (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) ∧
          sf.readReg64 .x19 = s2.readReg64 .x19 ∧
          sf.readReg64 .x20 = s2.readReg64 .x20 ∧
          sf.readReg64 .x23 = s2.readReg64 .x23 ∧
          sf.readReg64 .x29 = s2.readReg64 .x29 ∧
          P_f = (prostSSAt A0 (L + 0x420#64) ((ssvAfter x.f k).apply fl) ∗
            ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
            Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
            stackAt sm.sp mergeFieldStack))
        hpc2 hrun2 hx0_2
        (fun _ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩)).elim hmem2 hL2 with
      ⟨sf, hsteps3, ⟨-, -, P_f, hmf, hpcf, hrunf, hspf, ⟨htrf, _⟩,
        hx19f, hx20f, hx23f, hx29f, hPf⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    subst hPf
    have hsteps_all : Steps (lsProg_46 H) s sf := (hsteps1.trans hsteps2).trans hsteps3
    have hsp_sf : sf.sp = L := by reg_chain
    have hsp_s : sf.sp = s.sp := by reg_chain
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned] at hal ⊢
      rwa [hsp_s]
    refine ⟨sf, hsteps_all, Or.inl ?_⟩
    refine ⟨hpcf, hrunf, by reg_chain, hcrl.of_keepsFrozen hsteps_all.keepsFrozen,
      hsp_sf, hal_sf, by reg_chain, by reg_chain, by reg_chain, by reg_chain, ?_⟩
    change sf.mem ⊨ deserLocals L x.p x.bs
        (((seedFields x.f).drop (k + 1)).flatMap SeedField.enc) (ssvAfter x.f (k + 1)) ∗
      memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
    rw [deserLocals_decomp_loopIter, deserOutRegion_eq_loopIter,
      ssvAfter_succ_loopIter hk, ← sliceCursorAfter_unsplit_key_loopIter L x.p hf hbs hk,
      stackAt_deserCallee_split_loopIter L, ← sep_perm3_loopIter]
    rw [hspm_L] at hmf
    exact hmf
  · have hsteps_all : Steps (lsProg_46 H) s s2 := hsteps1.trans hsteps2
    refine ⟨s2, hsteps_all, Or.inr ⟨hpan2, ?_⟩⟩
    dsimp only [mergeFieldSeedPlacedSpec, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeFieldSeedRawSpec, deserializeSeedRawSpec, Serialization.allocPanic] at hpost2 ⊢
    rw [← sepConj_assoc] at hpost2
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hpost2
    rw [allocFailedIn, htrm, htr] at ha
    rw [htrm, htr] at hp
    exact ⟨ha, hp⟩
  · exact (not_satisfies_false_sepConj hpost2).elim
  · exact (not_satisfies_false_sepConj hpost2).elim

end CryptoVerification.E2E.Record.DeserializeSeed
