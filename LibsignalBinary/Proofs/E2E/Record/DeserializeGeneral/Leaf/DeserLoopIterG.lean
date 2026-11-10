/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.BodyDefs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.LoopIter
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Loop-Iteration Leaf (`deserLoopIterG_ok`) for General `SessionRecord::deserialize`

Proves `deserLoopIterG_ok` (`+0x254 → +0x254`, `k → k + 1`), decoding one 1-byte field key and
invoking `SessionStructure::merge_field` on field `k` of `recFields r`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)
open CryptoVerification.E2E.Record.DeserializeSeed.LoopIterStateSimp

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? sessionImg0
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero ofNat_succ_sub_one_loopIter

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setPC_pre_loopIterG (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pre_loopIterG (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

/-! ## Pure `GenField`, `recFields`, and `ssgAfter` Helpers -/

def keyByte_loopIterG (fl : GenField) : BitVec 8 :=
  BitVec.ofNat 8 (fl.tag * 8 + if fl.wt = .varint then 0 else 2)

theorem enc_eq_keyByte_cons_loopIterG (fl : GenField) :
    fl.enc = keyByte_loopIterG fl :: fl.payload := by
  cases fl <;> rfl

theorem drop_flatMap_enc_loopIterG {r : SessionRecord (List (BitVec 8))} {k : Nat}
    (hk : k < (recFields r).length) :
    ((recFields r).drop k).flatMap GenField.enc =
      (recFields r)[k].enc ++ ((recFields r).drop (k + 1)).flatMap GenField.enc := by
  rw [List.drop_eq_getElem_cons hk, List.flatMap_cons]

theorem ssgAfter_succ_loopIterG {r : SessionRecord (List (BitVec 8))} {k : Nat}
    (hk : k < (recFields r).length) :
    ssgAfter r (k + 1) = (ssgAfter r k).apply (recFields r)[k] := by
  simp only [ssgAfter, List.take_succ_eq_append_getElem hk, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-! ## Spatial Cursor and Length Helpers -/

def preBytes_loopIterG (r : SessionRecord (List (BitVec 8))) (k : Nat) : List (BitVec 8) :=
  encodeKey 1 .lengthDelimited ++
    encodeVarint (BitVec.ofNat 64 ((recFields r).flatMap GenField.enc).length) ++
    ((recFields r).take k).flatMap GenField.enc

def curPtr_loopIterG (p : BitVec 64) (r : SessionRecord (List (BitVec 8))) (k : Nat) : BitVec 64 :=
  p + BitVec.ofNat 64 (preBytes_loopIterG r k).length

theorem encodeRecord_eq_preBytes_append_loopIterG {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScope r) (k : Nat) :
    encodeRecord r = preBytes_loopIterG r k ++ ((recFields r).drop k).flatMap GenField.enc := by
  have hs : (recFields r).flatMap GenField.enc =
      ((recFields r).take k).flatMap GenField.enc ++
        ((recFields r).drop k).flatMap GenField.enc := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [encodeRecord_eq_recFields r hr, preBytes_loopIterG, List.append_assoc, List.append_assoc, ← hs,
    ← List.append_assoc]

theorem rem_length_lt_loopIterG {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScope r) (k : Nat) :
    (((recFields r).drop k).flatMap GenField.enc).length < 2 ^ 20 := by
  have h1 := encodeRecord_length_lt hr
  rw [encodeRecord_eq_preBytes_append_loopIterG hr k, List.length_append] at h1
  omega

theorem payload_rest_length_lt_loopIterG {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScope r)
    {k : Nat} (hk : k < (recFields r).length) :
    ((recFields r)[k].payload ++ ((recFields r).drop (k + 1)).flatMap GenField.enc).length <
      2 ^ 20 := by
  have h := rem_length_lt_loopIterG hr k
  rw [drop_flatMap_enc_loopIterG hk, enc_eq_keyByte_cons_loopIterG, List.cons_append,
    List.length_cons] at h
  omega

theorem encodeRecord_sub_rem_length_loopIterG {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScope r) (k : Nat) :
    (encodeRecord r).length - (((recFields r).drop k).flatMap GenField.enc).length =
      (preBytes_loopIterG r k).length := by
  rw [encodeRecord_eq_preBytes_append_loopIterG hr k, List.length_append]
  omega

theorem sliceCursorAfter_split_key_loopIterG (L p : BitVec 64) {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScope r) {k : Nat} (hk : k < (recFields r).length) :
    Prost.sliceCursorAfter (L + 0x3f8#64) p (encodeRecord r)
      (((recFields r).drop k).flatMap GenField.enc) =
      ((L + 0x3f8#64) ↦₆₄ curPtr_loopIterG p r k) ∗
        ((L + 0x400#64) ↦₆₄ BitVec.ofNat 64
          (((recFields r)[k].payload ++
            ((recFields r).drop (k + 1)).flatMap GenField.enc).length + 1)) ∗
        (curPtr_loopIterG p r k ↦₈ keyByte_loopIterG (recFields r)[k]) ∗
        ((curPtr_loopIterG p r k + 1#64) ↦ₛ
          ((recFields r)[k].payload ++ ((recFields r).drop (k + 1)).flatMap GenField.enc)) ∗
        (p ↦ₛ preBytes_loopIterG r k) := by
  unfold Prost.sliceCursorAfter
  have hsub := encodeRecord_sub_rem_length_loopIterG hr k
  have hrem : ((recFields r).drop k).flatMap GenField.enc =
      keyByte_loopIterG (recFields r)[k] ::
        ((recFields r)[k].payload ++ ((recFields r).drop (k + 1)).flatMap GenField.enc) := by
    rw [drop_flatMap_enc_loopIterG hk, enc_eq_keyByte_cons_loopIterG, List.cons_append]
  have hbs_split : (p ↦ₛ encodeRecord r) =
      (p ↦ₛ preBytes_loopIterG r k) ∗
        (curPtr_loopIterG p r k ↦₈ keyByte_loopIterG (recFields r)[k]) ∗
        ((curPtr_loopIterG p r k + 1#64) ↦ₛ
          ((recFields r)[k].payload ++ ((recFields r).drop (k + 1)).flatMap GenField.enc)) := by
    conv_lhs => rw [encodeRecord_eq_preBytes_append_loopIterG hr k, hrem]
    rw [pointsToBytes_append, ← curPtr_loopIterG, pointsToBytes_cons]
  have ha : L + 0x3f8#64 + 8#64 = L + 0x400#64 := by bv_omega
  rw [hsub, ← curPtr_loopIterG, ha, hbs_split, hrem, List.length_cons]
  ac_rfl

theorem sliceCursorAfter_unsplit_key_loopIterG (L p : BitVec 64) {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScope r) {k : Nat} (hk : k < (recFields r).length) :
    Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr_loopIterG p r k + 1#64)
      ((recFields r)[k].payload ++ ((recFields r).drop (k + 1)).flatMap GenField.enc)
      (((recFields r).drop (k + 1)).flatMap GenField.enc) ∗
      (curPtr_loopIterG p r k ↦₈ keyByte_loopIterG (recFields r)[k]) ∗
      (p ↦ₛ preBytes_loopIterG r k) =
    Prost.sliceCursorAfter (L + 0x3f8#64) p (encodeRecord r)
      (((recFields r).drop (k + 1)).flatMap GenField.enc) := by
  let fl := (recFields r)[k]
  let rest := ((recFields r).drop (k + 1)).flatMap GenField.enc
  have hrem : ((recFields r).drop k).flatMap GenField.enc =
      keyByte_loopIterG fl :: (fl.payload ++ rest) := by
    rw [drop_flatMap_enc_loopIterG hk, enc_eq_keyByte_cons_loopIterG, List.cons_append]
  have hbs_eq : encodeRecord r = preBytes_loopIterG r k ++ (keyByte_loopIterG fl :: (fl.payload ++ rest)) := by
    rw [encodeRecord_eq_preBytes_append_loopIterG hr k, hrem]
  have hpay_sub : (fl.payload ++ rest).length - rest.length = fl.payload.length := by
    rw [List.length_append]; omega
  have hbs_sub : (encodeRecord r).length - rest.length =
      (preBytes_loopIterG r k).length + 1 + fl.payload.length := by
    rw [hbs_eq, List.length_append, List.length_cons, List.length_append]; omega
  have hptr : curPtr_loopIterG p r k + 1#64 +
      BitVec.ofNat 64 ((fl.payload ++ rest).length - rest.length) =
      p + BitVec.ofNat 64 ((encodeRecord r).length - rest.length) := by
    rw [hpay_sub, hbs_sub, curPtr_loopIterG]
    have hadd : BitVec.ofNat 64 ((preBytes_loopIterG r k).length + 1 + fl.payload.length) =
        BitVec.ofNat 64 (preBytes_loopIterG r k).length + 1#64 + BitVec.ofNat 64 fl.payload.length := by
      rw [BitVec.ofNat_add, BitVec.ofNat_add]
    rw [hadd]
    bv_omega
  have hbs_pts : (p ↦ₛ encodeRecord r) =
      (p ↦ₛ preBytes_loopIterG r k) ∗
        (curPtr_loopIterG p r k ↦₈ keyByte_loopIterG fl) ∗
        ((curPtr_loopIterG p r k + 1#64) ↦ₛ (fl.payload ++ rest)) := by
    conv_lhs => rw [hbs_eq]
    rw [pointsToBytes_append, ← curPtr_loopIterG, pointsToBytes_cons]
  unfold Prost.sliceCursorAfter
  rw [hptr, hbs_pts]
  ac_rfl

theorem deserLocalsG_decomp_loopIterG (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSG) :
    deserLocalsG L p bs rest v =
      Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗
      prostSSGAt A0 (L + 0x420#64) v ∗
      ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
      deserFixed_loopIter L := by
  unfold deserLocalsG deserFixed_loopIter
  generalize memRegion L 0x3f8 = m1
  generalize memRegion (L + 0x578#64) 0x170 = m2
  generalize memRegion (L + 0x6f0#64) 0x20 = m3
  ac_rfl

theorem ule_zero_ofNat_succ_loopIterG {n : Nat} (hn : n < 2 ^ 20) :
    (BitVec.ofNat 64 (n + 1)).ule 0#64 = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_zero,
    Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 64)]
  omega

@[local arm64_norm]
theorem keyByte_signExtend_lsb63_loopIterG (fl : GenField) :
    (BitVec.signExtend 64 (keyByte_loopIterG fl)).getLsbD 63 = false := by
  cases fl <;> simp [keyByte_loopIterG, GenField.tag, GenField.wt]

@[local arm64_norm]
theorem keyByte_signExtend_lsr32_loopIterG (fl : GenField) :
    (BitVec.signExtend 64 (keyByte_loopIterG fl)) >>> 32 = 0#64 := by
  cases fl <;> simp [keyByte_loopIterG, GenField.tag, GenField.wt]

@[local arm64_norm]
theorem keyByte_signExtend_and7_ule6_loopIterG (fl : GenField) :
    (6#64).ule (BitVec.signExtend 64 (keyByte_loopIterG fl) &&& 7#64) = false := by
  cases fl <;> simp [keyByte_loopIterG, GenField.tag, GenField.wt]

@[local arm64_norm]
theorem keyByte_signExtend_tag_w1_loopIterG (fl : GenField) :
    BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (keyByte_loopIterG fl))) >>> 3)) =
      BitVec.ofNat 64 fl.tag := by
  cases fl <;> simp [keyByte_loopIterG, GenField.tag, GenField.wt]

@[local arm64_norm]
theorem tag_zeroExtend_ofNat32_loopIterG (fl : GenField) :
    BitVec.zeroExtend 64 (BitVec.ofNat 32 fl.tag) = BitVec.ofNat 64 fl.tag := by
  cases fl <;> simp [GenField.tag]

@[local arm64_norm]
theorem tag_ofNat64_beq0_loopIterG (fl : GenField) :
    (BitVec.ofNat 64 fl.tag == 0#64) = false := by
  cases fl <;> simp [GenField.tag]

@[local arm64_norm]
theorem tag_ofNat64_setWidth32_loopIterG (fl : GenField) :
    (BitVec.ofNat 64 fl.tag).setWidth 32 = BitVec.ofNat 32 fl.tag := by
  cases fl <;> simp [GenField.tag]

theorem step_254_to_2e8_loopIterG (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (L curPtr : BitVec 64) (fl : GenField) (n : Nat) (s : State)
    {post : State → SepProp → Prop}
    (hpc : s.pc = deserEntry_loopIter + 596#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = L + 0x710#64)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hx23 : s.readReg64 .x23 = L + 0x408#64)
    (hn : n < 2 ^ 20)
    (hnext : ∀ sm : State,
      sm.pc = deserEntry_loopIter + bv% (2 ^ 64 - 71352) →
      sm.status = .Running →
      sm.sp = s.sp →
      (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) →
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
      post sm (stepPost_loopIter L curPtr (keyByte_loopIterG fl) n)) :
    SepWP (recordProg C ctl abs) (deserEntry_loopIter + bv% (2 ^ 64 - 71352)) s
      (stepPre_loopIter L curPtr (keyByte_loopIterG fl) n) post := by
  have hule := ule_zero_ofNat_succ_loopIterG hn
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  diter_fetches sessionImg0.base H
  change SepWP (libsignalSessionCode.rebase sessionImg0.base H)
    (deserEntry_loopIter + bv% (2 ^ 64 - 71352)) s
    (stepPre_loopIter L curPtr (keyByte_loopIterG fl) n) post
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
    (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]; cases fl <;> simp [keyByte_loopIterG, GenField.tag, GenField.wt, WireType.toNat])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])

theorem deserLoopIterG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hMF : MergeFieldGenOk C ctl (fun _ => True) abs) (x : DeserializeGenGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hr : DeserializeScope x.r) (hk : k < (recFields x.r).length)
    (hs : DeserLoopG C ctl x R s0 k s) :
    DeserStepG C ctl x R s0 s (DeserLoopG C ctl x R s0 (k + 1)) abs := by
  obtain ⟨hpc, hrun, htr, hsym, hF, hsp, hal, hx29, hx19, hx20, hx23, hmem⟩ := hs
  let L := deserSpL s0.sp
  let fl := (recFields x.r)[k]
  let rest := ((recFields x.r).drop (k + 1)).flatMap GenField.enc
  let payRest := fl.payload ++ rest
  let curPtr := curPtr_loopIterG x.p x.r k
  have hpc_entry : s.pc = deserEntry_loopIter + 596#64 := by
    rw [hpc, deserPC_eq_deserEntry_loopIter]
  have hn_lt : payRest.length < 2 ^ 20 := payload_rest_length_lt_loopIterG hr hk
  set F_loop : SepProp :=
    (x.p ↦ₛ preBytes_loopIterG x.r k) ∗
      prostSSGAt A0 (L + 0x420#64) (ssgAfter x.r k) ∗
      ((curPtr + 1#64) ↦ₛ payRest) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIter L ∗ stackAt L mergeFieldStack ∗
      deserSaved s0 ∗ R
  have hmem1 : s.mem ⊨ stepPre_loopIter L curPtr (keyByte_loopIterG fl) payRest.length ∗ F_loop := by
    change s.mem ⊨ deserLocalsG L x.p (encodeRecord x.r) (((recFields x.r).drop k).flatMap GenField.enc)
        (ssgAfter x.r k) ∗
      memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R at hmem
    rw [deserLocalsG_decomp_loopIterG, deserOutRegion_eq_loopIter,
      sliceCursorAfter_split_key_loopIterG L x.p hr hk,
      stackAt_deserCallee_split_loopIter L, sep_perm1_loopIter] at hmem
    exact hmem
  intro hL
  rcases (step_254_to_2e8_loopIterG C ctl L curPtr fl payRest.length s
      (post := fun sm Pm =>
        sm.pc = deserEntry_loopIter + bv% (2 ^ 64 - 71352) ∧
        sm.status = .Running ∧
        sm.sp = s.sp ∧
        (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
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
        Pm = stepPost_loopIter L curPtr (keyByte_loopIterG fl) payRest.length)
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
      (deserEntry_loopIter + bv% (2 ^ 64 - 71352)) (mergeFieldGenSpec (fun _ => True)) := by
    rw [mergeField_fnAddr_eq_loopIter C ctl]
    exact hMF
  let g : MergeFieldGenGhost :=
    ⟨L + 0x420#64, ssgAfter x.r k, fl, L + 0x6e8#64, L + 0x3f8#64, curPtr + 1#64, rest⟩
  set F_mf : SepProp :=
    (curPtr ↦₈ keyByte_loopIterG fl) ∗
      (x.p ↦ₛ preBytes_loopIterG x.r k) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIter L ∗ deserSaved s0
  have hok : fl.Ok := recFields_ok x.r hr fl (List.getElem_mem hk)
  have hfresh : fl.Fresh (ssgAfter x.r k) := recFields_fresh x.r hr k hk
  have hpay_lt32 : (fl.payload ++ rest).length < 2 ^ 32 :=
    Nat.lt_trans hn_lt (by decide)
  have hpre_mf : sm.mem ⊨ (mergeFieldGenSpec (fun _ => True)).pre g sm ∗ (F_mf ∗ R) := by
    dsimp only [mergeFieldGenSpec, g]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hx1m, hx2m, hx3m, hx4m, trivial, hok, hfresh, hpay_lt32, hFm, hsymm⟩, ?_⟩
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
    dsimp only [mergeFieldGenSpec, g] at hpost2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost2
    obtain ⟨⟨htr2, hx0_2⟩, hmem2⟩ := hpost2
    have hL2 : (recordProg C ctl abs).CodeLoaded s2.mem := hsteps2.codeLoaded hLm
    rcases (step_2ec_loopIter C ctl s2
        (P := prostSSGAt A0 (L + 0x420#64) ((ssgAfter x.r k).apply fl) ∗
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
          P_f = (prostSSGAt A0 (L + 0x420#64) ((ssgAfter x.r k).apply fl) ∗
            ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
            Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
            stackAt sm.sp mergeFieldStack))
        hpc2 hrun2 hx0_2
        (fun _ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩)).elim hmem2 hL2 with
      ⟨sf, hsteps3, ⟨-, -, P_f, hmf, hpcf, hrunf, hspf, htrf,
        hx19f, hx20f, hx23f, hx29f, hPf⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    subst hPf
    have hsteps_all : Steps (recordProg C ctl abs) s sf := (hsteps1.trans hsteps2).trans hsteps3
    have hsp_sf : sf.sp = L := hspf.trans (hsp2.trans hspm_L)
    have hsp_s : sf.sp = s.sp := hsp_sf.trans hsp.symm
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned] at hal ⊢
      rwa [hsp_s]
    refine ⟨sf, hsteps_all, Or.inl ?_⟩
    refine ⟨?_, hrunf, ⟨htrf.1.trans (htr2.trans (htrm.1.trans htr.1)), htrf.2.trans (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans (htrm.2.trans htr.2))⟩, hsteps_all.symtab_eq.trans hsym, hsteps_all.frozenLoaded hF,
      hsp_sf, hal_sf, by reg_chain, by reg_chain, by reg_chain, by reg_chain, ?_⟩
    · rw [deserPC_eq_deserEntry_loopIter]; exact hpcf
    · change sf.mem ⊨ deserLocalsG L x.p (encodeRecord x.r)
          (((recFields x.r).drop (k + 1)).flatMap GenField.enc) (ssgAfter x.r (k + 1)) ∗
        memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
      rw [deserLocalsG_decomp_loopIterG, deserOutRegion_eq_loopIter,
        ssgAfter_succ_loopIterG hk, ← sliceCursorAfter_unsplit_key_loopIterG L x.p hr hk,
        stackAt_deserCallee_split_loopIter L, ← sep_perm3_loopIter]
      rw [hspm_L] at hmf
      exact hmf
  · have hsteps_all : Steps (recordProg C ctl abs) s s2 := hsteps1.trans hsteps2
    refine ⟨s2, hsteps_all, Or.inr ⟨hpan2, ?_⟩⟩
    dsimp only [mergeFieldGenSpec, deserializeGenSpec, Serialization.allocPanic] at hpost2 ⊢
    rw [← sepConj_assoc] at hpost2
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hpost2
    rw [allocFailedIn, htrm.1, htr.1] at ha
    rw [htrm.1, htr.1] at hp
    exact ⟨ha, hp⟩
  · exact (not_satisfies_false_sepConj hpost2).elim
  · exact (not_satisfies_false_sepConj hpost2).elim

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG
