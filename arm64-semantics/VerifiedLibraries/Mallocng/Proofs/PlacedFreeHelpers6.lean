/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.PlacedFreeHelpers5b

/-!
# Context Cell Focus and Reserved-Meta Recycling Helpers

Pure invariant-transition helpers for multi-block `nontrivial_free`: `CtxFields.toBytes` cell
focus/update lemmas, all-free group bitfield and child-absence facts, and `free_meta` transitions
(`free_recycle_reserved_meta_empty`, `free_recycle_reserved_meta_nonempty`) moving a reserved meta
slot onto `ctx.free_meta_head`.
-/

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## `CtxFields.toBytes` Cell Focus and Update Helpers -/

private theorem flatMap_unpack64_len6 (xs : List (BitVec 64)) :
    (xs.flatMap unpack64).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ rest ih =>
    simp only [List.flatMap_cons, List.length_append, unpack64_length, ih, List.length_cons]
    omega

private theorem flatMap_unpack64_split (xs : List (BitVec 64)) {i : Nat} (hi : i < xs.length) :
    xs.flatMap unpack64 =
      (xs.take i).flatMap unpack64 ++ unpack64 (xs[i]'hi) ++ (xs.drop (i + 1)).flatMap unpack64 := by
  conv => lhs; rw [← List.take_append_drop i xs]
  have hDrop : xs.drop i = (xs[i]'hi) :: xs.drop (i + 1) := List.drop_eq_getElem_cons hi
  rw [List.flatMap_append, hDrop, List.flatMap_cons, List.append_assoc]

private theorem flatMap_unpack64_set (xs : List (BitVec 64)) {i : Nat} (hi : i < xs.length)
    (v : BitVec 64) :
    (xs.set i v).flatMap unpack64 =
      (xs.take i).flatMap unpack64 ++ unpack64 v ++ (xs.drop (i + 1)).flatMap unpack64 := by
  have hi' : i < (xs.set i v).length := by simp [hi]
  rw [flatMap_unpack64_split (xs.set i v) hi']
  simp [List.take_set_of_le (Nat.le_refl i), List.drop_set_of_lt (Nat.lt_succ_self i)]

private theorem list_split_byte (xs : List (BitVec 8)) {i : Nat} (hi : i < xs.length) :
    xs = xs.take i ++ [xs[i]'hi] ++ xs.drop (i + 1) := by
  conv => lhs; rw [← List.take_append_drop i xs]
  rw [List.drop_eq_getElem_cons hi]
  simp only [List.append_assoc, List.singleton_append]

private theorem list_set_byte (xs : List (BitVec 8)) {i : Nat} (hi : i < xs.length)
    (v : BitVec 8) :
    xs.set i v = xs.take i ++ [v] ++ xs.drop (i + 1) := by
  have hi' : i < (xs.set i v).length := by simp [hi]
  conv => lhs; rw [list_split_byte (xs.set i v) hi']
  simp [List.take_set_of_le (Nat.le_refl i), List.drop_set_of_lt (Nat.lt_succ_self i)]

private theorem pointsToBytes_split3_eq (ctx : BitVec 64) (p m s : List (BitVec 8)) :
    (ctx ↦ₛ (p ++ (m ++ s))) =
      ((ctx ↦ₛ p) ∗ ((ctx + BitVec.ofNat 64 p.length) ↦ₛ m) ∗
        (((ctx + BitVec.ofNat 64 p.length) + BitVec.ofNat 64 m.length) ↦ₛ s)) := by
  rw [pointsToBytes_append, pointsToBytes_append]

private theorem swap_left_comm (P Q R : SepProp) : P ∗ (Q ∗ R) = Q ∗ (P ∗ R) := by ac_rfl

theorem ctx_focus_update_active (ctx : BitVec 64) (c : CtxFields)
    (hAct : c.active.length = 48) {sc : Nat} (hsc : sc < 48) (v : BitVec 64) :
    ∃ Rest : SepProp,
      (ctx ↦ₛ c.toBytes) =
        (((ctx + BitVec.ofNat 64 (80 + 8 * sc)) ↦₆₄ (c.active[sc]'(hAct ▸ hsc))) ∗ Rest) ∧
      (((ctx + BitVec.ofNat 64 (80 + 8 * sc)) ↦₆₄ v) ∗ Rest) =
        (ctx ↦ₛ { c with active := c.active.set sc v }.toBytes) := by
  have hsc' : sc < c.active.length := hAct ▸ hsc
  let pre := unpack64 c.secret ++ unpack32 c.initDone ++ unpack32 c.mmapCounter ++
    unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
    unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
    unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++ (c.active.take sc).flatMap unpack64
  let suf := (c.active.drop (sc + 1)).flatMap unpack64 ++
    c.usageByClass.flatMap unpack64 ++ c.unmapSeq ++ c.bounces ++ [c.seq] ++ c.seqPad ++
    unpack64 c.brk
  have hPreLen : pre.length = 80 + 8 * sc := by
    simp only [pre, List.length_append, unpack64_length, unpack32_length,
      flatMap_unpack64_len6, List.length_take, hAct]
    omega
  have hOff : (ctx + BitVec.ofNat 64 (80 + 8 * sc)) + BitVec.ofNat 64 8 =
      ctx + BitVec.ofNat 64 (88 + 8 * sc) := by bv_omega
  refine ⟨(ctx ↦ₛ pre) ∗ ((ctx + BitVec.ofNat 64 (88 + 8 * sc)) ↦ₛ suf), ?_, ?_⟩
  · have hEq : c.toBytes = pre ++ (unpack64 (c.active[sc]'hsc') ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, flatMap_unpack64_split c.active hsc',
        List.append_assoc]
    rw [hEq, pointsToBytes_split3_eq ctx pre _ suf, hPreLen, unpack64_length,
      ← pointsTo64_eq_pointsToBytes, hOff]
    ac_rfl
  · have hEq : { c with active := c.active.set sc v }.toBytes =
        pre ++ (unpack64 v ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, flatMap_unpack64_set c.active hsc' v,
        List.append_assoc]
    rw [hEq, pointsToBytes_split3_eq ctx pre _ suf, hPreLen, unpack64_length,
      ← pointsTo64_eq_pointsToBytes, hOff]
    ac_rfl

theorem ctx_focus_update_usage (ctx : BitVec 64) (c : CtxFields)
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    {sc : Nat} (hsc : sc < 48) (v : BitVec 64) :
    ∃ Rest : SepProp,
      (ctx ↦ₛ c.toBytes) =
        (((ctx + BitVec.ofNat 64 (464 + 8 * sc)) ↦₆₄ (c.usageByClass[sc]'(hUse ▸ hsc))) ∗ Rest) ∧
      (((ctx + BitVec.ofNat 64 (464 + 8 * sc)) ↦₆₄ v) ∗ Rest) =
        (ctx ↦ₛ { c with usageByClass := c.usageByClass.set sc v }.toBytes) := by
  have hsc' : sc < c.usageByClass.length := hUse ▸ hsc
  let pre := unpack64 c.secret ++ unpack32 c.initDone ++ unpack32 c.mmapCounter ++
    unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
    unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
    unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++ c.active.flatMap unpack64 ++
    (c.usageByClass.take sc).flatMap unpack64
  let suf := (c.usageByClass.drop (sc + 1)).flatMap unpack64 ++
    c.unmapSeq ++ c.bounces ++ [c.seq] ++ c.seqPad ++ unpack64 c.brk
  have hPreLen : pre.length = 464 + 8 * sc := by
    simp only [pre, List.length_append, unpack64_length, unpack32_length,
      flatMap_unpack64_len6, List.length_take, hAct, hUse]
    omega
  have hOff : (ctx + BitVec.ofNat 64 (464 + 8 * sc)) + BitVec.ofNat 64 8 =
      ctx + BitVec.ofNat 64 (472 + 8 * sc) := by bv_omega
  refine ⟨(ctx ↦ₛ pre) ∗ ((ctx + BitVec.ofNat 64 (472 + 8 * sc)) ↦ₛ suf), ?_, ?_⟩
  · have hEq : c.toBytes = pre ++ (unpack64 (c.usageByClass[sc]'hsc') ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, flatMap_unpack64_split c.usageByClass hsc',
        List.append_assoc]
    rw [hEq, pointsToBytes_split3_eq ctx pre _ suf, hPreLen, unpack64_length,
      ← pointsTo64_eq_pointsToBytes, hOff]
    ac_rfl
  · have hEq : { c with usageByClass := c.usageByClass.set sc v }.toBytes =
        pre ++ (unpack64 v ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, flatMap_unpack64_set c.usageByClass hsc' v,
        List.append_assoc]
    rw [hEq, pointsToBytes_split3_eq ctx pre _ suf, hPreLen, unpack64_length,
      ← pointsTo64_eq_pointsToBytes, hOff]
    ac_rfl

theorem ctx_focus_bounces_byte (ctx : BitVec 64) (c : CtxFields)
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) (hBnc : c.bounces.length = 32)
    {k : Nat} (hk : k < 32) :
    ∃ Rest : SepProp,
      (ctx ↦ₛ c.toBytes) =
        (((ctx + BitVec.ofNat 64 (880 + k)) ↦₈ (c.bounces[k]'(hBnc ▸ hk))) ∗ Rest) := by
  have hk' : k < c.bounces.length := hBnc ▸ hk
  let pre := unpack64 c.secret ++ unpack32 c.initDone ++ unpack32 c.mmapCounter ++
    unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
    unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
    unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++ c.active.flatMap unpack64 ++
    c.usageByClass.flatMap unpack64 ++ c.unmapSeq ++ c.bounces.take k
  let suf := c.bounces.drop (k + 1) ++ [c.seq] ++ c.seqPad ++ unpack64 c.brk
  have hPreLen : pre.length = 880 + k := by
    simp only [pre, List.length_append, unpack64_length, unpack32_length,
      flatMap_unpack64_len6, List.length_take, hAct, hUse, hUnm, hBnc]
    omega
  refine ⟨(ctx ↦ₛ pre) ∗ (((ctx + BitVec.ofNat 64 (880 + k)) + 1#64) ↦ₛ suf), ?_⟩
  have hEq : c.toBytes = pre ++ ([c.bounces[k]'hk'] ++ suf) := by
    conv => lhs; unfold CtxFields.toBytes; rw [list_split_byte c.bounces hk']
    simp only [pre, suf, List.append_assoc]
  rw [hEq, pointsToBytes_split3_eq ctx pre _ suf, hPreLen, pointsToBytes_singleton,
    List.length_singleton]
  exact swap_left_comm _ _ _

theorem ctx_focus_update_unmapSeq_byte (ctx : BitVec 64) (c : CtxFields)
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) {k : Nat} (hk : k < 32) (v : BitVec 8) :
    ∃ Rest : SepProp,
      (ctx ↦ₛ c.toBytes) =
        (((ctx + BitVec.ofNat 64 (848 + k)) ↦₈ (c.unmapSeq[k]'(hUnm ▸ hk))) ∗ Rest) ∧
      (((ctx + BitVec.ofNat 64 (848 + k)) ↦₈ v) ∗ Rest) =
        (ctx ↦ₛ { c with unmapSeq := c.unmapSeq.set k v }.toBytes) := by
  have hk' : k < c.unmapSeq.length := hUnm ▸ hk
  let pre := unpack64 c.secret ++ unpack32 c.initDone ++ unpack32 c.mmapCounter ++
    unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
    unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
    unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++ c.active.flatMap unpack64 ++
    c.usageByClass.flatMap unpack64 ++ c.unmapSeq.take k
  let suf := c.unmapSeq.drop (k + 1) ++ c.bounces ++ [c.seq] ++ c.seqPad ++ unpack64 c.brk
  have hPreLen : pre.length = 848 + k := by
    simp only [pre, List.length_append, unpack64_length, unpack32_length,
      flatMap_unpack64_len6, List.length_take, hAct, hUse, hUnm]
    omega
  refine ⟨(ctx ↦ₛ pre) ∗ (((ctx + BitVec.ofNat 64 (848 + k)) + 1#64) ↦ₛ suf), ?_, ?_⟩
  · have hEq : c.toBytes = pre ++ ([c.unmapSeq[k]'hk'] ++ suf) := by
      conv => lhs; unfold CtxFields.toBytes; rw [list_split_byte c.unmapSeq hk']
      simp only [pre, suf, List.append_assoc]
    rw [hEq, pointsToBytes_split3_eq ctx pre _ suf, hPreLen, pointsToBytes_singleton,
      List.length_singleton]
    exact swap_left_comm _ _ _
  · have hEq : { c with unmapSeq := c.unmapSeq.set k v }.toBytes = pre ++ ([v] ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, list_set_byte c.unmapSeq hk' v, List.append_assoc]
    rw [hEq, pointsToBytes_split3_eq ctx pre _ suf, hPreLen, pointsToBytes_singleton,
      List.length_singleton]
    exact (swap_left_comm _ _ _).symm

theorem ctx_focus_update_unmapSeq_slice (ctx : BitVec 64) (c : CtxFields)
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) (bs : List (BitVec 8)) (hbs : bs.length = 32) :
    ∃ Rest : SepProp,
      (ctx ↦ₛ c.toBytes) = (((ctx + 848#64) ↦ₛ c.unmapSeq) ∗ Rest) ∧
      (((ctx + 848#64) ↦ₛ bs) ∗ Rest) = (ctx ↦ₛ { c with unmapSeq := bs }.toBytes) := by
  let pre := unpack64 c.secret ++ unpack32 c.initDone ++ unpack32 c.mmapCounter ++
    unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
    unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
    unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++ c.active.flatMap unpack64 ++
    c.usageByClass.flatMap unpack64
  let suf := c.bounces ++ [c.seq] ++ c.seqPad ++ unpack64 c.brk
  have hPreLen : pre.length = 848 := by
    simp only [pre, List.length_append, unpack64_length, unpack32_length,
      flatMap_unpack64_len6, hAct, hUse]
  refine ⟨(ctx ↦ₛ pre) ∗ ((ctx + 880#64) ↦ₛ suf), ?_, ?_⟩
  · have hEq : c.toBytes = pre ++ (c.unmapSeq ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, List.append_assoc]
    rw [hEq, pointsToBytes_split3_eq ctx pre _ suf, hPreLen, hUnm]
    change (ctx ↦ₛ pre) ∗ (((ctx + 848#64) ↦ₛ c.unmapSeq) ∗ (((ctx + 848#64) + 32#64) ↦ₛ suf)) = _
    rw [show (ctx + 848#64) + 32#64 = ctx + 880#64 by bv_omega]
    ac_rfl
  · have hEq : { c with unmapSeq := bs }.toBytes = pre ++ (bs ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, List.append_assoc]
    rw [hEq, pointsToBytes_split3_eq ctx pre _ suf, hPreLen, hbs]
    change _ = (ctx ↦ₛ pre) ∗ (((ctx + 848#64) ↦ₛ bs) ∗ (((ctx + 848#64) + 32#64) ↦ₛ suf))
    rw [show (ctx + 848#64) + 32#64 = ctx + 880#64 by bv_omega]
    ac_rfl

theorem ctx_focus_update_seq (ctx : BitVec 64) (c : CtxFields)
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) (hBnc : c.bounces.length = 32) (v : BitVec 8) :
    ∃ Rest : SepProp,
      (ctx ↦ₛ c.toBytes) = (((ctx + 912#64) ↦₈ c.seq) ∗ Rest) ∧
      (((ctx + 912#64) ↦₈ v) ∗ Rest) = (ctx ↦ₛ { c with seq := v }.toBytes) := by
  let pre := unpack64 c.secret ++ unpack32 c.initDone ++ unpack32 c.mmapCounter ++
    unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
    unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
    unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++ c.active.flatMap unpack64 ++
    c.usageByClass.flatMap unpack64 ++ c.unmapSeq ++ c.bounces
  let suf := c.seqPad ++ unpack64 c.brk
  have hPreLen : pre.length = 912 := by
    simp only [pre, List.length_append, unpack64_length, unpack32_length,
      flatMap_unpack64_len6, hAct, hUse, hUnm, hBnc]
  refine ⟨(ctx ↦ₛ pre) ∗ ((ctx + 913#64) ↦ₛ suf), ?_, ?_⟩
  · have hEq : c.toBytes = pre ++ ([c.seq] ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, List.append_assoc]
    rw [hEq, pointsToBytes_split3_eq ctx pre _ suf, hPreLen, pointsToBytes_singleton,
      List.length_singleton]
    change (ctx ↦ₛ pre) ∗ (((ctx + 912#64) ↦₈ c.seq) ∗ (((ctx + 912#64) + 1#64) ↦ₛ suf)) = _
    rw [show (ctx + 912#64) + 1#64 = ctx + 913#64 by bv_omega]
    ac_rfl
  · have hEq : { c with seq := v }.toBytes = pre ++ ([v] ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, List.append_assoc]
    rw [hEq, pointsToBytes_split3_eq ctx pre _ suf, hPreLen, pointsToBytes_singleton,
      List.length_singleton]
    change _ = (ctx ↦ₛ pre) ∗ (((ctx + 912#64) ↦₈ v) ∗ (((ctx + 912#64) + 1#64) ↦ₛ suf))
    rw [show (ctx + 912#64) + 1#64 = ctx + 913#64 by bv_omega]
    ac_rfl

theorem ctx_focus_update_freeMetaHead (ctx : BitVec 64) (c : CtxFields) (v : BitVec 64) :
    ∃ Rest : SepProp,
      (ctx ↦ₛ c.toBytes) = (((ctx + 16#64) ↦₆₄ c.freeMetaHead) ∗ Rest) ∧
      (((ctx + 16#64) ↦₆₄ v) ∗ Rest) = (ctx ↦ₛ { c with freeMetaHead := v }.toBytes) := by
  let pre := unpack64 c.secret ++ unpack32 c.initDone ++ unpack32 c.mmapCounter
  let suf := unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
    unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
    unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++ c.active.flatMap unpack64 ++
    c.usageByClass.flatMap unpack64 ++ c.unmapSeq ++ c.bounces ++ [c.seq] ++ c.seqPad ++
    unpack64 c.brk
  have hPreLen : pre.length = 16 := by simp [pre]
  refine ⟨(ctx ↦ₛ pre) ∗ ((ctx + 24#64) ↦ₛ suf), ?_, ?_⟩
  · have hEq : c.toBytes = pre ++ (unpack64 c.freeMetaHead ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, List.append_assoc]
    rw [hEq, pointsToBytes_split3_eq ctx pre _ suf, hPreLen, unpack64_length,
      ← pointsTo64_eq_pointsToBytes]
    change (ctx ↦ₛ pre) ∗ (((ctx + 16#64) ↦₆₄ c.freeMetaHead) ∗ (((ctx + 16#64) + 8#64) ↦ₛ suf)) = _
    rw [show (ctx + 16#64) + 8#64 = ctx + 24#64 by bv_omega]
    ac_rfl
  · have hEq : { c with freeMetaHead := v }.toBytes = pre ++ (unpack64 v ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, List.append_assoc]
    rw [hEq, pointsToBytes_split3_eq ctx pre _ suf, hPreLen, unpack64_length,
      ← pointsTo64_eq_pointsToBytes]
    change _ = (ctx ↦ₛ pre) ∗ (((ctx + 16#64) ↦₆₄ v) ∗ (((ctx + 16#64) + 8#64) ↦ₛ suf))
    rw [show (ctx + 16#64) + 8#64 = ctx + 24#64 by bv_omega]
    ac_rfl

/-! ## Packed Bitfield and All-Free Group Properties -/

theorem packedWord_bit5_true (g : GroupDesc) :
    ((g.packedWord.extractLsb' 0 8).zeroExtend 32).getLsbD 5 = true ∧
    (g.packedWord.extractLsb' 0 8) &&& 0x1f#8 = BitVec.ofNat 8 (g.lastIdx % 32) := by
  unfold GroupDesc.packedWord
  constructor
  · bv_robdd
  · have h1 : (BitVec.ofNat 64 g.lastIdx &&& 0x1f#64).extractLsb' 0 8 =
        BitVec.ofNat 8 (g.lastIdx % 32) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_and,
        BitVec.toNat_ofNat]
      change ((g.lastIdx % (2 ^ 64)) &&& 31) % 256 = (g.lastIdx % 32) % 256
      rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    rw [← h1]
    bv_robdd

theorem free_no_child_groups_of_allFree {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hAllFree : (g.availMask ||| g.freedMask) + (1#32 <<< idx) = (2#32 <<< g.lastIdx) - 1#32) :
    (∀ j : Nat, (hj : j < g.slots.length) →
      if j = idx then g.slots[j]'hj = .claimed
      else g.slots[j]'hj = .freeAvail ∨ g.slots[j]'hj = .freeInactive) ∧
    (g.slots.filter SlotState.isClaimed).length = 1 ∧
    (g.slots.map slotEffCost).sum = 0 ∧
    (g.slots.map slotLiveCount).sum = 0 ∧
    (∀ s ∈ g.slots, ∀ p req ec, s ≠ .liveUser p req ec) ∧
    (∀ cg ∈ st.groups, cg.parentMeta ≠ some g.metaPtr) := by
  have hGWf := hwf.groups_wf g hg
  have hSWf := hGWf.slot_wf idx hIdx
  rw [hClaimed] at hSWf
  have hIdxLe : idx ≤ g.lastIdx := by have := hGWf.2.2.1; unfold GroupDesc.cnt at this; omega
  have hAv0 : g.availMask.getLsbD idx = false :=
    Bool.eq_false_iff.mpr fun h => by have := hSWf.2.1.mp h; cases this
  have hFr0 : g.freedMask.getLsbD idx = false :=
    Bool.eq_false_iff.mpr fun h => by have := hSWf.2.2.1.mp h; cases this
  have hMP := freeSlot_mask_props hIdxLe hGWf.2.1
    (BitVec.and_comm g.availMask g.freedMask ▸ hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (BitVec.or_comm g.availMask g.freedMask ▸ hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    hFr0 hAv0
  have hBitsOther := hMP.2.2.2.2.2.2.mp (BitVec.or_comm g.availMask g.freedMask ▸ hAllFree)
  have hSlotsChar : ∀ j : Nat, (hj : j < g.slots.length) →
      if j = idx then g.slots[j]'hj = .claimed
      else g.slots[j]'hj = .freeAvail ∨ g.slots[j]'hj = .freeInactive := by
    intro j hj
    by_cases hEq : j = idx
    · subst hEq; simp [hClaimed]
    · simp only [hEq, ↓reduceIte]
      have hjLe : j ≤ g.lastIdx := by have := hGWf.2.2.1; unfold GroupDesc.cnt at this; omega
      have hSWfJ := hGWf.slot_wf j hj
      rcases hBitsOther j hjLe hEq with hFrJ | hAvJ
      · exact Or.inr (hSWfJ.2.2.1.mp hFrJ)
      · exact Or.inl (hSWfJ.2.1.mp hAvJ)
  have hSetEmpty : ∀ s ∈ g.slots.set idx .freeInactive,
      s = .freeAvail ∨ s = .freeInactive := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    have hj0 : j < g.slots.length := by simpa using hj
    by_cases hEq : j = idx
    · subst hEq; simp
    · simp only [List.getElem_set, Ne.symm hEq, ↓reduceIte]
      have hC := hSlotsChar j hj0
      simpa [hEq] using hC
  have hFilterSet0 : ((g.slots.set idx .freeInactive).filter SlotState.isClaimed).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro s hs
    rcases hSetEmpty s hs with rfl | rfl <;> simp [SlotState.isClaimed]
  have hClaim1 : (g.slots.filter SlotState.isClaimed).length = 1 := by
    have hS := list_set_filter_len g.slots hIdx .freeInactive SlotState.isClaimed
    rw [hClaimed, hFilterSet0] at hS
    simp only [SlotState.isClaimed, Bool.false_eq_true, ↓reduceIte] at hS
    omega
  have hNoLiveUser : ∀ s ∈ g.slots, ∀ p req ec, s ≠ .liveUser p req ec := by
    intro s hs p req ec hEq
    obtain ⟨j, hj, hsJ⟩ := List.getElem_of_mem hs
    have hEqJ : g.slots[j]'hj = .liveUser p req ec := hsJ.trans hEq
    have hC := hSlotsChar j hj
    by_cases hJ : j = idx
    · subst hJ
      simp only [↓reduceIte] at hC
      rw [hC] at hEqJ; cases hEqJ
    · simp only [hJ, ↓reduceIte] at hC
      rcases hC with h1 | h2 <;> (rw [hEqJ] at *; cases ‹_›)
  have hNatSum0 : ∀ {xs : List Nat}, (∀ x ∈ xs, x = 0) → xs.sum = 0 := by
    intro xs hZ
    induction xs with
    | nil => rfl
    | cons a tl ih =>
      simp [hZ a (List.mem_cons_self ..), ih fun y hy => hZ y (List.mem_cons_of_mem _ hy)]
  have hSumZero : ∀ (f : SlotState → Nat),
      f .claimed = 0 → f .freeAvail = 0 → f .freeInactive = 0 →
      (g.slots.map f).sum = 0 := by
    intro f hC hA hI
    apply hNatSum0
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj, hsJ⟩ := List.getElem_of_mem hs
    rw [← hsJ]
    have hCh := hSlotsChar j hj
    by_cases hJ : j = idx
    · subst hJ
      simp only [↓reduceIte] at hCh; rw [hCh, hC]
    · simp only [hJ, ↓reduceIte] at hCh
      rcases hCh with h1 | h2
      · rw [h1, hA]
      · rw [h2, hI]
  have hNoChild : ∀ cg ∈ st.groups, cg.parentMeta ≠ some g.metaPtr := by
    intro cg hcg hPar
    have hCgWf := hwf.groups_wf cg hcg
    have hMap0 : cg.maplen = 0 := by
      by_cases hPos : 0 < cg.maplen
      · have hNone := hCgWf.2.2.2.2.2.2.2.2.2.2.1.mp hPos
        rw [hPar] at hNone; cases hNone
      · omega
    obtain ⟨_, pg, hpg, pIdx, hp, hPgSome, _, _, _, hSlotNest, _, _, _⟩ :=
      hCgWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hMap0
    rw [hPar] at hPgSome
    injection hPgSome with hMetaEq
    have hPgEq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hg hMetaEq.symm
    subst pg
    have hCh := hSlotsChar pIdx hp
    rw [hSlotNest] at hCh
    by_cases hJ : pIdx = idx <;> simp [hJ] at hCh
  exact ⟨hSlotsChar, hClaim1, hSumZero slotEffCost rfl rfl rfl,
    hSumZero slotLiveCount rfl rfl rfl, hNoLiveUser, hNoChild⟩

/-! ## Reserved-Meta Recycling Transitions -/

theorem erase_nodup_and_mem {α : Type} [BEq α] [LawfulBEq α] {xs : List α}
    (hNd : xs.Nodup) (m : α) :
    (xs.erase m).Nodup ∧
    (∀ x, x ∈ xs.erase m ↔ (x ∈ xs ∧ x ≠ m)) ∧
    (m ∈ xs → (xs.erase m).length + 1 = xs.length) := by
  induction xs with
  | nil => simp
  | cons a tl ih =>
    obtain ⟨haNotTl, hNdTl⟩ := List.nodup_cons.mp hNd
    obtain ⟨hErNd, hErMem, hErLen⟩ := ih hNdTl
    by_cases hEq : a == m
    · have haEq : a = m := beq_iff_eq.mp hEq
      subst haEq
      simp only [List.erase_cons_head, hNdTl, true_and]
      refine ⟨fun x => ⟨fun hx => ⟨List.mem_cons_of_mem _ hx, fun hxm => haNotTl (hxm ▸ hx)⟩,
        fun ⟨hx, hne⟩ => ?_⟩, fun _ => rfl⟩
      rcases List.mem_cons.mp hx with rfl | hxtl
      · exact False.elim (hne rfl)
      · exact hxtl
    · simp only [List.erase_cons_tail hEq]
      have haNe : a ≠ m := fun h => by subst h; simp at hEq
      refine ⟨List.nodup_cons.mpr ⟨fun haIn => haNotTl ((hErMem a).mp haIn).1, hErNd⟩,
        fun x => ?_, fun hmIn => ?_⟩
      · constructor
        · intro hx
          rcases List.mem_cons.mp hx with rfl | hxEr
          · exact ⟨List.mem_cons_self .., haNe⟩
          · obtain ⟨hxtl, hne⟩ := (hErMem x).mp hxEr
            exact ⟨List.mem_cons_of_mem _ hxtl, hne⟩
        · rintro ⟨hx, hne⟩
          rcases List.mem_cons.mp hx with rfl | hxtl
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ ((hErMem x).mpr ⟨hxtl, hne⟩)
      · rcases List.mem_cons.mp hmIn with rfl | hmtl
        · exact False.elim (haNe rfl)
        · simp only [List.length_cons]
          have := hErLen hmtl
          omega

theorem nodup_move_erase_to_mid {α : Type} [BEq α] [LawfulBEq α]
    {a b c d : List α} {m : α}
    (hNd : (a ++ b ++ c ++ d).Nodup) (hm : m ∈ d) :
    (a ++ (b ++ [m]) ++ c ++ d.erase m).Nodup ∧
    (∀ x, x ∈ (a ++ (b ++ [m]) ++ c ++ d.erase m) ↔ x ∈ (a ++ b ++ c ++ d)) := by
  have ⟨hNdABC, hNdD, hDisjD⟩ := List.nodup_append.mp hNd
  have ⟨hNdAB, hNdC, hDisjC⟩ := List.nodup_append.mp hNdABC
  have ⟨hNdA, hNdB, hDisjB⟩ := List.nodup_append.mp hNdAB
  obtain ⟨hErNd, hErMem, _⟩ := erase_nodup_and_mem hNdD m
  have hmNotABC : m ∉ a ++ b ++ c := fun h => hDisjD m h m hm rfl
  have hmNotA : m ∉ a := fun h => hmNotABC (List.mem_append_left _ (List.mem_append_left _ h))
  have hmNotB : m ∉ b := fun h => hmNotABC (List.mem_append_left _ (List.mem_append_right _ h))
  have hmNotC : m ∉ c := fun h => hmNotABC (List.mem_append_right _ h)
  have hNdBM : (b ++ [m]).Nodup :=
    List.nodup_append.mpr ⟨hNdB, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
      fun x hx y hy hEq => by simp at hy; subst hy hEq; exact hmNotB hx⟩
  have hNdABM : (a ++ (b ++ [m])).Nodup :=
    List.nodup_append.mpr ⟨hNdA, hNdBM, fun x hx y hy hEq => by
      subst hEq
      rcases List.mem_append.mp hy with hyb | hym
      · exact hDisjB x hx x hyb rfl
      · simp at hym; subst hym; exact hmNotA hx⟩
  have hNdABMC : (a ++ (b ++ [m]) ++ c).Nodup :=
    List.nodup_append.mpr ⟨hNdABM, hNdC, fun x hx y hy hEq => by
      subst hEq
      rcases List.mem_append.mp hx with hxa | hxbm
      · exact hDisjC x (List.mem_append_left _ hxa) x hy rfl
      · rcases List.mem_append.mp hxbm with hxb | hxm
        · exact hDisjC x (List.mem_append_right _ hxb) x hy rfl
        · simp at hxm; subst hxm; exact hmNotC hy⟩
  have hNdAll : (a ++ (b ++ [m]) ++ c ++ d.erase m).Nodup :=
    List.nodup_append.mpr ⟨hNdABMC, hErNd, fun x hx y hy hEq => by
      subst hEq
      obtain ⟨hyd, hxNeM⟩ := (hErMem x).mp hy
      rcases List.mem_append.mp hx with hxabm | hxc
      · rcases List.mem_append.mp hxabm with hxa | hxbm
        · exact hDisjD x (List.mem_append_left _ (List.mem_append_left _ hxa)) x hyd rfl
        · rcases List.mem_append.mp hxbm with hxb | hxm
          · exact hDisjD x (List.mem_append_left _ (List.mem_append_right _ hxb)) x hyd rfl
          · simp at hxm; exact hxNeM hxm
      · exact hDisjD x (List.mem_append_right _ hxc) x hyd rfl⟩
  refine ⟨hNdAll, fun x => ?_⟩
  simp only [List.mem_append, List.mem_singleton, hErMem]
  constructor
  · rintro (((ha | (hb | rfl)) | hc) | ⟨hd, _⟩)
    · exact Or.inl (Or.inl (Or.inl ha))
    · exact Or.inl (Or.inl (Or.inr hb))
    · exact Or.inr hm
    · exact Or.inl (Or.inr hc)
    · exact Or.inr hd
  · rintro (((ha | hb) | hc) | hd)
    · exact Or.inl (Or.inl (Or.inl ha))
    · exact Or.inl (Or.inl (Or.inr (Or.inl hb)))
    · exact Or.inl (Or.inr hc)
    · by_cases hEq : x = m
      · subst hEq; exact Or.inl (Or.inl (Or.inr (Or.inr rfl)))
      · exact Or.inr ⟨hd, hEq⟩

theorem metaSlot_disjoint_of_ne {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {m1 m2 : BitVec 64} (hm1 : m1 ∈ allMetaSlots st) (hm2 : m2 ∈ allMetaSlots st)
    (hNe : m1 ≠ m2) {a : BitVec 64} (ha1 : InRegion m1 40 a) (ha2 : InRegion m2 40 a) :
    False :=
  DisjointRegions.not_both ((allMetaSlots_info hwf hm1).2.2.2.2 m2 hm2 (Ne.symm hNe)) ha1 ha2

theorem allMetaSlot_disjoint_other {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {x : BitVec 64} (hx : x ∈ allMetaSlots st) :
    x ≠ 0#64 ∧
    (∃ ma ∈ st.metaAreas, ∀ a, InRegion x 40 a → InRegion ma.base 4096 a) ∧
    (∀ a, InRegion x 40 a → ¬ CarvedUserByte st a) ∧
    (∀ ma ∈ st.metaAreas, ∀ a, InRegion ma.base 24 a → ¬ InRegion x 40 a) ∧
    (∀ ap ∈ st.availMetaPages, ∀ a, InRegion ap 4096 a → ¬ InRegion x 40 a) ∧
    (∀ gp ∈ st.guardPages, ∀ a, InRegion gp 4096 a → ¬ InRegion x 40 a) ∧
    (∀ g ∈ st.groups, 0 < g.maplen → ∀ a, InRegion g.mem (g.maplen * 4096) a → ¬ InRegion x 40 a) := by
  have hxUnf := hx; unfold allMetaSlots at hxUnf
  obtain ⟨maX, hmaX, hkXm⟩ := List.mem_flatMap.mp hxUnf
  obtain ⟨kX, hkXr, hSlotX⟩ := List.mem_map.mp hkXm
  obtain ⟨hLoX, hAlX, hHiX, _⟩ := hwf.metaAreas_wf.2.1 maX hmaX
  obtain ⟨hNatX, hSlotLoX, _, hSlotFitX, hSubX⟩ := slotAddr_bounds hLoX hAlX hHiX (List.mem_range.mp hkXr)
  have hxNe0 : x ≠ 0#64 := fun h0 => by rw [hSlotX, h0] at hSlotLoX; simp at hSlotLoX
  have hSubMa : ∀ a, InRegion x 40 a → InRegion maX.base 4096 a := fun a ha => hSubX a (hSlotX ▸ ha)
  have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd
  rw [List.append_assoc, List.append_assoc, PairwiseDisjointRegions.append_iff] at hpd
  refine ⟨hxNe0, ⟨maX, hmaX, hSubMa⟩,
    fun a haX hCu => ?_,
    fun ma hma a ha24 haX => ?_,
    fun ap hap a haAp haX => ?_,
    fun gp hgp a haGp haX => ?_,
    fun g hg hMp a haG haX =>
      DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hmaX hg hMp) (hSubMa a haX) haG⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, gr, hgr, hgrPos, haGr⟩ := carvedUserByte_witness hwf hCu
    exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hmaX hgr hgrPos) (hSubMa a haX) haGr
  · by_cases hEqMa : ma = maX
    · subst hEqMa
      have ⟨_, haHi⟩ := (inRegion_iff_toNat (by omega) a).mp ha24
      have ⟨hxLo, _⟩ := (inRegion_iff_toNat (by rw [← hSlotX]; omega) a).mp haX
      rw [← hSlotX, hNatX] at hxLo; omega
    · obtain ⟨i1, hi1, hget1⟩ := List.getElem_of_mem hma
      obtain ⟨i2, hi2, hget2⟩ := List.getElem_of_mem hmaX
      have hij : i1 ≠ i2 := fun h => hEqMa (hget1.symm.trans (h ▸ hget2))
      let metaRegs := st.metaAreas.map fun m => (m.base, 4096)
      have hlen : metaRegs.length = st.metaAreas.length := List.length_map _
      have hdisj := PairwiseDisjointRegions.getElem_disjoint hpd.1 (hlen ▸ hi1) (hlen ▸ hi2) hij
      have hm1 : metaRegs[i1]'(hlen ▸ hi1) = (ma.base, 4096) := by
        simp only [metaRegs, List.getElem_map]; exact congrArg (fun m => (m.base, 4096)) hget1
      have hm2 : metaRegs[i2]'(hlen ▸ hi2) = (maX.base, 4096) := by
        simp only [metaRegs, List.getElem_map]; exact congrArg (fun m => (m.base, 4096)) hget2
      rw [hm1, hm2] at hdisj
      have ⟨haLo, haHi⟩ := (inRegion_iff_toNat (by have := hwf.metaAreas_wf.2.1 ma hma; omega) a).mp ha24
      have ha4096 : InRegion ma.base 4096 a :=
        (inRegion_iff_toNat (by have := hwf.metaAreas_wf.2.1 ma hma; omega) a).mpr ⟨haLo, by omega⟩
      exact DisjointRegions.not_both hdisj ha4096 (hSubMa a haX)
  · exact DisjointRegions.not_both
      (hpd.2.2 (maX.base, 4096) (List.mem_map_of_mem hmaX) (ap, 4096)
        (List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hap))))
      (hSubMa a haX) haAp
  · exact DisjointRegions.not_both
      (hpd.2.2 (maX.base, 4096) (List.mem_map_of_mem hmaX) (gp, 4096)
        (List.mem_append_left _ (List.mem_map_of_mem hgp)))
      (hSubMa a haX) haGp

theorem reservedMeta_common_props {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {m : BitVec 64} (hmRes : m ∈ st.reservedMetas) :
    m ≠ 0#64 ∧
    m ∈ allMetaSlots st ∧
    (∃ ma ∈ st.metaAreas, ∀ a, InRegion m 40 a → InRegion ma.base 4096 a) ∧
    (∀ a, InRegion m 40 a → ¬ OwnedRwByte st a ∧ ¬ CarvedUserByte st a) ∧
    (∀ a, (∃ x ∈ st.reservedMetas.erase m, InRegion x 40 a) ↔
      (CarvedMetaByte st a ∧ ¬ InRegion m 40 a)) ∧
    (∀ ma ∈ st.metaAreas, ∀ a, InRegion ma.base 24 a → ¬ InRegion m 40 a) ∧
    (∀ ap ∈ st.availMetaPages, ∀ a, InRegion ap 4096 a → ¬ InRegion m 40 a) ∧
    (∀ gp ∈ st.guardPages, ∀ a, InRegion gp 4096 a → ¬ InRegion m 40 a) ∧
    (∀ fm ∈ st.freeMetas, ∀ a, InRegion fm.ptr 40 a → ¬ InRegion m 40 a) ∧
    (∀ bm ∈ st.bumpMetas, ∀ a, InRegion bm 40 a → ¬ InRegion m 40 a) ∧
    (∀ g ∈ st.groups, ∀ a,
      (InRegion g.metaPtr 40 a ∨ (0 < g.maplen ∧ InRegion g.mem (g.maplen * 4096) a)) →
        ¬ InRegion m 40 a) := by
  have ⟨_, _, _, _, hUfNd, hUfIff⟩ := hwf.free_bump_metas_wf
  have hmAll : m ∈ allMetaSlots st := (hUfIff m).mp (List.mem_append_right _ hmRes)
  obtain ⟨hmNe0, hSubMa, hNotCu, hDisjMa, hDisjAp, hDisjGp, hDisjRoot⟩ :=
    allMetaSlot_disjoint_other hwf hmAll
  have ⟨_, hResNd, hLeftDisj⟩ := List.nodup_append.mp hUfNd
  obtain ⟨_, hErMem, _⟩ := erase_nodup_and_mem hResNd m
  have hCarvedEr : ∀ a, (∃ x ∈ st.reservedMetas.erase m, InRegion x 40 a) ↔
      (CarvedMetaByte st a ∧ ¬ InRegion m 40 a) := by
    intro a; constructor
    · rintro ⟨x, hxEr, haX⟩
      obtain ⟨hxRes, hxNe⟩ := (hErMem x).mp hxEr
      have hxAll : x ∈ allMetaSlots st := (hUfIff x).mp (List.mem_append_right _ hxRes)
      exact ⟨⟨x, hxRes, haX⟩, fun haM => metaSlot_disjoint_of_ne hwf hxAll hmAll hxNe haX haM⟩
    · rintro ⟨⟨x, hxRes, haX⟩, hNotM⟩
      have hxNe : x ≠ m := fun hEq => by subst hEq; exact hNotM haX
      exact ⟨x, (hErMem x).mpr ⟨hxRes, hxNe⟩, haX⟩
  refine ⟨hmNe0, hmAll, hSubMa,
    fun a ha => ⟨fun hRw => hRw.2.2 ⟨m, hmRes, ha⟩, hNotCu a ha⟩,
    hCarvedEr, hDisjMa, hDisjAp, hDisjGp,
    fun fm hfm a ha haM => ?_,
    fun bm hbm a ha haM => ?_,
    fun g hg a hGA haM => ?_⟩
  · have hfmUf : fm.ptr ∈ st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas :=
      List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hfm))
    exact metaSlot_disjoint_of_ne hwf ((hUfIff fm.ptr).mp (List.mem_append_left _ hfmUf)) hmAll
      (fun hEq => hLeftDisj fm.ptr hfmUf m hmRes hEq) ha haM
  · have hbmUf : bm ∈ st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas :=
      List.mem_append_right _ hbm
    exact metaSlot_disjoint_of_ne hwf ((hUfIff bm).mp (List.mem_append_left _ hbmUf)) hmAll
      (fun hEq => hLeftDisj bm hbmUf m hmRes hEq) ha haM
  · rcases hGA with haMeta | ⟨hMp, haMem⟩
    · have hgUf : g.metaPtr ∈ st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas :=
        List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))
      exact metaSlot_disjoint_of_ne hwf ((hUfIff g.metaPtr).mp (List.mem_append_left _ hgUf)) hmAll
        (fun hEq => hLeftDisj g.metaPtr hgUf m hmRes hEq) haMeta haM
    · exact hDisjRoot g hg hMp a haMem haM

theorem nodup_filter_pred {α : Type} (p : α → Bool) {xs : List α} (h : xs.Nodup) :
    (xs.filter p).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a tl ih =>
    obtain ⟨haNot, hTl⟩ := List.nodup_cons.mp h
    by_cases hp : p a = true
    · simp only [List.filter_cons_of_pos hp]
      exact List.nodup_cons.mpr ⟨fun hIn => haNot (List.mem_filter.mp hIn).1, ih hTl⟩
    · simp only [List.filter_cons_of_neg hp]
      exact ih hTl

def extendDom40 (dom : List (BitVec 64)) (m : BitVec 64) : List (BitVec 64) :=
  dom ++ (rangeAddrs m 40).filter (fun x => !decide (x ∈ dom))

theorem extendDom40_props {dom : List (BitVec 64)} (hNd : dom.Nodup) (m : BitVec 64) :
    (extendDom40 dom m).Nodup ∧
    (∀ a, InRegion m 40 a → a ∈ extendDom40 dom m) ∧
    (∀ a ∈ extendDom40 dom m, a ∈ dom ∨ InRegion m 40 a) ∧
    (∀ {P : BitVec 64 → Prop} [DecidablePred P] (f : BitVec 64 → SepProp),
      (∀ a, P a → a ∈ dom) →
      SetSep (extendDom40 dom m) P f = SetSep dom P f) := by
  have h40 : (40 : Nat) ≤ 2 ^ 64 := by decide
  have hFiltNd : ((rangeAddrs m 40).filter (fun x => !decide (x ∈ dom))).Nodup :=
    nodup_filter_pred _ (nodup_rangeAddrs m h40)
  have hNdExt : (extendDom40 dom m).Nodup :=
    List.nodup_append.mpr ⟨hNd, hFiltNd, fun x hx y hy hEq => by
      subst hEq
      have hNot := (List.mem_filter.mp hy).2
      simp [hx] at hNot⟩
  refine ⟨hNdExt, fun a ha => ?_, fun a ha => ?_, fun {P} _ f hImp => ?_⟩
  · by_cases hIn : a ∈ dom
    · exact List.mem_append_left _ hIn
    · exact List.mem_append_right _ (List.mem_filter.mpr
        ⟨(mem_rangeAddrs_iff_inRegion m h40 a).mpr ha, by simp [hIn]⟩)
  · rcases List.mem_append.mp ha with hIn | hF
    · exact Or.inl hIn
    · exact Or.inr ((mem_rangeAddrs_iff_inRegion m h40 a).mp (List.mem_filter.mp hF).1)
  · exact SetSep_append_right_empty f fun x hx hp => by
      have hNot := (List.mem_filter.mp hx).2
      have hIn := hImp x hp
      simp [hIn] at hNot

set_option maxHeartbeats 400000 in
/-- `free_meta` when `st.ctx.freeMetaHead = 0#64`: sets `ctx.freeMetaHead := m` and
    `freeMetas := [⟨m, m, m⟩]`, pops `m` from `st.reservedMetas`, and absorbs
    `(m ↦ₛ ⟨m, m, m⟩.toBytes)` into `ByteMap` (`MallocngWFInflight (k + 1)` to
    `MallocngWFInflight k`). -/
theorem free_recycle_reserved_meta_empty {k : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight (k + 1) base brkStart brk liveCost peakCost st)
    {m : BitVec 64} (hmRes : m ∈ st.reservedMetas)
    (hHead0 : st.ctx.freeMetaHead = 0#64) :
    let fmNew : FreeMetaDesc := ⟨m, m, m⟩
    let dom1 := extendDom40 st.masterDom m
    let bv1 := writeBytesToMap st.byteVal m fmNew.toBytes
    let st1 : MallocngSt :=
      { st with
        ctx           := { st.ctx with freeMetaHead := m }
        freeMetas     := [fmNew]
        reservedMetas := st.reservedMetas.erase m
        masterDom     := dom1
        byteVal       := bv1 }
    (((m ↦ₛ fmNew.toBytes) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal) =
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal) ∧
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧
    MappedSet st1.masterDom (OwnedMappedByte st1) =
      MappedSet st.masterDom (OwnedMappedByte st) ∧
    MallocngWFInflight k base brkStart brk liveCost peakCost st1 ∧
    st1.reservedMetas = st.reservedMetas.erase m ∧
    dynamicRootRegions st1 = dynamicRootRegions st ∧
    totalLiveCount st1 = totalLiveCount st := by
  dsimp only []
  let fmNew : FreeMetaDesc := ⟨m, m, m⟩
  let dom1 := extendDom40 st.masterDom m
  let bv1 := writeBytesToMap st.byteVal m fmNew.toBytes
  let st1 : MallocngSt :=
    { st with
      ctx           := { st.ctx with freeMetaHead := m }
      freeMetas     := [fmNew]
      reservedMetas := st.reservedMetas.erase m
      masterDom     := dom1
      byteVal       := bv1 }
  have ⟨hmNe0, _, ⟨maM, hmaM, hSubMa⟩, hNotRwCu, hCarvedEr, hDisjMa, hDisjAp, hDisjGp,
    _, hDisjBm, hDisjGrp⟩ := reservedMeta_common_props hwf hmRes
  have ⟨hDomNd1, hMInDom1, hDom1Split, hSetSepExt⟩ := extendDom40_props hwf.masterDom_wf.1 m
  have ⟨hDll0, _, hBumpOr, hBumpBytes, hUfNd, hUfIff⟩ := hwf.free_bump_metas_wf
  have hFmNil : st.freeMetas = [] := by
    cases hF : st.freeMetas with
    | nil => rfl
    | cons hd tl =>
      have hDllC : CircularDllWf 0#64 ((hd.ptr, hd.prev, hd.next) ::
          tl.map fun x => (x.ptr, x.prev, x.next)) := by simpa [hF, hHead0] using hDll0
      exact False.elim (hDllC.2.2.1 (hd.ptr, hd.prev, hd.next) (List.mem_cons_self ..) hDllC.1.symm)
  have hInit1 : st.ctx.initDone = 1#32 := by
    rcases hwf.initDone_wf with h0 | h1
    · have := (hwf.initZero_wf h0).2.2.2.2.2.2.2.2.1; rw [this] at hmRes; cases hmRes
    · exact h1
  have hOwnIff : ∀ a : BitVec 64, OwnedRwByte st1 a ↔ (OwnedRwByte st a ∨ InRegion m 40 a) := by
    intro a; unfold OwnedRwByte
    have hCuEq : CarvedUserByte st1 a ↔ CarvedUserByte st a := Iff.rfl
    have hCm1 : CarvedMetaByte st1 a ↔ (CarvedMetaByte st a ∧ ¬ InRegion m 40 a) := hCarvedEr a
    change (((∃ ma ∈ st.metaAreas, InRegion ma.base 4096 a) ∨
        (∃ g ∈ st.groups, 0 < g.maplen ∧ InRegion g.mem (g.maplen * 4096) a)) ∧
        ¬ CarvedUserByte st1 a ∧ ¬ CarvedMetaByte st1 a) ↔ _
    rw [hCuEq, hCm1]
    constructor
    · rintro ⟨hSrc, hNCu, hNCm⟩
      by_cases haM : InRegion m 40 a
      · exact Or.inr haM
      · exact Or.inl ⟨hSrc, hNCu, fun hCm => hNCm ⟨hCm, haM⟩⟩
    · rintro (⟨hSrc, hNCu, hNCm⟩ | haM)
      · exact ⟨hSrc, hNCu, fun ⟨hCm, _⟩ => hNCm hCm⟩
      · exact ⟨Or.inl ⟨maM, hmaM, hSubMa a haM⟩, (hNotRwCu a haM).2, fun ⟨_, hNM⟩ => hNM haM⟩
  have hByteAbs : ((m ↦ₛ fmNew.toBytes) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal) =
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal := by
    have hExtRw : ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
        ByteMap dom1 (OwnedRwByte st) st.byteVal :=
      (hSetSepExt _ fun a hRw => hwf.masterDom_wf.2.1 a (Or.inl hRw)).symm
    rw [hExtRw, ByteMap_absorb_slice hDomNd1 st.byteVal m fmNew.toBytes
      (by simp) (fun a ha => hMInDom1 a (by simpa using ha))
      (fun a ha => (hNotRwCu a (by simpa using ha)).1)]
    exact SetSep_congr (fun a _ => by simp only [FreeMetaDesc.toBytes_length]; exact (hOwnIff a).symm)
      (fun _ _ _ => rfl)
  have hProtEq : ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal := by
    have hExtPn : ProtNoneByteMap dom1 (OwnedProtNoneByte st) bv1 =
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) bv1 :=
      hSetSepExt _ fun a hPn => hwf.masterDom_wf.2.1 a (Or.inr (Or.inl hPn))
    change ProtNoneByteMap dom1 (OwnedProtNoneByte st) bv1 = _
    rw [hExtPn]
    exact SetSep_congr (fun _ _ => Iff.rfl) fun a _ hPn => by
      have hNotM : ¬ InRegion m 40 a := by
        rcases hPn with ⟨gp, hgp, ha⟩ | ⟨ap, hap, ha⟩
        · exact hDisjGp gp hgp a ha
        · exact hDisjAp ap hap a ha
      exact congrArg (a ↦₈ₙ ·)
        (writeBytesToMap_out st.byteVal m fmNew.toBytes (by simpa using hNotM))
  have hMapSetEq : MappedSet st1.masterDom (OwnedMappedByte st1) =
      MappedSet st.masterDom (OwnedMappedByte st) :=
    hSetSepExt _ fun a hMp => hwf.masterDom_wf.2.1 a (Or.inr (Or.inr hMp))
  have ⟨_, _, hErLen⟩ := erase_nodup_and_mem (List.nodup_append.mp hUfNd).2.1 m
  have hLenRes := hErLen hmRes
  have hGrpAct := groups_active_wf_congr hwf (st' := st1) rfl rfl rfl fun g hg a hGA =>
    writeBytesToMap_out st.byteVal m fmNew.toBytes (by simpa using hDisjGrp g hg a hGA)
  have ⟨hUfNd1, hUfMem1⟩ := nodup_move_erase_to_mid
    (a := st.groups.map (·.metaPtr)) (b := []) (c := st.bumpMetas) (d := st.reservedMetas)
    (by simpa [hFmNil] using hUfNd) hmRes
  have hDll1 : CircularDllWf m [(m, m, m)] := CircularDllWf.singleton hmNe0
  have hWf1 : MallocngWFInflight k base brkStart brk liveCost peakCost st1 :=
    { base_wf := trivial
      brk_bounds := hwf.brk_bounds
      ctx_lens := hwf.ctx_lens
      initDone_wf := hwf.initDone_wf
      initZero_wf := fun h0 => by simp [st1, hInit1] at h0
      bounces_wf := hwf.bounces_wf
      usage_wf := hwf.usage_wf
      brk_mode_wf := hwf.brk_mode_wf
      metaAreas_wf := ⟨hwf.metaAreas_wf.1, fun ma hma => by
        obtain ⟨h1, h2, h3, hHdr⟩ := hwf.metaAreas_wf.2.1 ma hma
        refine ⟨h1, h2, h3, (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => ?_).trans hHdr⟩
        exact writeBytesToMap_out st.byteVal m fmNew.toBytes (by simpa using hDisjMa ma hma a ha),
        hwf.metaAreas_wf.2.2⟩
      guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1,
        fun ap hap => by
          obtain ⟨h1, h2, h3, hZ⟩ := hwf.guard_avail_wf.2.2.2 ap hap
          refine ⟨h1, h2, h3, (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => ?_).trans hZ⟩
          exact writeBytesToMap_out st.byteVal m fmNew.toBytes (by simpa using hDisjAp ap hap a ha)⟩
      inflight_wf := by
        have hInf := hwf.inflight_wf
        have hClEq : totalClaimedSlots st1 = totalClaimedSlots st := rfl
        change (st.reservedMetas.erase m).length + totalClaimedSlots st1 ≤ k
        omega
      free_bump_metas_wf := ⟨hDll1,
        fun fm hfm => by
          simp only [st1, List.mem_singleton] at hfm; subst hfm
          exact readBytesFromMap_writeBytesToMap st.byteVal m fmNew.toBytes (by simp),
        hBumpOr,
        fun bm hbm =>
          (readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
            writeBytesToMap_out st.byteVal m fmNew.toBytes (by simpa using hDisjBm bm hbm a ha)).trans
            (hwf.free_bump_metas_wf.2.2.2.1 bm hbm),
        by simpa [st1] using hUfNd1,
        fun x => by
          change x ∈ st.groups.map (·.metaPtr) ++ [m] ++ st.bumpMetas ++ st.reservedMetas.erase m ↔
            x ∈ allMetaSlots st
          have hM := hUfMem1 x
          simp only [List.nil_append] at hM
          have hU := hUfIff x
          rw [hFmNil, List.map_nil] at hU
          exact hM.trans hU⟩
      groups_nodup := hwf.groups_nodup
      groups_wf := hGrpAct.1
      regions_disjoint := hwf.regions_disjoint
      active_wf := hGrpAct.2.1
      liveMap_wf := hwf.liveMap_wf
      live_le_peak := hwf.live_le_peak
      effCost_le_live := hwf.effCost_le_live
      meta_pages_bound := hwf.meta_pages_bound
      empty_groups_bound := hwf.empty_groups_bound
      masterDom_wf := ⟨hDomNd1,
        fun a hOwn => by
          rcases hOwn with hRw1 | hPn1 | hMp1
          · rcases (hOwnIff a).mp hRw1 with hRw0 | haM
            · exact List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inl hRw0))
            · exact hMInDom1 a haM
          · exact List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inr (Or.inl hPn1)))
          · exact List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inr (Or.inr hMp1))),
        fun a ha => by
          rcases hDom1Split a ha with hIn0 | haM
          · exact hwf.masterDom_wf.2.2 a hIn0
          · exact ⟨(maM.base, 4096),
              List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_left _ (List.mem_map_of_mem hmaM))),
              hSubMa a haM⟩⟩ }
  exact ⟨hByteAbs, hProtEq, hMapSetEq, hWf1, rfl, rfl, rfl⟩

end VerifiedLibraries.Mallocng.Proofs
