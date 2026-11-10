/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Internal

/-!
# Invariant and `ByteMap` Helpers for Mallocng Slot Allocation

Proves count-table bounds, `CircularDllWf` list operations, `GroupDesc.metaBytes` and
`CtxFields.toBytes` decompositions, and `OwnedRwByte` disjointness and nesting properties for
`try_avail`, `alloc_group`, and `alloc_slot`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Count-Table and Page-Span Bounds -/

def ValidNestedCnt (sc cnt : Nat) : Prop :=
  2 ≤ cnt ∧ cnt ≤ 32 ∧ cnt * slotStride sc + 16 ≤ 2048 ∧
  (sc ≤ 8 → cnt = (smallCntTabBytes.getD (3 * sc) 0#8).toNat ∨
    cnt = (smallCntTabBytes.getD (3 * sc + 1) 0#8).toNat ∨
    cnt = (smallCntTabBytes.getD (3 * sc + 2) 0#8).toNat)

private def checkSmallCntProps : Bool :=
  (List.range 9).all fun sc =>
    let c0 := (smallCntTabBytes.getD (3 * sc) 0#8).toNat
    let c1 := (smallCntTabBytes.getD (3 * sc + 1) 0#8).toNat
    let c2 := (smallCntTabBytes.getD (3 * sc + 2) 0#8).toNat
    (4 ≤ c0 && c0 ≤ 31) && (4 ≤ c1 && c1 ≤ 31) && (4 ≤ c2 && c2 ≤ 31) &&
    (c0 * slotStride sc ≤ 1048575) && (c1 * slotStride sc ≤ 1048575) && (c2 * slotStride sc ≤ 1048575) &&
    (if sc ≤ 6 then (c0 * slotStride sc + 16 ≤ 2048) && (c1 * slotStride sc + 16 ≤ 2048) &&
      (c2 * slotStride sc + 16 ≤ 2048) else true)

private theorem checkSmallCntProps_true : checkSmallCntProps = true := by decide +kernel

theorem smallCntTab_bounds {sc j : Nat} (hsc : sc ≤ 8) (hj : j < 3) :
    let c := (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat
    4 ≤ c ∧ c ≤ 31 ∧ c * slotStride sc ≤ 1048575 ∧ (sc ≤ 6 → c * slotStride sc + 16 ≤ 2048) := by
  have h := List.all_eq_true.mp checkSmallCntProps_true sc (List.mem_range.mpr (by omega))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · simp only [Nat.add_zero]; refine ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.2, fun h6 => ?_⟩
    have hsub := h.2; simp only [h6, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hsub; exact hsub.1.1
  · refine ⟨h.1.1.1.1.1.2.1, h.1.1.1.1.1.2.2, h.1.1.2, fun h6 => ?_⟩
    have hsub := h.2; simp only [h6, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hsub; exact hsub.1.2
  · refine ⟨h.1.1.1.1.2.1, h.1.1.1.1.2.2, h.1.2, fun h6 => ?_⟩
    have hsub := h.2; simp only [h6, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hsub; exact hsub.2

private def checkMedCntProps : Bool :=
  (List.range 48).all fun sc =>
    let mc := (medCntTabBytes.getD (sc % 4) 0#8).toNat
    (20 ≤ mc && mc ≤ 32 && mc % 2 == 0) && (if 9 ≤ sc && sc ≤ 25 then mc * slotStride sc + 16 ≤ 65536 else true)

private theorem checkMedCntProps_true : checkMedCntProps = true := by decide +kernel

theorem medCntTab_bounds {sc : Nat} (hsc : sc < 48) :
    let mc := (medCntTabBytes.getD (sc % 4) 0#8).toNat
    20 ≤ mc ∧ mc ≤ 32 ∧ mc % 2 = 0 ∧ (9 ≤ sc → sc ≤ 25 → mc * slotStride sc + 16 ≤ 65536) := by
  have h := List.all_eq_true.mp checkMedCntProps_true sc (List.mem_range.mpr hsc)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  refine ⟨h.1.1.1, h.1.1.2, h.1.2, fun h9 h25 => ?_⟩
  have hsub := h.2; simp only [h9, h25, and_self, ↓reduceIte, decide_eq_true_eq] at hsub; exact hsub

private def checkNestedParentGrid : Bool :=
  (List.range 48).all fun sc => (List.range 33).all fun cnt =>
    if 2 ≤ cnt && cnt * slotStride sc + 16 ≤ 2048 &&
       (if sc ≤ 8 then cnt == (smallCntTabBytes.getD (3 * sc) 0#8).toNat ||
          cnt == (smallCntTabBytes.getD (3 * sc + 1) 0#8).toNat ||
          cnt == (smallCntTabBytes.getD (3 * sc + 2) 0#8).toNat else true) then
      let needed := cnt * slotStride sc + 12; let u := cnt * sizeClass sc; let pSc := sizeToClassUnits u
      (sc ≤ 19) && ((needed + 3) / 16 == u) && (sc < pSc) && (pSc ≤ 24) &&
      (needed ≤ nominalSlotCap pSc) && (allocSlotDepthBound pSc < allocSlotDepthBound sc)
    else true

private theorem checkNestedParentGrid_true : checkNestedParentGrid = true := by decide +kernel

theorem nestedParentSc_spec {sc cnt : Nat} (hsc : sc < 48) (hv : ValidNestedCnt sc cnt) :
    let needed := cnt * slotStride sc + 12; let u := cnt * sizeClass sc; let pSc := sizeToClassUnits u
    sc ≤ 19 ∧ (needed + 3) / 16 = u ∧ sc < pSc ∧ pSc ≤ 24 ∧
    needed ≤ nominalSlotCap pSc ∧ allocSlotDepthBound pSc < allocSlotDepthBound sc := by
  obtain ⟨hlo, hhi, hspan, hsmall⟩ := hv
  have h1 := List.all_eq_true.mp checkNestedParentGrid_true sc (List.mem_range.mpr hsc)
  have h2 := List.all_eq_true.mp h1 cnt (List.mem_range.mpr (by omega))
  have hcond : (2 ≤ cnt && cnt * slotStride sc + 16 ≤ 2048 &&
      (if sc ≤ 8 then cnt == (smallCntTabBytes.getD (3 * sc) 0#8).toNat ||
         cnt == (smallCntTabBytes.getD (3 * sc + 1) 0#8).toNat ||
         cnt == (smallCntTabBytes.getD (3 * sc + 2) 0#8).toNat else true)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; refine ⟨⟨hlo, hspan⟩, ?_⟩
    split <;> rename_i hle8
    · simp only [Bool.or_eq_true, beq_iff_eq]
      rcases hsmall hle8 with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rfl
  simp only [hcond, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
  exact ⟨h2.1.1.1.1.1, h2.1.1.1.1.2, h2.1.1.1.2, h2.1.1.2, h2.1.2, h2.2⟩

def pageSpanSteps (stride : BitVec 32) : Nat → BitVec 32 → BitVec 32 → Option (BitVec 32 × BitVec 32)
  | 0, _, _ => none
  | fuel + 1, cnt, span =>
    let span' := stride + span
    if ((span' - 1#32) ^^^ span).slt 4096#32 then pageSpanSteps stride fuel (cnt + 1#32) span'
    else some (cnt, span)

private def checkPageSpanGrid : Bool :=
  (List.range 47).all fun scMinus1 =>
    let stride := BitVec.ofNat 32 (slotStride (scMinus1 + 1))
    (List.range 31).all fun activeIdx =>
      let cnt0 := BitVec.ofNat 32 (activeIdx + 2)
      match pageSpanSteps stride 260 cnt0 (cnt0 * stride + 16#32) with
      | some (cntF, _) => (activeIdx + 2 ≤ cntF.toNat) && (cntF.toNat ≤ 300)
      | none => false

set_option maxRecDepth 50000 in
private theorem checkPageSpanGrid_true : checkPageSpanGrid = true := by decide +kernel

theorem pageSpanSteps_terminates {sc activeIdx : Nat}
    (hscLo : 1 ≤ sc) (hscHi : sc < 48) (hAct : activeIdx < 31) :
    ∃ cntF spanF, pageSpanSteps (BitVec.ofNat 32 (slotStride sc)) 260
      (BitVec.ofNat 32 (activeIdx + 2))
      (BitVec.ofNat 32 (activeIdx + 2) * BitVec.ofNat 32 (slotStride sc) + 16#32) = some (cntF, spanF) ∧
      activeIdx + 2 ≤ cntF.toNat ∧ cntF.toNat ≤ 300 := by
  have h1 := List.all_eq_true.mp checkPageSpanGrid_true (sc - 1) (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 activeIdx (List.mem_range.mpr hAct)
  dsimp only at h2; rw [show sc - 1 + 1 = sc by omega] at h2
  split at h2
  · rename_i cntF spanF heq; simp only [Bool.and_eq_true, decide_eq_true_eq] at h2; exact ⟨cntF, spanF, heq, h2.1, h2.2⟩
  · contradiction

theorem enframe_fold_off_le (slack : BitVec 64) (w2 : BitVec 32) :
    let maxUnits := slack >>> 4; let rawOff := w2 &&& 0xff#32
    maxUnits.ult (rawOff.signExtend 64) = true →
    let m1 := maxUnits ||| (slack >>> 5); let m2 := m1 ||| (m1 >>> 2); let m3 := m2 ||| (m2 >>> 4)
    let masked := rawOff &&& m3.truncate 32; let subVal := masked + (~~~(maxUnits.truncate 32))
    let folded := if maxUnits.ult (masked.zeroExtend 64) then subVal else masked
    (folded.signExtend 64).ule maxUnits = true ∧ (folded.signExtend 64).toNat = folded.toNat ∧
    folded.toNat ≤ maxUnits.toNat := by
  dsimp only; intro hlt
  let mu := slack >>> 4; let ro := w2 &&& 0xff#32
  let m3 := ((mu ||| (slack >>> 5)) ||| ((mu ||| (slack >>> 5)) >>> 2)) |||
            (((mu ||| (slack >>> 5)) ||| ((mu ||| (slack >>> 5)) >>> 2)) >>> 4)
  let mk := ro &&& m3.truncate 32
  let fl := if mu.ult (mk.zeroExtend 64) then mk + ~~~(mu.truncate 32) else mk
  have h1 : (fl.signExtend 64).ule mu = true ∧ fl.signExtend 64 = fl.zeroExtend 64 := by
    dsimp only [mu, ro, m3, mk, fl] at hlt ⊢; revert hlt; bv_robdd
  obtain ⟨hule, hse⟩ := h1
  have hflLt := fl.isLt
  have hflEq : (fl.signExtend 64).toNat = fl.toNat := by
    rw [hse, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hle : fl.toNat ≤ mu.toNat := by
    have h2 := hule; rw [BitVec.ule, decide_eq_true_eq, hflEq] at h2; exact h2
  exact ⟨hule, hflEq, hle⟩

/-! ## Circular Doubly-Linked List Operations -/

theorem CircularDllWf.head_eq_zero_iff {head : BitVec 64}
    {nodes : List (BitVec 64 × BitVec 64 × BitVec 64)} (h : CircularDllWf head nodes) :
    head = 0#64 ↔ nodes = [] := by
  cases nodes with
  | nil => simp only [CircularDllWf] at h; exact ⟨fun _ => rfl, fun _ => h⟩
  | cons hd tl =>
    rcases hd with ⟨p0, pv0, nx0⟩; obtain ⟨hhead, _, hnz, _⟩ := h
    have hp0 : p0 ≠ 0#64 := hnz (p0, pv0, nx0) (List.mem_cons_self ..)
    exact ⟨fun h0 => absurd (hhead.symm.trans h0) hp0, fun hnil => by cases hnil⟩

theorem CircularDllWf.singleton {m : BitVec 64} (hm : m ≠ 0#64) :
    CircularDllWf m [(m, m, m)] :=
  ⟨rfl, by simp, fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hm,
   fun i hi => by
     have hi0 : i = 0 := by simpa using hi
     subst hi0; simp only [List.length_singleton, Nat.mod_one, List.getElem_cons_zero]; exact ⟨trivial, trivial⟩⟩

theorem CircularDllWf.singleton_iff_next_eq {head p0 pv0 nx0 : BitVec 64}
    {rest : List (BitVec 64 × BitVec 64 × BitVec 64)}
    (h : CircularDllWf head ((p0, pv0, nx0) :: rest)) :
    (nx0 = p0 ↔ rest = []) ∧ (rest = [] → pv0 = p0 ∧ nx0 = p0) := by
  obtain ⟨_, hnodup, _, hlinks⟩ := h; have h0 := hlinks 0 (by simp)
  cases rest with
  | nil =>
    simp only [List.length_singleton, Nat.mod_one, List.getElem_cons_zero] at h0
    exact ⟨⟨fun _ => rfl, fun _ => h0.1⟩, fun _ => ⟨h0.2, h0.1⟩⟩
  | cons hd1 tl =>
    rcases hd1 with ⟨p1, pv1, nx1⟩
    have hmod : (0 + 1) % ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tl).length = 1 := by
      rw [Nat.zero_add, Nat.mod_eq_of_lt]; simp
    simp only [hmod, List.getElem_cons_zero, List.getElem_cons_succ] at h0
    simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hnodup
    exact ⟨⟨fun hnx => absurd (h0.1.symm.trans hnx).symm (fun heq => hnodup.1 (Or.inl heq)),
      fun hnil => by cases hnil⟩, fun hnil => by cases hnil⟩

private theorem nodup_getElem_inj {α : Type} :
    ∀ {xs : List α}, xs.Nodup → ∀ {i j : Nat} (hi : i < xs.length) (hj : j < xs.length),
      xs[i]'hi = xs[j]'hj → i = j
  | [], _, i, _, hi, _, _ => by simp at hi
  | x :: xs, _, 0, 0, _, _, _ => rfl
  | x :: xs, hnd, 0, j + 1, _, hj, heq => by
    have hx_mem : xs[j]'(Nat.lt_of_succ_lt_succ hj) ∈ xs := List.getElem_mem ..
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
    exact absurd (heq ▸ hx_mem) (List.nodup_cons.mp hnd).1
  | x :: xs, hnd, i + 1, 0, hi, _, heq => by
    have hx_mem : xs[i]'(Nat.lt_of_succ_lt_succ hi) ∈ xs := List.getElem_mem ..
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
    exact absurd (heq.symm ▸ hx_mem) (List.nodup_cons.mp hnd).1
  | x :: xs, hnd, i + 1, j + 1, hi, hj, heq => by
    simp only [List.getElem_cons_succ] at heq
    exact congrArg Nat.succ (nodup_getElem_inj (List.nodup_cons.mp hnd).2
      (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) heq)

theorem CircularDllWf.rotate_head {head p0 pv0 nx0 : BitVec 64}
    {rest : List (BitVec 64 × BitVec 64 × BitVec 64)}
    (h : CircularDllWf head ((p0, pv0, nx0) :: rest)) :
    CircularDllWf nx0 (rest ++ [(p0, pv0, nx0)]) := by
  cases rest with
  | nil =>
    obtain ⟨_, hnx⟩ := (CircularDllWf.singleton_iff_next_eq h).2 rfl
    have hhead : head = p0 := h.1; subst hnx; subst hhead; exact h
  | cons hd1 tl =>
    rcases hd1 with ⟨p1, pv1, nx1⟩; obtain ⟨_, hnodup, hnz, hlinks⟩ := h
    let old := (p0, pv0, nx0) :: (p1, pv1, nx1) :: tl
    let rot := (p1, pv1, nx1) :: (tl ++ [(p0, pv0, nx0)])
    have hn_len : rot.length = old.length := by simp [old, rot]
    have hget : ∀ k : Nat, (hk : k < rot.length) →
        rot[k]'hk = old[(k + 1) % old.length]'(Nat.mod_lt _ (by simp [old])) := by
      intro k hk
      have hlen_old : old.length = tl.length + 2 := by simp [old]
      have hk_bound : k < tl.length + 2 := by simpa [rot] using hk
      by_cases hk_last : k = tl.length + 1
      · subst hk_last; have hmod : (tl.length + 1 + 1) % old.length = 0 := by rw [hlen_old]; exact Nat.mod_self _
        simp only [hmod, old, List.getElem_cons_zero, rot, List.getElem_cons_succ]
        rw [List.getElem_append_right (by omega)]; simp
      · have hmod : (k + 1) % old.length = k + 1 := by rw [hlen_old]; exact Nat.mod_eq_of_lt (by omega)
        simp only [hmod, old, List.getElem_cons_succ]
        cases k with
        | zero => simp [rot]
        | succ k' => simp only [rot, List.getElem_cons_succ]; rw [List.getElem_append_left (by omega)]
    have h0 := hlinks 0 (by simp); dsimp only at h0
    have hmod01 : (0 + 1) % ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tl).length = 1 := Nat.mod_eq_of_lt (by simp)
    have hnx0 : nx0 = p1 := by
      have h01 := h0.1; simp only [hmod01, List.getElem_cons_zero, List.getElem_cons_succ] at h01; exact h01
    change CircularDllWf nx0 rot
    refine ⟨hnx0, (by simpa [old, rot] using List.perm_append_singleton p0 (p1 :: tl.map Prod.fst) :
        (rot.map Prod.fst).Perm (old.map Prod.fst)).nodup_iff.mpr hnodup, ?_, ?_⟩
    · intro x hx; apply hnz x
      rcases (by simpa [rot] using hx : x = (p1, pv1, nx1) ∨ x ∈ tl ∨ x = (p0, pv0, nx0)) with rfl | htl | rfl
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ htl)
      · exact List.mem_cons_self ..
    · intro i hi
      let n := old.length; have hn_pos : 0 < n := by simp [n, old]
      have hli := hlinks ((i + 1) % n) (Nat.mod_lt _ hn_pos); dsimp only at hli ⊢; rw [hget i hi]
      have h_nxt_idx : ((i + 1) % rot.length + 1) % n = ((i + 1) % n + 1) % n := by rw [hn_len]
      have h_prv_idx : ((i + rot.length - 1) % rot.length + 1) % n = ((i + 1) % n + n - 1) % n := by
        rw [hn_len]; have hi_lt : i < n := by simpa [hn_len] using hi
        have h1 : (i + n - 1) % n = if i = 0 then n - 1 else i - 1 := by
          split <;> rename_i hi0
          · subst hi0; simp [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
          · rw [show i + n - 1 = (i - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have h2 : ((i + 1) % n + n - 1) % n = i := by
          by_cases hi_end : i + 1 = n
          · rw [show (i + 1) % n = 0 by rw [hi_end, Nat.mod_self], Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
          · have hi1 : i + 1 < n := by omega
            rw [Nat.mod_eq_of_lt hi1, show i + 1 + n - 1 = i + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi_lt]
        rw [h1]; split <;> rename_i hi0
        · subst hi0; rw [show n - 1 + 1 = n by omega, Nat.mod_self, h2]
        · rw [show i - 1 + 1 = i by omega, Nat.mod_eq_of_lt hi_lt, h2]
      have hnxt_eq : rot[(i + 1) % rot.length]'(Nat.mod_lt _ (by omega)) =
          old[((i + 1) % n + 1) % n]'(Nat.mod_lt _ hn_pos) := by
        rw [hget ((i + 1) % rot.length) (Nat.mod_lt _ (by omega))]; congr 1
      have hprv_eq : rot[(i + rot.length - 1) % rot.length]'(Nat.mod_lt _ (by omega)) =
          old[((i + 1) % n + n - 1) % n]'(Nat.mod_lt _ hn_pos) := by
        rw [hget ((i + rot.length - 1) % rot.length) (Nat.mod_lt _ (by omega))]; congr 1
      rw [hnxt_eq, hprv_eq]; exact hli

theorem CircularDllWf.dequeue_head {head p0 pv0 nx0 p1 pv1 nx1 : BitVec 64}
    {tl : List (BitVec 64 × BitVec 64 × BitVec 64)}
    (h : CircularDllWf head ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tl)) :
    let tail' := ((p1, pv1, nx1) :: tl).map fun d =>
      (d.1, if d.1 == nx0 then pv0 else d.2.1, if d.1 == pv0 then nx0 else d.2.2)
    nx0 = p1 ∧ CircularDllWf nx0 tail' := by
  obtain ⟨_, hnodup, hnz, hlinks⟩ := h
  let old := (p0, pv0, nx0) :: (p1, pv1, nx1) :: tl
  have hn_old : old.length = tl.length + 2 := by simp [old]
  have h0 := hlinks 0 (by simp); dsimp only at h0
  have hmod01 : (0 + 1) % ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tl).length = 1 := Nat.mod_eq_of_lt (by simp)
  have hmod0p : (0 + ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tl).length - 1) %
      ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tl).length = tl.length + 1 := by
    change (0 + old.length - 1) % old.length = tl.length + 1
    rw [hn_old, Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
  have hnx0 : nx0 = p1 := by
    have h01 := h0.1; simp only [hmod01, List.getElem_cons_zero, List.getElem_cons_succ] at h01; exact h01
  have hpv0 : pv0 = (old[tl.length + 1]'(by omega)).1 := by
    have h02 := h0.2; simp only [hmod0p, List.getElem_cons_zero] at h02; exact h02
  dsimp only; refine ⟨hnx0, ?_⟩
  let rawTail := (p1, pv1, nx1) :: tl
  let f : (BitVec 64 × BitVec 64 × BitVec 64) → (BitVec 64 × BitVec 64 × BitVec 64) := fun d =>
    (d.1, if d.1 == nx0 then pv0 else d.2.1, if d.1 == pv0 then nx0 else d.2.2)
  let tail' := rawTail.map f
  have hlen_tail : rawTail.length = tl.length + 1 := by simp [rawTail]
  have hlen_tail' : tail'.length = tl.length + 1 := by simp [tail', rawTail]
  have hraw_eq_old : ∀ j : Nat, (hj : j < rawTail.length) → rawTail[j]'hj = old[j + 1]'(by omega) := fun _ _ => rfl
  have hnodup_raw : (rawTail.map Prod.fst).Nodup := (List.nodup_cons.mp hnodup).2
  have hfst_map : tail'.map Prod.fst = rawTail.map Prod.fst := by simp [tail', f, List.map_map, Function.comp_def]
  have hinj : ∀ j₁ j₂ : Nat, (hj₁ : j₁ < rawTail.length) → (hj₂ : j₂ < rawTail.length) →
      (rawTail[j₁]'hj₁).1 = (rawTail[j₂]'hj₂).1 → j₁ = j₂ := fun j₁ j₂ hj₁ hj₂ heq =>
    nodup_getElem_inj hnodup_raw (by simpa using hj₁) (by simpa using hj₂) (by simpa using heq)
  have hpv0_raw : pv0 = (rawTail[tl.length]'(by omega)).1 := by rw [hpv0, ← hraw_eq_old tl.length (by omega)]
  change CircularDllWf nx0 (f (p1, pv1, nx1) :: tl.map f)
  refine ⟨hnx0, by change (tail'.map Prod.fst).Nodup; rw [hfst_map]; exact hnodup_raw,
    fun x hx => by
      change x ∈ tail' at hx; simp only [tail', List.mem_map] at hx
      rcases hx with ⟨d, hd_mem, rfl⟩; exact hnz d (List.mem_cons_of_mem _ hd_mem), ?_⟩
  intro i hi; change i < tail'.length at hi
  let m := tail'.length; have hm_eq : m = tl.length + 1 := hlen_tail'
  have hi_raw : i < rawTail.length := by omega
  have hi_old_lt : i + 1 < ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tl).length := by change i + 1 < old.length; omega
  have hget_tail' : ∀ k : Nat, (hk : k < m) → tail'[k]'hk = f (rawTail[k]'(by omega)) := fun k _ => by simp [tail']
  have hfst_tail' : ∀ k : Nat, (hk : k < m) → (tail'[k]'hk).1 = (rawTail[k]'(by omega)).1 := fun k hk => by rw [hget_tail' k hk]
  have hli := hlinks (i + 1) hi_old_lt; dsimp only at hli ⊢
  change (tail'[i]'hi).2.2 = (tail'[(i + 1) % m]'(Nat.mod_lt _ (by omega))).1 ∧
    (tail'[i]'hi).2.1 = (tail'[(i + m - 1) % m]'(Nat.mod_lt _ (by omega))).1
  rw [hget_tail' i hi, hfst_tail' ((i + 1) % m) (Nat.mod_lt _ (by omega)),
    hfst_tail' ((i + m - 1) % m) (Nat.mod_lt _ (by omega))]; dsimp only [f]
  constructor
  · by_cases hi_last : i = tl.length
    · have heq_pv : ((rawTail[i]'hi_raw).1 == pv0) = true := by subst hi_last; simp [hpv0_raw]
      simp only [heq_pv, ↓reduceIte, show (i + 1) % m = 0 by rw [hm_eq, hi_last, Nat.mod_self], hnx0]; rfl
    · have heq_pv : ((rawTail[i]'hi_raw).1 == pv0) = false := beq_eq_false_iff_ne.mpr fun hc =>
        hi_last (hinj i tl.length hi_raw (by omega) (hpv0_raw ▸ hc))
      have hmod_old : (i + 1 + 1) % ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tl).length = i + 2 := by
        change (i + 1 + 1) % old.length = i + 2; rw [hn_old]; exact Nat.mod_eq_of_lt (by omega)
      simp only [heq_pv, Bool.false_eq_true, ↓reduceIte, show (i + 1) % m = i + 1 by rw [hm_eq]; exact Nat.mod_eq_of_lt (by omega)]
      have hli1 := hli.1; simp only [hmod_old] at hli1; exact hli1
  · by_cases hi_zero : i = 0
    · subst hi_zero
      simp only [show ((rawTail[0]'hi_raw).1 == nx0) = true by simp [rawTail, hnx0], ↓reduceIte,
        show (0 + m - 1) % m = tl.length by rw [hm_eq, Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega), hpv0_raw]
    · have heq_nx : ((rawTail[i]'hi_raw).1 == nx0) = false := beq_eq_false_iff_ne.mpr fun hc =>
        hi_zero (hinj i 0 hi_raw (by omega) ((show nx0 = (rawTail[0]'(by omega)).1 by simp [rawTail, hnx0]) ▸ hc))
      have hmod_prv : (i + m - 1) % m = i - 1 := by
        rw [hm_eq, show i + (tl.length + 1) - 1 = (i - 1) + (tl.length + 1) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hmod_old : (i + 1 + ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tl).length - 1) %
          ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tl).length = i := by
        change (i + 1 + old.length - 1) % old.length = i
        rw [hn_old, show i + 1 + (tl.length + 2) - 1 = i + (tl.length + 2) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      simp only [heq_nx, Bool.false_eq_true, ↓reduceIte, hmod_prv]
      have hli2 := hli.2; simp only [hmod_old] at hli2
      have hraw_pred : ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tl)[i]'(by omega) = rawTail[i - 1]'(by omega) := by
        have hstep := hraw_eq_old (i - 1) (by omega); simp only [show i - 1 + 1 = i by omega] at hstep; exact hstep.symm
      rw [hraw_pred] at hli2; exact hli2

/-! ## Metadata Byte Decompositions -/

theorem GroupDesc.metaBytes_pointsTo (m : BitVec 64) (g : GroupDesc) :
    (m ↦ₛ g.metaBytes) = ((m ↦₆₄ g.prev) ∗ ((m + 8#64) ↦₆₄ g.next) ∗ ((m + 16#64) ↦₆₄ g.mem) ∗
      ((m + 24#64) ↦₃₂ g.availMask) ∗ ((m + 28#64) ↦₃₂ g.freedMask) ∗ ((m + 32#64) ↦₆₄ g.packedWord)) := by
  simp only [GroupDesc.metaBytes, List.append_assoc, pointsToBytes_append, unpack64_length,
    unpack32_length, ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes, BitVec.add_assoc]; rfl

theorem GroupDesc.packedWord_byte0 (g : GroupDesc) (hLast : g.lastIdx ≤ 31) :
    let b0 := g.packedWord.extractLsb' 0 8
    b0.getLsbD 5 = true ∧ (b0.zeroExtend 32) &&& 0x1f#32 = BitVec.ofNat 32 g.lastIdx := by
  have hL : (BitVec.ofNat 64 g.lastIdx).ult 32#64 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change g.lastIdx % (2 ^ 64) < 32
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  dsimp only [GroupDesc.packedWord]; rw [show BitVec.ofNat 32 g.lastIdx = (BitVec.ofNat 64 g.lastIdx).truncate 32 by bv_omega]
  revert hL; bv_robdd

theorem GroupDesc.packedWord_fields (g : GroupDesc)
    (hLast : g.lastIdx ≤ 31) (hSc : g.sc < 64) (hMap : g.maplen < 2 ^ 52) :
    g.packedWord &&& 0x1f#64 = BitVec.ofNat 64 g.lastIdx ∧
    (g.packedWord >>> 6) &&& 0x3f#64 = BitVec.ofNat 64 g.sc ∧
    g.packedWord >>> 12 = BitVec.ofNat 64 g.maplen ∧
    (((g.packedWord.extractLsb' 0 16).zeroExtend 64) >>> 6) &&& 0x3f#64 = BitVec.ofNat 64 g.sc := by
  have hL : (BitVec.ofNat 64 g.lastIdx).ult 32#64 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change g.lastIdx % (2 ^ 64) < 32; rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hS : (BitVec.ofNat 64 g.sc).ult 64#64 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change g.sc % (2 ^ 64) < 64; rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hM : (BitVec.ofNat 64 g.maplen).ult (1#64 <<< 52) = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change g.maplen % (2 ^ 64) < 2 ^ 52; rw [Nat.mod_eq_of_lt (by omega)]; omega
  dsimp only [GroupDesc.packedWord]; revert hL hS hM; bv_robdd

theorem CtxFields.toBytes_pointsTo (a : BitVec 64) (c : CtxFields)
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) (hBnc : c.bounces.length = 32) :
    (a ↦ₛ c.toBytes) =
      ((a ↦₆₄ c.secret) ∗ ((a + 8#64) ↦₃₂ c.initDone) ∗ ((a + 12#64) ↦₃₂ c.mmapCounter) ∗
       ((a + 16#64) ↦ₛ (unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
         unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
         unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas)) ∗
       ((a + 80#64) ↦₆₄* c.active) ∗ ((a + 464#64) ↦₆₄* c.usageByClass) ∗
       ((a + 848#64) ↦ₛ c.unmapSeq) ∗ ((a + 880#64) ↦ₛ c.bounces) ∗
       ((a + 912#64) ↦₈ c.seq) ∗ ((a + 913#64) ↦ₛ (c.seqPad ++ unpack64 c.brk))) := by
  let hdrMid := unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
    unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
    unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas
  let tailEnd := c.seqPad ++ unpack64 c.brk
  have hGrouping : c.toBytes = unpack64 c.secret ++ (unpack32 c.initDone ++ (unpack32 c.mmapCounter ++
      (hdrMid ++ (unpackL c.active ++ (unpackL c.usageByClass ++ (c.unmapSeq ++ (c.bounces ++ ([c.seq] ++ tailEnd)))))))) := by
    simp only [CtxFields.toBytes, hdrMid, tailEnd, show c.active.flatMap unpack64 = unpackL c.active from rfl,
      show c.usageByClass.flatMap unpack64 = unpackL c.usageByClass from rfl, List.append_assoc]
  rw [hGrouping,
    pointsToBytes_append _ (unpack64 c.secret), unpack64_length, ← pointsTo64_eq_pointsToBytes,
    pointsToBytes_append _ (unpack32 c.initDone), unpack32_length, ← pointsTo32_eq_pointsToBytes, show a + 8#64 + 4#64 = a + 12#64 by bv_omega,
    pointsToBytes_append _ (unpack32 c.mmapCounter), unpack32_length, ← pointsTo32_eq_pointsToBytes, show a + 12#64 + 4#64 = a + 16#64 by bv_omega,
    pointsToBytes_append _ hdrMid, show hdrMid.length = 64 by simp [hdrMid, unpack64_length], show a + 16#64 + 64#64 = a + 80#64 by bv_omega,
    pointsToBytes_append _ (unpackL c.active), show (unpackL c.active).length = 384 by simp [unpackL_length, hAct], ← pointsToWords64_eq_pointsToBytes, show a + 80#64 + 384#64 = a + 464#64 by bv_omega,
    pointsToBytes_append _ (unpackL c.usageByClass), show (unpackL c.usageByClass).length = 384 by simp [unpackL_length, hUse], ← pointsToWords64_eq_pointsToBytes, show a + 464#64 + 384#64 = a + 848#64 by bv_omega,
    pointsToBytes_append _ c.unmapSeq, hUnm, show a + 848#64 + 32#64 = a + 880#64 by bv_omega,
    pointsToBytes_append _ c.bounces, hBnc, show a + 880#64 + 32#64 = a + 912#64 by bv_omega,
    pointsToBytes_append _ [c.seq], List.length_singleton, pointsToBytes_singleton, show a + 912#64 + 1#64 = a + 913#64 by bv_omega]

/-! ## Region Disjointness and Nesting -/

theorem DisjointRegions.symm {b₁ : BitVec 64} {n₁ : Nat} {b₂ : BitVec 64} {n₂ : Nat}
    (h : DisjointRegions b₁ n₁ b₂ n₂) : DisjointRegions b₂ n₂ b₁ n₁ := ⟨h.2, h.1⟩

theorem DisjointRegions.not_both {b₁ : BitVec 64} {n₁ : Nat} {b₂ : BitVec 64} {n₂ : Nat}
    (h : DisjointRegions b₁ n₁ b₂ n₂) {a : BitVec 64}
    (h₁ : InRegion b₁ n₁ a) (h₂ : InRegion b₂ n₂ a) : False := by
  unfold DisjointRegions InRegion at *; bv_omega

theorem PairwiseDisjointRegions.append_iff {xs ys : List (BitVec 64 × Nat)} :
    PairwiseDisjointRegions (xs ++ ys) ↔
      PairwiseDisjointRegions xs ∧ PairwiseDisjointRegions ys ∧
      (∀ x ∈ xs, ∀ y ∈ ys, DisjointRegions x.1 x.2 y.1 y.2) := by
  induction xs with
  | nil => simp [PairwiseDisjointRegions]
  | cons r rest ih =>
    simp only [List.cons_append, PairwiseDisjointRegions, List.mem_append, ih, List.mem_cons]
    refine ⟨fun ⟨hhead, hrest, hys, hcross⟩ => ⟨⟨fun x hx => hhead x (Or.inl hx), hrest⟩, hys,
      fun x hx y hy => by rcases hx with rfl | hx; exact hhead y (Or.inr hy); exact hcross x hx y hy⟩,
      fun ⟨⟨hhead_xs, hrest⟩, hys, hcross⟩ => ⟨fun z hz => by rcases hz with hz | hz; exact hhead_xs z hz; exact hcross r (Or.inl rfl) z hz,
      hrest, hys, fun x hx y hy => hcross x (Or.inr hx) y hy⟩⟩

theorem PairwiseDisjointRegions.getElem_disjoint :
    ∀ {rs : List (BitVec 64 × Nat)}, PairwiseDisjointRegions rs →
      ∀ {i j : Nat} (hi : i < rs.length) (hj : j < rs.length), i ≠ j →
        DisjointRegions (rs[i]'hi).1 (rs[i]'hi).2 (rs[j]'hj).1 (rs[j]'hj).2
  | [], _, i, _, hi, _, _ => by simp at hi
  | _ :: _, ⟨_, _⟩, 0, 0, _, _, hne => absurd rfl hne
  | _ :: rest, ⟨hhead, _⟩, 0, j + 1, _, hj, _ => hhead (rest[j]'(Nat.lt_of_succ_lt_succ hj)) (List.getElem_mem ..)
  | _ :: rest, ⟨hhead, _⟩, i + 1, 0, hi, _, _ => (hhead (rest[i]'(Nat.lt_of_succ_lt_succ hi)) (List.getElem_mem ..)).symm
  | _ :: rest, ⟨_, hrest⟩, i + 1, j + 1, hi, hj, hne =>
    PairwiseDisjointRegions.getElem_disjoint hrest (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) (fun h => hne (congrArg Nat.succ h))

theorem group_slot_toNat {st : MallocngSt} {g : GroupDesc} (hg : GroupWf st g) :
    16 ≤ g.stride ∧ 1 ≤ g.cnt ∧ g.storage.toNat = g.mem.toNat + 16 ∧
    (g.slotEnd g.lastIdx).toNat = g.mem.toNat + 12 + g.cnt * g.stride ∧
    g.mem.toNat + 12 + g.cnt * g.stride ≤ g.mem.toNat + g.totalBytes ∧
    (∀ idx : Nat, idx < g.cnt →
      (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride ∧
      (g.slotEnd idx).toNat = g.mem.toNat + 12 + (idx + 1) * g.stride ∧
      (g.slotStart idx - 4#64).toNat = g.mem.toNat + 12 + idx * g.stride) := by
  have hSc := hg.1; have hSc63 := hg.2.2.2.1; have hMemLo := hg.2.2.2.2.1
  have hMemHi := hg.2.2.2.2.2.2.1; have hFit := hg.2.2.2.2.2.2.2.1
  have hStrideGe : 16 ≤ g.stride := by
    unfold GroupDesc.stride; split <;> rename_i hCond
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hCond; omega
    · rcases hSc with hlt48 | heq63
      · have hb := (sizeClass_bounds hlt48).1; unfold slotStride; omega
      · obtain ⟨hL0, hMpos, _⟩ := hSc63 heq63; exfalso; apply hCond; simp [hL0, hMpos]
  have hCntGe : 1 ≤ g.cnt := by unfold GroupDesc.cnt; omega
  have hStor : g.storage.toNat = g.mem.toNat + 16 := by unfold GroupDesc.storage; bv_omega
  have hSlotCalc : ∀ idx : Nat, idx < g.cnt →
      (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride ∧
      (g.slotEnd idx).toNat = g.mem.toNat + 12 + (idx + 1) * g.stride ∧
      (g.slotStart idx - 4#64).toNat = g.mem.toNat + 12 + idx * g.stride := by
    intro idx hIdx
    have hMulLe : (idx + 1) * g.stride ≤ g.cnt * g.stride := Nat.mul_le_mul_right _ hIdx
    have hIdxMul : idx * g.stride + g.stride = (idx + 1) * g.stride := by
      rw [Nat.add_mul, Nat.one_mul]
    have hStart : (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride := by
      unfold GroupDesc.slotStart
      rw [BitVec.toNat_add, hStor, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : idx * g.stride < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    have hEnd : (g.slotEnd idx).toNat = g.mem.toNat + 12 + (idx + 1) * g.stride := by
      unfold GroupDesc.slotEnd
      rw [BitVec.toNat_add, hStart, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : g.stride - 4 < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
      omega
    have hSub4 : (g.slotStart idx - 4#64).toNat = g.mem.toNat + 12 + idx * g.stride := by
      have : (g.slotStart idx - 4#64).toNat = (g.slotStart idx).toNat - 4 := by bv_omega
      omega
    exact ⟨hStart, hEnd, hSub4⟩
  have hLast := hSlotCalc g.lastIdx (by unfold GroupDesc.cnt; omega)
  exact ⟨hStrideGe, hCntGe, hStor, hLast.2.1, by omega, hSlotCalc⟩

theorem group_root_containment {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    ∀ {g : GroupDesc}, g ∈ st.groups →
      ∃ gr ∈ st.groups, 0 < gr.maplen ∧ gr.mem.toNat ≤ g.mem.toNat ∧
        g.mem.toNat + g.totalBytes ≤ gr.mem.toNat + gr.maplen * 4096 ∧
        (g.slotEnd g.lastIdx).toNat < gr.mem.toNat + gr.maplen * 4096 := by
  suffices hAux : ∀ (fuel : Nat) {g : GroupDesc}, g ∈ st.groups →
      (if 0 < g.maplen then 0 else 48 - g.sc) ≤ fuel →
      ∃ gr ∈ st.groups, 0 < gr.maplen ∧ gr.mem.toNat ≤ g.mem.toNat ∧
        g.mem.toNat + g.totalBytes ≤ gr.mem.toNat + gr.maplen * 4096 ∧
        (g.slotEnd g.lastIdx).toNat < gr.mem.toNat + gr.maplen * 4096 by
    intro g hg; exact hAux (if 0 < g.maplen then 0 else 48 - g.sc) hg (Nat.le_refl _)
  intro fuel; induction fuel with
  | zero =>
    intro g hg hle
    by_cases hPos : 0 < g.maplen
    · have hgWf := hwf.groups_wf g hg
      have hStrict := hgWf.2.2.2.2.2.2.2.2.1 hPos
      have hTot : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hPos]
      have hEndEq := (group_slot_toNat hgWf).2.2.2.1
      exact ⟨g, hg, hPos, Nat.le_refl _, by omega, by omega⟩
    · have ⟨_, pg, _, _, _, _, hPgSc48, hLt, _⟩ :=
        (hwf.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
      simp only [hPos, ↓reduceIte] at hle; omega
  | succ fuel ih =>
    intro g hg hle
    by_cases hPos : 0 < g.maplen
    · have hgWf := hwf.groups_wf g hg
      have hStrict := hgWf.2.2.2.2.2.2.2.2.1 hPos
      have hTot : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hPos]
      have hEndEq := (group_slot_toNat hgWf).2.2.2.1
      exact ⟨g, hg, hPos, Nat.le_refl _, by omega, by omega⟩
    · have hMap0 : g.maplen = 0 := by omega
      have hgWf := hwf.groups_wf g hg
      obtain ⟨_, pg, hpg, pIdx, hpIdx, _, hPgSc48, hScLt, _, _, hStartLe, hCapLe, _⟩ :=
        hgWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hMap0
      simp only [hPos, ↓reduceIte] at hle
      have hpgWf := hwf.groups_wf pg hpg
      have hpIdxCnt : pIdx < pg.cnt := by rw [← hpgWf.2.2.1]; exact hpIdx
      have hPgSlot := (group_slot_toNat hpgWf).2.2.2.2.2 pIdx hpIdxCnt
      have hPgLast := (group_slot_toNat hpgWf).2.2.2.1; have hPgFit := (group_slot_toNat hpgWf).2.2.2.2.1
      have hGTot : g.totalBytes = g.nestedCap := by simp [GroupDesc.totalBytes, hMap0]
      have hGEndLe := (group_slot_toNat hgWf).2.2.2.2.1; have hGEndEq := (group_slot_toNat hgWf).2.2.2.1
      have hPgEndMono : (pg.slotEnd pIdx).toNat ≤ (pg.slotEnd pg.lastIdx).toNat := by
        rw [hPgSlot.2.1, hPgLast]
        have : (pIdx + 1) * pg.stride ≤ pg.cnt * pg.stride := Nat.mul_le_mul_right _ hpIdxCnt; omega
      obtain ⟨gr, hgr, hgrPos, hGrLo, hGrHi, hGrStrict⟩ := ih hpg (by split <;> omega)
      have : pg.mem.toNat ≤ (pg.slotStart pIdx).toNat := by rw [hPgSlot.1]; omega
      exact ⟨gr, hgr, hgrPos, by omega, by omega, by omega⟩

def GroupContains (g : GroupDesc) (x : Nat) : Prop :=
  g.mem.toNat ≤ x ∧ x ≤ (g.slotEnd g.lastIdx).toNat

inductive IsStrictAncestor (st : MallocngSt) : GroupDesc → GroupDesc → Prop
  | direct {a b : GroupDesc} :
      b ∈ st.groups → b.parentMeta = some a.metaPtr → IsStrictAncestor st a b
  | step {a c b : GroupDesc} :
      c ∈ st.groups → c.parentMeta = some a.metaPtr →
      IsStrictAncestor st c b → IsStrictAncestor st a b

theorem IsStrictAncestor.trans {st : MallocngSt} {a b c : GroupDesc}
    (hab : IsStrictAncestor st a b) (hbc : IsStrictAncestor st b c) :
    IsStrictAncestor st a c := by
  induction hab with
  | direct hb hpar => exact .step hb hpar hbc
  | step hc hpar _ ih => exact .step hc hpar (ih hbc)

theorem parent_step_info {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {ch pg : GroupDesc} (hch : ch ∈ st.groups) (hpg : pg ∈ st.groups)
    (hPar : ch.parentMeta = some pg.metaPtr) :
    ch.maplen = 0 ∧ pg.sc < 48 ∧ ch.sc < pg.sc ∧
    ∃ k : Nat, ∃ hk : k < pg.slots.length,
      pg.slots[k]'hk = .liveNested ch.metaPtr ∧ (pg.slotStart k).toNat ≤ ch.mem.toNat ∧
      (ch.slotEnd ch.lastIdx).toNat ≤ (pg.slotEnd k).toNat ∧
      ∀ x : Nat, GroupContains ch x → GroupContains pg x := by
  have hchWf := hwf.groups_wf ch hch
  have hchMap0 : ch.maplen = 0 := by
    by_cases hPos : 0 < ch.maplen
    · have hNone := hchWf.2.2.2.2.2.2.2.2.2.2.1.mp hPos; rw [hPar] at hNone; cases hNone
    · omega
  obtain ⟨_, pg', hpg', k, hk, hPar', hPgSc, hScLt, _, hSlot, hStartLe, hCapLe, _⟩ :=
    hchWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hchMap0
  have hpgEq : pg' = pg := by
    rw [hPar] at hPar'; injection hPar' with hmEq
    exact mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg' hpg hmEq.symm
  subst pg'
  have hpgWf := hwf.groups_wf pg hpg
  have hkCnt : k < pg.cnt := by rw [← hpgWf.2.2.1]; exact hk
  have hPgSlot := (group_slot_toNat hpgWf).2.2.2.2.2 k hkCnt; have hPgLast := (group_slot_toNat hpgWf).2.2.2.1
  have hChTot : ch.totalBytes = ch.nestedCap := by simp [GroupDesc.totalBytes, hchMap0]
  have hChEndLe : (ch.slotEnd ch.lastIdx).toNat ≤ ch.mem.toNat + ch.nestedCap := by
    have h1 := (group_slot_toNat hchWf).2.2.2.1; have h2 := (group_slot_toNat hchWf).2.2.2.2.1; omega
  have hPgEndMono : (pg.slotEnd k).toNat ≤ (pg.slotEnd pg.lastIdx).toNat := by
    rw [hPgSlot.2.1, hPgLast]
    have : (k + 1) * pg.stride ≤ pg.cnt * pg.stride := Nat.mul_le_mul_right _ hkCnt; omega
  refine ⟨hchMap0, hPgSc, hScLt, k, hk, hSlot, hStartLe, by omega, fun x hx => ?_⟩
  unfold GroupContains at hx ⊢
  have : pg.mem.toNat ≤ (pg.slotStart k).toNat := by rw [hPgSlot.1]; omega
  omega

theorem closed_slots_disjoint {st : MallocngSt} {g : GroupDesc}
    (hg : GroupWf st g) {k₁ k₂ x : Nat}
    (hk₁ : k₁ < g.slots.length) (hk₂ : k₂ < g.slots.length)
    (h1 : (g.slotStart k₁).toNat ≤ x ∧ x ≤ (g.slotEnd k₁).toNat)
    (h2 : (g.slotStart k₂).toNat ≤ x ∧ x ≤ (g.slotEnd k₂).toNat) :
    k₁ = k₂ := by
  have hk₁c : k₁ < g.cnt := by rw [← hg.2.2.1]; exact hk₁
  have hk₂c : k₂ < g.cnt := by rw [← hg.2.2.1]; exact hk₂
  have hs := group_slot_toNat hg
  have hc1 := hs.2.2.2.2.2 k₁ hk₁c; have hc2 := hs.2.2.2.2.2 k₂ hk₂c; have hStride := hs.1
  by_cases hlt : k₁ < k₂
  · have : (k₁ + 1) * g.stride ≤ k₂ * g.stride := Nat.mul_le_mul_right _ hlt; omega
  · by_cases hgt : k₂ < k₁
    · have : (k₂ + 1) * g.stride ≤ k₁ * g.stride := Nat.mul_le_mul_right _ hgt; omega
    · omega

theorem strictAncestor_contains {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {a b : GroupDesc} {x : Nat}
    (hAnc : IsStrictAncestor st a b) (ha : a ∈ st.groups) (hbContain : GroupContains b x) :
    GroupContains a x ∧ ∃ ch ∈ st.groups, ch.parentMeta = some a.metaPtr ∧ GroupContains ch x ∧
      (ch = b ∨ IsStrictAncestor st ch b) := by
  induction hAnc with
  | @direct a₀ b₀ hb₀ hpar =>
    obtain ⟨_, _, _, _, _, _, _, _, hSub⟩ := parent_step_info hwf hb₀ ha hpar
    exact ⟨hSub x hbContain, b₀, hb₀, hpar, hbContain, Or.inl rfl⟩
  | @step a₀ c₀ b₀ hc₀ hpar hcb ih =>
    obtain ⟨hcCont, _⟩ := ih hc₀ hbContain
    obtain ⟨_, _, _, _, _, _, _, _, hSub⟩ := parent_step_info hwf hc₀ ha hpar
    exact ⟨hSub x hcCont, c₀, hc₀, hpar, hcCont, Or.inr hcb⟩

private theorem unique_child_containing {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {c ch₁ ch₂ : GroupDesc} {x : Nat}
    (hc : c ∈ st.groups) (hch₁ : ch₁ ∈ st.groups) (hch₂ : ch₂ ∈ st.groups)
    (hp₁ : ch₁.parentMeta = some c.metaPtr) (hp₂ : ch₂.parentMeta = some c.metaPtr)
    (hc₁ : GroupContains ch₁ x) (hc₂ : GroupContains ch₂ x) : ch₁ = ch₂ := by
  obtain ⟨_, _, _, k₁, hk₁, hs₁, hlo₁, hhi₁, _⟩ := parent_step_info hwf hch₁ hc hp₁
  obtain ⟨_, _, _, k₂, hk₂, hs₂, hlo₂, hhi₂, _⟩ := parent_step_info hwf hch₂ hc hp₂
  unfold GroupContains at hc₁ hc₂
  have hkEq : k₁ = k₂ := closed_slots_disjoint (x := x) (hwf.groups_wf c hc) hk₁ hk₂
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  subst hkEq; rw [hs₁] at hs₂; injection hs₂ with hmEq
  exact mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hch₁ hch₂ hmEq

private theorem root_groups_eq_of_overlap {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g₁ g₂ : GroupDesc} {a : BitVec 64}
    (hg₁ : g₁ ∈ st.groups) (hg₂ : g₂ ∈ st.groups) (hp₁ : 0 < g₁.maplen) (hp₂ : 0 < g₂.maplen)
    (hin₁ : InRegion g₁.mem (g₁.maplen * 4096) a) (hin₂ : InRegion g₂.mem (g₂.maplen * 4096) a) :
    g₁ = g₂ := by
  let rootGs := st.groups.filter fun g => decide (0 < g.maplen)
  obtain ⟨i₁, hi₁, heq₁⟩ := List.getElem_of_mem (List.mem_filter.mpr ⟨hg₁, decide_eq_true hp₁⟩ : g₁ ∈ rootGs)
  obtain ⟨i₂, hi₂, heq₂⟩ := List.getElem_of_mem (List.mem_filter.mpr ⟨hg₂, decide_eq_true hp₂⟩ : g₂ ∈ rootGs)
  by_cases hij : i₁ = i₂
  · subst hij; exact heq₁.symm.trans heq₂
  · have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd
    rw [List.append_assoc, List.append_assoc, PairwiseDisjointRegions.append_iff] at hpd
    have hpdRoot := (PairwiseDisjointRegions.append_iff.mp
      (PairwiseDisjointRegions.append_iff.mp hpd.2.1).2.1).2.1
    let rootRegs := rootGs.map fun g => (g.mem, g.maplen * 4096)
    have hlen : rootRegs.length = rootGs.length := List.length_map _
    have hdisj := PairwiseDisjointRegions.getElem_disjoint hpdRoot (hlen ▸ hi₁) (hlen ▸ hi₂) hij
    have hr1 : rootRegs[i₁]'(hlen ▸ hi₁) = (g₁.mem, g₁.maplen * 4096) := by
      simp only [rootRegs, List.getElem_map]; exact congrArg (fun g => (g.mem, g.maplen * 4096)) heq₁
    have hr2 : rootRegs[i₂]'(hlen ▸ hi₂) = (g₂.mem, g₂.maplen * 4096) := by
      simp only [rootRegs, List.getElem_map]; exact congrArg (fun g => (g.mem, g.maplen * 4096)) heq₂
    rw [hr1, hr2] at hdisj; dsimp only at hdisj
    exact False.elim (DisjointRegions.not_both hdisj hin₁ hin₂)

theorem inRegion_bounds {b a : BitVec 64} {n : Nat} (hFit : b.toNat + n ≤ 2 ^ 64) :
    InRegion b n a ↔ b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + n := by
  unfold InRegion; have := b.isLt; have := a.isLt; rw [BitVec.toNat_sub]; omega

theorem comparable_of_groupContains {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g₁ g₂ : GroupDesc} {x : Nat}
    (hg₁ : g₁ ∈ st.groups) (hg₂ : g₂ ∈ st.groups)
    (hc₁ : GroupContains g₁ x) (hc₂ : GroupContains g₂ x) :
    g₁ = g₂ ∨ IsStrictAncestor st g₁ g₂ ∨ IsStrictAncestor st g₂ g₁ := by
  have hxLt : x < 2 ^ 64 := by
    obtain ⟨gr, hgr, hpos, _, _, hstrict⟩ := group_root_containment hwf hg₁
    have hgrHi := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
    have hgrTot : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hpos]
    unfold GroupContains at hc₁; omega
  let a : BitVec 64 := BitVec.ofNat 64 x
  have haNat : a.toNat = x := by simp only [a, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxLt]
  have hBothRoot : ∀ {r₁ r₂ : GroupDesc}, r₁ ∈ st.groups → r₂ ∈ st.groups →
      0 < r₁.maplen → 0 < r₂.maplen → GroupContains r₁ a.toNat → GroupContains r₂ a.toNat → r₁ = r₂ := by
    intro r₁ r₂ hr₁ hr₂ hp₁ hp₂ hcr₁ hcr₂
    have hHi₁ := (hwf.groups_wf r₁ hr₁).2.2.2.2.2.2.1; have hHi₂ := (hwf.groups_wf r₂ hr₂).2.2.2.2.2.2.1
    have hStr₁ := (hwf.groups_wf r₁ hr₁).2.2.2.2.2.2.2.2.1 hp₁; have hStr₂ := (hwf.groups_wf r₂ hr₂).2.2.2.2.2.2.2.2.1 hp₂
    have hEnd₁ := (group_slot_toNat (hwf.groups_wf r₁ hr₁)).2.2.2.1; have hEnd₂ := (group_slot_toNat (hwf.groups_wf r₂ hr₂)).2.2.2.1
    have hTot₁ : r₁.totalBytes = r₁.maplen * 4096 := by simp [GroupDesc.totalBytes, hp₁]
    have hTot₂ : r₂.totalBytes = r₂.maplen * 4096 := by simp [GroupDesc.totalBytes, hp₂]
    unfold GroupContains at hcr₁ hcr₂
    exact root_groups_eq_of_overlap (a := a) hwf hr₁ hr₂ hp₁ hp₂
      ((inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩) ((inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩)
  suffices hAux : ∀ (fuel : Nat) {g₁ g₂ : GroupDesc}, g₁ ∈ st.groups → g₂ ∈ st.groups →
      GroupContains g₁ a.toNat → GroupContains g₂ a.toNat →
      (if 0 < g₁.maplen then 0 else 48 - g₁.sc) + (if 0 < g₂.maplen then 0 else 48 - g₂.sc) ≤ fuel →
      g₁ = g₂ ∨ IsStrictAncestor st g₁ g₂ ∨ IsStrictAncestor st g₂ g₁ by
    exact hAux _ hg₁ hg₂ (haNat.symm ▸ hc₁) (haNat.symm ▸ hc₂) (Nat.le_refl _)
  intro fuel; induction fuel with
  | zero =>
    intro g₁ g₂ hg₁ hg₂ hc₁ hc₂ hle
    by_cases hp₁ : 0 < g₁.maplen
    · by_cases hp₂ : 0 < g₂.maplen
      · exact Or.inl (hBothRoot hg₁ hg₂ hp₁ hp₂ hc₁ hc₂)
      · obtain ⟨_, p₂, _, _, _, _, hpSc, hLt, _⟩ :=
          (hwf.groups_wf g₂ hg₂).2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
        simp only [hp₁, hp₂, ↓reduceIte] at hle; omega
    · obtain ⟨_, p₁, _, _, _, _, hpSc, hLt, _⟩ :=
        (hwf.groups_wf g₁ hg₁).2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
      simp only [hp₁, ↓reduceIte] at hle; omega
  | succ fuel ih =>
    intro g₁ g₂ hg₁ hg₂ hc₁ hc₂ hle
    by_cases hp₁ : 0 < g₁.maplen
    · by_cases hp₂ : 0 < g₂.maplen
      · exact Or.inl (hBothRoot hg₁ hg₂ hp₁ hp₂ hc₁ hc₂)
      · obtain ⟨_, p₂, hp₂m, _, _, hPar₂, _, _, _⟩ :=
          (hwf.groups_wf g₂ hg₂).2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
        obtain ⟨_, hScP₂, hLt₂, _, _, _, _, _, hSub₂⟩ := parent_step_info hwf hg₂ hp₂m hPar₂
        simp only [hp₁, hp₂, ↓reduceIte] at hle
        rcases ih hg₁ hp₂m hc₁ (hSub₂ a.toNat hc₂)
            (by simp only [hp₁, ↓reduceIte, Nat.zero_add]; split <;> omega) with rfl | hAnc12 | hAnc21
        · exact Or.inr (Or.inl (.direct hg₂ hPar₂))
        · exact Or.inr (Or.inl (hAnc12.trans (.direct hg₂ hPar₂)))
        · obtain ⟨_, ch, hch, hchPar, hchCont, hchStep⟩ := strictAncestor_contains hwf hAnc21 hp₂m hc₁
          cases unique_child_containing hwf hp₂m hch hg₂ hchPar hPar₂ hchCont hc₂
          exact hchStep.elim (fun h => Or.inl h.symm) (Or.inr ∘ Or.inr)
    · obtain ⟨_, p₁, hp₁m, _, _, hPar₁, _, _, _⟩ :=
        (hwf.groups_wf g₁ hg₁).2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
      obtain ⟨_, hScP₁, hLt₁, _, _, _, _, _, hSub₁⟩ := parent_step_info hwf hg₁ hp₁m hPar₁
      simp only [hp₁, ↓reduceIte] at hle
      rcases ih hp₁m hg₂ (hSub₁ a.toNat hc₁) hc₂ (by split at hle <;> split <;> omega) with rfl | hAnc12 | hAnc21
      · exact Or.inr (Or.inr (.direct hg₁ hPar₁))
      · obtain ⟨_, ch, hch, hchPar, hchCont, hchStep⟩ := strictAncestor_contains hwf hAnc12 hp₁m hc₂
        cases unique_child_containing hwf hp₁m hch hg₁ hchPar hPar₁ hchCont hc₁
        exact hchStep.elim Or.inl (Or.inr ∘ Or.inl)
      · exact Or.inr (Or.inr (hAnc21.trans (.direct hg₁ hPar₁)))

theorem disjointRegions_of_bounds {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (_h₁ : 0 < n₁) (_h₂ : 0 < n₂) (_hFit₁ : b₁.toNat + n₁ ≤ 2 ^ 64) (_hFit₂ : b₂.toNat + n₂ ≤ 2 ^ 64)
    (_hDisj : b₁.toNat + n₁ ≤ b₂.toNat ∨ b₂.toNat + n₂ ≤ b₁.toNat) :
    DisjointRegions b₁ n₁ b₂ n₂ := by unfold DisjointRegions; bv_omega

theorem disjointRegions_bounds {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (_h₁ : 0 < n₁) (_h₂ : 0 < n₂) (_hFit₁ : b₁.toNat + n₁ ≤ 2 ^ 64) (_hFit₂ : b₂.toNat + n₂ ≤ 2 ^ 64)
    (hDisj : DisjointRegions b₁ n₁ b₂ n₂) :
    b₁.toNat + n₁ ≤ b₂.toNat ∨ b₂.toNat + n₂ ≤ b₁.toNat := by unfold DisjointRegions at hDisj; bv_omega

theorem slotAddr_bounds {ma : MetaAreaDesc} {k : Nat}
    (hLo : 4096 ≤ ma.base.toNat) (hAl : ma.base.toNat % 4096 = 0)
    (hHi : ma.base.toNat + 4096 ≤ 2 ^ 48) (hk : k < 101) :
    (ma.slotAddr k).toNat = ma.base.toNat + (24 + 40 * k) ∧ 4096 ≤ (ma.slotAddr k).toNat ∧
    (ma.slotAddr k).toNat % 8 = 0 ∧ (ma.slotAddr k).toNat + 40 ≤ ma.base.toNat + 4096 ∧
    (∀ a : BitVec 64, InRegion (ma.slotAddr k) 40 a → InRegion ma.base 4096 a) := by
  have hEq : (ma.slotAddr k).toNat = ma.base.toNat + (24 + 40 * k) := by
    unfold MetaAreaDesc.slotAddr
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 24 + 40 * k < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  refine ⟨hEq, by omega, by omega, by omega, fun a ha => ?_⟩
  rw [inRegion_bounds (by omega)] at ha; rw [inRegion_bounds (by omega)]; omega

theorem allMetaSlots_info {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {m : BitVec 64} (hm : m ∈ allMetaSlots st) :
    4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧
    (∃ ma ∈ st.metaAreas, ∀ a : BitVec 64, InRegion m 40 a → InRegion ma.base 4096 a) ∧
    (∀ m' ∈ allMetaSlots st, m' ≠ m → DisjointRegions m 40 m' 40) := by
  unfold allMetaSlots at hm
  obtain ⟨ma₁, hma₁, hm₁⟩ := List.mem_flatMap.mp hm; obtain ⟨k₁, hk₁r, rfl⟩ := List.mem_map.mp hm₁
  obtain ⟨hLo₁, hAl₁, hHi₁, _⟩ := hwf.metaAreas_wf.2.1 ma₁ hma₁
  obtain ⟨hEq₁, hSlotLo₁, hSlotAl₁, hSlotFit₁, hSub₁⟩ := slotAddr_bounds hLo₁ hAl₁ hHi₁ (List.mem_range.mp hk₁r)
  refine ⟨hSlotLo₁, hSlotAl₁, by omega, ⟨ma₁, hma₁, hSub₁⟩, fun m' hm' hne => ?_⟩
  unfold allMetaSlots at hm'
  obtain ⟨ma₂, hma₂, hm₂⟩ := List.mem_flatMap.mp hm'; obtain ⟨k₂, hk₂r, rfl⟩ := List.mem_map.mp hm₂
  obtain ⟨hLo₂, hAl₂, hHi₂, _⟩ := hwf.metaAreas_wf.2.1 ma₂ hma₂
  obtain ⟨hEq₂, _, _, hSlotFit₂, _⟩ := slotAddr_bounds hLo₂ hAl₂ hHi₂ (List.mem_range.mp hk₂r)
  have hk₁ := List.mem_range.mp hk₁r; have hk₂ := List.mem_range.mp hk₂r
  by_cases hMaEq : ma₁ = ma₂
  · subst hMaEq; have hkNe : k₁ ≠ k₂ := fun h => hne (h ▸ rfl)
    exact disjointRegions_of_bounds (by omega) (by omega) (by omega) (by omega) (by omega)
  · obtain ⟨i₁, hi₁, hget₁⟩ := List.getElem_of_mem hma₁; obtain ⟨i₂, hi₂, hget₂⟩ := List.getElem_of_mem hma₂
    have hij : i₁ ≠ i₂ := fun h => hMaEq (hget₁.symm.trans (h ▸ hget₂))
    have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd
    rw [List.append_assoc, List.append_assoc, PairwiseDisjointRegions.append_iff] at hpd
    let metaRegs := st.metaAreas.map fun ma => (ma.base, 4096)
    have hlen : metaRegs.length = st.metaAreas.length := List.length_map _
    have hdisj := PairwiseDisjointRegions.getElem_disjoint hpd.1 (hlen ▸ hi₁) (hlen ▸ hi₂) hij
    have hm1 : metaRegs[i₁]'(hlen ▸ hi₁) = (ma₁.base, 4096) := by
      simp only [metaRegs, List.getElem_map]; exact congrArg (fun ma => (ma.base, 4096)) hget₁
    have hm2 : metaRegs[i₂]'(hlen ▸ hi₂) = (ma₂.base, 4096) := by
      simp only [metaRegs, List.getElem_map]; exact congrArg (fun ma => (ma.base, 4096)) hget₂
    rw [hm1, hm2] at hdisj; dsimp only at hdisj
    have := disjointRegions_bounds (by omega) (by omega) (by omega) (by omega) hdisj
    exact disjointRegions_of_bounds (by omega) (by omega) (by omega) (by omega) (by omega)

theorem metaArea_disjoint_rootGroup {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {ma : MetaAreaDesc} (hma : ma ∈ st.metaAreas) {gr : GroupDesc} (hgr : gr ∈ st.groups)
    (hPos : 0 < gr.maplen) : DisjointRegions ma.base 4096 gr.mem (gr.maplen * 4096) := by
  have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd
  rw [List.append_assoc, List.append_assoc, PairwiseDisjointRegions.append_iff] at hpd
  exact hpd.2.2 (ma.base, 4096) (List.mem_map_of_mem hma) (gr.mem, gr.maplen * 4096)
    (List.mem_append_right _ (List.mem_append_right _
      (List.mem_map_of_mem (List.mem_filter.mpr ⟨hgr, decide_eq_true hPos⟩))))

theorem carvedUserByte_witness {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {a : BitVec 64} (hCarved : CarvedUserByte st a) :
    ∃ h ∈ st.groups, ∃ idx : Nat, ∃ hIdx : idx < h.slots.length,
      ∃ userPtr : BitVec 64, ∃ reqSize effCost : Nat,
        h.slots[idx]'hIdx = .liveUser userPtr reqSize effCost ∧
        (h.slotStart idx).toNat ≤ a.toNat ∧ a.toNat < (h.slotEnd idx).toNat ∧
        (h.slotEnd idx).toNat ≤ (h.slotEnd h.lastIdx).toNat ∧ GroupContains h a.toNat ∧
        ∃ gr ∈ st.groups, 0 < gr.maplen ∧ InRegion gr.mem (gr.maplen * 4096) a := by
  obtain ⟨h, hh, s, hsMem, hsIn⟩ := hCarved; obtain ⟨idx, hIdx, rfl⟩ := List.getElem_of_mem hsMem
  cases hSlot : h.slots[idx]'hIdx with
  | freeAvail | freeInactive | claimed | liveNested _ => rw [hSlot] at hsIn; cases hsIn
  | liveUser userPtr reqSize effCost =>
    rw [hSlot] at hsIn; have hhWf := hwf.groups_wf h hh
    have hSlotWf := GroupWf.slot_wf hhWf idx hIdx; rw [hSlot] at hSlotWf
    obtain ⟨_, _, _, _, hBlockWf, hStartLe, hEndLe, _⟩ := hSlotWf
    have hIdxCnt : idx < h.cnt := by rw [← hhWf.2.2.1]; exact hIdx
    have hGs := group_slot_toNat hhWf; have hSc := hGs.2.2.2.2.2 idx hIdxCnt
    have hEndMono : (h.slotEnd idx).toNat ≤ (h.slotEnd h.lastIdx).toNat := by
      have : (idx + 1) * h.stride ≤ h.cnt * h.stride := Nat.mul_le_mul_right _ hIdxCnt; omega
    obtain ⟨gr, hgr, hgrPos, hGrLo, hGrHi, hGrStrict⟩ := group_root_containment hwf hh
    have hGrBound := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
    have hGrTot : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPos]
    have haRange := (inRegion_bounds (by omega)).mp hsIn
    exact ⟨h, hh, idx, hIdx, userPtr, reqSize, effCost, hSlot, by omega, by omega,
      hEndMono, ⟨by omega, by omega⟩, gr, hgr, hgrPos, (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩⟩

theorem strictAncestor_slot_bounds {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {a b : GroupDesc} (hAnc : IsStrictAncestor st a b) (ha : a ∈ st.groups) :
    ∃ ch ∈ st.groups, ∃ k : Nat, ∃ hk : k < a.slots.length,
      a.slots[k]'hk = .liveNested ch.metaPtr ∧ (a.slotStart k).toNat ≤ ch.mem.toNat ∧
      ch.mem.toNat ≤ b.mem.toNat ∧ (b.slotEnd b.lastIdx).toNat ≤ (ch.slotEnd ch.lastIdx).toNat ∧
      (ch.slotEnd ch.lastIdx).toNat ≤ (a.slotEnd k).toNat := by
  induction hAnc with
  | @direct a₀ b₀ hb₀ hpar =>
    obtain ⟨_, _, _, k, hk, hs, hlo, hhi, _⟩ := parent_step_info hwf hb₀ ha hpar
    exact ⟨b₀, hb₀, k, hk, hs, hlo, Nat.le_refl _, Nat.le_refl _, hhi⟩
  | @step a₀ c₀ b₀ hc₀ hpar _ ih =>
    obtain ⟨_, _, kC, hkC, _, hloC, hmemCB, hendBC, hhiC⟩ := ih hc₀
    obtain ⟨_, _, _, k, hk, hs, hloA, hhiA, _⟩ := parent_step_info hwf hc₀ ha hpar
    have hcWf := hwf.groups_wf c₀ hc₀; have hkCCnt : kC < c₀.cnt := by rw [← hcWf.2.2.1]; exact hkC
    have hcGs := group_slot_toNat hcWf; have hcSlot := hcGs.2.2.2.2.2 kC hkCCnt
    have : (kC + 1) * c₀.stride ≤ c₀.cnt * c₀.stride := Nat.mul_le_mul_right _ hkCCnt
    exact ⟨c₀, hc₀, k, hk, hs, hloA, by omega, by omega, hhiA⟩

theorem meta_ownedRw_of_mem_groups {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) :
    4096 ≤ g.metaPtr.toNat ∧ g.metaPtr.toNat % 8 = 0 ∧ g.metaPtr.toNat + 40 ≤ 2 ^ 48 ∧
    readBytesFromMap st.byteVal g.metaPtr 40 = g.metaBytes ∧
    (∀ a : BitVec 64, InRegion g.metaPtr 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom) := by
  have hgWf := hwf.groups_wf g hg
  obtain ⟨_, _, _, _, hNd, hAll⟩ := hwf.free_bump_metas_wf
  have hgMemMap : g.metaPtr ∈ st.groups.map (·.metaPtr) := List.mem_map_of_mem hg
  have hgAll : g.metaPtr ∈ allMetaSlots st := (hAll g.metaPtr).mp
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hgMemMap)))
  obtain ⟨hLo, hAl, hHi, ⟨ma, hma, hInMa⟩, hDisjSlots⟩ := allMetaSlots_info hwf hgAll
  have hNotRes : g.metaPtr ∉ st.reservedMetas := fun hRes => by
    rw [List.nodup_append] at hNd
    exact hNd.2.2 g.metaPtr (List.mem_append_left _ (List.mem_append_left _ hgMemMap)) g.metaPtr hRes rfl
  refine ⟨hLo, hAl, hHi, hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, fun a ha => ?_⟩
  have haMa := hInMa a ha
  have hNoUser : ¬ CarvedUserByte st a := fun hCu => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, gr, hgr, hgrPos, haGr⟩ := carvedUserByte_witness hwf hCu
    exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hma hgr hgrPos) haMa haGr
  have hNoMeta : ¬ CarvedMetaByte st a := fun ⟨mr, hmr, haMr⟩ =>
    DisjointRegions.not_both (hDisjSlots mr ((hAll mr).mp (List.mem_append_right _ hmr))
      (fun h => hNotRes (h ▸ hmr))) ha haMr
  have hOwn : OwnedRwByte st a := ⟨Or.inl ⟨ma, hma, haMa⟩, hNoUser, hNoMeta⟩
  exact ⟨hOwn, hwf.masterDom_wf.2.1 a (Or.inl hOwn)⟩

theorem group_header_ownedRw {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) :
    readBytesFromMap st.byteVal g.mem 8 = unpack64 g.metaPtr ∧
    st.byteVal (g.mem + 8#64) = g.activeByte ∧
    (∀ a : BitVec 64, InRegion g.mem 16 a → OwnedRwByte st a ∧ a ∈ st.masterDom) := by
  have hgWf := hwf.groups_wf g hg
  obtain ⟨gr, hgr, hgrPos, hGrLo, _, hGrStrict⟩ := group_root_containment hwf hg
  have hGrBound := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
  have hGrTot : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPos]
  have hGs := group_slot_toNat hgWf
  have hEndGe16 : g.mem.toNat + 16 ≤ (g.slotEnd g.lastIdx).toNat := by
    rw [hGs.2.2.2.1]; have : 1 * 16 ≤ g.cnt * g.stride := Nat.mul_le_mul hGs.2.1 hGs.1; omega
  refine ⟨hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, fun a ha => ?_⟩
  have haRange : g.mem.toNat ≤ a.toNat ∧ a.toNat < g.mem.toNat + 16 := by unfold InRegion at ha; bv_omega
  have haGr : InRegion gr.mem (gr.maplen * 4096) a := by unfold InRegion; bv_omega
  have hgCont : GroupContains g a.toNat := ⟨haRange.1, by omega⟩
  have hNoMeta : ¬ CarvedMetaByte st a := fun ⟨mr, hmr, haMr⟩ => by
    obtain ⟨_, _, _, ⟨ma, hma, hInMa⟩, _⟩ := allMetaSlots_info hwf
      ((hwf.free_bump_metas_wf.2.2.2.2.2 mr).mp (List.mem_append_right _ hmr))
    exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hma hgr hgrPos) (hInMa a haMr) haGr
  have hNoUser : ¬ CarvedUserByte st a := fun hCu => by
    obtain ⟨h, hh, idx, hIdx, _, _, _, hSlot, hLoIdx, hHiIdx, _, hhCont, _⟩ := carvedUserByte_witness hwf hCu
    have := hhCont.1
    rcases comparable_of_groupContains hwf hg hh hgCont hhCont with rfl | hAncGH | hAncHG
    · have := (group_slot_toNat hgWf).2.2.2.2.2 idx (hgWf.2.2.1 ▸ hIdx); omega
    · obtain ⟨_, _, k, hk, _, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncGH hg
      have := hGs.2.2.2.2.2 k (hgWf.2.2.1 ▸ hk); omega
    · obtain ⟨_, _, k, hk, hsK, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncHG hh
      cases closed_slots_disjoint (x := a.toNat) (hwf.groups_wf h hh) hk hIdx ⟨by omega, by omega⟩ ⟨hLoIdx, by omega⟩
      rw [hsK] at hSlot; cases hSlot
  have hOwn : OwnedRwByte st a := ⟨Or.inr ⟨gr, hgr, hgrPos, haGr⟩, hNoUser, hNoMeta⟩
  exact ⟨hOwn, hwf.masterDom_wf.2.1 a (Or.inl hOwn)⟩

theorem claimed_slot_ownedRw {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {pg : GroupDesc} (hpg : pg ∈ st.groups) {pIdx : Nat} (hpIdx : pIdx < pg.slots.length)
    (hClaimed : pg.slots[pIdx]'hpIdx = .claimed) :
    st.byteVal (pg.slotStart pIdx - 4#64) = 0#8 ∧ st.byteVal (pg.slotEnd pIdx) = 0#8 ∧
    (∀ a : BitVec 64, InRegion (pg.slotStart pIdx - 4#64) (pg.stride + 1) a →
      OwnedRwByte st a ∧ a ∈ st.masterDom) := by
  have hpgWf := hwf.groups_wf pg hpg; have hpCnt : pIdx < pg.cnt := hpgWf.2.2.1 ▸ hpIdx
  have hGs := group_slot_toNat hpgWf; have hSlotCalc := hGs.2.2.2.2.2 pIdx hpCnt
  have hEndMono : (pg.slotEnd pIdx).toNat ≤ (pg.slotEnd pg.lastIdx).toNat := by
    have : (pIdx + 1) * pg.stride ≤ pg.cnt * pg.stride := Nat.mul_le_mul_right _ hpCnt; omega
  have hZEnd : st.byteVal (pg.slotEnd pIdx) = 0#8 := by
    by_cases hNext : pIdx + 1 < pg.cnt
    · have := hGs.2.2.2.2.2 (pIdx + 1) hNext
      rw [show pg.slotEnd pIdx = pg.slotStart (pIdx + 1) - 4#64 from BitVec.eq_of_toNat_eq (by omega)]
      exact (GroupWf.slot_wf hpgWf (pIdx + 1) (hpgWf.2.2.1.symm ▸ hNext)).1
    · rw [show pIdx = pg.lastIdx by unfold GroupDesc.cnt at hNext hpCnt; omega]
      exact hpgWf.2.2.2.2.2.2.2.2.2.1
  obtain ⟨gr, hgr, hgrPos, hGrLo, _, hGrStrict⟩ := group_root_containment hwf hpg
  have hGrBound := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
  have hGrTot : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPos]
  refine ⟨(GroupWf.slot_wf hpgWf pIdx hpIdx).1, hZEnd, fun a ha => ?_⟩
  have : pIdx * pg.stride + pg.stride = (pIdx + 1) * pg.stride := by rw [Nat.add_mul, Nat.one_mul]
  have haRange := (inRegion_bounds (by omega)).mp ha
  have haGr : InRegion gr.mem (gr.maplen * 4096) a := (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩
  have hNoMeta : ¬ CarvedMetaByte st a := fun ⟨mr, hmr, haMr⟩ => by
    obtain ⟨_, _, _, ⟨ma, hma, hInMa⟩, _⟩ := allMetaSlots_info hwf
      ((hwf.free_bump_metas_wf.2.2.2.2.2 mr).mp (List.mem_append_right _ hmr))
    exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hma hgr hgrPos) (hInMa a haMr) haGr
  have hNoUser : ¬ CarvedUserByte st a := fun hCu => by
    obtain ⟨h, hh, idx, hIdx, _, _, _, hSlot, hLoIdx, hHiIdx, _, hhCont, _⟩ := carvedUserByte_witness hwf hCu
    have := hhCont.1
    rcases comparable_of_groupContains hwf hpg hh ⟨by omega, by omega⟩ hhCont with rfl | hAncPgH | hAncHPg
    · have := hGs.2.2.2.2.2 idx (hpgWf.2.2.1 ▸ hIdx)
      rcases Nat.lt_trichotomy idx pIdx with hlt | rfl | hgt
      · have : (idx + 1) * pg.stride ≤ pIdx * pg.stride := Nat.mul_le_mul_right _ hlt; omega
      · rw [hClaimed] at hSlot; cases hSlot
      · have : (pIdx + 1) * pg.stride ≤ idx * pg.stride := Nat.mul_le_mul_right _ hgt; omega
    · obtain ⟨_, _, k, hk, hsK, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncPgH hpg
      have := hGs.2.2.2.2.2 k (hpgWf.2.2.1 ▸ hk)
      rcases Nat.lt_trichotomy k pIdx with hlt | rfl | hgt
      · have : (k + 1) * pg.stride ≤ pIdx * pg.stride := Nat.mul_le_mul_right _ hlt; omega
      · rw [hClaimed] at hsK; cases hsK
      · have : (pIdx + 1) * pg.stride ≤ k * pg.stride := Nat.mul_le_mul_right _ hgt; omega
    · obtain ⟨_, _, k, hk, hsK, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncHPg hh
      cases closed_slots_disjoint (x := a.toNat) (hwf.groups_wf h hh) hk hIdx ⟨by omega, by omega⟩ ⟨hLoIdx, by omega⟩
      rw [hsK] at hSlot; cases hSlot
  have hOwn : OwnedRwByte st a := ⟨Or.inr ⟨gr, hgr, hgrPos, haGr⟩, hNoUser, hNoMeta⟩
  exact ⟨hOwn, hwf.masterDom_wf.2.1 a (Or.inl hOwn)⟩

theorem reservedMeta_info {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {m : BitVec 64} (hm : m ∈ st.reservedMetas) :
    4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.groups.map (·.metaPtr) ∧
    (∃ ma ∈ st.metaAreas, ∀ a : BitVec 64, InRegion m 40 a → InRegion ma.base 4096 a) ∧
    (∀ a : BitVec 64, InRegion m 40 a → ¬ CarvedUserByte st a) ∧
    (∀ a : BitVec 64, InRegion m 40 a → ¬ OwnedRwByte st a) ∧
    (∀ mr ∈ st.reservedMetas, mr ≠ m → DisjointRegions m 40 mr 40) ∧
    (∀ g ∈ st.groups, DisjointRegions m 40 g.metaPtr 40 ∧
      ∀ a : BitVec 64, InRegion m 40 a → ¬ InRegion g.mem g.totalBytes a) := by
  obtain ⟨_, _, _, _, hNd, hAll⟩ := hwf.free_bump_metas_wf
  obtain ⟨hLo, hAl, hHi, ⟨ma, hma, hInMa⟩, hDisjSlots⟩ :=
    allMetaSlots_info hwf ((hAll m).mp (List.mem_append_right _ hm))
  have hNotGrp : m ∉ st.groups.map (·.metaPtr) := fun hGrp => by
    rw [List.nodup_append] at hNd
    exact hNd.2.2 m (List.mem_append_left _ (List.mem_append_left _ hGrp)) m hm rfl
  have hNoUser : ∀ a : BitVec 64, InRegion m 40 a → ¬ CarvedUserByte st a := fun a ha hCu => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, gr, hgr, hgrPos, haGr⟩ := carvedUserByte_witness hwf hCu
    exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hma hgr hgrPos) (hInMa a ha) haGr
  refine ⟨hLo, hAl, hHi, hNotGrp, ⟨ma, hma, hInMa⟩, hNoUser, fun a ha hOwn => hOwn.2.2 ⟨m, hm, ha⟩,
    fun mr hmr hne => hDisjSlots mr ((hAll mr).mp (List.mem_append_right _ hmr)) hne, fun g hg => ?_⟩
  have hgMem : g.metaPtr ∈ st.groups.map (·.metaPtr) := List.mem_map_of_mem hg
  have hgAll := (hAll g.metaPtr).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hgMem)))
  refine ⟨hDisjSlots g.metaPtr hgAll (fun h => hNotGrp (h ▸ hgMem)), fun a ha haG => ?_⟩
  have hgWf := hwf.groups_wf g hg
  by_cases hPos : 0 < g.maplen
  · exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hma hg hPos) (hInMa a ha)
      (by simpa [GroupDesc.totalBytes, hPos] using haG)
  · obtain ⟨_, pg, hpg, pIdx, hp, _, _, _, _, _, hLoP, hHiP, _⟩ := hgWf.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
    have hpgWf := hwf.groups_wf pg hpg; have hpCnt : pIdx < pg.cnt := hpgWf.2.2.1 ▸ hp
    have hpGs := group_slot_toNat hpgWf; have hpSc := hpGs.2.2.2.2.2 pIdx hpCnt
    have : (pIdx + 1) * pg.stride ≤ pg.cnt * pg.stride := Nat.mul_le_mul_right _ hpCnt
    obtain ⟨gr, hgr, hgrPos, hGrLo, _, hGrStrict⟩ := group_root_containment hwf hpg
    have := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
    have hGrTot : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPos]
    have hGTot : g.totalBytes = g.nestedCap := by simp [GroupDesc.totalBytes, show g.maplen = 0 by omega]
    have := hgWf.2.2.2.2.2.2.1; have haGB := (inRegion_bounds (by omega)).mp haG
    exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hma hgr hgrPos) (hInMa a ha)
      ((inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩)

theorem readBytesFromMap_congr {v₁ v₂ : BitVec 64 → BitVec 8} {b : BitVec 64} {n : Nat}
    (hn : n ≤ 2 ^ 64) (hEq : ∀ a : BitVec 64, InRegion b n a → v₁ a = v₂ a) :
    readBytesFromMap v₁ b n = readBytesFromMap v₂ b n := by
  unfold readBytesFromMap
  exact List.map_congr_left fun a ha => hEq a ((mem_rangeAddrs_iff_inRegion b hn a).mp ha)

def newGroupSlots (lastIdx activeIdx : Nat) : List SlotState :=
  .claimed :: (List.replicate activeIdx .freeAvail ++ List.replicate (lastIdx - activeIdx) .freeInactive)

theorem newGroupSlots_info {lastIdx activeIdx : Nat} (hAct : activeIdx ≤ lastIdx) :
    (newGroupSlots lastIdx activeIdx).length = lastIdx + 1 ∧
    (newGroupSlots lastIdx activeIdx).all SlotState.isFree = false ∧
    ((newGroupSlots lastIdx activeIdx).filter SlotState.isClaimed).length = 1 ∧
    ((newGroupSlots lastIdx activeIdx).map slotEffCost).sum = 0 ∧
    (∀ idx : Nat, (hIdx : idx < (newGroupSlots lastIdx activeIdx).length) →
      (idx = 0 → (newGroupSlots lastIdx activeIdx)[idx]'hIdx = .claimed) ∧
      ((1 ≤ idx ∧ idx ≤ activeIdx) ↔ (newGroupSlots lastIdx activeIdx)[idx]'hIdx = .freeAvail) ∧
      (activeIdx < idx ↔ (newGroupSlots lastIdx activeIdx)[idx]'hIdx = .freeInactive)) := by
  have hLen : (newGroupSlots lastIdx activeIdx).length = lastIdx + 1 := by simp [newGroupSlots]; omega
  have hf1 : (List.replicate activeIdx SlotState.freeAvail).filter SlotState.isClaimed = [] := by
    rw [List.filter_eq_nil_iff]; intro x hx; rw [List.mem_replicate.mp hx |>.2]; decide
  have hf2 : (List.replicate (lastIdx - activeIdx) SlotState.freeInactive).filter SlotState.isClaimed = [] := by
    rw [List.filter_eq_nil_iff]; intro x hx; rw [List.mem_replicate.mp hx |>.2]; decide
  have hClaimed : ((newGroupSlots lastIdx activeIdx).filter SlotState.isClaimed).length = 1 := by
    unfold newGroupSlots; rw [List.filter_cons_of_pos rfl, List.filter_append, hf1, hf2]; rfl
  refine ⟨hLen, by simp [newGroupSlots, SlotState.isFree], hClaimed,
    by simp [newGroupSlots, slotEffCost], fun idx hIdx => ?_⟩
  cases idx with
  | zero => simp [newGroupSlots]
  | succ j =>
    have hjLt : j < activeIdx + (lastIdx - activeIdx) := by rw [hLen] at hIdx; omega
    simp only [newGroupSlots, List.getElem_cons_succ]
    by_cases hjAct : j < activeIdx
    · have hGet : (List.replicate activeIdx SlotState.freeAvail ++
          List.replicate (lastIdx - activeIdx) SlotState.freeInactive)[j]'(by simp; omega) = .freeAvail := by
        rw [List.getElem_append_left (by simp; exact hjAct), List.getElem_replicate]
      rw [hGet]; exact ⟨by omega, ⟨fun _ => rfl, fun _ => ⟨by omega, by omega⟩⟩, ⟨by omega, fun h => by cases h⟩⟩
    · have hGet : (List.replicate activeIdx SlotState.freeAvail ++
          List.replicate (lastIdx - activeIdx) SlotState.freeInactive)[j]'(by simp; omega) = .freeInactive := by
        rw [List.getElem_append_right (by simp; omega), List.getElem_replicate]
      rw [hGet]; exact ⟨by omega, ⟨fun ⟨_, hle⟩ => by omega, fun h => by cases h⟩, ⟨fun _ => rfl, fun _ => by omega⟩⟩

private def checkNewGroupBitmaps : Bool :=
  (List.range 32).all fun lastIdx => (List.range (lastIdx + 1)).all fun activeIdx =>
    let initAvail : BitVec 32 := (2#32 <<< (BitVec.ofNat 32 activeIdx)) - 1#32
    let freed : BitVec 32 := (2#32 <<< (BitVec.ofNat 32 lastIdx)) + (~~~initAvail)
    let avail : BitVec 32 := initAvail - 1#32
    (avail &&& freed == 0#32) && decide ((avail ||| freed).toNat < 2 ^ (lastIdx + 1)) &&
    (List.range (lastIdx + 1)).all fun idx =>
      (avail.getLsbD idx == decide (1 ≤ idx ∧ idx ≤ activeIdx)) && (freed.getLsbD idx == decide (activeIdx < idx))

private theorem checkNewGroupBitmaps_true : checkNewGroupBitmaps = true := by decide +kernel

theorem newGroupBitmaps_spec {lastIdx activeIdx : Nat} (hLast : lastIdx ≤ 31) (hAct : activeIdx ≤ lastIdx) :
    let initAvail : BitVec 32 := (2#32 <<< (BitVec.ofNat 32 activeIdx)) - 1#32
    let freed : BitVec 32 := (2#32 <<< (BitVec.ofNat 32 lastIdx)) + (~~~initAvail)
    let avail : BitVec 32 := initAvail - 1#32
    avail &&& freed = 0#32 ∧ (avail ||| freed).toNat < 2 ^ (lastIdx + 1) ∧
    ∀ idx : Nat, idx < lastIdx + 1 →
      (avail.getLsbD idx = true ↔ (1 ≤ idx ∧ idx ≤ activeIdx)) ∧ (freed.getLsbD idx = true ↔ activeIdx < idx) := by
  have h1 := List.all_eq_true.mp checkNewGroupBitmaps_true lastIdx (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 activeIdx (List.mem_range.mpr (by omega))
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
  refine ⟨h2.1.1, h2.1.2, fun idx hIdx => ?_⟩
  have h3 := List.all_eq_true.mp h2.2 idx (List.mem_range.mpr hIdx)
  simp only [Bool.and_eq_true, beq_iff_eq] at h3
  exact ⟨by rw [h3.1]; exact decide_eq_true_iff, by rw [h3.2]; exact decide_eq_true_iff⟩

private theorem nodup_lt_length_le : ∀ (B : Nat) {xs : List Nat}, xs.Nodup → (∀ x ∈ xs, x < B) → xs.length ≤ B
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, hb => absurd (hb x (List.Mem.head _)) (by omega)
  | B + 1, xs, hnd, hb => by
    by_cases hMem : B ∈ xs
    · obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hMem
      obtain ⟨hnd₁, hnd₂c, hdisj⟩ := List.nodup_append.mp hnd
      obtain ⟨hBNot₂, hnd₂⟩ := List.nodup_cons.mp hnd₂c
      have hBNot₁ : B ∉ l₁ := fun h1 => hdisj B h1 B (List.Mem.head _) rfl
      have hnd12 : (l₁ ++ l₂).Nodup := List.nodup_append.mpr ⟨hnd₁, hnd₂, fun a ha b hb₂ => hdisj a ha b (List.Mem.tail B hb₂)⟩
      have hb12 : ∀ y ∈ l₁ ++ l₂, y < B := fun y hy => by
        rcases List.mem_append.mp hy with hy1 | hy2
        · have := hb y (List.mem_append_left _ hy1); have : y ≠ B := fun h => hBNot₁ (h ▸ hy1); omega
        · have := hb y (List.mem_append_right _ (List.Mem.tail B hy2)); have : y ≠ B := fun h => hBNot₂ (h ▸ hy2); omega
      have hih := nodup_lt_length_le B hnd12 hb12; simp only [List.length_append, List.length_cons] at hih ⊢; omega
    · exact Nat.le_trans (nodup_lt_length_le B hnd fun y hy => by
        have := hb y hy; have : y ≠ B := fun h => hMem (h ▸ hy); omega) (by omega)

theorem usageByClass_bound {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {sc : Nat} (hsc : sc < st.ctx.usageByClass.length) :
    (st.ctx.usageByClass[sc]'hsc).toNat ≤ 32 * 2 ^ 48 := by
  rw [hwf.usage_wf sc hsc]
  have hSumLe : ∀ gs : List GroupDesc, (∀ g ∈ gs, g.cnt ≤ 32) → (gs.map GroupDesc.cnt).sum ≤ 32 * gs.length := by
    intro gs hle; induction gs with
    | nil => simp
    | cons g rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := hle g (List.Mem.head _); have := ih (fun x hx => hle x (List.Mem.tail _ hx)); omega
  have hFiltLen : (st.groups.filter (·.sc == sc)).length ≤ st.groups.length := List.length_filter_le _ _
  have hCntLe : ∀ g ∈ st.groups.filter (·.sc == sc), g.cnt ≤ 32 := fun g hg => by
    have hgWf := hwf.groups_wf g (List.mem_filter.mp hg).1; unfold GroupDesc.cnt; have := hgWf.2.1; omega
  let natMetas := (st.groups.map (·.metaPtr)).map BitVec.toNat
  have hNdNat : natMetas.Nodup :=
    List.Pairwise.map BitVec.toNat (fun _ _ hne heq => hne (BitVec.eq_of_toNat_eq heq)) hwf.groups_nodup.1
  have hGrpLen : st.groups.length ≤ 2 ^ 48 := by
    have := nodup_lt_length_le (2 ^ 48) hNdNat fun x hx => by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx; obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
      have ⟨_, _, hHi, _, _⟩ := meta_ownedRw_of_mem_groups hwf hg; omega
    simpa [natMetas] using this
  have := hSumLe _ hCntLe
  have : 32 * (st.groups.filter (·.sc == sc)).length ≤ 32 * 2 ^ 48 :=
    Nat.mul_le_mul_left 32 (Nat.le_trans hFiltLen hGrpLen)
  omega

theorem usageWf_after_allocGroup {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {sc : Nat} (hscU : sc < st.ctx.usageByClass.length)
    {cg : GroupDesc} (hcgSc : cg.sc = sc) (hcgLast : cg.lastIdx ≤ 31)
    {groupsBase : List GroupDesc}
    (hSameScCnt : groupsBase.map (fun g => (g.sc, g.cnt)) = st.groups.map (fun g => (g.sc, g.cnt)))
    (sc₀ : Nat)
    (hsc₀ : sc₀ < (st.ctx.usageByClass.set sc
      (st.ctx.usageByClass[sc]'hscU + BitVec.ofNat 64 cg.cnt)).length) :
    ((st.ctx.usageByClass.set sc
      (st.ctx.usageByClass[sc]'hscU + BitVec.ofNat 64 cg.cnt))[sc₀]'hsc₀).toNat =
      (((cg :: groupsBase).filter (·.sc == sc₀)).map GroupDesc.cnt).sum := by
  have hsc₀Old : sc₀ < st.ctx.usageByClass.length := by simpa using hsc₀
  have hBaseSum : ∀ s : Nat, ((groupsBase.filter (·.sc == s)).map GroupDesc.cnt).sum =
      ((st.groups.filter (·.sc == s)).map GroupDesc.cnt).sum := fun s => by
    have hMapEq : ∀ gs : List GroupDesc, ((gs.filter (·.sc == s)).map GroupDesc.cnt) =
        (((gs.map fun g => (g.sc, g.cnt)).filter (·.1 == s)).map Prod.snd) := fun gs => by
      induction gs with
      | nil => rfl
      | cons g rest ih => simp only [List.map_cons]; by_cases hs : (g.sc == s) = true <;> simp [hs, ih]
    rw [hMapEq groupsBase, hMapEq st.groups, hSameScCnt]
  by_cases hEq : sc = sc₀
  · subst hEq; rw [List.getElem_set_self]
    have := usageByClass_bound hwf hscU; have : cg.cnt ≤ 32 := by unfold GroupDesc.cnt; omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cg.cnt < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega), hwf.usage_wf sc hscU, ← hBaseSum sc]
    simp [hcgSc]; omega
  · rw [List.getElem_set_ne hEq, hwf.usage_wf sc₀ hsc₀Old, ← hBaseSum sc₀]
    simp [beq_false_of_ne (hcgSc ▸ hEq)]

theorem sub_ofNat_toNat {x : BitVec 64} {k : Nat} (hk : k ≤ x.toNat) :
    (x - BitVec.ofNat 64 k).toNat = x.toNat - k := by
  have := x.isLt; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]; omega

theorem add_ofNat_toNat {x : BitVec 64} {k : Nat} (hk : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt hk]

end VerifiedLibraries.Mallocng.Proofs
