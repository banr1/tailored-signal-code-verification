/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2
public import VerifiedLibraries.Mallocng.Proofs.GetMetaHelpers
public import VerifiedLibraries.Mallocng.Proofs.InternalPlaced
public import VerifiedLibraries.Mallocng.Proofs.PlacedLeavesRuntimeProof

/-!
# Placed `__malloc_allzerop` Proof

Verifies block `10` (`__malloc_allzerop`) under any `[MallocngMultiPlacement]`, proving
`sf.readReg32 .x0 = (if g'.isMmapped then 1#32 else 0#32)` and `sf.mem = s0.mem`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

private theorem pointsTo64_split_lo8 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) = ((a ↦₈ w.extractLsb' 0 8) ∗ ((a + 1#64) ↦ₛ (unpack64 w).drop 1)) := by
  have h : unpack64 w = [w.extractLsb' 0 8] ++ (unpack64 w).drop 1 := by simp [unpack64]
  conv => lhs; rw [pointsTo64_eq_pointsToBytes, h]
  simp only [pointsToBytes_append, pointsToBytes_singleton, List.length_cons, List.length_nil, addr_norm]

private theorem pointsTo64_split_lo16 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) = ((a ↦₁₆ w.extractLsb' 0 16) ∗ ((a + 2#64) ↦ₛ (unpack64 w).drop 2)) := by
  have h : unpack64 w = [w.extractLsb' 0 8, w.extractLsb' 8 8] ++ (unpack64 w).drop 2 := by simp [unpack64]
  conv => lhs; rw [pointsTo64_eq_pointsToBytes, h]
  rw [pointsToBytes_append, pointsToBytes2_eq_pointsTo16]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, addr_norm]
  rw [show (w.extractLsb' 8 8 ++ w.extractLsb' 0 8) = w.extractLsb' 0 16 by bv_bits]

private theorem hdrB_mask64 (b : BitVec 8) {idx : BitVec 32} (h : b.zeroExtend 32 &&& 0x1f#32 = idx) :
    b.zeroExtend 64 &&& 133143986207#64 = idx.zeroExtend 64 := by subst h; bv_robdd

@[simp, arm64_norm, wp_norm] private theorem trunc32_zx64_shl4 (x : BitVec 32) :
    (x.zeroExtend 64 <<< 4).truncate 32 = x <<< 4 := by bv_robdd

private theorem split_sizeClass_roTablesAt (A : MallocngAddrs) {sc : Nat} (hsc : sc < 48) (R : SepProp) :
    ∃ Rest : SepProp, (MallocngRoTablesAt A ∗ R) =
      (((A.sizeClasses + BitVec.ofNat 64 (2 * sc)) ↦₁₆ᵣ BitVec.ofNat 16 (sizeClass sc)) ∗ Rest ∗ R) := by
  refine ⟨(A.sizeClasses ↦ᵣ sizeClassBytes.take (2 * sc)) ∗
    ((A.sizeClasses + BitVec.ofNat 64 (2 * sc + 2)) ↦ᵣ sizeClassBytes.drop (2 * sc + 2)) ∗
    (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗ (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
    (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗ (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table), ?_⟩
  unfold MallocngRoTablesAt; change ((A.sizeClasses ↦ᵣ sizeClassBytes) ∗ _) ∗ R = _
  rw [pointsToBytesRO_split3 A.sizeClasses sizeClassBytes (2 * sc) 2 (by rw [sizeClassBytes_length]; omega),
    pointsToBytesRO_take2_eq_pointsTo16RO _ _ _ (by rw [sizeClassBytes_length]; omega),
    pack16_sizeClassBytes hsc]
  ac_rfl

private theorem ctx_toBytes_split_secret (ctx : BitVec 64) (c : CtxFields) :
    ∃ rest : List (BitVec 8), (ctx ↦ₛ c.toBytes) = ((ctx ↦₆₄ c.secret) ∗ ((ctx + 8#64) ↦ₛ rest)) := by
  refine ⟨unpack32 c.initDone ++ unpack32 c.mmapCounter ++ unpack64 c.freeMetaHead ++
    unpack64 c.availMeta ++ unpack64 c.availMetaCount ++ unpack64 c.availMetaAreaCount ++
    unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++ unpack64 c.metaAreaTail ++
    unpack64 c.availMetaAreas ++ c.active.flatMap unpack64 ++ c.usageByClass.flatMap unpack64 ++
    c.unmapSeq ++ c.bounces ++ [c.seq] ++ c.seqPad ++ unpack64 c.brk, ?_⟩
  simp only [CtxFields.toBytes, List.append_assoc, pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes, addr_norm]

private theorem bv32_toInt_of_lt31 {a : Nat} (ha : a < 2 ^ 31) : (BitVec.ofNat 32 a).toInt = (a : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; split <;> omega

private theorem bv32_slt_iff_of_lt31 {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (BitVec.ofNat 32 a).slt (BitVec.ofNat 32 b) = decide (a < b) := by
  rw [BitVec.slt, bv32_toInt_of_lt31 ha, bv32_toInt_of_lt31 hb]; by_cases h : a < b <;> simp [h] <;> omega

private theorem bv32_sle_iff_of_lt31 {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (BitVec.ofNat 32 a).sle (BitVec.ofNat 32 b) = decide (a ≤ b) := by
  rw [BitVec.sle, bv32_toInt_of_lt31 ha, bv32_toInt_of_lt31 hb]; by_cases h : a ≤ b <;> simp [h] <;> omega

private theorem sxtw32_of_lt31 {n : Nat} (h : n < 2 ^ 31) :
    (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hLt : (BitVec.ofNat 32 n).ult (1#32 <<< 31) = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change n % 4294967296 < 2147483648; omega
  rw [show BitVec.ofNat 64 n = (BitVec.ofNat 32 n).zeroExtend 64 by bv_omega]; revert hLt; bv_robdd

private theorem sxtw_lsl1_sc {sc : Nat} (hsc : sc < 48) :
    (((BitVec.ofNat 64 sc).truncate 32).signExtend 64 <<< 1) = BitVec.ofNat 64 (2 * sc) := by
  rw [show (BitVec.ofNat 64 sc).truncate 32 = BitVec.ofNat 32 sc by bv_omega, sxtw32_of_lt31 (by omega)]; bv_omega

private theorem sxtw_sbfm_sc {sc : Nat} (hsc : sc < 48) :
    ((BitVec.ofNat 64 sc >>> 0 &&& 4294967295#64 |||
      (if (BitVec.ofNat 64 sc).getLsbD 31 = true then 18446744073709551615#64 else 0#64) &&&
        18446744069414584320#64) <<< 1) = BitVec.ofNat 64 (2 * sc) := by
  have h : (BitVec.ofNat 64 sc).ult 48#64 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change sc % (2 ^ 64) < 48; omega
  rw [show BitVec.ofNat 64 (2 * sc) = BitVec.ofNat 64 sc <<< 1 by bv_omega]
  revert h; bv_robdd

private theorem madd32_idx_sc {idx scVal : Nat} (hsc : scVal < 65536) :
    0#32 + BitVec.ofNat 32 idx * (BitVec.ofNat 16 scVal).zeroExtend 32 = BitVec.ofNat 32 (idx * scVal) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt hsc, Nat.mul_mod]

private theorem add32_sc_madd {idx scVal : Nat} (hsc : scVal < 65536) :
    (BitVec.ofNat 16 scVal).zeroExtend 32 + (0#32 + BitVec.ofNat 32 idx * (BitVec.ofNat 16 scVal).zeroExtend 32) =
      BitVec.ofNat 32 ((idx + 1) * scVal) := by
  rw [madd32_idx_sc hsc]; apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt hsc, Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem sc16_ubfiz_shl4 {sc : Nat} (hsc : sc < 48) :
    ((BitVec.ofNat 16 (sizeClass sc)).zeroExtend 64 &&& 65535#64) <<< 4 = BitVec.ofNat 64 (16 * sizeClass sc) := by
  have ⟨_, hMax, _, _⟩ := sizeClass_bounds hsc
  rw [show ∀ x : BitVec 16, x.zeroExtend 64 &&& 65535#64 = x.zeroExtend 64 by intro x; bv_robdd]
  rw [show (BitVec.ofNat 16 (sizeClass sc)).zeroExtend 64 = BitVec.ofNat 64 (sizeClass sc) by
    apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt (by omega : sizeClass sc < 65536), Nat.mod_eq_of_lt (by omega : sizeClass sc < 2 ^ 64)]]
  bv_omega

private theorem maplen_shr4_sub1_ult_false {m tot : Nat} (hm0 : 0 < m) (hm48 : m * 4096 ≤ 2 ^ 48)
    (htot : tot < 2 ^ 27) (hoff : tot + 2 ≤ m * 256) :
    ((BitVec.ofNat 64 (m * 4096) >>> 4 - 1#64).ult ((BitVec.ofNat 32 tot).signExtend 64)) = false := by
  have hShr : BitVec.ofNat 64 (m * 4096) >>> 4 = BitVec.ofNat 64 (m * 256) := by
    apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega : m * 4096 < 2 ^ 64)]; omega
  rw [sxtw32_of_lt31 (by omega), hShr, show BitVec.ofNat 64 (m * 256) - 1#64 = BitVec.ofNat 64 (m * 256 - 1) by bv_omega,
    BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

private theorem tot_ule_maplen_shr4_sub1_true {m tot : Nat} (hm0 : 0 < m) (hm48 : m * 4096 ≤ 2 ^ 48)
    (htot : tot < 2 ^ 27) (hoff : tot + 2 ≤ m * 256) :
    (((BitVec.ofNat 32 tot).signExtend 64).ule (BitVec.ofNat 64 (m * 4096) >>> 4 - 1#64)) = true := by
  have h := maplen_shr4_sub1_ult_false hm0 hm48 htot hoff
  revert h; bv_robdd

private theorem bv64_ult_of_lt {n k : Nat} (hk : k < 2 ^ 64) (h : n < k) :
    (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 k) = true := by
  rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hk]; exact h

private theorem packedWord_sc63_mask (g : GroupDesc) (hLast : g.lastIdx ≤ 31)
    (hSc63 : g.sc = 63) (hMap : g.maplen < 2 ^ 52) :
    ((g.packedWord.extractLsb' 0 16).zeroExtend 32) &&& 0xfc0#32 = 0xfc0#32 := by
  have hL := bv64_ult_of_lt (by omega) (Nat.lt_succ_of_le hLast)
  have hM := bv64_ult_of_lt (k := 2 ^ 52) (by omega) hMap
  dsimp only [GroupDesc.packedWord]; rw [hSc63]; revert hL hM; bv_robdd

private theorem packedWord_maplen_mask (g : GroupDesc) (hLast : g.lastIdx ≤ 31)
    (hSc : g.sc < 64) (hMap48 : g.maplen * 4096 ≤ 2 ^ 48) :
    g.packedWord &&& -4096#64 = BitVec.ofNat 64 (g.maplen * 4096) := by
  have hL := bv64_ult_of_lt (by omega) (Nat.lt_succ_of_le hLast)
  have hS := bv64_ult_of_lt (by omega) hSc
  have hM := bv64_ult_of_lt (k := 2 ^ 52) (by omega) (by omega : g.maplen < 2 ^ 52)
  rw [← show (BitVec.ofNat 64 g.maplen <<< 12) = BitVec.ofNat 64 (g.maplen * 4096) by bv_omega]
  dsimp only [GroupDesc.packedWord]; revert hL hS hM; bv_robdd

private theorem packedWord_byte0_and31 (g : GroupDesc) (hLast : g.lastIdx ≤ 31) :
    ((g.packedWord.extractLsb' 0 8).zeroExtend 32) &&& 0x1f#32 = BitVec.ofNat 32 g.lastIdx ∧
    (((g.packedWord.extractLsb' 0 8).zeroExtend 64)) &&& 0x1f#64 = BitVec.ofNat 64 g.lastIdx := by
  have hL := bv64_ult_of_lt (by omega) (Nat.lt_succ_of_le hLast)
  refine ⟨?_, by dsimp only [GroupDesc.packedWord]; revert hL; bv_robdd⟩
  rw [show BitVec.ofNat 32 g.lastIdx = (BitVec.ofNat 64 g.lastIdx).truncate 32 by bv_omega]
  dsimp only [GroupDesc.packedWord]; revert hL; bv_robdd

@[irreducible] private def AllzeropRest (γ : GhostName) (A : MallocngAddrs)
    (st : MallocngSt) (p : BitVec 64) (bs : List (BitVec 8)) (T : SepProp) : SepProp :=
  MallocngLiveAuth γ st.liveMap ∗
  (A.lock ↦₃₂ 0#32) ∗
  (A.replaced ↦₃₂ 0#32) ∗
  (A.aaReplaced ↦₃₂ 0#32) ∗
  ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
  MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
  ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
  MappedSet st.masterDom (OwnedMappedByte st) ∗
  (p ↦ₛ bs) ∗
  T

private def allzeropPre (γ : GhostName) (A : MallocngAddrs) (st : MallocngSt)
    (p : BitVec 64) (bs : List (BitVec 8)) (T : SepProp) : SepProp :=
  MallocngRoTablesAt A ∗ (A.ctx ↦ₛ st.ctx.toBytes) ∗
  ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
  AllzeropRest γ A st p bs T

private def AllzeropFramePres (s0 s : State) : Prop :=
  s.mem = s0.mem ∧ s.brk = s0.brk ∧ MallocngProcPreserved s0 s ∧
  s.sp = s0.sp ∧ s.spAligned = s0.spAligned ∧
  s.readReg64 .x30 = s0.readReg64 .x30 ∧ CalleeSavedPreserved s0 s

private theorem allzeropFramePres_trans {s0 s1 s2 : State}
    (h01 : AllzeropFramePres s0 s1) (h12 : AllzeropFramePres s1 s2) :
    AllzeropFramePres s0 s2 := by
  obtain ⟨hm1, hb1, hp1, hsp1, hal1, hlr1, hcs1⟩ := h01
  obtain ⟨hm2, hb2, hp2, hsp2, hal2, hlr2, hcs2⟩ := h12
  refine ⟨hm2.trans hm1, hb2.trans hb1, ?_, hsp2.trans hsp1, hal2.trans hal1, hlr2.trans hlr1, ?_⟩
  · unfold MallocngProcPreserved at hp1 hp2 ⊢; simp only [hp2, hp1, and_self]
  · unfold CalleeSavedPreserved at hcs1 hcs2 ⊢; simp only [hcs2, hcs1, and_self]

private theorem allzerop_hdr_ok [MallocngMultiPlacement] {b : BitVec 64} (_hb : BlkBase 10 b)
    {γ : GhostName} {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {p : BitVec 64} {bs : List (BitVec 8)} {req effCost : Nat} {T : SepProp}
    (hF : LiveUserBlockFacts st g idx p req effCost)
    {s0 : State} (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = p) :
    let tot := (p.toNat - g.storage.toNat) / 16
    let P := allzeropPre γ maddrs st p bs T
    SepWP (blkPC_b10.rebase b (fun _ => none)) (b + 0x38#64) s0 P
      (sepPost (fun s1 => AllzeropFramePres s0 s1 ∧ s1.readReg64 .x0 = p ∧
        s1.readReg64 .x1 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s1.readReg64 .x2 = (BitVec.ofNat 32 tot).zeroExtend 64) P) (fun _ => ⌜False⌝) := by
  intro tot P
  let res := (g.slotEnd idx).toNat - (p.toNat + req)
  let r5 := min res 5
  let hdrB : BitVec 8 := BitVec.ofNat 8 ((r5 <<< 5) ||| idx)
  have hAnd15 := hF.p_and_15
  have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
  have ⟨hHdrIdx, _, _, _⟩ := hdrByte_extract r5 idx (Nat.min_le_right _ _) hIdx31
  by_cases hShort : tot ≤ 0xffff
  · conv => arg 4; dsimp only [P, allzeropPre]; rw [hF.focus_hdr_short hShort]
    wp_steps
    conv => arg 4; rw [← hF.focus_hdr_short hShort]
    refine SepWP.done rfl (by simp [hrun]) ⟨⟨?_, by simp [hx0], ?_, ?_⟩, Entails.refl _⟩
    · exact ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp [CalleeSavedPreserved]⟩
    · simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]
      exact hdrB_mask64 hdrB hHdrIdx
    · simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]
      change BitVec.zeroExtend 64 (BitVec.ofNat 16 tot) = (BitVec.ofNat 32 tot).zeroExtend 64; bv_omega
  · have hLong : 0xffff < tot := by omega
    have hTotLt27 := hF.totalOff_lt_27
    have hSleF : (BitVec.ofNat 32 tot).sle 0xffff#32 = false := by
      rw [show (0xffff#32 : BitVec 32) = BitVec.ofNat 32 0xffff from rfl, bv32_sle_iff_of_lt31 (by omega) (by omega)]
      simp [show ¬ (tot ≤ 0xffff) by omega]
    conv => arg 4; dsimp only [P, allzeropPre]; rw [hF.focus_hdr_long hLong]
    wp_steps
    conv => arg 4; rw [← hF.focus_hdr_long hLong]
    refine SepWP.done rfl (by simp [hrun]) ⟨⟨?_, by simp [hx0], ?_, ?_⟩, Entails.refl _⟩
    · exact ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp [CalleeSavedPreserved]⟩
    · simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]
      exact hdrB_mask64 hdrB hHdrIdx
    · simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]; rfl

private theorem allzerop_meta_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 10 b)
    {γ : GhostName} {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {p : BitVec 64} {bs : List (BitVec 8)} {req effCost : Nat} {T : SepProp}
    (hF : LiveUserBlockFacts st g idx p req effCost)
    {s1 : State} (hpc : s1.pc = b + 0x38#64) (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = p)
    (hx1 : s1.readReg64 .x1 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx2 : s1.readReg64 .x2 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64) :
    let P := allzeropPre γ maddrs st p bs T
    SepWP (blkPC_b10.rebase b (fun _ => none)) (b + 0xa4#64) s1 P
      (sepPost (fun s2 => AllzeropFramePres s1 s2 ∧ s2.readReg64 .x0 = g.metaPtr ∧
        s2.readReg64 .x1 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s2.readReg64 .x2 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64 ∧
        s2.readReg64 .x5 = (g.packedWord.extractLsb' 0 8).zeroExtend 64) P) (fun _ => ⌜False⌝) := by
  intro P
  have _ := hb
  have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
  have hMemAddr : p + (-16#64 - ((BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16) <<< 4).signExtend 64)) = g.mem :=
    group_mem_addr_of_totalOff hF.totalOff_lt_27
      (by have := hF.p_add_n_48; rw [← hF.p_eq_storage_off]; omega) hF.p_eq_storage_off
  have hMemAddrU : p + (18446744073709551600#64 - ((BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16) <<< 4).signExtend 64)) = g.mem :=
    hMemAddr
  have ⟨hByte32, _⟩ := packedWord_byte0_and31 g hF.last_le_31
  have hByteMask := hdrB_mask64 (g.packedWord.extractLsb' 0 8) hByte32
  have ⟨hAv1, hAv2⟩ := mask_ushiftRight_bit0_false g.availMask hIdx31 hF.avail_bit_false
  have ⟨hFr1, hFr2⟩ := mask_ushiftRight_bit0_false g.freedMask hIdx31 hF.freed_bit_false
  obtain ⟨ma, _, hMaBase, hFocusMa⟩ := hF.meta_page_base
  have hMaBase' : g.metaPtr &&& -4096#64 = ma.base := hMaBase
  obtain ⟨ctxRest, hCtxSplit⟩ := ctx_toBytes_split_secret maddrs.ctx st.ctx
  have hPageCtx := pageOf_add_lo12Of maddrs.ctx
  conv => arg 4; dsimp only [P, allzeropPre]; rw [hF.focus_group_mem]
  wp_step; wp_step; wp_step; wp_step; wp_step
  conv => arg 4; rw [← hF.focus_group_mem, hF.focus_meta, pointsTo64_split_lo8 (g.metaPtr + 32#64) g.packedWord]
  wp_steps
  wp_if hgt
  · exfalso; have := hF.last_le_31; have := hF.idx_le_last
    rw [bv32_slt_iff_of_lt31 (by omega) (by omega), decide_eq_true_eq] at hgt; omega
  · wp_steps
    conv => arg 4; rw [← pointsTo64_split_lo8 (g.metaPtr + 32#64) g.packedWord, ← hF.focus_meta, hFocusMa, hCtxSplit]
    wp_steps
    conv => arg 4; rw [← hCtxSplit, ← hFocusMa]
    refine SepWP.done rfl (by simp [hrun])
      ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp [CalleeSavedPreserved]⟩,
        by simp, by simp [hx1], by simp [hx2], by simp⟩, Entails.refl _⟩

set_option maxHeartbeats 400000 in
private theorem allzerop_tail_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 10 b)
    {γ : GhostName} {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {p : BitVec 64} {bs : List (BitVec 8)} {req effCost : Nat} {T : SepProp}
    (hF : LiveUserBlockFacts st g idx p req effCost)
    {s2 : State} (hpc : s2.pc = b + 0xa4#64) (hrun : s2.status = .Running)
    (hx0 : s2.readReg64 .x0 = g.metaPtr)
    (hx1 : s2.readReg64 .x1 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx2 : s2.readReg64 .x2 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64)
    (hx5 : s2.readReg64 .x5 = (g.packedWord.extractLsb' 0 8).zeroExtend 64) :
    let P := allzeropPre γ maddrs st p bs T
    SepWP (blkPC_b10.rebase b (fun _ => none)) (s2.readReg64 .x30) s2 P
      (sepPost (fun sf => AllzeropFramePres s2 sf ∧
        sf.readReg32 .x0 = (if g.isMmapped then 1#32 else 0#32)) P) (fun _ => ⌜False⌝) := by
  intro P
  have _ := hb
  have hSc64 : g.sc < 64 := by rcases hF.sc_cases with h | h <;> omega
  have hUbfxSc : (((g.packedWord.extractLsb' 0 16).zeroExtend 64 >>> 6) &&& 0x3f#64) = BitVec.ofNat 64 g.sc := by
    have hL : (BitVec.ofNat 64 g.lastIdx).ult 32#64 = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; have := hF.last_le_31; change g.lastIdx % (2 ^ 64) < 32; omega
    have hS : (BitVec.ofNat 64 g.sc).ult 64#64 = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change g.sc % (2 ^ 64) < 64; omega
    have hM : (BitVec.ofNat 64 g.maplen).ult (1#64 <<< 52) = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; have := hF.maplen_lt_52; change g.maplen % (2 ^ 64) < 2 ^ 52; omega
    dsimp only [GroupDesc.packedWord]; revert hL hS hM; bv_robdd
  have hMapMask := packedWord_maplen_mask g hF.last_le_31 hSc64 hF.maplen_bytes_48
  have ⟨_, hByte64⟩ := packedWord_byte0_and31 g hF.last_le_31
  have hPageSc := pageOf_add_lo12Of maddrs.sizeClasses
  conv => arg 4; dsimp only [P, allzeropPre]; rw [hF.focus_meta, pointsTo64_split_lo16 (g.metaPtr + 32#64) g.packedWord]
  wp_step; wp_step; wp_step; wp_step
  conv => arg 4; rw [← pointsTo64_split_lo16 (g.metaPtr + 32#64) g.packedWord, ← hF.focus_meta]
  rcases hF.sc_cases with hsc48 | hsc63
  · wp_if hhi
    · exfalso
      rw [show (BitVec.ofNat 64 g.sc).truncate 32 = BitVec.ofNat 32 g.sc by bv_omega,
        BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hhi
      change 47 < g.sc % 4294967296 at hhi; omega
    · obtain ⟨roRest, hRoSplit⟩ := split_sizeClass_roTablesAt maddrs hsc48
        ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
          AllzeropRest γ maddrs st p bs T)
      have hOffSc := sxtw_lsl1_sc hsc48
      have hSbfmSc := sxtw_sbfm_sc hsc48
      have hSxtwSc : ((BitVec.ofNat 64 g.sc).truncate 32).signExtend 64 = BitVec.ofNat 64 g.sc := by
        rw [show (BitVec.ofNat 64 g.sc).truncate 32 = BitVec.ofNat 32 g.sc by bv_omega, sxtw32_of_lt31 (by omega)]
      have hLsl1Sc : BitVec.ofNat 64 g.sc <<< 1 = BitVec.ofNat 64 (2 * g.sc) := by bv_omega
      have ⟨_, huMax, _, _⟩ := sizeClass_bounds hsc48
      have ⟨hLow, hHigh⟩ := hF.sc_lt_48_off hsc48
      have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
      have hMulB1 : idx * sizeClass g.sc ≤ 31 * 8191 := Nat.mul_le_mul hIdx31 huMax
      have hMulB2 : (idx + 1) * sizeClass g.sc ≤ 32 * 8191 := Nat.mul_le_mul (by omega) huMax
      have hTot27 := hF.totalOff_lt_27
      conv => arg 4; dsimp only [P, allzeropPre]; rw [hRoSplit]
      wp_steps
      wp_if hlt
      · exfalso
        rw [madd32_idx_sc (by omega), bv32_slt_iff_of_lt31 (by omega) (by omega), decide_eq_true_eq] at hlt; omega
      · wp_steps
        wp_if hge
        · exfalso
          rw [add32_sc_madd (by omega), bv32_sle_iff_of_lt31 (by omega) (by omega), decide_eq_true_eq] at hge; omega
        ·
          conv => arg 4; rw [← hRoSplit, hF.focus_meta]
          wp_step; wp_step; wp_step
          conv => arg 4; rw [← hF.focus_meta]
          by_cases hMap0 : g.maplen = 0
          ·
            have hIsMmap : g.isMmapped = false := by
              simp [GroupDesc.isMmapped, show g.sc ≠ 63 by omega, hMap0]
            wp_if hneMap
            · exfalso; simp [hMap0] at hneMap
            · conv => arg 4; rw [hRoSplit]
              wp_steps
              by_cases hLast0 : g.lastIdx = 0
              · exfalso
                have ⟨_, hGe1⟩ := hF.maplen_zero_sc hMap0
                omega
              · wp_if hneLast
                · wp_steps
                  conv => arg 4; rw [← hRoSplit]
                  refine SepWP.done rfl (by simp [hrun])
                    ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp [CalleeSavedPreserved]⟩,
                      by simp [arm64_norm, hIsMmap]⟩, Entails.refl _⟩
                · exfalso
                  have h0 : (BitVec.ofNat 64 g.lastIdx).toNat = 0 := by rw [hneLast]; rfl
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hF.last_le_31; omega)] at h0
                  exact hLast0 h0
          ·
            have hMapPos : 0 < g.maplen := Nat.pos_of_ne_zero hMap0
            have hMap48 := hF.maplen_bytes_48
            have hMapOff := hF.maplen_pos_off hMapPos
            wp_if hneMap
            · wp_steps
              wp_if hlo
              · exfalso; rw [maplen_shr4_sub1_ult_false hMapPos hMap48 hTot27 hMapOff] at hlo; cases hlo
              · wp_step
                conv => arg 4; rw [hRoSplit]
                wp_steps
                by_cases hLast0 : g.lastIdx = 0
                · wp_if hneLast
                  · exfalso; simp [hLast0] at hneLast
                  · wp_steps
                    conv => arg 4; rw [← hRoSplit]
                    have hSub16 : BitVec.ofNat 64 (g.maplen * 4096) - 16#64 =
                        BitVec.ofNat 64 (g.maplen * 4096 - 16) := by bv_omega
                    have hUleEq :
                        (BitVec.ofNat 64 (16 * sizeClass g.sc)).ule (BitVec.ofNat 64 (g.maplen * 4096 - 16)) =
                          !g.isMmapped := by
                      rw [BitVec.ule, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                      have hscNe63 : (g.sc == 63) = false := beq_false_of_ne (by omega)
                      have hBool : ∀ a b : Nat, decide (a ≤ b) = !decide (b < a) := fun a b => by
                        by_cases h : a ≤ b <;> simp [h] <;> omega
                      rw [hBool]
                      unfold GroupDesc.isMmapped slotStride
                      rw [hscNe63, hLast0, decide_eq_true hMapPos]
                      rfl
                    refine SepWP.done rfl (by simp [hrun])
                      ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp [CalleeSavedPreserved]⟩,
                        ?_⟩, Entails.refl _⟩
                    simp [arm64_norm, sc16_ubfiz_shl4 hsc48, hSub16, hUleEq]
                    cases g.isMmapped <;> rfl
                · have hIsMmap : g.isMmapped = false := by
                    simp [GroupDesc.isMmapped, show g.sc ≠ 63 by omega, hLast0]
                  wp_if hneLast
                  · wp_steps
                    conv => arg 4; rw [← hRoSplit]
                    refine SepWP.done rfl (by simp [hrun])
                      ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp [CalleeSavedPreserved]⟩,
                        by simp [arm64_norm, hIsMmap]⟩, Entails.refl _⟩
                  · exfalso
                    have h0 : (BitVec.ofNat 64 g.lastIdx).toNat = 0 := by rw [hneLast]; rfl
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hF.last_le_31; omega)] at h0
                    exact hLast0 h0
            · exfalso
              have h0 : (BitVec.ofNat 64 (g.maplen * 4096)).toNat = 0 := by rw [hneMap]; rfl
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
  ·
    have hMask63 := packedWord_sc63_mask g hF.last_le_31 hsc63 hF.maplen_lt_52
    have ⟨_, hMapPos, _, _⟩ := hF.sc_63_props hsc63
    have hMap48 := hF.maplen_bytes_48
    have hTot27 := hF.totalOff_lt_27
    have hMapOff := hF.maplen_pos_off hMapPos
    have hIsMmap : g.isMmapped = true := by simp [GroupDesc.isMmapped, hsc63]
    wp_if hhi
    · wp_steps
      conv => arg 4; rw [hF.focus_meta]
      wp_step; wp_step; wp_step
      conv => arg 4; rw [← hF.focus_meta]
      wp_if hneMap
      · wp_steps
        wp_if hhs
        · wp_steps
          refine SepWP.done rfl (by simp [hrun])
            ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp [CalleeSavedPreserved]⟩,
              by simp [arm64_norm, hIsMmap]⟩, Entails.refl _⟩
        · exfalso
          rw [tot_ule_maplen_shr4_sub1_true hMapPos hMap48 hTot27 hMapOff] at hhs
          exact hhs rfl
      · exfalso
        have h0 : (BitVec.ofNat 64 (g.maplen * 4096)).toNat = 0 := by rw [hneMap]; rfl
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
    · exfalso; rw [hsc63] at hhi; exact hhi rfl

set_option maxRecDepth 20000 in
private theorem coreStA_eq_allzeropPre (γ : GhostName) (A : MallocngAddrs)
    (brkStart brk : BitVec 64) (liveCost peakCost : Nat) (st : MallocngSt)
    (p : BitVec 64) (bs : List (BitVec 8)) (T : SepProp) :
    (MallocngRoTablesA A ∗
      MallocngCoreStA γ A brkStart brk liveCost peakCost st ∗
      (p ↦ₛ bs) ∗
      T) =
    (⌜MallocngWFInflight 0 A.base brkStart brk liveCost peakCost st⌝ ∗
      allzeropPre γ A st p bs T) := by
  dsimp only [MallocngRoTablesA, MallocngCoreStA, MallocngCoreStInflightA, allzeropPre]
  unfold AllzeropRest
  ac_rfl

private theorem blk10_mallocAllzerop [MallocngMultiPlacement]
    (γ : GhostName) (brkStart p : BitVec 64) (bs : List (BitVec 8))
    (req effCost liveCost peakCost idx : Nat) (st : MallocngSt) (g' : GroupDesc) (T : SepProp)
    (hg' : g' ∈ st.groups) (hIdx : idx < g'.slots.length)
    (hSlot : g'.slots[idx]'hIdx = .liveUser p req effCost) :
    subroutine_ok (mallocngBlockProg mmpl 10 msvc) (mbase 10) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.readReg64 .x0 = p⌝ ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStA γ maddrs brkStart s0.brk liveCost peakCost st ∗
        (p ↦ₛ bs) ∗
        T
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem = s0.mem ∧
         sf.readReg32 .x0 = (if g'.isMmapped then 1#32 else 0#32)⌝ ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStA γ maddrs brkStart sf.brk liveCost peakCost st ∗
        (p ↦ₛ bs) ∗
        T
    }) := by
  refine subroutine_ok_withCL_of_cl fun m0 _hcl0 => ?_
  have hfn : ∀ c, (blkPC_b10.rebase c (fun _ => none)).fnAddr "__malloc_allzerop" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase]
    change c + BitVec.ofNat 64 (blkPC_b10.fnOff "__malloc_allzerop") = c
    rw [blkPC_b10_fnOff_0x0]
    exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b10 (hfn (mbase 10)) fun b hb => ?_
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre _hsp
  rw [hfn b] at hpc
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨_hm0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hx0, hpre⟩ := hpre
  rw [coreStA_eq_allzeropPre, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hwf, hpreP⟩ := hpre
  have hF : LiveUserBlockFacts st g' idx p req effCost :=
    liveUserBlockFacts_of hwf hg' hIdx hSlot
  refine ⟨allzeropPre γ maddrs st p bs T, hpreP, ?_⟩
  refine SepWP.seq (allzerop_hdr_ok hb hF hpc hrun hx0) ?_
  rintro s1 P1 hpc1 hrun1 ⟨⟨hP01, hx0_1, hx1_1, hx2_1⟩, hE1⟩
  refine SepWP.weaken_pre hE1 ?_
  refine SepWP.seq (allzerop_meta_ok hb hF hpc1 hrun1 hx0_1 hx1_1 hx2_1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨⟨hP12, hx0_2, hx1_2, hx2_2, hx5_2⟩, hE2⟩
  refine SepWP.weaken_pre hE2 ?_
  have hlr2 : s2.readReg64 .x30 = s0.readReg64 Reg.lr := hP12.2.2.2.2.2.1.trans hP01.2.2.2.2.2.1
  rw [← hlr2]
  refine SepWP.mono (allzerop_tail_ok hb hF hpc2 hrun2 hx0_2 hx1_2 hx2_2 hx5_2) ?_
  rintro sf Pf _ _ ⟨⟨hP2f, hret⟩, hEf⟩
  have hAll := allzeropFramePres_trans hP01 (allzeropFramePres_trans hP12 hP2f)
  obtain ⟨hmem_eq, hbrk_eq, hproc, hsp_eq, _, _, hcs⟩ := hAll
  refine ⟨fun hm => ?_, hsp_eq, hcs⟩
  dsimp only []
  rw [coreStA_eq_allzeropPre]
  refine Satisfies.mono (sepConj_mono_left ?_) (Satisfies.mono (sepConj_mono_left hEf) hm)
  exact Entails.pure_right ⟨hproc, hbrk_eq, hmem_eq, hret⟩
    (Entails.pure_right (hbrk_eq ▸ hwf) (Entails.refl _))

/-- Polymorphic cross-block `__malloc_allzerop(p)` (`blk10`, `0` B stack, `sf.mem = s0.mem`). -/
theorem placed_mallocAllzerop_ok [MallocngMultiPlacement] {P : Program}
    (γ : GhostName) (brkStart p : BitVec 64) (bs : List (BitVec 8))
    (req effCost liveCost peakCost idx : Nat) (st : MallocngSt) (g' : GroupDesc) (T : SepProp)
    (hg' : g' ∈ st.groups) (hIdx : idx < g'.slots.length)
    (hSlot : g'.slots[idx]'hIdx = .liveUser p req effCost)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 10) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.readReg64 .x0 = p⌝ ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStA γ maddrs brkStart s0.brk liveCost peakCost st ∗
        (p ↦ₛ bs) ∗
        T
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem = s0.mem ∧
         sf.readReg32 .x0 = (if g'.isMmapped then 1#32 else 0#32)⌝ ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStA γ maddrs brkStart sf.brk liveCost peakCost st ∗
        (p ↦ₛ bs) ∗
        T
    }) :=
  subroutine_ok_block_to_block (j := 10) (by decide)
    (blk10_mallocAllzerop γ brkStart p bs req effCost liveCost peakCost idx st g' T hg' hIdx hSlot)
    hext hsvc

end VerifiedLibraries.Mallocng.Proofs
