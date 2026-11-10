/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocStage3Absorb

/-!
# Placed `__libc_realloc` Stack Frame, Epilogue, and Stage 1

Defines the 800-byte stack-frame predicates (`ReallocSavedLo`, `ReallocSavedHi`, `ReallocSavedAll`)
for placed `__libc_realloc` (`blkPC_b14`), proves the shared return epilogue (`realloc_epilogue_ok`,
`+0x294..+0x2a4`), and verifies Stage 1 (`realloc_stage1_read_ok`, `+0x03c..+0x1b8`), which
executes `get_meta`, `get_stride`, and `get_nominal_size` without modifying memory.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Sub-word splits and bitvector lemmas -/

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

theorem split_sizeClass_roTablesAt (A : MallocngAddrs) {sc : Nat} (hsc : sc < 48) (R : SepProp) :
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

theorem bv32_toInt_of_lt31 {a : Nat} (ha : a < 2 ^ 31) : (BitVec.ofNat 32 a).toInt = (a : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; split <;> omega

theorem bv32_slt_iff_of_lt31 {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (BitVec.ofNat 32 a).slt (BitVec.ofNat 32 b) = decide (a < b) := by
  rw [BitVec.slt, bv32_toInt_of_lt31 ha, bv32_toInt_of_lt31 hb]; by_cases h : a < b <;> simp [h] <;> omega

theorem bv32_sle_iff_of_lt31 {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (BitVec.ofNat 32 a).sle (BitVec.ofNat 32 b) = decide (a ≤ b) := by
  rw [BitVec.sle, bv32_toInt_of_lt31 ha, bv32_toInt_of_lt31 hb]; by_cases h : a ≤ b <;> simp [h] <;> omega

theorem sxtw32_of_lt31 {n : Nat} (h : n < 2 ^ 31) :
    (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hLt : (BitVec.ofNat 32 n).ult (1#32 <<< 31) = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change n % 4294967296 < 2147483648; omega
  rw [show BitVec.ofNat 64 n = (BitVec.ofNat 32 n).zeroExtend 64 by bv_omega]; revert hLt; bv_robdd

theorem sxtw_lsl1_sc {sc : Nat} (hsc : sc < 48) :
    (((BitVec.ofNat 64 sc).truncate 32).signExtend 64 <<< 1) = BitVec.ofNat 64 (2 * sc) := by
  rw [show (BitVec.ofNat 64 sc).truncate 32 = BitVec.ofNat 32 sc by bv_omega, sxtw32_of_lt31 (by omega)]; bv_omega

theorem sxtw_sbfm_sc {sc : Nat} (hsc : sc < 48) :
    ((BitVec.ofNat 64 sc >>> 0 &&& 4294967295#64 |||
      (if (BitVec.ofNat 64 sc).getLsbD 31 = true then BitVec.ofNat 64 (2 ^ 64 - 1) else 0#64) &&&
        BitVec.ofNat 64 ((2 ^ 32 - 1) <<< 32)) <<< 1) = BitVec.ofNat 64 (2 * sc) := by
  have h : (BitVec.ofNat 64 sc).ult 48#64 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change sc % (2 ^ 64) < 48; omega
  rw [show BitVec.ofNat 64 (2 * sc) = BitVec.ofNat 64 sc <<< 1 by bv_omega]; revert h; bv_robdd

private theorem madd32_idx_sc {idx scVal : Nat} (hsc : scVal < 65536) :
    0#32 + BitVec.ofNat 32 idx * (BitVec.ofNat 16 scVal).zeroExtend 32 = BitVec.ofNat 32 (idx * scVal) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt hsc, Nat.mul_mod]

private theorem add32_sc_madd {idx scVal : Nat} (hsc : scVal < 65536) :
    (BitVec.ofNat 16 scVal).zeroExtend 32 + (0#32 + BitVec.ofNat 32 idx * (BitVec.ofNat 16 scVal).zeroExtend 32) =
      BitVec.ofNat 32 ((idx + 1) * scVal) := by
  rw [madd32_idx_sc hsc]; apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt hsc, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem sc16_ubfiz_shl4 {sc : Nat} (hsc : sc < 48) :
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

theorem bv64_ult_of_lt {n k : Nat} (hk : k < 2 ^ 64) (h : n < k) :
    (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 k) = true := by
  rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hk]; exact h

theorem packedWord_sc63_mask (g : GroupDesc) (hLast : g.lastIdx ≤ 31)
    (hSc63 : g.sc = 63) (hMap : g.maplen < 2 ^ 52) :
    ((g.packedWord.extractLsb' 0 16).zeroExtend 32) &&& 0xfc0#32 = 0xfc0#32 := by
  have hL := bv64_ult_of_lt (by omega) (Nat.lt_succ_of_le hLast)
  have hM := bv64_ult_of_lt (k := 2 ^ 52) (by omega) hMap
  dsimp only [GroupDesc.packedWord]; rw [hSc63]; revert hL hM; bv_robdd

theorem packedWord_maplen_mask (g : GroupDesc) (hLast : g.lastIdx ≤ 31)
    (hSc : g.sc < 64) (hMap48 : g.maplen * 4096 ≤ 2 ^ 48) :
    g.packedWord &&& -4096#64 = BitVec.ofNat 64 (g.maplen * 4096) := by
  have hL := bv64_ult_of_lt (by omega) (Nat.lt_succ_of_le hLast)
  have hS := bv64_ult_of_lt (by omega) hSc
  have hM := bv64_ult_of_lt (k := 2 ^ 52) (by omega) (by omega : g.maplen < 2 ^ 52)
  rw [← show (BitVec.ofNat 64 g.maplen <<< 12) = BitVec.ofNat 64 (g.maplen * 4096) by bv_omega]
  dsimp only [GroupDesc.packedWord]; revert hL hS hM; bv_robdd

theorem packedWord_byte0_and31 (g : GroupDesc) (hLast : g.lastIdx ≤ 31) :
    ((g.packedWord.extractLsb' 0 8).zeroExtend 32) &&& 0x1f#32 = BitVec.ofNat 32 g.lastIdx ∧
    (((g.packedWord.extractLsb' 0 8).zeroExtend 64)) &&& 0x1f#64 = BitVec.ofNat 64 g.lastIdx := by
  have hL := bv64_ult_of_lt (by omega) (Nat.lt_succ_of_le hLast)
  refine ⟨?_, by dsimp only [GroupDesc.packedWord]; revert hL; bv_robdd⟩
  rw [show BitVec.ofNat 32 g.lastIdx = (BitVec.ofNat 64 g.lastIdx).truncate 32 by bv_omega]
  dsimp only [GroupDesc.packedWord]; revert hL; bv_robdd

private theorem hdr8_ule_0x9f (b : BitVec 8) :
    (b.zeroExtend 64).ule 0x9f#64 = (b.zeroExtend 32).ule 0x9f#32 ∧
    ((b.zeroExtend 64).truncate 32).ule 0x9f#32 = (b.zeroExtend 32).ule 0x9f#32 ∧
    (((b.zeroExtend 64).truncate 32).zeroExtend 64).ule 0x9f#64 = (b.zeroExtend 32).ule 0x9f#32 ∧
    (b >>> 5).zeroExtend 64 = ((b.zeroExtend 32) >>> 5).zeroExtend 64 :=
  ⟨by bv_robdd, by bv_robdd, by bv_robdd, by bv_robdd⟩

/-! ## Stack frame layout and shared epilogue -/

def ReallocSavedLo (s0 : State) (sp1 : BitVec 64) : SepProp :=
  (sp1 ↦₆₄ s0.readReg64 .x29) ∗
  ((sp1 + 8#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp1 + 16#64) ↦₆₄ s0.readReg64 .x19) ∗
  ((sp1 + 24#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp1 + 32#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp1 + 40#64) ↦₆₄ s0.readReg64 .x22)

def ReallocSavedHi (s0 : State) (sp1 : BitVec 64) : SepProp :=
  ((sp1 + 48#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp1 + 56#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp1 + 64#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp1 + 72#64) ↦₆₄ s0.readReg64 .x26)

def ReallocSavedAll (s0 : State) (sp1 : BitVec 64) : SepProp :=
  ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1

def ReallocUntouchedCS (s0 s : State) : Prop :=
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem stackFrame800_split (s0 : State) :
    let sp1 := s0.sp - 80#64
    stackFrame s0 800 =
      ((memRegion sp1 8 ∗ memRegion (sp1 + 8#64) 8 ∗
        memRegion (sp1 + 16#64) 8 ∗ memRegion (sp1 + 24#64) 8 ∗
        memRegion (sp1 + 32#64) 8 ∗ memRegion (sp1 + 40#64) 8) ∗
       (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
        memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
       stackFrameAt sp1 720) := by
  intro sp1
  have hSplit : stackFrame s0 800 = (memRegion sp1 80 ∗ stackFrameAt sp1 720) := by
    unfold stackFrame
    rw [← stackFrameAt_eq_memRegion s0.sp 800, show (800 : Nat) = 80 + 720 from rfl,
        stackFrameAt_split s0.sp 80 720, stackFrameAt_eq_memRegion s0.sp 80]
  rw [hSplit,
      memRegion_split' (b' := sp1 + 8#64) (n := 8) (k := 72) rfl rfl (by decide),
      memRegion_split' (b := sp1 + 8#64) (b' := sp1 + 16#64) (n := 8) (k := 64) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 16#64) (b' := sp1 + 24#64) (n := 8) (k := 56) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 24#64) (b' := sp1 + 32#64) (n := 8) (k := 48) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 32#64) (b' := sp1 + 40#64) (n := 8) (k := 40) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 40#64) (b' := sp1 + 48#64) (n := 8) (k := 32) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 48#64) (b' := sp1 + 56#64) (n := 8) (k := 24) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 56#64) (b' := sp1 + 64#64) (n := 8) (k := 16) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 64#64) (b' := sp1 + 72#64) (n := 8) (k := 8) rfl (by bv_lin) (by decide)]
  generalize (stackFrameAt sp1 720) = SF
  ac_rfl

theorem reallocSavedLo_entails_stackFrame800 (s0 : State) :
    let sp1 := s0.sp - 80#64
    ReallocSavedLo s0 sp1 ∗
    (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
     memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
    stackFrameAt sp1 720 ⊢ stackFrame s0 800 := by
  intro sp1; rw [stackFrame800_split s0]; unfold ReallocSavedLo
  exact sepConj_mono_left (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _))))))

theorem reallocSavedHi_entails_memRegions (s0 : State) (sp1 : BitVec 64) :
    ReallocSavedHi s0 sp1 ⊢
      memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
      memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8 := by
  unfold ReallocSavedHi
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))

/-- Shared epilogue (`+0x294..+0x2a4`): moves `x20` into `x0`, restores `x19..x22, x29, x30`,
    advances `sp` by `80` back to `s0.sp`, and returns to `s0.readReg64 .x30`. -/
theorem realloc_epilogue_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    {s0 s : State} {retVal : BitVec 64} {Rest : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x294#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx20 : s.readReg64 .x20 = retVal)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23) (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hcs : ReallocUntouchedCS s0 s) :
    let sp1 := s0.sp - 80#64
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗
       (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
        memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
       stackFrameAt sp1 720 ∗ Rest)
      (fun sf Pf => sf.mem = s.mem ∧ sf.brk = s.brk ∧ MallocngProcPreserved s sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = retVal ∧
        (Pf ⊢ stackFrame s0 800 ∗ Rest)) oom := by
  intro sp1; have _ := hb
  have hspAlign1 : (s0.sp - 80#64) &&& 15#64 = 0#64 := by revert hsp0; bv_robdd
  have hLoEq : ReallocSavedLo s0 (s0.sp - 80#64) =
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22)) := by
    unfold ReallocSavedLo
    rw [show s0.sp - 80#64 + 8#64 = s0.sp - 72#64 by bv_lin,
        show s0.sp - 80#64 + 16#64 = s0.sp - 64#64 by bv_lin,
        show s0.sp - 80#64 + 24#64 = s0.sp - 56#64 by bv_lin,
        show s0.sp - 80#64 + 32#64 = s0.sp - 48#64 by bv_lin,
        show s0.sp - 80#64 + 40#64 = s0.sp - 40#64 by bv_lin]
  conv => arg 4; dsimp only [sp1]; rw [hLoEq]
  wp_steps
  conv => arg 4; rw [← hLoEq]
  refine SepWP.done (by simp) (by simp [hrun])
    ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp, ?_, by simp, ?_⟩
  · obtain ⟨hx27, hx28, hv⟩ := hcs
    refine ⟨by simp, by simp, by simp, by simp, by simpa using hx23, by simpa using hx24,
      by simpa using hx25, by simpa using hx26, by simpa using hx27, by simpa using hx28,
      by simp, ?_⟩
    simpa [calleeSavedVRegs] using hv
  · rw [← sepConj_assoc _ (stackFrameAt (s0.sp - 80#64) 720) Rest,
        ← sepConj_assoc (ReallocSavedLo s0 (s0.sp - 80#64)) _ Rest]
    exact sepConj_mono_left (reallocSavedLo_entails_stackFrame800 s0)

/-! ## Stage 1 (`+0x03c..+0x1b8`): `get_meta`, `get_stride`, and `get_nominal_size` -/

def reallocReadPre (A : MallocngAddrs) (st : MallocngSt) (Rest : SepProp) : SepProp :=
  MallocngRoTablesAt A ∗ (A.ctx ↦ₛ st.ctx.toBytes) ∗
  ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Rest

def ReallocReadPres (s1 s2 : State) : Prop :=
  s2.mem = s1.mem ∧ s2.brk = s1.brk ∧ MallocngProcPreserved s1 s2 ∧
  s2.sp = s1.sp ∧ s2.spAligned = s1.spAligned ∧
  s2.readReg64 .x25 = s1.readReg64 .x25 ∧ s2.readReg64 .x26 = s1.readReg64 .x26 ∧
  ReallocUntouchedCS s1 s2

theorem reallocReadPres_trans {s1 s2 s3 : State}
    (h12 : ReallocReadPres s1 s2) (h23 : ReallocReadPres s2 s3) :
    ReallocReadPres s1 s3 := by
  obtain ⟨hm1, hb1, hp1, hsp1, hal1, h25_1, h26_1, h27_1, h28_1, hv1⟩ := h12
  obtain ⟨hm2, hb2, hp2, hsp2, hal2, h25_2, h26_2, h27_2, h28_2, hv2⟩ := h23
  refine ⟨hm2.trans hm1, hb2.trans hb1, ?_, hsp2.trans hsp1, hal2.trans hal1,
    h25_2.trans h25_1, h26_2.trans h26_1, h27_2.trans h27_1, h28_2.trans h28_1, hv2.trans hv1⟩
  unfold MallocngProcPreserved at hp1 hp2 ⊢
  simp only [hp2, hp1, and_self]

private theorem realloc_s1_hdr_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p newSize : BitVec 64} {oldSz effCost : Nat}
    {Rest : SepProp} {oom : State → SepProp}
    (hF : LiveUserBlockFacts st g idx p oldSz effCost)
    {s1 : State} (hpc : s1.pc = b + 0x3c#64) (hrun : s1.status = .Running)
    (hx19 : s1.readReg64 .x19 = p) (hx21 : s1.readReg64 .x21 = newSize) :
    let tot := (p.toNat - g.storage.toNat) / 16
    let r5 := min ((g.slotEnd idx).toNat - (p.toNat + oldSz)) 5
    let hdrB : BitVec 8 := BitVec.ofNat 8 ((r5 <<< 5) ||| idx)
    let P := reallocReadPre maddrs st Rest
    SepWP (blkPC_b14.rebase b (fun _ => none)) (b + 0x7c#64) s1 P
      (sepPost (fun s2 => ReallocReadPres s1 s2 ∧
        s2.readReg64 .x2 = hdrB.zeroExtend 64 ∧
        s2.readReg64 .x3 = (BitVec.ofNat 32 tot).zeroExtend 64 ∧
        s2.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s2.readReg64 .x19 = p ∧ s2.readReg64 .x21 = newSize) P) oom := by
  intro tot r5 hdrB P
  have _ := hb
  have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
  have ⟨hHdrIdx, _, _, _⟩ := hdrByte_extract r5 idx (Nat.min_le_right _ _) hIdx31
  by_cases hShort : tot ≤ 0xffff
  · conv => arg 4; dsimp only [P, reallocReadPre]; rw [hF.focus_hdr_short hShort]
    wp_steps
    conv => arg 4; rw [← hF.focus_hdr_short hShort]
    refine SepWP.done rfl (by simp [hrun])
      ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
          by simp, by simp, by simp [calleeSavedVRegs]⟩,
        ?_, ?_, ?_, by simp [hx19], by simp [hx21]⟩, Entails.refl _⟩
    · simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]; rfl
    · simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]
      change BitVec.zeroExtend 64 (BitVec.ofNat 16 tot) = (BitVec.ofNat 32 tot).zeroExtend 64; bv_omega
    · simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]
      exact hdrB_mask64 hdrB hHdrIdx
  · have hLong : 0xffff < tot := by omega
    have hTotLt27 := hF.totalOff_lt_27
    have hSleF : (BitVec.ofNat 32 tot).sle 0xffff#32 = false := by
      rw [show (0xffff#32 : BitVec 32) = BitVec.ofNat 32 0xffff from rfl,
        bv32_sle_iff_of_lt31 (by omega) (by omega)]
      simp [show ¬ (tot ≤ 0xffff) by omega]
    conv => arg 4; dsimp only [P, reallocReadPre]; rw [hF.focus_hdr_long hLong]
    wp_steps
    conv => arg 4; rw [← hF.focus_hdr_long hLong]
    refine SepWP.done rfl (by simp [hrun])
      ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
          by simp, by simp, by simp [calleeSavedVRegs]⟩,
        ?_, ?_, ?_, by simp [hx19], by simp [hx21]⟩, Entails.refl _⟩
    · simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        Reg.gpr.injEq, BitVec.reduceEq, reduceIte]; rfl
    · simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        Reg.gpr.injEq, BitVec.reduceEq, reduceIte]; rfl
    · simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        Reg.gpr.injEq, BitVec.reduceEq, reduceIte]
      exact hdrB_mask64 hdrB hHdrIdx

private theorem realloc_s1_meta_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p newSize : BitVec 64} {oldSz effCost : Nat}
    {hdrB : BitVec 8} {Rest : SepProp} {oom : State → SepProp}
    (hF : LiveUserBlockFacts st g idx p oldSz effCost)
    {s2 : State} (hpc : s2.pc = b + 0x7c#64) (hrun : s2.status = .Running)
    (hx2 : s2.readReg64 .x2 = hdrB.zeroExtend 64)
    (hx3 : s2.readReg64 .x3 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64)
    (hx4 : s2.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx19 : s2.readReg64 .x19 = p) (hx21 : s2.readReg64 .x21 = newSize) :
    let P := reallocReadPre maddrs st Rest
    SepWP (blkPC_b14.rebase b (fun _ => none)) (b + 0xe8#64) s2 P
      (sepPost (fun s3 => ReallocReadPres s2 s3 ∧
        s3.readReg64 .x0 = g.mem ∧
        s3.readReg64 .x2 = hdrB.zeroExtend 64 ∧
        s3.readReg64 .x3 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64 ∧
        s3.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s3.readReg64 .x5 = (g.packedWord.extractLsb' 0 8).zeroExtend 64 ∧
        s3.readReg64 .x19 = p ∧ s3.readReg64 .x21 = newSize ∧
        s3.readReg64 .x22 = g.metaPtr) P) oom := by
  intro P
  have _ := hb
  have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
  have hMemAddr : p + (-16#64 - ((BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16) <<< 4).signExtend 64)) = g.mem :=
    group_mem_addr_of_totalOff hF.totalOff_lt_27
      (by have := hF.p_add_n_48; rw [← hF.p_eq_storage_off]; omega) hF.p_eq_storage_off
  have hMemAddrU : p + (BitVec.ofNat 64 (2 ^ 64 - 16) -
      ((BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16) <<< 4).signExtend 64)) = g.mem := hMemAddr
  have ⟨hByte32, _⟩ := packedWord_byte0_and31 g hF.last_le_31
  have hByteMask := hdrB_mask64 (g.packedWord.extractLsb' 0 8) hByte32
  have ⟨hAv1, hAv2⟩ := mask_ushiftRight_bit0_false g.availMask hIdx31 hF.avail_bit_false
  have ⟨hFr1, hFr2⟩ := mask_ushiftRight_bit0_false g.freedMask hIdx31 hF.freed_bit_false
  obtain ⟨ma, _, hMaBase, hFocusMa⟩ := hF.meta_page_base
  have hMaBase' : g.metaPtr &&& -4096#64 = ma.base := hMaBase
  obtain ⟨ctxRest, hCtxSplit⟩ := ctx_toBytes_split_secret maddrs.ctx st.ctx
  have hPageCtx := pageOf_add_lo12Of maddrs.ctx
  conv => arg 4; dsimp only [P, reallocReadPre]; rw [hF.focus_group_mem]
  wp_step; wp_step; wp_step; wp_step; wp_step
  conv => arg 4; rw [← hF.focus_group_mem, hF.focus_meta, pointsTo64_split_lo8 (g.metaPtr + 32#64) g.packedWord]
  wp_steps
  wp_if hgt
  · exfalso; have := hF.last_le_31; have := hF.idx_le_last
    rw [bv32_slt_iff_of_lt31 (by omega) (by omega), decide_eq_true_eq] at hgt; omega
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    conv => arg 4; rw [← pointsTo64_split_lo8 (g.metaPtr + 32#64) g.packedWord, ← hF.focus_meta, hFocusMa, hCtxSplit]
    wp_steps
    conv => arg 4; rw [← hCtxSplit, ← hFocusMa]
    refine SepWP.done rfl (by simp [hrun])
      ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
          by simp, by simp, by simp [calleeSavedVRegs]⟩,
        by simp, by simp [hx2], by simp [hx3], by simp [hx4], by simp,
        by simp [hx19], by simp [hx21], by simp⟩, Entails.refl _⟩

set_option maxHeartbeats 400000 in
private theorem realloc_s1_sc_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p newSize : BitVec 64} {oldSz effCost : Nat}
    {hdrB : BitVec 8} {Rest : SepProp} {oom : State → SepProp}
    (hF : LiveUserBlockFacts st g idx p oldSz effCost)
    {s3 : State} (hpc : s3.pc = b + 0xe8#64) (hrun : s3.status = .Running)
    (hx0 : s3.readReg64 .x0 = g.mem)
    (hx2 : s3.readReg64 .x2 = hdrB.zeroExtend 64)
    (hx3 : s3.readReg64 .x3 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64)
    (hx4 : s3.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx5 : s3.readReg64 .x5 = (g.packedWord.extractLsb' 0 8).zeroExtend 64)
    (hx19 : s3.readReg64 .x19 = p) (hx21 : s3.readReg64 .x21 = newSize)
    (hx22 : s3.readReg64 .x22 = g.metaPtr) :
    let P := reallocReadPre maddrs st Rest
    SepWP (blkPC_b14.rebase b (fun _ => none)) (b + 0x11c#64) s3 P
      (sepPost (fun s4 => ReallocReadPres s3 s4 ∧
        s4.readReg64 .x0 = g.mem ∧
        s4.readReg64 .x2 = hdrB.zeroExtend 64 ∧
        s4.readReg64 .x3 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64 ∧
        s4.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s4.readReg64 .x5 = (g.packedWord.extractLsb' 0 8).zeroExtend 64 ∧
        s4.readReg64 .x6 = BitVec.ofNat 64 g.sc ∧
        s4.readReg64 .x7 = (g.packedWord.extractLsb' 0 16).zeroExtend 64 ∧
        s4.readReg64 .x19 = p ∧ s4.readReg64 .x21 = newSize ∧
        s4.readReg64 .x22 = g.metaPtr) P) oom := by
  intro P
  have _ := hb
  have hSc64 : g.sc < 64 := by rcases hF.sc_cases with h | h <;> omega
  have hUbfxSc : (((g.packedWord.extractLsb' 0 16).zeroExtend 64 >>> 6) &&& 0x3f#64) = BitVec.ofNat 64 g.sc := by
    have hL := bv64_ult_of_lt (by omega) (Nat.lt_succ_of_le hF.last_le_31)
    have hS := bv64_ult_of_lt (by omega) hSc64
    have hM := bv64_ult_of_lt (k := 2 ^ 52) (by omega) hF.maplen_lt_52
    dsimp only [GroupDesc.packedWord]; revert hL hS hM; bv_robdd
  have hPageSc := pageOf_add_lo12Of maddrs.sizeClasses
  conv => arg 4; dsimp only [P, reallocReadPre]; rw [hF.focus_meta, pointsTo64_split_lo16 (g.metaPtr + 32#64) g.packedWord]
  wp_step; wp_step; wp_step; wp_step
  conv => arg 4; rw [← pointsTo64_split_lo16 (g.metaPtr + 32#64) g.packedWord, ← hF.focus_meta]
  rcases hF.sc_cases with hsc48 | hsc63
  · wp_if hhi
    · exfalso
      rw [show (BitVec.ofNat 64 g.sc).truncate 32 = BitVec.ofNat 32 g.sc by bv_omega,
        BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hhi
      change 47 < g.sc % 4294967296 at hhi; omega
    · obtain ⟨roRest, hRoSplit⟩ := split_sizeClass_roTablesAt maddrs hsc48
        ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Rest)
      have hOffSc := sxtw_lsl1_sc hsc48
      have hSbfmSc := sxtw_sbfm_sc hsc48
      have ⟨_, huMax, _, _⟩ := sizeClass_bounds hsc48
      have ⟨hLow, hHigh⟩ := hF.sc_lt_48_off hsc48
      have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
      have hMulB1 : idx * sizeClass g.sc ≤ 31 * 8191 := Nat.mul_le_mul hIdx31 huMax
      have hMulB2 : (idx + 1) * sizeClass g.sc ≤ 32 * 8191 := Nat.mul_le_mul (by omega) huMax
      have hTot27 := hF.totalOff_lt_27
      conv => arg 4; dsimp only [P, reallocReadPre]; rw [hRoSplit]
      wp_steps
      wp_if hlt
      · exfalso
        rw [madd32_idx_sc (by omega), bv32_slt_iff_of_lt31 (by omega) (by omega), decide_eq_true_eq] at hlt; omega
      · wp_steps
        wp_if hge
        · exfalso
          rw [add32_sc_madd (by omega), bv32_sle_iff_of_lt31 (by omega) (by omega), decide_eq_true_eq] at hge; omega
        · conv => arg 4; rw [← hRoSplit]
          refine SepWP.done rfl (by simp [hrun])
            ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
                by simp, by simp, by simp [calleeSavedVRegs]⟩,
              by simp [hx0], by simp [hx2], by simp [hx3], by simp [hx4], by simp [hx5],
              by simp, by simp, by simp [hx19], by simp [hx21], by simp [hx22]⟩, Entails.refl _⟩
  · have hMask63 := packedWord_sc63_mask g hF.last_le_31 hsc63 hF.maplen_lt_52
    wp_if hhi
    · wp_steps
      refine SepWP.done rfl (by simp [hrun])
        ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
            by simp, by simp, by simp [calleeSavedVRegs]⟩,
          by simp [hx0], by simp [hx2], by simp [hx3], by simp [hx4], by simp [hx5],
          by simp [hsc63], by simp, by simp [hx19], by simp [hx21], by simp [hx22]⟩, Entails.refl _⟩
    · exfalso; rw [hsc63] at hhi; exact hhi rfl

set_option maxHeartbeats 400000 in
private theorem realloc_s1_stride_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p newSize : BitVec 64} {oldSz effCost : Nat}
    {hdrB : BitVec 8} {Rest : SepProp} {oom : State → SepProp}
    (hF : LiveUserBlockFacts st g idx p oldSz effCost)
    {s4 : State} (hpc : s4.pc = b + 0x11c#64) (hrun : s4.status = .Running)
    (hx0 : s4.readReg64 .x0 = g.mem)
    (hx2 : s4.readReg64 .x2 = hdrB.zeroExtend 64)
    (hx3 : s4.readReg64 .x3 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64)
    (hx4 : s4.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx5 : s4.readReg64 .x5 = (g.packedWord.extractLsb' 0 8).zeroExtend 64)
    (hx6 : s4.readReg64 .x6 = BitVec.ofNat 64 g.sc)
    (hx7 : s4.readReg64 .x7 = (g.packedWord.extractLsb' 0 16).zeroExtend 64)
    (hx19 : s4.readReg64 .x19 = p) (hx21 : s4.readReg64 .x21 = newSize)
    (hx22 : s4.readReg64 .x22 = g.metaPtr) :
    let P := reallocReadPre maddrs st Rest
    SepWP (blkPC_b14.rebase b (fun _ => none)) (b + 0x158#64) s4 P
      (sepPost (fun s5 => ReallocReadPres s4 s5 ∧
        s5.readReg64 .x0 = g.mem ∧
        s5.readReg64 .x1 = g.packedWord ∧
        s5.readReg64 .x2 = hdrB.zeroExtend 64 ∧
        s5.readReg64 .x3 = BitVec.ofNat 64 g.stride ∧
        s5.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s5.readReg64 .x6 = BitVec.ofNat 64 g.sc ∧
        s5.readReg64 .x7 = (g.packedWord.extractLsb' 0 16).zeroExtend 64 ∧
        s5.readReg64 .x19 = p ∧ s5.readReg64 .x21 = newSize ∧
        s5.readReg64 .x22 = g.metaPtr) P) oom := by
  intro P
  have _ := hb
  have hSc64 : g.sc < 64 := by rcases hF.sc_cases with h | h <;> omega
  have hMapMask := packedWord_maplen_mask g hF.last_le_31 hSc64 hF.maplen_bytes_48
  have ⟨_, hByte64⟩ := packedWord_byte0_and31 g hF.last_le_31
  have hPageSc := pageOf_add_lo12Of maddrs.sizeClasses
  conv => arg 4; dsimp only [P, reallocReadPre]; rw [hF.focus_meta]
  wp_step; wp_step; wp_step
  conv => arg 4; rw [← hF.focus_meta]
  by_cases hMap0 : g.maplen = 0
  · have ⟨hsc48, _⟩ := hF.maplen_zero_sc hMap0
    have hStride : g.stride = 16 * sizeClass g.sc := by simp [GroupDesc.stride, slotStride, hMap0]
    have hOffSc := sxtw_lsl1_sc hsc48
    have hSbfmSc := sxtw_sbfm_sc hsc48
    obtain ⟨roRest, hRoSplit⟩ := split_sizeClass_roTablesAt maddrs hsc48
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Rest)
    wp_if heq
    · conv => arg 4; dsimp only [P, reallocReadPre]; rw [hRoSplit]
      wp_steps
      conv => arg 4; rw [← hRoSplit]
      refine SepWP.done rfl (by simp [hrun])
        ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
            by simp, by simp, by simp [calleeSavedVRegs]⟩,
          by simp [hx0], by simp, by simp [hx2], ?_, by simp [hx4], by simp [hx6], by simp [hx7],
          by simp [hx19], by simp [hx21], by simp [hx22]⟩, Entails.refl _⟩
      simp [hStride, sc16_ubfiz_shl4 hsc48]
    · exfalso; rw [hMap0] at heq; exact heq rfl
  · have hMapPos : 0 < g.maplen := Nat.pos_of_ne_zero hMap0
    have hMap48 := hF.maplen_bytes_48; have hTot27 := hF.totalOff_lt_27; have hMapOff := hF.maplen_pos_off hMapPos
    wp_if heq
    · exfalso
      have h0 : (BitVec.ofNat 64 (g.maplen * 4096)).toNat = 0 := by rw [heq]; rfl
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
    · wp_steps
      wp_if hlo
      · exfalso; rw [maplen_shr4_sub1_ult_false hMapPos hMap48 hTot27 hMapOff] at hlo; cases hlo
      · wp_steps
        by_cases hLast0 : g.lastIdx = 0
        · have hStride : g.stride = g.maplen * 4096 - 16 := by simp [GroupDesc.stride, hLast0, hMapPos]
          wp_if hlastEq
          · refine SepWP.done rfl (by simp [hrun])
              ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
                  by simp, by simp, by simp [calleeSavedVRegs]⟩,
                by simp [hx0], by simp, by simp [hx2], ?_, by simp [hx4], by simp [hx6], by simp [hx7],
                by simp [hx19], by simp [hx21], by simp [hx22]⟩, Entails.refl _⟩
            simp [hStride]; bv_omega
          · exfalso; rw [hLast0] at hlastEq; exact hlastEq rfl
        · have hsc48 : g.sc < 48 := by
            rcases hF.sc_cases with h | h; · exact h
            · exact absurd (hF.sc_63_props h).1 hLast0
          have hStride : g.stride = 16 * sizeClass g.sc := by simp [GroupDesc.stride, slotStride, hLast0]
          have hOffSc := sxtw_lsl1_sc hsc48
          have hSbfmSc := sxtw_sbfm_sc hsc48
          obtain ⟨roRest, hRoSplit⟩ := split_sizeClass_roTablesAt maddrs hsc48
            ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Rest)
          wp_if hlastEq
          · exfalso; have := hF.last_le_31
            have h0 : (BitVec.ofNat 64 g.lastIdx).toNat = 0 := by rw [hlastEq]; rfl
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
          · conv => arg 4; dsimp only [P, reallocReadPre]; rw [hRoSplit]
            wp_steps
            conv => arg 4; rw [← hRoSplit]
            refine SepWP.done rfl (by simp [hrun])
              ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
                  by simp, by simp, by simp [calleeSavedVRegs]⟩,
                by simp [hx0], by simp, by simp [hx2], ?_, by simp [hx4], by simp [hx6], by simp [hx7],
                by simp [hx19], by simp [hx21], by simp [hx22]⟩, Entails.refl _⟩
            simp [hStride, sc16_ubfiz_shl4 hsc48]

private theorem realloc_s1_canaries_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p newSize : BitVec 64} {oldSz effCost : Nat}
    {Rest : SepProp} {oom : State → SepProp}
    (hF : LiveUserBlockFacts st g idx p oldSz effCost)
    {s6 : State} (hpc : s6.pc = b + 0x198#64) (hrun : s6.status = .Running)
    (hx0 : s6.readReg64 .x0 = g.mem) (hx1 : s6.readReg64 .x1 = g.packedWord)
    (hx2 : s6.readReg64 .x2 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - (p.toNat + oldSz)))
    (hx4 : s6.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx5 : s6.readReg64 .x5 = g.slotEnd idx) (hx6 : s6.readReg64 .x6 = BitVec.ofNat 64 g.sc)
    (hx7 : s6.readReg64 .x7 = (g.packedWord.extractLsb' 0 16).zeroExtend 64)
    (hx8 : s6.readReg64 .x8 = BitVec.ofNat 64 g.stride - 4#64)
    (hx19 : s6.readReg64 .x19 = p) (hx20 : s6.readReg64 .x20 = g.slotStart idx)
    (hx21 : s6.readReg64 .x21 = newSize) (hx22 : s6.readReg64 .x22 = g.metaPtr) :
    let P := reallocReadPre maddrs st Rest
    SepWP (blkPC_b14.rebase b (fun _ => none)) (b + 0x1b8#64) s6 P
      (sepPost (fun s7 => ReallocReadPres s6 s7 ∧
        s7.readReg64 .x0 = g.mem ∧ s7.readReg64 .x1 = g.packedWord ∧
        s7.readReg64 .x3 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat) ∧
        s7.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s7.readReg64 .x5 = g.slotEnd idx ∧ s7.readReg64 .x6 = BitVec.ofNat 64 g.sc ∧
        s7.readReg64 .x7 = (g.packedWord.extractLsb' 0 16).zeroExtend 64 ∧
        s7.readReg64 .x19 = p ∧ s7.readReg64 .x20 = g.slotStart idx ∧
        s7.readReg64 .x21 = newSize ∧ s7.readReg64 .x22 = g.metaPtr ∧
        s7.readReg64 .x23 = p + BitVec.ofNat 64 oldSz ∧ s7.readReg64 .x24 = 0#64) P) oom := by
  intro P
  have _ := hb
  have hEnd48 : (g.slotEnd idx).toNat ≤ 2 ^ 48 := hF.stride_bounds.2.2.2.2.2
  have hP48 := hF.p_add_n_48
  have hPLeEnd := hF.p_add_n_le_end
  have hSlotEnd : g.slotStart idx + (BitVec.ofNat 64 g.stride - 4#64) = g.slotEnd idx := by
    have ⟨hStr16, _, _, _, hEndNat, _⟩ := hF.stride_bounds
    have hStrLe : g.stride ≤ (idx + 1) * g.stride := Nat.le_mul_of_pos_left _ (by omega)
    have hSub4 : BitVec.ofNat 64 g.stride - 4#64 = BitVec.ofNat 64 (g.stride - 4) := by
      apply BitVec.eq_of_toNat_eq
      have hLe : (4#64 : BitVec 64) ≤ BitVec.ofNat 64 g.stride := by
        simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
      rw [BitVec.toNat_sub_of_le hLe]; simp only [BitVec.toNat_ofNat]; omega
    unfold GroupDesc.slotEnd; rw [hSub4]
  have hEndSubP : g.slotEnd idx - p = BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega)), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hEndSubRes :
      g.slotEnd idx - BitVec.ofNat 64 ((g.slotEnd idx).toNat - (p.toNat + oldSz)) =
        p + BitVec.ofNat 64 oldSz := by
    apply BitVec.eq_of_toNat_eq
    have hLe : BitVec.ofNat 64 ((g.slotEnd idx).toNat - (p.toNat + oldSz)) ≤ g.slotEnd idx := by
      rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [BitVec.toNat_sub_of_le hLe, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  wp_steps
  wp_if hlo
  · exfalso; try rw [hEndSubP] at hlo
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlo; omega
  · wp_step
    conv => arg 4; dsimp only [P, reallocReadPre]; rw [hF.focus_end_req]
    wp_step; wp_step
    conv => arg 4; rw [← hF.focus_end_req, hF.focus_slot_end]
    wp_steps
    conv => arg 4; rw [← hF.focus_slot_end]
    refine SepWP.done rfl (by simp [hrun])
      ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
          by simp, by simp, by simp [calleeSavedVRegs]⟩,
        by simp [hx0], by simp [hx1], by simp, by simp [hx4], by simp [hx5],
        by simp [hx6], by simp [hx7], by simp [hx19], by simp [hx20], by simp [hx21],
        by simp [hx22], by simp, by simp⟩, Entails.refl _⟩

set_option maxHeartbeats 400000 in
private theorem realloc_s1_nom_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p newSize : BitVec 64} {oldSz effCost : Nat}
    {Rest : SepProp} {oom : State → SepProp}
    (hF : LiveUserBlockFacts st g idx p oldSz effCost)
    {s5 : State} (hpc : s5.pc = b + 0x158#64) (hrun : s5.status = .Running)
    (hx0 : s5.readReg64 .x0 = g.mem) (hx1 : s5.readReg64 .x1 = g.packedWord)
    (hx2 : s5.readReg64 .x2 =
      (BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (p.toNat + oldSz)) 5 <<< 5) ||| idx)).zeroExtend 64)
    (hx3 : s5.readReg64 .x3 = BitVec.ofNat 64 g.stride)
    (hx4 : s5.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx6 : s5.readReg64 .x6 = BitVec.ofNat 64 g.sc)
    (hx7 : s5.readReg64 .x7 = (g.packedWord.extractLsb' 0 16).zeroExtend 64)
    (hx19 : s5.readReg64 .x19 = p) (hx21 : s5.readReg64 .x21 = newSize)
    (hx22 : s5.readReg64 .x22 = g.metaPtr) :
    let P := reallocReadPre maddrs st Rest
    SepWP (blkPC_b14.rebase b (fun _ => none)) (b + 0x1b8#64) s5 P
      (sepPost (fun s7 => ReallocReadPres s5 s7 ∧
        s7.readReg64 .x0 = g.mem ∧ s7.readReg64 .x1 = g.packedWord ∧
        s7.readReg64 .x3 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat) ∧
        s7.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s7.readReg64 .x5 = g.slotEnd idx ∧ s7.readReg64 .x6 = BitVec.ofNat 64 g.sc ∧
        s7.readReg64 .x7 = (g.packedWord.extractLsb' 0 16).zeroExtend 64 ∧
        s7.readReg64 .x19 = p ∧ s7.readReg64 .x20 = g.slotStart idx ∧
        s7.readReg64 .x21 = newSize ∧ s7.readReg64 .x22 = g.metaPtr ∧
        s7.readReg64 .x23 = p + BitVec.ofNat 64 oldSz ∧ s7.readReg64 .x24 = 0#64) P) oom := by
  intro P
  have _ := hb
  let res := (g.slotEnd idx).toNat - (p.toNat + oldSz)
  let r5 := min res 5
  have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
  have ⟨_, hHdrShr, hHdrUbfx, hHdrUle⟩ := hdrByte_extract r5 idx (Nat.min_le_right _ _) hIdx31
  have hIdxMask : (BitVec.ofNat 32 idx).zeroExtend 64 &&& 0xff#64 = BitVec.ofNat 64 idx := by
    have h8 : ∀ b8 : BitVec 8, (b8.zeroExtend 32).zeroExtend 64 &&& 0xff#64 = b8.zeroExtend 64 := fun _ => by bv_bits
    rw [show BitVec.ofNat 32 idx = (BitVec.ofNat 8 idx).zeroExtend 32 by bv_omega, h8]; bv_omega
  have hSlotStart : (g.mem + 16#64) + BitVec.ofNat 64 idx * BitVec.ofNat 64 g.stride = g.slotStart idx := by
    unfold GroupDesc.slotStart GroupDesc.storage; rw [← BitVec.ofNat_mul]
  have hSlotEnd : g.slotStart idx + (BitVec.ofNat 64 g.stride - 4#64) = g.slotEnd idx := by
    have ⟨hStr16, _, _, _, hEndNat, hEnd48⟩ := hF.stride_bounds
    have hStrLe : g.stride ≤ (idx + 1) * g.stride := Nat.le_mul_of_pos_left _ (by omega)
    have hSub4 : BitVec.ofNat 64 g.stride - 4#64 = BitVec.ofNat 64 (g.stride - 4) := by
      apply BitVec.eq_of_toNat_eq
      have hLe : (4#64 : BitVec 64) ≤ BitVec.ofNat 64 g.stride := by
        simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
      rw [BitVec.toNat_sub_of_le hLe]; simp only [BitVec.toNat_ofNat]; omega
    unfold GroupDesc.slotEnd; rw [hSub4]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  have ⟨h9f1, h9f2, h9f3, _⟩ := hdr8_ule_0x9f (BitVec.ofNat 8 ((r5 <<< 5) ||| idx))
  by_cases hLt5 : res < 5
  · have hr5Eq : r5 = res := Nat.min_eq_left (by omega)
    wp_if hls
    · refine SepWP.mono (realloc_s1_canaries_ok (newSize := newSize) hb hF rfl (by simp [hrun])
        (by simp [hx0]) (by simp [hx1])
        (by simp only [wp_norm, arm64_norm]; dsimp only [r5, res] at hHdrUbfx hr5Eq; rw [hr5Eq]; simpa [hr5Eq] using hHdrUbfx)
        (by simp [hx4]) (by simp) (by simp [hx6]) (by simp [hx7]) (by simp)
        (by simp [hx19]) (by simp) (by simpa using hx21) (by simp [hx22])) ?_
      intro s7 _ _ _ ⟨⟨hP67, hR⟩, hE⟩
      exact ⟨⟨reallocReadPres_trans
        ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
          by simp, by simp, by simp [calleeSavedVRegs]⟩ hP67, hR⟩, hE⟩
    · exfalso; dsimp only [r5, res] at hHdrUle h9f1 h9f2 h9f3
      try rw [h9f3] at hls; try rw [h9f2] at hls; try rw [h9f1] at hls
      exact hls (hHdrUle.mpr (by omega))
  · have hGe5 : 5 ≤ res := by omega
    have hr5Eq : r5 = 5 := Nat.min_eq_right hGe5
    have hRes31 := hF.reserved_lt_31
    wp_if hls
    · exfalso; dsimp only [r5, res] at hHdrUle h9f1 h9f2 h9f3
      try rw [h9f3] at hls; try rw [h9f2] at hls; try rw [h9f1] at hls
      exact absurd (hHdrUle.mp hls) (by omega)
    · have hw9Eq : (((BitVec.ofNat 8 ((r5 <<< 5) ||| idx)).zeroExtend 64).truncate 32) >>> 5 = 5#32 := by
        have hTr : ∀ b8 : BitVec 8, (b8.zeroExtend 64).truncate 32 = b8.zeroExtend 32 := fun _ => by bv_bits
        dsimp only [r5, res] at hHdrShr hr5Eq
        rw [hTr, hHdrShr, hr5Eq]
      wp_step; wp_step
      conv => arg 4; dsimp only [P, reallocReadPre]; rw [hF.focus_trailer5 hGe5]
      wp_steps
      have hZx : (BitVec.ofNat 32 res).zeroExtend 64 = BitVec.ofNat 64 res := by
        dsimp only [res]; generalize (g.slotEnd idx).toNat - (p.toNat + oldSz) = r at hRes31 ⊢; bv_omega
      wp_if hls4
      · exfalso; dsimp only [res] at hZx
        rw [hZx, BitVec.ule, decide_eq_true_eq] at hls4; simp only [BitVec.toNat_ofNat] at hls4; omega
      · wp_step; wp_step
        conv => arg 4; rw [← hF.focus_trailer5 hGe5]
        refine SepWP.mono (realloc_s1_canaries_ok (newSize := newSize) hb hF rfl (by simp [hrun])
          (by simp [hx0]) (by simp [hx1])
          (by simp only [wp_norm, arm64_norm]; exact hZx)
          (by simp [hx4]) (by simp) (by simp [hx6]) (by simp [hx7]) (by simp)
          (by simp [hx19]) (by simp) (by simpa using hx21) (by simp [hx22])) ?_
        intro s7 _ _ _ ⟨⟨hP67, hR⟩, hE⟩
        exact ⟨⟨reallocReadPres_trans
          ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
            by simp, by simp, by simp [calleeSavedVRegs]⟩ hP67, hR⟩, hE⟩

/-- Stage 1 (`+0x03c..+0x1b8`): executes `get_meta(p)`, `get_stride(g)`, and
    `get_nominal_size(p, end)` without modifying memory, preserving arbitrary `Rest : SepProp`. -/
theorem realloc_stage1_read_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p newSize : BitVec 64} {oldSz effCost : Nat}
    {Rest : SepProp} {oom : State → SepProp}
    (hF : LiveUserBlockFacts st g idx p oldSz effCost)
    {s1 : State} (hpc : s1.pc = b + 0x3c#64) (hrun : s1.status = .Running)
    (hx19 : s1.readReg64 .x19 = p) (hx21 : s1.readReg64 .x21 = newSize) :
    let P := reallocReadPre maddrs st Rest
    SepWP (blkPC_b14.rebase b (fun _ => none)) (b + 0x1b8#64) s1 P
      (sepPost (fun s7 => ReallocReadPres s1 s7 ∧
        s7.readReg64 .x0 = g.mem ∧ s7.readReg64 .x1 = g.packedWord ∧
        s7.readReg64 .x3 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat) ∧
        s7.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s7.readReg64 .x5 = g.slotEnd idx ∧ s7.readReg64 .x6 = BitVec.ofNat 64 g.sc ∧
        s7.readReg64 .x7 = (g.packedWord.extractLsb' 0 16).zeroExtend 64 ∧
        s7.readReg64 .x19 = p ∧ s7.readReg64 .x20 = g.slotStart idx ∧
        s7.readReg64 .x21 = newSize ∧ s7.readReg64 .x22 = g.metaPtr ∧
        s7.readReg64 .x23 = p + BitVec.ofNat 64 oldSz ∧ s7.readReg64 .x24 = 0#64) P) oom := by
  intro P
  apply SepWP.seq (realloc_s1_hdr_ok hb hF hpc hrun hx19 hx21)
  intro s2 P2 hpc2 hrun2 ⟨⟨hP12, hx2_2, hx3_2, hx4_2, hx19_2, hx21_2⟩, hEnt2⟩
  refine SepWP.weaken_pre hEnt2 ?_
  apply SepWP.seq (realloc_s1_meta_ok hb hF hpc2 hrun2 hx2_2 hx3_2 hx4_2 hx19_2 hx21_2)
  intro s3 P3 hpc3 hrun3 ⟨⟨hP23, hx0_3, hx2_3, hx3_3, hx4_3, hx5_3, hx19_3, hx21_3, hx22_3⟩, hEnt3⟩
  refine SepWP.weaken_pre hEnt3 ?_
  apply SepWP.seq (realloc_s1_sc_ok hb hF hpc3 hrun3 hx0_3 hx2_3 hx3_3 hx4_3 hx5_3 hx19_3 hx21_3 hx22_3)
  intro s4 P4 hpc4 hrun4 ⟨⟨hP34, hx0_4, hx2_4, hx3_4, hx4_4, hx5_4, hx6_4, hx7_4, hx19_4, hx21_4, hx22_4⟩, hEnt4⟩
  refine SepWP.weaken_pre hEnt4 ?_
  apply SepWP.seq (realloc_s1_stride_ok hb hF hpc4 hrun4 hx0_4 hx2_4 hx3_4 hx4_4 hx5_4 hx6_4 hx7_4 hx19_4 hx21_4 hx22_4)
  intro s5 P5 hpc5 hrun5 ⟨⟨hP45, hx0_5, hx1_5, hx2_5, hx3_5, hx4_5, hx6_5, hx7_5, hx19_5, hx21_5, hx22_5⟩, hEnt5⟩
  refine SepWP.weaken_pre hEnt5 ?_
  refine SepWP.mono (realloc_s1_nom_ok hb hF hpc5 hrun5 hx0_5 hx1_5 hx2_5 hx3_5 hx4_5 hx6_5 hx7_5 hx19_5 hx21_5 hx22_5) ?_
  intro s7 _ _ _ ⟨⟨hP57, hR⟩, hE⟩
  exact ⟨⟨reallocReadPres_trans hP12 (reallocReadPres_trans hP23 (reallocReadPres_trans hP34
    (reallocReadPres_trans hP45 hP57))), hR⟩, hE⟩

end VerifiedLibraries.Mallocng.Proofs
