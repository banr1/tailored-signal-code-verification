/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAlignedHelpers2
public import VerifiedLibraries.Mallocng.Proofs.GetMetaHelpers
public import VerifiedLibraries.Mallocng.Proofs.PlacedLeavesRuntimeProof
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Placed `aligned_alloc` Stage 1

Cross-block `__libc_malloc_impl` lifts and `ENOMEM` overflow contract (`blk09`), composed
`get_meta(p)` and `get_stride(g)` verification (`+0x068` to `+0x1b4` in `blk12`), and sub-word
`ByteMap`/stack helper rules for `aligned_alloc`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Cross-Block `__libc_malloc_impl` Lifts and `ENOMEM` Overflow Spec (`blk09`) -/

theorem alignedProcPreserved_trans {s0 s1 s2 : State}
    (h01 : MallocngProcPreserved s0 s1) (h12 : MallocngProcPreserved s1 s2) :
    MallocngProcPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

namespace AlignedStage1
theorem mallocngMappedDelta_of_perm_eq {k B : Nat} {m0 m0' mf mf' : Memory}
    (h0 : ∀ a, m0'.perm a = m0.perm a) (hf : ∀ a, mf'.perm a = mf.perm a)
    (h : MallocngMappedDelta k B m0 mf) : MallocngMappedDelta k B m0' mf' := by
  obtain ⟨ivs, hLen, hSum, hCov⟩ := h
  exact ⟨ivs, hLen, hSum, fun a hm => by rw [h0 a]; exact hCov a (by rwa [← hf a])⟩

theorem mallocngNoOrphanMappings_of_perm_eq {ivs0 ivsf : List (BitVec 64 × Nat)}
    {m0 m0' mf mf' : Memory} (h0 : ∀ a, m0'.perm a = m0.perm a) (hf : ∀ a, mf'.perm a = mf.perm a)
    (h : MallocngNoOrphanMappings ivs0 ivsf m0 mf) : MallocngNoOrphanMappings ivs0 ivsf m0' mf' :=
  fun a hm hOr => h a (by rwa [← hf a]) (by rwa [← h0 a])
end AlignedStage1
export AlignedStage1 (mallocngMappedDelta_of_perm_eq mallocngNoOrphanMappings_of_perm_eq)

theorem mallocngOomCond_of_perm_eq {svc : State → State} {req peak : Nat} {s0 s1 sf : State}
    (hFs : s1.fs = s0.fs) (hTr : s1.trace = s0.trace) (hSig : s1.sigActions = s0.sigActions)
    (hPerm : ∀ a, s0.mem.perm a = s1.mem.perm a) (h : MallocngOomCond svc req peak s1 sf) :
    MallocngOomCond svc req peak s0 sf :=
  ⟨h.1.trans hFs, h.2.1.trans hTr, h.2.2.1.trans hSig,
   mallocngMappedDelta_of_perm_eq hPerm (fun _ => rfl) h.2.2.2.1, h.2.2.2.2⟩

theorem mallocngTightOomCond_of_perm_eq {svc : State → State} {req peak : Nat} {s0 s1 sf : State}
    (hFs : s1.fs = s0.fs) (hTr : s1.trace = s0.trace) (hSig : s1.sigActions = s0.sigActions)
    (hPerm : ∀ a, s0.mem.perm a = s1.mem.perm a) (h : MallocngTightOomCond svc req peak s1 sf) :
    MallocngTightOomCond svc req peak s0 sf :=
  MallocngTightOomCond.of_pre_perm hFs hTr hSig (funext fun a => (hPerm a).symm) h

/-- Lift `hMalloc : LibcMallocImplPlaced24Stmt` (`blk09`) to any hook-free caller program `P`. -/
theorem placed_libcMallocImpl24_ok [MallocngMultiPlacement] {P : Program}
    (hMalloc : LibcMallocImplPlaced24Stmt)
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 9) (libcMallocImplPlacedSpec24 γ tp brkStart b ivs0 req) :=
  subroutine_ok_block_to_block (j := 9) (by decide)
    (hMalloc γ tp brkStart b ivs0 req) hext hsvc

abbrev OverflowErrnoGhost := BitVec 64 × BitVec 64 × BitVec 64 × BitVec 32

set_option maxHeartbeats 400000 in
private theorem blk09_overflow_errno [MallocngMultiPlacement] :
    subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9) (withCL mmpl {
      pre := fun (g : OverflowErrnoGhost) s0 =>
        ⌜s0.tpidrEl0 = g.1 ∧ MallocngMaxAllocSize < (s0.readReg64 .x0).toNat⌝ ∗
        ((s0.sp - 80#64) ↦₆₄ g.2.1) ∗ ((s0.sp - 72#64) ↦₆₄ g.2.2.1) ∗
        ((g.1 - 0xa4#64) ↦₃₂ g.2.2.2)
      post := fun g s0 sf =>
        ∃∗ (w0 : BitVec 64), ∃∗ (w1 : BitVec 64),
          ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm ∧
           sf.readReg64 .x0 = 0#64⌝ ∗
          ((s0.sp - 80#64) ↦₆₄ w0) ∗ ((s0.sp - 72#64) ↦₆₄ w1) ∗
          ((g.1 - 0xa4#64) ↦₃₂ 12#32)
    }) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have hfn : ∀ c, (blkPC_b09.rebase c (fun _ => none)).fnAddr "__libc_malloc_impl" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase, Program.fnOff, Program.findSymbol?, blkPC_b09, PlacedLib.program]
    rw [blkSymsEq_b09]
    have hf : (ProofLib.ProgramReflection.toStringSymbols blkSymChars_b09).find? (·.1 == "__libc_malloc_impl") =
        some ("__libc_malloc_impl", 0) := by decide
    rw [hf]; exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b09 (hfn (mbase 9)) fun b hb => ?_
  have _ := hb
  rw [hfn b]
  have herr := placed_errnoLocation_perm_ok (P := blkPC_b09.rebase b (fun _ => none))
    (externAt?_placedProgram_rebase_none _ _ _ _) rfl
  apply subroutine_ok_of_sepWP_init
  rintro ⟨tp, w0, w1, ev⟩ R s0 hpc hrun hpre hsp_align
  dsimp only at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hm0_eq, hpre⟩ := hpre
  subst hm0_eq
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨htp, hgt⟩, hpre⟩ := hpre
  subst htp
  refine ⟨((s0.sp - 80#64) ↦₆₄ w0) ∗ ((s0.sp - 72#64) ↦₆₄ w1) ∗ ((s0.tpidrEl0 - 0xa4#64) ↦₃₂ ev),
    by simpa [sepConj_assoc] using hpre, ?_⟩
  wp_stp64_cl m1 hm1 hcl0 hcl1
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_if hhi
  · wp_step
    have hpc_bl : b + 456#64 + (mbase 0 - mbase 9 - 456#64) = mbase 0 := by rw [hb]; bv_arith
    conv => arg 3; simp only [hpc_bl]
    wp_call herr
    simp only [MallocngProcPreserved] at *
    have hcl_herr : VerifiedLibraries.mallocngLib.CodeLoaded mmpl _ := ‹_›
    wp_step; wp_step; wp_step
    wp_str32_cl m2 hm2 hcl_herr hcl2
    wp_steps
    have _hperm : m2.perm = s0.mem.perm := Eq.trans hm2 (Eq.trans ‹_› hm1)
    wp_done
  · exfalso
    apply hhi
    rw [BitVec.ult_iff_toNat_lt]
    have hMax : (9223372036854771710#64 : BitVec 64).toNat = MallocngMaxAllocSize := by decide
    rw [hMax]
    exact hgt

/-- Polymorphic cross-block `__libc_malloc_impl` overflow contract (`MallocngMaxAllocSize < req`,
    `80` B stack) preserving `sf.mem.perm = s0.mem.perm` and writing `12#32` (`ENOMEM`) to `errno`. -/
theorem placed_libcMallocImpl_overflow_errno_ok [MallocngMultiPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 9) (withCL mmpl {
      pre := fun (g : OverflowErrnoGhost) s0 =>
        ⌜s0.tpidrEl0 = g.1 ∧ MallocngMaxAllocSize < (s0.readReg64 .x0).toNat⌝ ∗
        ((s0.sp - 80#64) ↦₆₄ g.2.1) ∗ ((s0.sp - 72#64) ↦₆₄ g.2.2.1) ∗
        ((g.1 - 0xa4#64) ↦₃₂ g.2.2.2)
      post := fun g s0 sf =>
        ∃∗ (w0 : BitVec 64), ∃∗ (w1 : BitVec 64),
          ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm ∧
           sf.readReg64 .x0 = 0#64⌝ ∗
          ((s0.sp - 80#64) ↦₆₄ w0) ∗ ((s0.sp - 72#64) ↦₆₄ w1) ∗
          ((g.1 - 0xa4#64) ↦₃₂ 12#32)
    }) :=
  subroutine_ok_block_to_block (j := 9) (by decide) blk09_overflow_errno hext hsvc

/-! ## `aligned_alloc` `get_meta(p)` and `get_stride(g)` (`blk12` `+0x068` to `+0x1b4`) -/

/-- State preservation across the pure read-only `get_meta` and `get_stride` block (`+0x068` to `+0x1b4`). -/
def AlignedGetMetaPres (s0 s1 : State) : Prop :=
  s1.mem = s0.mem ∧
  s1.brk = s0.brk ∧
  MallocngProcPreserved s0 s1 ∧
  s1.sp = s0.sp ∧
  s1.spAligned = s0.spAligned ∧
  s1.readReg64 .x30 = s0.readReg64 .x30 ∧
  CalleeSavedPreserved s0 s1

theorem AlignedGetMetaPres.trans {s0 s1 s2 : State}
    (h01 : AlignedGetMetaPres s0 s1) (h12 : AlignedGetMetaPres s1 s2) :
    AlignedGetMetaPres s0 s2 := by
  obtain ⟨hm1, hb1, hp1, hs1, ha1, hl1, hcs1⟩ := h01
  obtain ⟨hm2, hb2, hp2, hs2, ha2, hl2, hcs2⟩ := h12
  exact ⟨hm2.trans hm1, hb2.trans hb1, alignedProcPreserved_trans hp1 hp2,
    hs2.trans hs1, ha2.trans ha1, hl2.trans hl1, CalleeSavedPreserved.trans hcs1 hcs2⟩

def alignedGetMetaPre (A : MallocngAddrs) (st : MallocngSt) (Rest : SepProp) : SepProp :=
  MallocngRoTablesAt A ∗
  (A.ctx ↦ₛ st.ctx.toBytes) ∗
  ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
  Rest

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
    ((BitVec.ofNat 64 sc >>> 0 &&& 0xffffffff#64 |||
      (if (BitVec.ofNat 64 sc).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) <<< 1) = BitVec.ofNat 64 (2 * sc) := by
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

private theorem bv64_ult_of_lt {n k : Nat} (hk : k < 2 ^ 64) (h : n < k) :
    (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 k) = true := by
  rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hk]; exact h

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

private theorem aligned_hdr_ok [MallocngMultiPlacement] {b : BitVec 64} (_hb : BlkBase 12 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {p : BitVec 64} {req effCost : Nat} {Rest : SepProp}
    (hF : LiveUserBlockFacts st g idx p req effCost)
    {s0 : State} (hpc : s0.pc = b + 0x68#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = p) :
    let tot := (p.toNat - g.storage.toNat) / 16
    let P := alignedGetMetaPre maddrs st Rest
    SepWP (blkPC_b12.rebase b (fun _ => none)) (b + 0xd8#64) s0 P
      (sepPost (fun s1 => AlignedGetMetaPres s0 s1 ∧ s1.readReg64 .x0 = p ∧
        s1.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s1.readReg64 .x4 = (BitVec.ofNat 32 tot).zeroExtend 64) P) (fun _ => ⌜False⌝) := by
  intro tot P
  let res := (g.slotEnd idx).toNat - (p.toNat + req)
  let r5 := min res 5
  let hdrB : BitVec 8 := BitVec.ofNat 8 ((r5 <<< 5) ||| idx)
  have hAnd15 := hF.p_and_15
  have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
  have ⟨hHdrIdx, _, _, _⟩ := hdrByte_extract r5 idx (Nat.min_le_right _ _) hIdx31
  by_cases hShort : tot ≤ 0xffff
  · conv => arg 4; dsimp only [P, alignedGetMetaPre]; rw [hF.focus_hdr_short hShort]
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
    conv => arg 4; dsimp only [P, alignedGetMetaPre]; rw [hF.focus_hdr_long hLong]
    wp_steps
    conv => arg 4; rw [← hF.focus_hdr_long hLong]
    refine SepWP.done rfl (by simp [hrun]) ⟨⟨?_, by simp [hx0], ?_, ?_⟩, Entails.refl _⟩
    · exact ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp [CalleeSavedPreserved]⟩
    · simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]
      exact hdrB_mask64 hdrB hHdrIdx
    · simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]; rfl

private theorem aligned_meta_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 12 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {p : BitVec 64} {req effCost : Nat} {Rest : SepProp}
    (hF : LiveUserBlockFacts st g idx p req effCost)
    {s1 : State} (hpc : s1.pc = b + 0xd8#64) (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = p)
    (hx2 : s1.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx4 : s1.readReg64 .x4 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64) :
    let P := alignedGetMetaPre maddrs st Rest
    SepWP (blkPC_b12.rebase b (fun _ => none)) (b + 0x144#64) s1 P
      (sepPost (fun s2 => AlignedGetMetaPres s1 s2 ∧ s2.readReg64 .x0 = p ∧
        s2.readReg64 .x1 = g.metaPtr ∧
        s2.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s2.readReg64 .x4 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64 ∧
        s2.readReg64 .x6 = g.mem ∧
        s2.readReg64 .x7 = (g.packedWord.extractLsb' 0 8).zeroExtend 64) P) (fun _ => ⌜False⌝) := by
  intro P
  have _ := hb
  have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
  have hMemAddr : p + (-16#64 - ((BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16) <<< 4).signExtend 64)) = g.mem :=
    group_mem_addr_of_totalOff hF.totalOff_lt_27
      (by have := hF.p_add_n_48; rw [← hF.p_eq_storage_off]; omega) hF.p_eq_storage_off
  have hMemAddrU : p + (0xfffffffffffffff0#64 - ((BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16) <<< 4).signExtend 64)) = g.mem :=
    hMemAddr
  have ⟨hByte32, _⟩ := packedWord_byte0_and31 g hF.last_le_31
  have hByteMask := hdrB_mask64 (g.packedWord.extractLsb' 0 8) hByte32
  have ⟨hAv1, hAv2⟩ := mask_ushiftRight_bit0_false g.availMask hIdx31 hF.avail_bit_false
  have ⟨hFr1, hFr2⟩ := mask_ushiftRight_bit0_false g.freedMask hIdx31 hF.freed_bit_false
  obtain ⟨ma, _, hMaBase, hFocusMa⟩ := hF.meta_page_base
  have hMaBase' : g.metaPtr &&& -4096#64 = ma.base := hMaBase
  obtain ⟨ctxRest, hCtxSplit⟩ := ctx_toBytes_split_secret maddrs.ctx st.ctx
  have hPageCtx := pageOf_add_lo12Of maddrs.ctx
  conv => arg 4; dsimp only [P, alignedGetMetaPre]; rw [hF.focus_group_mem]
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
        by simp [hx0], by simp, by simp [hx2], by simp [hx4], by simp, by simp⟩, Entails.refl _⟩

set_option maxHeartbeats 400000 in
private theorem aligned_sc_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 12 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {p : BitVec 64} {req effCost : Nat} {Rest : SepProp}
    (hF : LiveUserBlockFacts st g idx p req effCost)
    {s2 : State} (hpc : s2.pc = b + 0x144#64) (hrun : s2.status = .Running)
    (hx0 : s2.readReg64 .x0 = p)
    (hx1 : s2.readReg64 .x1 = g.metaPtr)
    (hx2 : s2.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx4 : s2.readReg64 .x4 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64)
    (hx6 : s2.readReg64 .x6 = g.mem)
    (hx7 : s2.readReg64 .x7 = (g.packedWord.extractLsb' 0 8).zeroExtend 64) :
    let P := alignedGetMetaPre maddrs st Rest
    SepWP (blkPC_b12.rebase b (fun _ => none)) (b + 0x178#64) s2 P
      (sepPost (fun s3 => AlignedGetMetaPres s2 s3 ∧ s3.readReg64 .x0 = p ∧
        s3.readReg64 .x1 = g.metaPtr ∧
        s3.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s3.readReg64 .x4 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64 ∧
        s3.readReg64 .x5 = BitVec.ofNat 64 g.sc ∧
        s3.readReg64 .x6 = g.mem ∧
        s3.readReg64 .x7 = (g.packedWord.extractLsb' 0 8).zeroExtend 64) P) (fun _ => ⌜False⌝) := by
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
  have hPageSc := pageOf_add_lo12Of maddrs.sizeClasses
  conv => arg 4; dsimp only [P, alignedGetMetaPre]; rw [hF.focus_meta, pointsTo64_split_lo16 (g.metaPtr + 32#64) g.packedWord]
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
      have hSxtwSc : ((BitVec.ofNat 64 g.sc).truncate 32).signExtend 64 = BitVec.ofNat 64 g.sc := by
        rw [show (BitVec.ofNat 64 g.sc).truncate 32 = BitVec.ofNat 32 g.sc by bv_omega, sxtw32_of_lt31 (by omega)]
      have hLsl1Sc : BitVec.ofNat 64 g.sc <<< 1 = BitVec.ofNat 64 (2 * g.sc) := by bv_omega
      have ⟨_, huMax, _, _⟩ := sizeClass_bounds hsc48
      have ⟨hLow, hHigh⟩ := hF.sc_lt_48_off hsc48
      have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
      have hMulB1 : idx * sizeClass g.sc ≤ 31 * 8191 := Nat.mul_le_mul hIdx31 huMax
      have hMulB2 : (idx + 1) * sizeClass g.sc ≤ 32 * 8191 := Nat.mul_le_mul (by omega) huMax
      have hTot27 := hF.totalOff_lt_27
      conv => arg 4; dsimp only [P, alignedGetMetaPre]; rw [hRoSplit]
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
            ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp [CalleeSavedPreserved]⟩,
              by simp [hx0], by simp [hx1], by simp [hx2], by simp [hx4], by simp,
              by simp [hx6], by simp [hx7]⟩, Entails.refl _⟩
  · have hMask63 : ((g.packedWord.extractLsb' 0 16).zeroExtend 32 &&& 0xfc0#32) = 0xfc0#32 := by
      have hL : (BitVec.ofNat 64 g.lastIdx).ult 32#64 = true := by
        rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; have := hF.last_le_31; change g.lastIdx % (2 ^ 64) < 32; omega
      have hM : (BitVec.ofNat 64 g.maplen).ult (1#64 <<< 52) = true := by
        rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; have := hF.maplen_lt_52; change g.maplen % (2 ^ 64) < 2 ^ 52; omega
      dsimp only [GroupDesc.packedWord]; rw [hsc63]; revert hL hM; bv_robdd
    wp_if hhi
    · wp_steps
      refine SepWP.done rfl (by simp [hrun])
        ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp [CalleeSavedPreserved]⟩,
          by simp [hx0], by simp [hx1], by simp [hx2], by simp [hx4], by simp [hsc63],
          by simp [hx6], by simp [hx7]⟩, Entails.refl _⟩
    · exfalso; rw [hsc63] at hhi; exact hhi rfl

set_option maxHeartbeats 400000 in
private theorem aligned_stride_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 12 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {p : BitVec 64} {req effCost : Nat} {Rest : SepProp}
    (hF : LiveUserBlockFacts st g idx p req effCost)
    {s3 : State} (hpc : s3.pc = b + 0x178#64) (hrun : s3.status = .Running)
    (hx0 : s3.readReg64 .x0 = p)
    (hx1 : s3.readReg64 .x1 = g.metaPtr)
    (hx2 : s3.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx4 : s3.readReg64 .x4 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64)
    (hx5 : s3.readReg64 .x5 = BitVec.ofNat 64 g.sc)
    (hx6 : s3.readReg64 .x6 = g.mem)
    (hx7 : s3.readReg64 .x7 = (g.packedWord.extractLsb' 0 8).zeroExtend 64) :
    let P := alignedGetMetaPre maddrs st Rest
    SepWP (blkPC_b12.rebase b (fun _ => none)) (b + 0x1b4#64) s3 P
      (sepPost (fun s4 => AlignedGetMetaPres s3 s4 ∧ s4.readReg64 .x0 = p ∧
        s4.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s4.readReg64 .x4 = BitVec.ofNat 64 g.stride ∧
        s4.readReg64 .x6 = g.mem) P) (fun _ => ⌜False⌝) := by
  intro P
  have _ := hb
  have hSc64 : g.sc < 64 := by rcases hF.sc_cases with h | h <;> omega
  have hMapMask := packedWord_maplen_mask g hF.last_le_31 hSc64 hF.maplen_bytes_48
  have ⟨_, hByte64⟩ := packedWord_byte0_and31 g hF.last_le_31
  have hPageSc := pageOf_add_lo12Of maddrs.sizeClasses
  conv => arg 4; dsimp only [P, alignedGetMetaPre]; rw [hF.focus_meta]
  wp_step; wp_step; wp_step
  conv => arg 4; rw [← hF.focus_meta]
  by_cases hMap0 : g.maplen = 0
  · have ⟨hsc48, _⟩ := hF.maplen_zero_sc hMap0
    have hStride : g.stride = 16 * sizeClass g.sc := by simp [GroupDesc.stride, slotStride, hMap0]
    have hOffSc := sxtw_lsl1_sc hsc48
    have hSbfmSc := sxtw_sbfm_sc hsc48
    have hSxtwSc : ((BitVec.ofNat 64 g.sc).truncate 32).signExtend 64 = BitVec.ofNat 64 g.sc := by
      rw [show (BitVec.ofNat 64 g.sc).truncate 32 = BitVec.ofNat 32 g.sc by bv_omega, sxtw32_of_lt31 (by omega)]
    have hLsl1Sc : BitVec.ofNat 64 g.sc <<< 1 = BitVec.ofNat 64 (2 * g.sc) := by bv_omega
    have ⟨_, huMax, _, _⟩ := sizeClass_bounds hsc48
    obtain ⟨roRest, hRoSplit⟩ := split_sizeClass_roTablesAt maddrs hsc48
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Rest)
    wp_if heq
    · conv => arg 4; dsimp only [P, alignedGetMetaPre]; rw [hRoSplit]
      wp_steps
      conv => arg 4; rw [← hRoSplit]
      refine SepWP.done rfl (by simp [hrun])
        ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp [CalleeSavedPreserved]⟩,
          by simp [hx0], by simp [hx2], ?_, by simp [hx6]⟩, Entails.refl _⟩
      simp [hStride, sc16_ubfiz_shl4 hsc48]
    · exfalso; rw [hMap0] at heq; exact heq rfl
  · have hMapPos : 0 < g.maplen := Nat.pos_of_ne_zero hMap0
    have hMap48 := hF.maplen_bytes_48; have hTot27 := hF.totalOff_lt_27; have hMapOff := hF.maplen_pos_off hMapPos
    have hSxtwTot := sxtw32_of_lt31 (n := (p.toNat - g.storage.toNat) / 16) (by omega)
    wp_if heq
    · exfalso
      have h0 : (BitVec.ofNat 64 (g.maplen * 4096)).toNat = 0 := by rw [heq]; rfl
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
    · wp_steps; wp_if hlo
      · exfalso
        rw [← hSxtwTot, maplen_shr4_sub1_ult_false hMapPos hMap48 hTot27 hMapOff] at hlo
        cases hlo
      · wp_steps; by_cases hLast0 : g.lastIdx = 0
        · have hStride : g.stride = g.maplen * 4096 - 16 := by simp [GroupDesc.stride, hLast0, hMapPos]
          wp_if hlastEq
          · refine SepWP.done rfl (by simp [hrun])
              ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp [CalleeSavedPreserved]⟩,
                by simp [hx0], by simp [hx2], ?_, by simp [hx6]⟩, Entails.refl _⟩
            simp [hStride]; bv_omega
          · exfalso; rw [hLast0] at hlastEq; exact hlastEq rfl
        · have hsc48 : g.sc < 48 := by
            rcases hF.sc_cases with h | h; · exact h
            · exact absurd (hF.sc_63_props h).1 hLast0
          have hStride : g.stride = 16 * sizeClass g.sc := by simp [GroupDesc.stride, slotStride, hLast0]
          have hOffSc := sxtw_lsl1_sc hsc48
          have hSbfmSc := sxtw_sbfm_sc hsc48
          have hSxtwSc : ((BitVec.ofNat 64 g.sc).truncate 32).signExtend 64 = BitVec.ofNat 64 g.sc := by
            rw [show (BitVec.ofNat 64 g.sc).truncate 32 = BitVec.ofNat 32 g.sc by bv_omega, sxtw32_of_lt31 (by omega)]
          have hLsl1Sc : BitVec.ofNat 64 g.sc <<< 1 = BitVec.ofNat 64 (2 * g.sc) := by bv_omega
          have ⟨_, huMax, _, _⟩ := sizeClass_bounds hsc48
          obtain ⟨roRest, hRoSplit⟩ := split_sizeClass_roTablesAt maddrs hsc48
            ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Rest)
          wp_if hlastEq
          · exfalso; have := hF.last_le_31
            have h0 : (BitVec.ofNat 64 g.lastIdx).toNat = 0 := by rw [hlastEq]; rfl
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
          · conv => arg 4; dsimp only [P, alignedGetMetaPre]; rw [hRoSplit]
            wp_steps
            conv => arg 4; rw [← hRoSplit]
            refine SepWP.done rfl (by simp [hrun])
              ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp [CalleeSavedPreserved]⟩,
                by simp [hx0], by simp [hx2], ?_, by simp [hx6]⟩, Entails.refl _⟩
            simp [hStride, sc16_ubfiz_shl4 hsc48]

private theorem sepWP_false_oom {prog : Program} {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog tgt s P post (fun _ => ⌜False⌝)) : SepWP prog tgt s P post oom :=
  SepWP.of_reaches_pc fun _ hm => reaches_pc_mono (SepWP.to_reaches_pc h hm) (fun _ _ _ hp => hp)
    fun _ _ hf => False.elim (not_satisfies_false_sepConj hf)

/-- Composed `get_meta(p)` and `get_stride(g)` (`+0x068` to `+0x1b4`) in `blk12` (`aligned_alloc`),
    lifted to arbitrary `oom` and any program `prog = mallocngBlockProg mmpl 12 msvc`. -/
theorem alignedAlloc_getMeta_getStride_ok [MallocngMultiPlacement] {prog : Program}
    {b : BitVec 64} (hb : BlkBase 12 b) (hprog : prog = mallocngBlockProg mmpl 12 msvc)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {p : BitVec 64} {req effCost : Nat} {Rest : SepProp} {oom : State → SepProp}
    (hF : LiveUserBlockFacts st g idx p req effCost)
    {s0 : State} (hpc : s0.pc = b + 0x68#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = p) :
    let P := alignedGetMetaPre maddrs st Rest
    SepWP prog (b + 0x1b4#64) s0 P
      (sepPost (fun s4 => AlignedGetMetaPres s0 s4 ∧ s4.readReg64 .x0 = p ∧
        s4.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64 ∧
        s4.readReg64 .x4 = BitVec.ofNat 64 g.stride ∧
        s4.readReg64 .x6 = g.mem) P) oom := by
  intro P
  have hProgEq : prog = blkPC_b12.rebase b (fun _ => none) := by
    rw [hprog, mallocngBlockProg_eq_b12, hb]
  rw [hProgEq]
  refine sepWP_false_oom ?_
  refine SepWP.seq (aligned_hdr_ok hb hF hpc hrun hx0) ?_
  rintro s1 P1 hpc1 hrun1 ⟨⟨hP01, hx0_1, hx2_1, hx4_1⟩, hE1⟩
  refine SepWP.weaken_pre hE1 ?_
  refine SepWP.seq (aligned_meta_ok hb hF hpc1 hrun1 hx0_1 hx2_1 hx4_1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨⟨hP12, hx0_2, hx1_2, hx2_2, hx4_2, hx6_2, hx7_2⟩, hE2⟩
  refine SepWP.weaken_pre hE2 ?_
  refine SepWP.seq (aligned_sc_ok hb hF hpc2 hrun2 hx0_2 hx1_2 hx2_2 hx4_2 hx6_2 hx7_2) ?_
  rintro s3 P3 hpc3 hrun3 ⟨⟨hP23, hx0_3, hx1_3, hx2_3, hx4_3, hx5_3, hx6_3, hx7_3⟩, hE3⟩
  refine SepWP.weaken_pre hE3 ?_
  refine SepWP.mono (aligned_stride_ok hb hF hpc3 hrun3 hx0_3 hx1_3 hx2_3 hx4_3 hx5_3 hx6_3 hx7_3) ?_
  rintro s4 P4 _ _ ⟨⟨hP34, hx0_4, hx2_4, hx4_4, hx6_4⟩, hE4⟩
  exact ⟨⟨hP01.trans (hP12.trans (hP23.trans hP34)), hx0_4, hx2_4, hx4_4, hx6_4⟩, hE4⟩

/-! ## Sub-Word Store Rules, `ByteMap` Store Combinators, and Stack Splits -/

def CalleeSaved21_28 (s0 s : State) : Prop :=
  s.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧
  s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

namespace AlignedStage1
theorem step_str8_perm_kf {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg64 rt).truncate 8 = val) (hstore : SepStore8 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  let m' := s.mem.write8 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 1 = true := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m' (Memory.perm_write8 _ _ _) (Memory.keepsFrozen_write8 hcan val)) hm'

theorem step_str16_perm_kf {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 16}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .H16 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg64 rt).truncate 16 = val) (hstore : SepStore16 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  let m' := s.mem.write16 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 2 = true := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .H16 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m' (Memory.perm_write16 _ _ _) (Memory.keepsFrozen_write16 hcan val)) hm'

theorem sepWP_bupd_pre {prog : Program} {tgt : BitVec 64} {s : State} {P Q : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hUpd : P ⊢ |==> Q) (hwp : SepWP prog tgt s Q post oom) :
    SepWP prog tgt s P post oom := by
  apply SepWP.of_reaches_pc; intro _ hm
  exact SepWP.to_reaches_pc hwp (Satisfies.of_bupd_frame_left hUpd hm)

theorem mappedDelta_of_perm_eq {maxIvs maxBytes : Nat} {m0 mf : Memory}
    (h : mf.perm = m0.perm) : MallocngMappedDelta maxIvs maxBytes m0 mf :=
  ⟨[], Nat.zero_le _, Nat.zero_le _, fun _ ha => Or.inl (h ▸ ha)⟩

theorem mappedDelta_congr_perm {maxIvs maxBytes : Nat} {m0 m1 m2 m3 : Memory}
    (h01 : m1.perm = m0.perm) (hd : MallocngMappedDelta maxIvs maxBytes m1 m2)
    (h32 : m3.perm = m2.perm) : MallocngMappedDelta maxIvs maxBytes m0 m3 := by
  obtain ⟨ivs, hl, hs, hc⟩ := hd
  refine ⟨ivs, hl, hs, fun a ha => ?_⟩
  rw [h32] at ha
  rcases hc a ha with hm1 | hiv
  · exact Or.inl (h01 ▸ hm1)
  · exact Or.inr hiv

theorem noOrphanMappings_refl_of_perm_eq {ivs : List (BitVec 64 × Nat)} {m0 mf : Memory}
    (hperm : mf.perm = m0.perm) : MallocngNoOrphanMappings ivs ivs m0 mf := by
  intro a hmf hor
  rcases hor with hm0 | hivs
  · rw [hperm, hm0] at hmf; cases hmf
  · exact hivs

theorem noOrphanMappings_congr_perm {ivs0 ivsf : List (BitVec 64 × Nat)}
    {m0 m1 m2 m3 : Memory} (h01 : m1.perm = m0.perm)
    (hno : MallocngNoOrphanMappings ivs0 ivsf m1 m2) (h32 : m3.perm = m2.perm) :
    MallocngNoOrphanMappings ivs0 ivsf m0 m3 := by
  intro a h3 hor
  rw [h32] at h3
  exact hno a h3 (hor.imp_left fun h0 => h01.symm ▸ h0)
end AlignedStage1
export AlignedStage1 (step_str8_perm_kf step_str16_perm_kf sepWP_bupd_pre
  mappedDelta_of_perm_eq mappedDelta_congr_perm noOrphanMappings_refl_of_perm_eq
  noOrphanMappings_congr_perm)

theorem stackFrameAt_736_split (sp0 : BitVec 64) :
    stackFrameAt sp0 736 =
      (stackFrameAt (sp0 - 32#64) 704 ∗ cells (sp0 - 32#64) 4) := by
  rw [stackFrameAt_split sp0 32 704, stackFrameAt_eq_memRegion sp0 32,
    memRegion_cells (sp0 - 32#64) 4 (by decide), sepConj_comm]

theorem stackFrameAt_704_split_80 (sp1 : BitVec 64) :
    stackFrameAt sp1 704 =
      (stackFrameAt (sp1 - 80#64) 624 ∗ stackFrameAt sp1 64 ∗
        cells (sp1 - 80#64) 2) := by
  rw [stackFrameAt_split sp1 80 624, stackFrameAt_eq_memRegion sp1 80,
    stackFrameAt_eq_memRegion sp1 64]
  have hb : sp1 - 80#64 + BitVec.ofNat 64 16 = sp1 - 64#64 := by bv_arith
  rw [memRegion_split (sp1 - 80#64) 16 64 (by decide), hb,
    memRegion_cells (sp1 - 80#64) 2 (by decide)]
  ac_rfl

theorem step_byteMap_str8 {prog : Program} {tgt : BitVec 64}
    {s : State} {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep] {bv : BitVec 64 → BitVec 8}
    {Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {val : BitVec 8}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, none))
    (hval : (s.readReg64 rt).truncate 8 = val)
    (hDom : ∀ a, InRegion ea 1 a → a ∈ dom) (hKeep : ∀ a, InRegion ea 1 a → keep a)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog tgt ((s.setPC (pc + 4#64)).setMem m')
        (ByteMap dom keep (writeBytesToMap bv ea [val]) ∗ Rest) post oom) :
    SepWP prog tgt s (ByteMap dom keep bv ∗ Rest) post oom := by
  rw [byteMap_focus8 hNodup bv ea hDom hKeep, sepConj_assoc]
  refine step_str8_perm_kf hpc hrun hfetch hsp haddr hval (by wp_sep_access) rfl ?_
  intro m' hm' hkf'
  rw [← sepConj_assoc, byteMap_absorb8 hNodup bv ea val hDom hKeep]
  exact hnext m' hm' hkf'

theorem step_byteMap_str16 {prog : Program} {tgt : BitVec 64}
    {s : State} {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep] {bv : BitVec 64 → BitVec 8}
    {Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {val : BitVec 16}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .H16 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, none))
    (hval : (s.readReg64 rt).truncate 16 = val)
    (hDom : ∀ a, InRegion ea 2 a → a ∈ dom) (hKeep : ∀ a, InRegion ea 2 a → keep a)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog tgt ((s.setPC (pc + 4#64)).setMem m')
        (ByteMap dom keep (writeBytesToMap bv ea (unpack16 val)) ∗ Rest) post oom) :
    SepWP prog tgt s (ByteMap dom keep bv ∗ Rest) post oom := by
  rw [byteMap_focus16 hNodup bv ea hDom hKeep, sepConj_assoc]
  refine step_str16_perm_kf hpc hrun hfetch hsp haddr hval (by wp_sep_access) rfl ?_
  intro m' hm' hkf'
  rw [← sepConj_assoc, byteMap_absorb16 hNodup bv ea val hDom hKeep]
  exact hnext m' hm' hkf'

theorem step_byteMap_str32 {prog : Program} {tgt : BitVec 64}
    {s : State} {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep] {bv : BitVec 64 → BitVec 8}
    {Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {val : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .W32 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, none))
    (hval : s.readReg32 rt = val)
    (hDom : ∀ a, InRegion ea 4 a → a ∈ dom) (hKeep : ∀ a, InRegion ea 4 a → keep a)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog tgt ((s.setPC (pc + 4#64)).setMem m')
        (ByteMap dom keep (writeBytesToMap bv ea (unpack32 val)) ∗ Rest) post oom) :
    SepWP prog tgt s (ByteMap dom keep bv ∗ Rest) post oom := by
  rw [byteMap_focus32 hNodup bv ea hDom hKeep, sepConj_assoc]
  refine step_str32_perm_kf hpc hrun hfetch hsp haddr hval (by wp_sep_access) rfl ?_
  intro m' hm' hkf'
  rw [← sepConj_assoc, byteMap_absorb32 hNodup bv ea val hDom hKeep]
  exact hnext m' hm' hkf'

end VerifiedLibraries.Mallocng.Proofs

