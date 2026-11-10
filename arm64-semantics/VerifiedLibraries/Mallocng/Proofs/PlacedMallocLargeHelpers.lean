/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplHelpers4
public import VerifiedLibraries.Mallocng.Proofs.MallocLargeProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedLeavesProof
import VerifiedLibraries.Mallocng.Proofs.SyscallWrappersProof

/-!
# Placed Large `mmap` Helpers

Arithmetic bounds (`large_mmap_len_bounds`), unified `blk16` `__mmap` specification
(`placed_mmapRw_large_ok`), OOM composition lemmas, and `sc = 63` group re-bundling helpers for
large allocations in `__libc_malloc_impl`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Arithmetic, `pageAlignUp`, and `packedWord` bounds -/

theorem pageAlignUp_mono {a b : Nat} (h : a ≤ b) : pageAlignUp a ≤ pageAlignUp b := by
  unfold pageAlignUp PAGE_SIZE
  exact Nat.mul_le_mul_right 4096 (Nat.div_le_div_right (by omega))

theorem bv64_and_not_fff_toNat (x : BitVec 64) :
    (x &&& 0xfffffffffffff000#64).toNat = (x.toNat / 4096) * 4096 := by
  have hsh : x &&& 0xfffffffffffff000#64 = (x >>> 12) <<< 12 := by bv_bits
  rw [hsh, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  have hlt : (x.toNat >>> 12) <<< 12 < 2 ^ 64 := by
    have hx := x.isLt
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega
  rw [Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

theorem large_mmap_len_bounds {req peakCount : Nat}
    (hGt : 131051 < req) (hMax : req ≤ MallocngMaxAllocSize) :
    let rawLen := req + 20
    let len := pageAlignUp rawLen
    0 < rawLen ∧
    rawLen ≤ MallocngMaxAllocSize + 20 ∧
    (BitVec.ofNat 64 req + 0x14#64).toNat = rawLen ∧
    4096 ≤ len ∧
    len % 4096 = 0 ∧
    rawLen ≤ len ∧
    len ≤ req + 4115 ∧
    len ≤ MallocngStepBound req peakCount ∧
    allocMetaPlacedByteBound peakCount ≤ MallocngStepBound req peakCount ∧
    len + allocMetaPlacedByteBound peakCount ≤ MallocngStepBound req peakCount ∧
    (∀ m mb : BitVec 64, req + 4 ≤ (mkLargeGroup m mb len).stride) ∧
    ((len / 4096) * 4096 ≤ max req MallocngMinBlockCost + 8195) ∧
    (∀ m mb : BitVec 64,
      (((BitVec.ofNat 64 req + 0x1013#64) &&& 0xfffffffffffff000#64) ||| 0xfe0#64) =
        (mkLargeGroup m mb len).packedWord) := by
  dsimp only
  have hMaxEq : MallocngMaxAllocSize = 9223372036854771710 := mallocngMaxAllocSize_eq
  have hPage : pageAlignUp (req + 20) = ((req + 20 + 4095) / 4096) * 4096 := rfl
  have hLeAlign : pageAlignUp (req + 20) ≤ pageAlignUp (req + 8192) :=
    pageAlignUp_mono (by omega)
  have hAdd20 : (BitVec.ofNat 64 req + 0x14#64).toNat = req + 20 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hLenLo : 4096 ≤ pageAlignUp (req + 20) := by rw [hPage]; omega
  have hLenMod : (pageAlignUp (req + 20)) % 4096 = 0 := by rw [hPage]; omega
  have hRawLe : req + 20 ≤ pageAlignUp (req + 20) := by rw [hPage]; omega
  have hLenHi : pageAlignUp (req + 20) ≤ req + 4115 := by rw [hPage]; omega
  have hStep1 : pageAlignUp (req + 20) ≤ MallocngStepBound req peakCount := by
    unfold MallocngStepBound MallocngBaseOverhead; omega
  have hStep2 : allocMetaPlacedByteBound peakCount ≤ MallocngStepBound req peakCount := by
    unfold allocMetaPlacedByteBound MallocngStepBound MallocngBaseOverhead; omega
  have hStep3 :
      pageAlignUp (req + 20) + allocMetaPlacedByteBound peakCount ≤
        MallocngStepBound req peakCount := by
    unfold allocMetaPlacedByteBound MallocngStepBound MallocngBaseOverhead; omega
  have hMapPos : 0 < pageAlignUp (req + 20) / 4096 := by omega
  have hStride : ∀ m mb : BitVec 64,
      (mkLargeGroup m mb (pageAlignUp (req + 20))).stride = pageAlignUp (req + 20) - 16 := by
    intro m mb
    dsimp only [mkLargeGroup, GroupDesc.stride]
    simp only [beq_self_eq_true, decide_eq_true hMapPos, Bool.and_self, ↓reduceIte]
    omega
  refine ⟨by omega, by omega, hAdd20, hLenLo, hLenMod, hRawLe, hLenHi,
    hStep1, hStep2, hStep3, fun m mb => by rw [hStride m mb]; omega, by omega, ?_⟩
  intro m mb
  have hAdd4115 : (BitVec.ofNat 64 req + 0x1013#64).toNat = req + 4115 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hAndEq : (BitVec.ofNat 64 req + 0x1013#64) &&& 0xfffffffffffff000#64 =
      BitVec.ofNat 64 (pageAlignUp (req + 20)) := by
    apply BitVec.eq_of_toNat_eq
    rw [bv64_and_not_fff_toNat, hAdd4115, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64), hPage]
  rw [hAndEq]
  have hShl : BitVec.ofNat 64 (pageAlignUp (req + 20) / 4096) <<< 12 =
      BitVec.ofNat 64 (pageAlignUp (req + 20)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) / 4096 < 2 ^ 64),
      Nat.shiftLeft_eq]
    have hmul : (pageAlignUp (req + 20) / 4096) * 2 ^ 12 = pageAlignUp (req + 20) := by omega
    rw [hmul, Nat.mod_eq_of_lt (by omega)]
  dsimp only [mkLargeGroup, GroupDesc.packedWord]
  rw [← hShl]
  generalize BitVec.ofNat 64 (pageAlignUp (req + 20) / 4096) = K
  bv_bits

/-! ## Placed `__mmap` (`blk16`) contract and OOM composition -/

local macro "wp_norm_mbase_pc" : tactic =>
  `(tactic| conv in (mbase _ + _ + _) => rw [BitVec.add_assoc]; simp only [BitVec.reduceAdd])

def MmapNewInRegion (mb : BitVec 64) (len : Nat) (m0 mf : Memory) : Prop :=
  ∀ a : BitVec 64, (mf.perm a).mapped = true →
    (m0.perm a).mapped = true ∨ InRegion mb len a

private theorem perm_mapZero_inRegion {m0 m3 mf : Memory} {mb : BitVec 64} {len : Nat}
    (hm3 : m3.perm = m0.perm) (hmf : mf.perm = (m3.mapZero mb len).perm) :
    MmapNewInRegion mb len m0 mf := by
  intro a ha
  rw [hmf, Memory.perm_mapZero] at ha
  split at ha
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact Or.inr hc.1
  · exact Or.inl (hm3 ▸ ha)

set_option maxHeartbeats 400000 in
private theorem blk16_mmapRw_inRegion [MallocngMultiPlacement]
    (tp : BitVec 64) (errnoVal : BitVec 32) (rawLen : Nat)
    (hpos : 0 < rawLen) (hmax : rawLen ≤ 2 ^ 62) :
    let len := pageAlignUp rawLen
    subroutine_ok (mallocngBlockProg mmpl 16 msvc) (mbase 16) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = 0#64 ∧ (s0.readReg64 .x1).toNat = rawLen ∧
         s0.readReg32 .x2 = 3#32 ∧ s0.readReg32 .x3 = 0x22#32 ∧
         s0.readReg32 .x4 = BitVec.allOnes 32 ∧ s0.readReg64 .x5 = 0#64⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal)
      post := fun _ s0 sf =>
        ∃∗ mb : BitVec 64,
          ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧
           sf.readReg64 .x0 = mb ∧ mb ≠ 0#64 ∧ mb ≠ BitVec.allOnes 64 ∧
           4096 ∣ mb.toNat ∧ mb.toNat + len ≤ 2 ^ 48 ∧
           MallocngMappedDelta 1 len s0.mem sf.mem ∧
           MmapNewInRegion mb len s0.mem sf.mem⌝ ∗
          stackFrame s0 64 ∗
          ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
          (mb ↦ₛ List.replicate len 0#8) ∗
          memMapped mb len
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         (MallocngSanitizedSvc msvc → MallocngNoGapOrPhys sf len)⌝
    }) := by
  intro len
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have ⟨_hw, _hrange⟩ := hasWords_blk_of_checkSegment (i := 16) (by decide)
    (ws := mmapFnWords) (R := VerifiedLibraries.mallocng_blk16_mmap.relocs) (by decide +kernel)
  have hsys := placed_syscallRet_perm_ok (P := mallocngBlockProg mmpl 16 msvc) (by intro pc; simp) rfl
  simp only [stackFrame, show (64 : Nat) = 8 * 8 by rfl, memRegion_cells _ 8 (by decide)]; cells_unfold
  wp_init x s0; subst m0 tp
  wp_stp64_cl m1 hm1 hcl0 hcl1; wp_step; wp_step; wp_step
  wp_stp64_cl m2 hm2 hcl1 hcl2; wp_step; wp_step; wp_step; wp_step
  wp_if hhi
  · exfalso; rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat] at hhi; omega
  wp_stp64_cl m3 hm3 hcl2 hcl3; wp_steps
  refine step_svc_mmap_rw_rawLen (rawLen := rawLen) MallocngMultiPlacement.svcValid
    (by wp_norm_lhs) (by simp [arm64_norm, *]) (by wp_close_fetch_cl) (by simp [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp [arm64_norm, *]) (by simpa [arm64_norm] using ‹(s0.readReg64 (Reg.gpr 1#5)).toNat = rawLen›)
    hpos ?_ ?_
  · intro mb hmb_ne0 hmb_al hmb_fit
    clear hcl0 hcl1 hcl2
    wp_norm_mbase_pc; wp_step; wp_step; wp_step
    wp_if hccmn
    · wp_step; wp_step; wp_step; wp_step
      have hcl4 := hcl3.of_keepsFrozen (Memory.keepsFrozen_mapZero _ mb len)
      clear hcl3
      wp_call hsys; clear hcl4
      have hmble : mb.toNat ≤ 2 ^ 64 - 4096 := by omega
      have _hmb_ne1 : mb ≠ BitVec.allOnes 64 := by
        intro he; rw [he] at hmb_fit
        have hall : (BitVec.allOnes 64).toNat = 2 ^ 64 - 1 := by decide
        omega
      simp only [hmble, ↓reduceIte, MallocngProcPreserved] at *
      have hperm3 : m3.perm = s0.mem.perm := Eq.trans hm3 (Eq.trans hm2 hm1)
      have _hdelta : MallocngMappedDelta 1 len s0.mem _ :=
        mappedDelta_one_step hperm3 (mappedDelta_mapZero _ mb len) ‹_›
      have _hinReg : MmapNewInRegion mb len s0.mem _ :=
        perm_mapZero_inRegion hperm3 ‹_›
      wp_done
    · exfalso
      have ht := congrArg BitVec.toNat hccmn
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht; omega
  · intro hno R' hmR
    have hperm3 : m3.perm = s0.mem.perm := Eq.trans hm3 (Eq.trans hm2 hm1)
    exact Satisfies.pure_intro
      ⟨rfl, rfl, rfl, hperm3, mappedDelta_of_perm_eq hperm3, hno⟩ (Satisfies.drop_left hmR)

theorem SepWP.step_svc_oom_huge_mmap_placed {prog : Program} {target_pc : BitVec 64}
    {s s0 : State} {P : SepProp} {post : State → SepProp → Prop}
    {svc : State → State} {pc : BitVec 64} {rawLen : Nat}
    (hProgSvc : prog.svc = svc) (hpc : s.pc = pc)
    (hSvc : MallocngSvcValid svc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64) (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x22#64) (hoff : s.readReg64 .x5 = 0#64)
    (hlen_eq : (s.readReg64 .x1).toNat = rawLen) (hGt62 : 2 ^ 62 < rawLen)
    (hfs : s.fs = s0.fs) (htrace : s.trace = s0.trace)
    (hsig : s.sigActions = s0.sigActions) (hperm : s.mem.perm = s0.mem.perm) :
    SepWP prog target_pc s P post
      (fun sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         (MallocngSanitizedSvc svc → MallocngNoGapOrPhys sf (pageAlignUp rawLen))⌝) := by
  apply SepWP.of_reaches_pc
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.system false 0#16) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  have hx8' : s.readReg64 Reg.x8 = SYS_MMAP := hx8
  have hLenNe : s.readReg64 .x1 ≠ 0#64 := by
    intro hZ; rw [hZ] at hlen_eq; simp at hlen_eq; omega
  have hSanNone : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) = none := by
    rw [hlen_eq]; exact huge_rawLen_sanitize_none s.mem _ hGt62
  have hEval : prog.evalInst (.system false 0#16) s = s.setStatus .OutOfMemory := by
    rw [Program.evalInst_svc0, hProgSvc]
    unfold evalSvc; dsimp only
    rw [(hSvc s).2.2.1 hx8', execMmap_oom s hprot hflags hoff hLenNe hSanNone]
    cases s; simp [State.setStatus]
  rw [hEval]
  refine reaches_pc_oom rfl ?_
  rw [satisfies_pure_sepConj]
  refine ⟨⟨by simp [State.setStatus, hfs], by simp [State.setStatus, htrace],
    by simp [State.setStatus, hsig], by simp [State.setStatus, hperm],
    ⟨[], Nat.zero_le 0, Nat.zero_le 0, fun a ha => Or.inl (by simpa [State.setStatus, hperm] using ha)⟩,
    fun _ => Or.inl (huge_rawLen_no_gap _ hGt62)⟩, ?_⟩
  simpa [State.setStatus] using Satisfies.drop_left hm

set_option maxHeartbeats 400000 in
private theorem blk16_mmapRw_huge [MallocngMultiPlacement]
    (tp : BitVec 64) (errnoVal : BitVec 32) (rawLen : Nat)
    (hGt62 : 2 ^ 62 < rawLen) (hLeMax : rawLen ≤ MallocngMaxAllocSize + 20) :
    let len := pageAlignUp rawLen
    subroutine_ok (mallocngBlockProg mmpl 16 msvc) (mbase 16) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = 0#64 ∧ (s0.readReg64 .x1).toNat = rawLen ∧
         s0.readReg32 .x2 = 3#32 ∧ s0.readReg32 .x3 = 0x22#32 ∧
         s0.readReg32 .x4 = BitVec.allOnes 32 ∧ s0.readReg64 .x5 = 0#64⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal)
      post := fun _ _ _ => ⌜False⌝
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         (MallocngSanitizedSvc msvc → MallocngNoGapOrPhys sf len)⌝
    }) := by
  intro len
  rw [mallocngMaxAllocSize_eq] at hLeMax
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have ⟨_hw, _hrange⟩ := hasWords_blk_of_checkSegment (i := 16) (by decide)
    (ws := mmapFnWords) (R := VerifiedLibraries.mallocng_blk16_mmap.relocs) (by decide +kernel)
  simp only [stackFrame, show (64 : Nat) = 8 * 8 by rfl, memRegion_cells _ 8 (by decide)]; cells_unfold
  wp_init x s0; subst m0 tp
  wp_stp64_cl m1 hm1 hcl0 hcl1; wp_step; wp_step; wp_step
  wp_stp64_cl m2 hm2 hcl1 hcl2; wp_step; wp_step; wp_step; wp_step
  wp_if hhi
  · exfalso; rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat] at hhi; omega
  wp_stp64_cl m3 hm3 hcl2 hcl3; wp_steps
  have hperm3 : m3.perm = s0.mem.perm := Eq.trans hm3 (Eq.trans hm2 hm1)
  exact SepWP.step_svc_oom_huge_mmap_placed rfl (by wp_norm_lhs) MallocngMultiPlacement.svcValid
    (by simp [arm64_norm, *]) (by wp_close_fetch_cl)
    (by simp [arm64_norm]) (by simp [arm64_norm, *]) (by simp [arm64_norm, *])
    (by simp [arm64_norm, *])
    (by simpa [arm64_norm] using ‹(s0.readReg64 (Reg.gpr 1#5)).toNat = rawLen›)
    hGt62 rfl rfl rfl hperm3

theorem placed_mmapRw_large_ok [MallocngMultiPlacement] {P : Program}
    (tp : BitVec 64) (errnoVal : BitVec 32) (rawLen : Nat)
    (hpos : 0 < rawLen) (hLeMax : rawLen ≤ MallocngMaxAllocSize + 20)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    let len := pageAlignUp rawLen
    subroutine_ok P (mbase 16) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = 0#64 ∧ (s0.readReg64 .x1).toNat = rawLen ∧
         s0.readReg32 .x2 = 3#32 ∧ s0.readReg32 .x3 = 0x22#32 ∧
         s0.readReg32 .x4 = BitVec.allOnes 32 ∧ s0.readReg64 .x5 = 0#64⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal)
      post := fun _ s0 sf =>
        ∃∗ mb : BitVec 64,
          ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧
           sf.readReg64 .x0 = mb ∧ mb ≠ 0#64 ∧ mb ≠ BitVec.allOnes 64 ∧
           4096 ∣ mb.toNat ∧ mb.toNat + len ≤ 2 ^ 48 ∧
           MallocngMappedDelta 1 len s0.mem sf.mem ∧
           MmapNewInRegion mb len s0.mem sf.mem⌝ ∗
          stackFrame s0 64 ∗
          ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
          (mb ↦ₛ List.replicate len 0#8) ∗
          memMapped mb len
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         (MallocngSanitizedSvc msvc → MallocngNoGapOrPhys sf len)⌝
    }) := by
  intro len
  by_cases h62 : rawLen ≤ 2 ^ 62
  · exact subroutine_ok_block_to_block (j := 16) (by decide)
      (blk16_mmapRw_inRegion tp errnoVal rawLen hpos h62) hext hsvc
  · have hGt62 : 2 ^ 62 < rawLen := by omega
    have hHuge := subroutine_ok_block_to_block (P := P) (j := 16) (by decide)
      (blk16_mmapRw_huge tp errnoVal rawLen hGt62 hLeMax) hext hsvc
    refine subroutine_ok_mono hHuge (fun _ _ _ hp => hp) (fun _ R _ _ hq => ?_)
    refine Satisfies.mono ?_ hq
    dsimp only [withCL]
    rw [sepConj_assoc]
    exact Entails.pure_left fun hf => False.elim hf

theorem oomCond_of_mmap_large {svc : State → State} {req peakCount len : Nat}
    {s0 s_pre sf : State}
    (hLenLo : 4096 ≤ len) (hLenMod : len % 4096 = 0)
    (hLen4115 : len ≤ req + 4115)
    (hProc : MallocngProcPreserved s0 s_pre)
    (hPermPre : s_pre.mem.perm = s0.mem.perm)
    (hOom : sf.fs = s_pre.fs ∧ sf.trace = s_pre.trace ∧ sf.sigActions = s_pre.sigActions ∧
      sf.mem.perm = s_pre.mem.perm ∧ MallocngMappedDelta 0 0 s_pre.mem sf.mem ∧
      (MallocngSanitizedSvc svc → MallocngNoGapOrPhys sf len)) :
    MallocngTightOomCond svc req peakCount s0 sf := by
  obtain ⟨hfs, htr, hsig, hperm, _, hgap⟩ := hOom
  have hperm0 : sf.mem.perm = s0.mem.perm := hperm.trans hPermPre
  have hAlign : req + 8192 ≤ pageAlignUp (req + 8192) := by
    unfold pageAlignUp PAGE_SIZE; omega
  refine ⟨hfs.trans hProc.1, htr.trans hProc.2.1, hsig.trans hProc.2.2.2.2.2.2,
    [], Nat.zero_le _, Nat.zero_le _, fun a ha => Or.inl (hperm0 ▸ ha), fun hsan => ?_⟩
  refine ⟨len, hLenLo, hLenMod, ?_, ?_, hgap hsan⟩
  · rw [MallocngTightStepBound_eq]; omega
  · change 0 + len ≤ MallocngTightTotalBound req peakCount
    rw [MallocngTightTotalBound_eq]; omega

theorem oomCond_of_allocMeta_after_mmap {svc : State → State} {req peakCount len : Nat}
    {s0 s_mid sf : State}
    (hLen4115 : len ≤ req + 4115)
    (hProc : MallocngProcPreserved s0 s_mid)
    (hDelta1 : MallocngMappedDelta 1 len s0.mem s_mid.mem)
    (hOom : MallocngPlacedOomCond svc 1 (allocMetaPlacedByteBound peakCount) s_mid sf) :
    MallocngTightOomCond svc req peakCount s0 sf := by
  obtain ⟨hfs, htr, hsig, ivs, hlen, hsum, hcov, hgap⟩ :=
    MallocngPlacedOomCond.append_delta hProc.1 hProc.2.1 hProc.2.2.2.2.2.2 hDelta1 hOom
  have hStepSum : len + allocMetaPlacedByteBound peakCount ≤ MallocngTightStepBound req peakCount := by
    rw [MallocngTightStepBound_eq, allocMetaPlacedByteBound_eq_metaStep]
    unfold Cost.mallocngMetaStep
    exact Nat.le_trans (by omega) (Nat.le_max_right _ _)
  refine ⟨hfs, htr, hsig, ivs, by omega, Nat.le_trans hsum hStepSum, hcov, fun hsan => ?_⟩
  obtain ⟨sz, hlo, hmod, hhi, hng⟩ := hgap hsan
  refine ⟨sz, hlo, hmod, by omega, ?_, hng⟩
  exact Nat.le_trans hhi hStepSum

theorem oomCond_of_allocSlot {svc : State → State} {sc req peakCount : Nat}
    {s0 s_mid sf : State}
    (hProc : MallocngProcPreserved s0 s_mid)
    (hPerm : s_mid.mem.perm = s0.mem.perm)
    (hOom : MallocngPlacedOomCond svc (2 * (allocSlotDepthBound sc + 1))
      (allocSlotPlacedByteBound sc peakCount) s_mid sf) :
    MallocngTightOomCond svc req peakCount s0 sf := by
  have hd := allocSlotDepthBound_le_three sc
  have hb20 := allocSlotPlacedByteBound_le_slotReserve sc peakCount
  unfold Cost.mallocngSlotReserve Cost.mallocngMetaStep at hb20
  obtain ⟨hfs, htr, hsig, ivs, hl, hs, hc, hgap⟩ := hOom
  have hSB : allocSlotPlacedByteBound sc peakCount ≤ MallocngTightStepBound req peakCount := by
    rw [MallocngTightStepBound_eq]; exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
  refine ⟨hfs.trans hProc.1, htr.trans hProc.2.1, hsig.trans hProc.2.2.2.2.2.2,
    ivs, by omega, Nat.le_trans hs hSB, fun a ha => (hc a ha).imp (fun hm => hPerm ▸ hm) id,
    fun hsan => ?_⟩
  obtain ⟨sz, hlo, hmod, hhi, hng⟩ := hgap hsan
  exact ⟨sz, hlo, hmod, by omega, Nat.le_trans hhi hSB, hng⟩

/-! ## Context `seq` / `unmapSeq` slice and large-group re-bundling -/

private theorem flatMap_unpack64_len_eq (xs : List (BitVec 64)) :
    (xs.flatMap unpack64).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp [unpack64_length, ih]; omega

theorem ctxBytes_seq_split {c : CtxFields}
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (_hUnm : c.unmapSeq.length = 32) (_hBnc : c.bounces.length = 32)
    (hPad : c.seqPad.length = 7) :
    let pre848 := unpack64 c.secret ++ unpack32 c.initDone ++ unpack32 c.mmapCounter ++
      unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
      unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
      unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++
      c.active.flatMap unpack64 ++ c.usageByClass.flatMap unpack64
    let suf15 := c.seqPad ++ unpack64 c.brk
    pre848.length = 848 ∧
    suf15.length = 15 ∧
    c.toBytes = pre848 ++ c.unmapSeq ++ c.bounces ++ [c.seq] ++ suf15 ∧
    (∀ (seq' : BitVec 8) (unmapSeq' : List (BitVec 8)),
      pre848 ++ unmapSeq' ++ c.bounces ++ [seq'] ++ suf15 =
        ({ c with unmapSeq := unmapSeq', seq := seq' }).toBytes) := by
  dsimp only
  have h1 : (c.active.flatMap unpack64).length = 384 := by
    rw [flatMap_unpack64_len_eq, hAct]
  have h2 : (c.usageByClass.flatMap unpack64).length = 384 := by
    rw [flatMap_unpack64_len_eq, hUse]
  refine ⟨by simp [unpack64_length, unpack32_length, h1, h2],
    by simp [unpack64_length, hPad], ?_, ?_⟩
  · simp [CtxFields.toBytes, List.append_assoc]
  · intro seq' unmapSeq'
    simp [CtxFields.toBytes, List.append_assoc]

theorem large_meta_mem_writes (m mb : BitVec 64) (len : Nat) (hLenPos : 8 ≤ len) :
    let gNew := mkLargeGroup m mb len
    let m0 := List.replicate 40 0#8
    let m1 := ByteSlice.write64 m0 16 mb
    let m2 := ByteSlice.write32 m1 28 0#32
    let m3 := ByteSlice.write32 m2 24 0#32
    let m4 := ByteSlice.write64 m3 32 gNew.packedWord
    m1.length = 40 ∧ m2.length = 40 ∧ m3.length = 40 ∧
    m4 = gNew.metaBytes ∧
    ByteSlice.write64 (List.replicate len 0#8) 0 m =
      unpack64 m ++ List.replicate (len - 8) 0#8 := by
  dsimp only
  have hz64 : unpack64 0#64 = [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] := by decide
  have hz32 : unpack32 0#32 = [0#8, 0#8, 0#8, 0#8] := by decide
  have hrep : List.replicate len 0#8 = List.replicate 8 0#8 ++ List.replicate (len - 8) 0#8 := by
    rw [← List.replicate_add, Nat.add_sub_of_le hLenPos]
  rw [hrep]
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  dsimp only [mkLargeGroup, GroupDesc.metaBytes]
  rw [hz64, hz32]
  rfl

theorem large_group_bundle [MallocngMultiPlacement]
    {γ : GhostName} {brkStart brk m mb : BitVec 64}
    {liveCost peakCost len : Nat} {ivs0 : List (BitVec 64 × Nat)}
    {m0 m1 m2 m3 mf : Memory} {st1 : MallocngSt}
    (hwf1 : MallocngWFInflight 1 maddrs.base brkStart brk liveCost peakCost st1)
    (hRes : st1.reservedMetas = [m])
    (hMbNe : mb ≠ 0#64) (hMbDiv : 4096 ∣ mb.toNat)
    (hLenPos : 4096 ≤ len) (hLenMod : len % 4096 = 0)
    (hMbBound : mb.toNat + len ≤ 2 ^ 48)
    (hMmap : MmapNewInRegion mb len m0 m1)
    (h12 : m2.perm = m1.perm)
    (hMeta : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) m2 m3)
    (h3f : mf.perm = m3.perm)
    (hDisjDyn : ∀ r ∈ dynamicRootRegions st1, DisjointRegions r.1 r.2 mb len) :
    let gNew := mkLargeGroup m mb len
    let st2 := mkLargeGroupSt st1 m mb len
    let groupBytes := unpack64 m ++ List.replicate (len - 8) 0#8
    st2.reservedMetas = [] ∧
    totalLiveCount st2 = totalLiveCount st1 ∧
    st2.metaAreas.length = st1.metaAreas.length ∧
    gNew ∈ st2.groups ∧
    0 < gNew.slots.length ∧
    gNew.slots[0]'(by simp [gNew, mkLargeGroup]) = .claimed ∧
    gNew.sc = 63 ∧
    gNew.maplen = len / 4096 ∧
    (gNew.isMmapped = true →
      ∀ a : BitVec 64, InRegion (gNew.slotStart 0) gNew.stride a → st2.byteVal a = 0#8) ∧
    MallocngNoOrphanMappings ivs0 (dynamicRootRegions st2) m0 mf ∧
    MallocngWFInflight 1 maddrs.base brkStart brk liveCost peakCost st2 ∧
    (MallocngLiveAuth γ st1.liveMap ∗
     (maddrs.ctx ↦ₛ ({ st1.ctx with mmapCounter := st1.ctx.mmapCounter + 1#32 }).toBytes) ∗
     (maddrs.lock ↦₃₂ 0#32) ∗
     (maddrs.replaced ↦₃₂ 0#32) ∗
     (maddrs.aaReplaced ↦₃₂ 0#32) ∗
     ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗
     MallocngAuxvState γ st1.auxvPtr st1.auxvSnap ∗
     (m ↦ₛ gNew.metaBytes) ∗
     (mb ↦ₛ groupBytes) ∗
     memMapped mb len ∗
     ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
     ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
     MappedSet st1.masterDom (OwnedMappedByte st1) ⊢
       MallocngCoreStInflightA 1 γ maddrs brkStart brk liveCost peakCost st2) := by
  dsimp only
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMbAl : mb.toNat % 4096 = 0 := Nat.mod_eq_zero_of_dvd hMbDiv
  have hMapPos : 0 < len / 4096 := by omega
  have hCnt : totalLiveCount (mkLargeGroupSt st1 m mb len) = totalLiveCount st1 := by
    simp [totalLiveCount, mkLargeGroupSt, mkLargeGroup, slotLiveCount]
  have hZero : (mkLargeGroup m mb len).isMmapped = true →
      ∀ a : BitVec 64, InRegion ((mkLargeGroup m mb len).slotStart 0)
        (mkLargeGroup m mb len).stride a →
        (mkLargeGroupSt st1 m mb len).byteVal a = 0#8 := by
    intro _ a ha
    have hSt0 : ((mkLargeGroup m mb len).slotStart 0).toNat = mb.toNat + 16 := by
      dsimp only [mkLargeGroup, GroupDesc.slotStart, GroupDesc.storage]
      simp only [Nat.zero_mul, BitVec.add_zero]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hStr : (mkLargeGroup m mb len).stride = len - 16 := by
      dsimp only [mkLargeGroup, GroupDesc.stride]
      simp only [beq_self_eq_true, decide_eq_true hMapPos, Bool.and_self, ↓reduceIte]
      omega
    have haN := (inRegion_iff_toNat (base := (mkLargeGroup m mb len).slotStart 0)
      (n := (mkLargeGroup m mb len).stride) (by omega) a).mp ha
    let k := a.toNat - mb.toNat
    have haEq : a = mb + BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [haEq]
    exact mkLargeGroup_slot_zero hLenPos hMbBound (by omega) (by omega)
  have hNoOrph : MallocngNoOrphanMappings ivs0
      (dynamicRootRegions (mkLargeGroupSt st1 m mb len)) m0 mf := by
    refine mallocngNoOrphanMappings_large_mmap hMmap h12 hMeta h3f ?_ ?_
    · intro iv hiv
      unfold dynamicRootRegions at hiv ⊢
      dsimp only [mkLargeGroupSt, mkLargeGroup]
      simp only [List.filter_cons, decide_eq_true hMapPos, ↓reduceIte, List.map_cons]
      rcases List.mem_append.mp hiv with h123 | hgrp
      · exact List.mem_append_left _ h123
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hgrp)
    · unfold dynamicRootRegions
      dsimp only [mkLargeGroupSt, mkLargeGroup]
      simp only [List.filter_cons, decide_eq_true hMapPos, ↓reduceIte, List.map_cons]
      have hmul : (len / 4096) * 4096 = len := by omega
      rw [hmul]
      exact List.mem_append_right _ List.mem_cons_self
  let dummyBase := mb + BitVec.ofNat 64 len
  have hDummyNat : dummyBase.toNat = mb.toNat + len := by
    dsimp only [dummyBase]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hDisjDummy : DisjointRegions dummyBase 0x5000 mb len :=
    disjointRegions_of_nonwrap (by decide) (by omega) (by omega) (by omega) (Or.inr (by omega))
  have hwf2Dummy := createLargeMmapGroup_wf
    (mallocngWFInflight_change_base (b2 := dummyBase) hwf1)
    hRes hMbNe hMbAl hLenPos hLenMod hMbBound hDisjDummy hDisjDyn
  have hwf2 := mallocngWFInflight_change_base (b2 := maddrs.base) hwf2Dummy
  have hAbs := createLargeMmapGroup_absorb (γ := γ) (A := maddrs) hwf1 hRes hMbNe hMbAl
    hLenPos hLenMod hMbBound hDisjDyn
  exact ⟨rfl, hCnt, rfl, List.mem_cons_self, by simp [mkLargeGroup], rfl, rfl, rfl,
    hZero, hNoOrph, hwf2, hAbs⟩

end VerifiedLibraries.Mallocng.Proofs
