/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedLeavesRuntimeProof
import VerifiedLibraries.Mallocng.Proofs.SyscallWrappersProof

/-!
# Placed VM Syscall Wrapper Proofs

Re-exports `PlacedLeavesRuntimeProof` and proves cross-block `withCL mmpl` contracts for the four
VM syscall wrapper blocks of `VerifiedLibraries.mallocngLib` (`mmap`, `mprotect`, `mremap`, and
`munmap`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

local macro "wp_norm_mbase_pc" : tactic =>
  `(tactic| conv in (mbase _ + _ + _) => rw [BitVec.add_assoc]; simp only [BitVec.reduceAdd])

set_option maxHeartbeats 400000 in
private theorem blk19_munmap [MallocngMultiPlacement]
    (tp addr : BitVec 64) (errnoVal : BitVec 32) (rawLen : Nat)
    (hpos : 0 < rawLen)
    (hal : 4096 ∣ addr.toNat) (hfit : addr.toNat + pageAlignUp rawLen ≤ 2 ^ 48) :
    let len := pageAlignUp rawLen
    subroutine_ok (mallocngBlockProg mmpl 19 msvc) (mbase 19) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = addr ∧ (s0.readReg64 .x1).toNat = rawLen⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        memRegion addr len ∗
        memMapped addr len
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧
         sf.readReg32 .x0 = 0#32 ∧ MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal)
    }) := by
  intro len
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have ⟨_hw, _hrange⟩ := hasWords_blk_of_checkSegment (i := 19) (by decide)
    (ws := munmapFnWords) (R := VerifiedLibraries.mallocng_blk19_munmap.relocs) (by decide +kernel)
  have hvm := placed_vmWait_perm_ok (P := mallocngBlockProg mmpl 19 msvc) (by intro pc; simp) rfl
  have hsys := placed_syscallRet_perm_ok (P := mallocngBlockProg mmpl 19 msvc) (by intro pc; simp) rfl
  simp only [stackFrame, show (64 : Nat) = 8 * 8 by rfl, memRegion_cells _ 8 (by decide)]; cells_unfold
  wp_init x s0; subst m0 tp addr
  wp_stp64_cl m1 hm1 hcl0 hcl1; wp_step; wp_stp64_cl m2 hm2 hcl1 hcl2; wp_steps
  wp_call hvm; simp only [MallocngProcPreserved] at *; wp_steps
  have hcl3 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl _ := ‹_›
  refine SepWP.weaken_pre (P' := memRegion (s0.readReg64 (Reg.gpr 0#5)) len ∗
      memMapped (s0.readReg64 (Reg.gpr 0#5)) len ∗ _) (by sep_frame) ?_
  refine step_svc_munmap_rawLen MallocngMultiPlacement.svcValid (by wp_norm_lhs)
    (by simp [arm64_norm, *]) (by wp_close_fetch_cl)
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simpa [arm64_norm] using ‹_›) hpos hal hfit ?_
  clear hcl0 hcl1 hcl2
  wp_norm_mbase_pc; wp_step
  have hcl4 := hcl3.of_keepsFrozen
    (Memory.keepsFrozen_unmapNonFrozen _ (s0.readReg64 (Reg.gpr 0#5)) len)
  clear hcl3
  wp_call hsys; clear hcl4; wp_steps
  have _hdelta : MallocngMappedDelta 0 0 s0.mem _ :=
    mappedDelta_zero_step (Eq.trans ‹_› (Eq.trans hm2 hm1))
      (mappedDelta_unmapNonFrozen _ (s0.readReg64 (Reg.gpr 0#5)) len) ‹_›
  wp_done

/-- `munmap(addr, rawLen)` (`blk19`, `64` B stack). -/
theorem placed_munmapWrapper_ok [MallocngMultiPlacement] {P : Program}
    (tp addr : BitVec 64) (errnoVal : BitVec 32) (rawLen : Nat)
    (hpos : 0 < rawLen)
    (hal : 4096 ∣ addr.toNat) (hfit : addr.toNat + pageAlignUp rawLen ≤ 2 ^ 48)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    let len := pageAlignUp rawLen
    subroutine_ok P (mbase 19) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = addr ∧ (s0.readReg64 .x1).toNat = rawLen⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        memRegion addr len ∗
        memMapped addr len
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧
         sf.readReg32 .x0 = 0#32 ∧ MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal)
    }) :=
  subroutine_ok_block_to_block (j := 19) (by decide)
    (blk19_munmap tp addr errnoVal rawLen hpos hal hfit) hext hsvc

set_option maxHeartbeats 400000 in
private theorem blk17_mprotectRw [MallocngMultiPlacement]
    (tp addr : BitVec 64) (errnoVal : BitVec 32) (bs : List (BitVec 8)) (len : Nat)
    (hbs : bs.length = len) (hpos : 0 < len) (hl_al : 4096 ∣ len) (ha_al : 4096 ∣ addr.toNat)
    (hfit : addr.toNat + len ≤ 2 ^ 48) :
    subroutine_ok (mallocngBlockProg mmpl 17 msvc) (mbase 17) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = addr ∧
         (s0.readReg64 .x1).toNat = len ∧ s0.readReg32 .x2 = 3#32⌝ ∗
        stackFrame s0 48 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        (addr ↦ₙ bs)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧
         sf.readReg32 .x0 = 0#32 ∧ MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
        stackFrame s0 48 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        (addr ↦ₛ bs)
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         sf.physMemAvail < len⌝
    }) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have ⟨_hw, _hrange⟩ := hasWords_blk_of_checkSegment (i := 17) (by decide)
    (ws := mprotectFnWords) (R := VerifiedLibraries.mallocng_blk17_mprotect.relocs) (by decide +kernel)
  have hsys := placed_syscallRet_perm_ok (P := mallocngBlockProg mmpl 17 msvc) (by intro pc; simp) rfl
  simp only [stackFrame, show (48 : Nat) = 8 * 6 by rfl, memRegion_cells _ 6 (by decide)]; cells_unfold
  wp_init x s0; subst m0 tp addr; wp_stp64_cl m1 hm1 hcl0 hcl1; wp_steps
  have hx0_al := mprotect_align_addr (s0.readReg64 (Reg.gpr 0#5)) ha_al
  have hx1_al := mprotect_align_len (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5))
    len ‹_› ha_al hl_al hfit
  refine SepWP.weaken_pre (P' := ((s0.readReg64 (Reg.gpr 0#5)) ↦ₙ bs) ∗ _) (by sep_frame) ?_
  refine step_svc_mprotect_rw (len := len) MallocngMultiPlacement.svcValid
    (by wp_norm_lhs) (by simp [arm64_norm, *]) (by wp_close_fetch_cl)
    (by simp [arm64_norm]) (by simpa [arm64_norm] using hx0_al)
    (by simp only [arm64_norm]; rw [hx1_al]; exact ‹(s0.readReg64 (Reg.gpr 1#5)).toNat = len›)
    (by simp only [arm64_norm]; bv_bits) hbs hpos hl_al ha_al hfit ?_ ?_
  · clear hcl0
    wp_norm_mbase_pc; wp_step
    have hcl2 := hcl1.of_keepsFrozen
      (Memory.keepsFrozen_setPermNonFrozen _ (s0.readReg64 (Reg.gpr 0#5)) len Perm.rw)
    clear hcl1
    wp_call hsys; clear hcl2; simp only [MallocngProcPreserved] at *; wp_steps
    have _hdelta := mappedDelta_zero_step hm1
      (mappedDelta_setPermNonFrozen _ (s0.readReg64 (Reg.gpr 0#5)) len Perm.rw) ‹_›
    wp_done
  · intro hphys R' hmR
    exact Satisfies.pure_intro
      ⟨rfl, rfl, rfl, hm1, mappedDelta_of_perm_eq hm1, hphys⟩ (Satisfies.drop_left hmR)

/-- `mprotect(addr, len, PROT_READ|PROT_WRITE = 3)` (`blk17`, `48` B stack). -/
theorem placed_mprotectRwWrapper_ok [MallocngMultiPlacement] {P : Program}
    (tp addr : BitVec 64) (errnoVal : BitVec 32) (bs : List (BitVec 8)) (len : Nat)
    (hbs : bs.length = len) (hpos : 0 < len) (hl_al : 4096 ∣ len) (ha_al : 4096 ∣ addr.toNat)
    (hfit : addr.toNat + len ≤ 2 ^ 48)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 17) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = addr ∧
         (s0.readReg64 .x1).toNat = len ∧ s0.readReg32 .x2 = 3#32⌝ ∗
        stackFrame s0 48 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        (addr ↦ₙ bs)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧
         sf.readReg32 .x0 = 0#32 ∧ MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
        stackFrame s0 48 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        (addr ↦ₛ bs)
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         sf.physMemAvail < len⌝
    }) :=
  subroutine_ok_block_to_block (j := 17) (by decide)
    (blk17_mprotectRw tp addr errnoVal bs len hbs hpos hl_al ha_al hfit) hext hsvc

set_option maxHeartbeats 400000 in
private theorem blk16_mmapFixedProtNone [MallocngMultiPlacement]
    (tp addr : BitVec 64) (errnoVal : BitVec 32) (bs : List (BitVec 8)) (len : Nat)
    (hbs : bs.length = len) (hpos : 0 < len) (hl_al : 4096 ∣ len)
    (hmin : 0x10000 ≤ addr.toNat) (ha_al : 4096 ∣ addr.toNat) (hfit : addr.toNat + len ≤ 2 ^ 48) :
    subroutine_ok (mallocngBlockProg mmpl 16 msvc) (mbase 16) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = addr ∧ (s0.readReg64 .x1).toNat = len ∧
         s0.readReg32 .x2 = 0#32 ∧ s0.readReg32 .x3 = 0x32#32 ∧
         s0.readReg32 .x4 = BitVec.allOnes 32 ∧ s0.readReg64 .x5 = 0#64⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (addr ↦ₛ bs)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧
         sf.readReg64 .x0 = addr ∧ MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (addr ↦ₙ List.replicate len 0#8)
    }) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have ⟨_hw, _hrange⟩ := hasWords_blk_of_checkSegment (i := 16) (by decide)
    (ws := mmapFnWords) (R := VerifiedLibraries.mallocng_blk16_mmap.relocs) (by decide +kernel)
  have hvm := placed_vmWait_perm_ok (P := mallocngBlockProg mmpl 16 msvc) (by intro pc; simp) rfl
  have hsys := placed_syscallRet_perm_ok (P := mallocngBlockProg mmpl 16 msvc) (by intro pc; simp) rfl
  simp only [stackFrame, show (64 : Nat) = 8 * 8 by rfl, memRegion_cells _ 8 (by decide)]; cells_unfold
  wp_init x s0; subst m0 tp addr
  wp_stp64_cl m1 hm1 hcl0 hcl1; wp_step; wp_step; wp_step
  wp_stp64_cl m2 hm2 hcl1 hcl2; wp_step; wp_step; wp_step; wp_step
  wp_if hhi
  · exfalso; rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat] at hhi; omega
  wp_stp64_cl m3 hm3 hcl2 hcl3; wp_step; wp_step; wp_step; wp_step
  wp_stp64_cl m4 hm4 hcl3 hcl4; wp_step; wp_call hvm; simp only [MallocngProcPreserved] at *; wp_steps
  have hcl5 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl _ := ‹_›
  refine SepWP.weaken_pre (P' := ((s0.readReg64 (Reg.gpr 0#5)) ↦ₛ bs) ∗ _) (by sep_frame) ?_
  refine step_svc_mmap_fixed_protNone (len := len) MallocngMultiPlacement.svcValid
    (by wp_norm_lhs) (by simp [arm64_norm, *]) (by wp_close_fetch_cl)
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simpa [arm64_norm] using ‹(s0.readReg64 (Reg.gpr 1#5)).toNat = len›)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp [arm64_norm, *])
    hbs hpos hl_al hmin ha_al hfit ?_
  intro hmap_pre
  clear hcl0 hcl1 hcl2 hcl3 hcl4
  wp_norm_mbase_pc; wp_step; wp_step; wp_step
  wp_if hccmn
  · wp_step; wp_step; wp_step; wp_step
    have hcl6 := hcl5.of_keepsFrozen
      (Memory.keepsFrozen_mmapFixedProtNone _ (s0.readReg64 (Reg.gpr 0#5)) len)
    clear hcl5
    wp_call hsys; clear hcl6
    have hale : (s0.readReg64 (Reg.gpr 0#5)).toNat ≤ 2 ^ 64 - 4096 := by omega
    simp only [hale, ↓reduceIte] at *
    have _hdelta : MallocngMappedDelta 0 0 s0.mem _ :=
      mappedDelta_zero_step (Eq.trans ‹_› (Eq.trans hm4 (Eq.trans hm3 (Eq.trans hm2 hm1))))
        (mappedDelta_mmapFixedProtNone hmap_pre) ‹_›
    wp_done
  · exfalso
    have hne0 : s0.readReg64 (Reg.gpr 0#5) ≠ 0#64 := fun hz => by
      rw [hz, BitVec.toNat_ofNat] at hmin; omega
    simp only [hne0, ↓reduceIte] at hccmn; exact hccmn trivial

/-- `__mmap(addr, len, PROT_NONE = 0, MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED = 0x32, -1, 0)` (`blk16`). -/
theorem placed_mmapFixedProtNoneWrapper_ok [MallocngMultiPlacement] {P : Program}
    (tp addr : BitVec 64) (errnoVal : BitVec 32) (bs : List (BitVec 8)) (len : Nat)
    (hbs : bs.length = len) (hpos : 0 < len) (hl_al : 4096 ∣ len)
    (hmin : 0x10000 ≤ addr.toNat) (ha_al : 4096 ∣ addr.toNat) (hfit : addr.toNat + len ≤ 2 ^ 48)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 16) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = addr ∧ (s0.readReg64 .x1).toNat = len ∧
         s0.readReg32 .x2 = 0#32 ∧ s0.readReg32 .x3 = 0x32#32 ∧
         s0.readReg32 .x4 = BitVec.allOnes 32 ∧ s0.readReg64 .x5 = 0#64⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (addr ↦ₛ bs)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧
         sf.readReg64 .x0 = addr ∧ MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (addr ↦ₙ List.replicate len 0#8)
    }) :=
  subroutine_ok_block_to_block (j := 16) (by decide)
    (blk16_mmapFixedProtNone tp addr errnoVal bs len hbs hpos hl_al hmin ha_al hfit) hext hsvc

set_option maxHeartbeats 400000 in
private theorem blk16_mmapRw [MallocngMultiPlacement]
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
           MallocngMappedDelta 1 len s0.mem sf.mem⌝ ∗
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
      have _hdelta : MallocngMappedDelta 1 len s0.mem _ :=
        mappedDelta_one_step (Eq.trans hm3 (Eq.trans hm2 hm1)) (mappedDelta_mapZero _ mb len) ‹_›
      wp_done
    · exfalso
      have ht := congrArg BitVec.toNat hccmn
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht; omega
  · intro hno R' hmR
    have hperm3 : m3.perm = s0.mem.perm := Eq.trans hm3 (Eq.trans hm2 hm1)
    exact Satisfies.pure_intro
      ⟨rfl, rfl, rfl, hperm3, mappedDelta_of_perm_eq hperm3, hno⟩ (Satisfies.drop_left hmR)

/-- `__mmap(0, rawLen, PROT_READ|PROT_WRITE = 3, MAP_PRIVATE|MAP_ANONYMOUS = 0x22, -1, 0)` (`blk16`). -/
theorem placed_mmapRwWrapper_ok [MallocngMultiPlacement] {P : Program}
    (tp : BitVec 64) (errnoVal : BitVec 32) (rawLen : Nat)
    (hpos : 0 < rawLen) (hmax : rawLen ≤ 2 ^ 62)
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
           MallocngMappedDelta 1 len s0.mem sf.mem⌝ ∗
          stackFrame s0 64 ∗
          ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
          (mb ↦ₛ List.replicate len 0#8) ∗
          memMapped mb len
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         (MallocngSanitizedSvc msvc → MallocngNoGapOrPhys sf len)⌝
    }) :=
  subroutine_ok_block_to_block (j := 16) (by decide)
    (blk16_mmapRw tp errnoVal rawLen hpos hmax) hext hsvc

set_option maxHeartbeats 400000 in
private theorem blk16_mmapProtNone [MallocngMultiPlacement]
    (tp : BitVec 64) (errnoVal : BitVec 32) (rawLen : Nat)
    (hpos : 0 < rawLen) (hmax : rawLen ≤ 2 ^ 62) :
    let len := pageAlignUp rawLen
    subroutine_ok (mallocngBlockProg mmpl 16 msvc) (mbase 16) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = 0#64 ∧ (s0.readReg64 .x1).toNat = rawLen ∧
         s0.readReg32 .x2 = 0#32 ∧ s0.readReg32 .x3 = 0x22#32 ∧
         s0.readReg32 .x4 = BitVec.allOnes 32 ∧ s0.readReg64 .x5 = 0#64⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal)
      post := fun _ s0 sf =>
        ∃∗ mb : BitVec 64,
          ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧
           sf.readReg64 .x0 = mb ∧ mb ≠ 0#64 ∧ mb ≠ BitVec.allOnes 64 ∧
           4096 ∣ mb.toNat ∧ mb.toNat + len ≤ 2 ^ 48 ∧
           MallocngMappedDelta 1 len s0.mem sf.mem⌝ ∗
          stackFrame s0 64 ∗
          ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
          (mb ↦ₙ List.replicate len 0#8) ∗
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
  refine step_svc_mmap_protNone_rawLen (rawLen := rawLen) MallocngMultiPlacement.svcValid
    (by wp_norm_lhs) (by simp [arm64_norm, *]) (by wp_close_fetch_cl) (by simp [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp [arm64_norm, *]) (by simpa [arm64_norm] using ‹(s0.readReg64 (Reg.gpr 1#5)).toNat = rawLen›)
    hpos ?_ ?_
  · intro mb hmb_ne0 hmb_al hmb_fit
    clear hcl0 hcl1 hcl2
    wp_norm_mbase_pc; wp_step; wp_step; wp_step
    wp_if hccmn
    · wp_step; wp_step; wp_step; wp_step
      have hcl4 := hcl3.of_keepsFrozen (Memory.keepsFrozen_mapZero_protNone _ mb len)
      clear hcl3
      wp_call hsys; clear hcl4
      have hmble : mb.toNat ≤ 2 ^ 64 - 4096 := by omega
      have _hmb_ne1 : mb ≠ BitVec.allOnes 64 := by
        intro he; rw [he] at hmb_fit
        have hall : (BitVec.allOnes 64).toNat = 2 ^ 64 - 1 := by decide
        omega
      simp only [hmble, ↓reduceIte, MallocngProcPreserved] at *
      have _hdelta : MallocngMappedDelta 1 len s0.mem _ :=
        mappedDelta_one_step (Eq.trans hm3 (Eq.trans hm2 hm1))
          (mappedDelta_mapZeroProtNone _ mb len) ‹_›
      wp_done
    · exfalso
      have ht := congrArg BitVec.toNat hccmn
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht; omega
  · intro hno R' hmR
    have hperm3 : m3.perm = s0.mem.perm := Eq.trans hm3 (Eq.trans hm2 hm1)
    exact Satisfies.pure_intro
      ⟨rfl, rfl, rfl, hperm3, mappedDelta_of_perm_eq hperm3, hno⟩ (Satisfies.drop_left hmR)

/-- `__mmap(0, rawLen, PROT_NONE = 0, MAP_PRIVATE|MAP_ANONYMOUS = 0x22, -1, 0)` (`blk16`). -/
theorem placed_mmapProtNoneWrapper_ok [MallocngMultiPlacement] {P : Program}
    (tp : BitVec 64) (errnoVal : BitVec 32) (rawLen : Nat)
    (hpos : 0 < rawLen) (hmax : rawLen ≤ 2 ^ 62)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    let len := pageAlignUp rawLen
    subroutine_ok P (mbase 16) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = 0#64 ∧ (s0.readReg64 .x1).toNat = rawLen ∧
         s0.readReg32 .x2 = 0#32 ∧ s0.readReg32 .x3 = 0x22#32 ∧
         s0.readReg32 .x4 = BitVec.allOnes 32 ∧ s0.readReg64 .x5 = 0#64⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal)
      post := fun _ s0 sf =>
        ∃∗ mb : BitVec 64,
          ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧
           sf.readReg64 .x0 = mb ∧ mb ≠ 0#64 ∧ mb ≠ BitVec.allOnes 64 ∧
           4096 ∣ mb.toNat ∧ mb.toNat + len ≤ 2 ^ 48 ∧
           MallocngMappedDelta 1 len s0.mem sf.mem⌝ ∗
          stackFrame s0 64 ∗
          ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
          (mb ↦ₙ List.replicate len 0#8) ∗
          memMapped mb len
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         (MallocngSanitizedSvc msvc → MallocngNoGapOrPhys sf len)⌝
    }) :=
  subroutine_ok_block_to_block (j := 16) (by decide)
    (blk16_mmapProtNone tp errnoVal rawLen hpos hmax) hext hsvc

set_option maxHeartbeats 800000 in
private theorem blk18_mremap [MallocngMultiPlacement]
    (tp oldAddr : BitVec 64) (errnoVal : BitVec 32) (oldBs : List (BitVec 8))
    (oldLen newRawLen : Nat)
    (hbs : oldBs.length = oldLen) (hposOld : 0 < oldLen) (hdvdOld : 4096 ∣ oldLen)
    (hdvdAddr : 4096 ∣ oldAddr.toNat) (holdFit : oldAddr.toNat + oldLen ≤ 2 ^ 48)
    (hposNew : 0 < newRawLen) :
    let newLen := pageAlignUp newRawLen
    subroutine_ok (mallocngBlockProg mmpl 18 msvc) (mbase 18) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = oldAddr ∧
         (s0.readReg64 .x1).toNat = oldLen ∧ (s0.readReg64 .x2).toNat = newRawLen ∧
         s0.readReg32 .x3 = 1#32⌝ ∗
        stackFrame s0 144 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (oldAddr ↦ₛ oldBs) ∗
        memMapped oldAddr oldLen
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk⌝ ∗
        stackFrame s0 144 ∗
        if sf.readReg64 .x0 = BitVec.allOnes 64 then
          ⌜MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
          ((tp - 0xa4#64) ↦₃₂ 12#32) ∗
          (oldAddr ↦ₛ oldBs) ∗
          memMapped oldAddr oldLen
        else
          ∃∗ newBase : BitVec 64,
            ⌜sf.readReg64 .x0 = newBase ∧ newBase ≠ 0#64 ∧ newBase ≠ BitVec.allOnes 64 ∧
             4096 ∣ newBase.toNat ∧ newBase.toNat + newLen ≤ 2 ^ 48 ∧
             MallocngMappedDelta 1 newLen s0.mem sf.mem⌝ ∗
            ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
            (newBase ↦ₛ (oldBs.take newLen ++ List.replicate (newLen - oldLen) 0#8)) ∗
            memMapped newBase newLen
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         sf.physMemAvail < newLen⌝
    }) := by
  intro newLen
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have ⟨_hw, _hrange⟩ := hasWords_blk_of_checkSegment (i := 18) (by decide)
    (ws := mremapFnWords) (R := VerifiedLibraries.mallocng_blk18_mremap.relocs) (by decide +kernel)
  have herr := placed_errnoLocation_perm_ok (P := mallocngBlockProg mmpl 18 msvc) (by intro pc; simp) rfl
  have hsys := placed_syscallRet_perm_ok (P := mallocngBlockProg mmpl 18 msvc) (by intro pc; simp) rfl
  simp only [stackFrame, show (144 : Nat) = 8 * 18 by rfl, memRegion_cells _ 18 (by decide)]; cells_unfold
  wp_init x s0; subst m0 tp oldAddr
  wp_stp64_cl m1 hm1 hcl0 hcl1; wp_step
  wp_str64_cl m2 hm2 hcl1 hcl2; wp_step
  wp_str64_cl m3 hm3 hcl2 hcl3; wp_step; wp_step; wp_step
  wp_if hhi
  · wp_step; wp_call herr; simp only [MallocngProcPreserved] at *
    have hcl4 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl _ := ‹_›
    wp_step; wp_step; wp_step; wp_str32_cl m4 hm4 hcl4 hcl5; wp_steps
    simp only [Reg.x0]
    have _hdelta : MallocngMappedDelta 0 0 s0.mem _ :=
      mappedDelta_of_perm_eq (Eq.trans hm4 (Eq.trans ‹_› (Eq.trans hm3 (Eq.trans hm2 hm1))))
    wp_done
  · have hmaxNew : newRawLen ≤ 2 ^ 64 - 4096 := by
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat] at hhi; omega
    wp_steps
    refine SepWP.weaken_pre (P' := ((s0.readReg64 (Reg.gpr 0#5)) ↦ₛ oldBs) ∗
        memMapped (s0.readReg64 (Reg.gpr 0#5)) oldLen ∗ _) (by sep_frame) ?_
    refine step_svc_mremap (oldLen := oldLen) (newRawLen := newRawLen)
      MallocngMultiPlacement.svcValid
      (by wp_norm_lhs) (by simp [arm64_norm, *]) (by wp_close_fetch_cl)
      (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simpa [arm64_norm] using ‹(s0.readReg64 (Reg.gpr 1#5)).toNat = oldLen›)
      (by simpa [arm64_norm] using ‹(s0.readReg64 (Reg.gpr 2#5)).toNat = newRawLen›)
      (by simp only [arm64_norm]) hbs hposOld hdvdOld hdvdAddr holdFit hposNew hmaxNew ?_ ?_ ?_
    · clear hcl0 hcl1 hcl2
      wp_norm_mbase_pc; wp_step
      wp_call hsys; clear hcl3
      have hnle : ¬ ((-12#64 : BitVec 64).toNat ≤ 2 ^ 64 - 4096) := by decide
      have herr12 : (0#32 - (-12#64 : BitVec 64).truncate 32) = 12#32 := by decide
      simp only [hnle, herr12, MallocngProcPreserved] at *
      wp_steps; simp only [Reg.x0]
      have _hdelta : MallocngMappedDelta 0 0 s0.mem _ :=
        mappedDelta_of_perm_eq (Eq.trans ‹_› (Eq.trans hm3 (Eq.trans hm2 hm1)))
      wp_done
    · intro newBase hne hdvdNew hfitNew
      clear hcl0 hcl1 hcl2
      wp_norm_mbase_pc; wp_step
      have hcl4 := hcl3.of_keepsFrozen
        (Memory.keepsFrozen_remapRw _ (s0.readReg64 (Reg.gpr 0#5)) oldLen newBase newLen)
      clear hcl3
      wp_call hsys; clear hcl4
      have hnble : newBase.toNat ≤ 2 ^ 64 - 4096 := by omega
      have hnb_ne1 : newBase ≠ BitVec.allOnes 64 := by
        intro he; rw [he] at hfitNew
        have hall : (BitVec.allOnes 64).toNat = 2 ^ 64 - 1 := by decide
        omega
      simp only [hnble, ↓reduceIte, MallocngProcPreserved] at *
      wp_steps; simp only [Reg.x0]
      have _hdelta : MallocngMappedDelta 1 newLen s0.mem _ :=
        mappedDelta_one_step (Eq.trans hm3 (Eq.trans hm2 hm1))
          (mappedDelta_remapRw _ _ oldLen newBase newLen) ‹_›
      wp_done
    · intro hphys R' hmR
      have hperm3 : m3.perm = s0.mem.perm := Eq.trans hm3 (Eq.trans hm2 hm1)
      exact Satisfies.pure_intro
        ⟨rfl, rfl, rfl, hperm3, mappedDelta_of_perm_eq hperm3, hphys⟩ (Satisfies.drop_left hmR)

/-- `__mremap(oldAddr, oldLen, newRawLen, MREMAP_MAYMOVE = 1)` (`blk18`, `144` B stack). -/
theorem placed_mremapWrapper_ok [MallocngMultiPlacement] {P : Program}
    (tp oldAddr : BitVec 64) (errnoVal : BitVec 32) (oldBs : List (BitVec 8))
    (oldLen newRawLen : Nat)
    (hbs : oldBs.length = oldLen) (hposOld : 0 < oldLen) (hdvdOld : 4096 ∣ oldLen)
    (hdvdAddr : 4096 ∣ oldAddr.toNat) (holdFit : oldAddr.toNat + oldLen ≤ 2 ^ 48)
    (hposNew : 0 < newRawLen)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    let newLen := pageAlignUp newRawLen
    subroutine_ok P (mbase 18) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = oldAddr ∧
         (s0.readReg64 .x1).toNat = oldLen ∧ (s0.readReg64 .x2).toNat = newRawLen ∧
         s0.readReg32 .x3 = 1#32⌝ ∗
        stackFrame s0 144 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (oldAddr ↦ₛ oldBs) ∗
        memMapped oldAddr oldLen
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk⌝ ∗
        stackFrame s0 144 ∗
        if sf.readReg64 .x0 = BitVec.allOnes 64 then
          ⌜MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
          ((tp - 0xa4#64) ↦₃₂ 12#32) ∗
          (oldAddr ↦ₛ oldBs) ∗
          memMapped oldAddr oldLen
        else
          ∃∗ newBase : BitVec 64,
            ⌜sf.readReg64 .x0 = newBase ∧ newBase ≠ 0#64 ∧ newBase ≠ BitVec.allOnes 64 ∧
             4096 ∣ newBase.toNat ∧ newBase.toNat + newLen ≤ 2 ^ 48 ∧
             MallocngMappedDelta 1 newLen s0.mem sf.mem⌝ ∗
            ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
            (newBase ↦ₛ (oldBs.take newLen ++ List.replicate (newLen - oldLen) 0#8)) ∗
            memMapped newBase newLen
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         sf.physMemAvail < newLen⌝
    }) :=
  subroutine_ok_block_to_block (j := 18) (by decide)
    (blk18_mremap tp oldAddr errnoVal oldBs oldLen newRawLen hbs hposOld hdvdOld hdvdAddr holdFit hposNew)
    hext hsvc

end VerifiedLibraries.Mallocng.Proofs
