/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.BV
public import ProofLib.SyscallModels
public import VerifiedLibraries.Mallocng.Spec.Top
public import VerifiedLibraries.Mallocng.Proofs.GhostToken
public import VerifiedLibraries.Mallocng.Proofs.SizeClasses
public import VerifiedLibraries.Mallocng.Proofs.Cells
public import VerifiedLibraries.Mallocng.Proofs.Defs
public import VerifiedLibraries.Mallocng.Proofs.Common
public import VerifiedLibraries.Mallocng.Proofs.Accounting

/-!
# Internal Syscall Instantiations and Budget Bounds

`Syscall.standard` validity proofs (`mallocngSvcValid_standard`, `mallocngSanitizedSvc_standard`),
mapped-delta combinators, recursion-depth and byte-budget bounds for `__malloc_alloc_meta` and
`alloc_slot`, and instruction-word lists.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## `Syscall.standard` Instantiations and Mapped-Delta Helpers -/

theorem mallocngRemapRw_eq_remapRw : mallocngRemapRw = Memory.remapRw := rfl

private theorem standard_eq_execBrk (s : State) (h : s.readReg64 Reg.x8 = SYS_BRK) :
    Syscall.standard s = execBrk s := by
  unfold Syscall.standard Syscall.dispatch
  rw [h]; rfl

private theorem standard_eq_execMunmap (s : State) (h : s.readReg64 Reg.x8 = SYS_MUNMAP) :
    Syscall.standard s = execMunmap s := by
  unfold Syscall.standard Syscall.dispatch
  rw [h]; rfl

private theorem standard_eq_execMmap (s : State) (h : s.readReg64 Reg.x8 = SYS_MMAP) :
    Syscall.standard s = execMmap s := by
  unfold Syscall.standard Syscall.dispatch
  rw [h]; rfl

private theorem standard_eq_execMprotect (s : State) (h : s.readReg64 Reg.x8 = SYS_MPROTECT) :
    Syscall.standard s = execMprotect s := by
  unfold Syscall.standard Syscall.dispatch
  rw [h]; rfl

private theorem standard_eq_execMremap (s : State) (h : s.readReg64 Reg.x8 = MALLOCNG_SYS_MREMAP) :
    Syscall.standard s = execMremap s := by
  unfold Syscall.standard Syscall.dispatch
  rw [h]; rfl

theorem mallocngSvcValid_standard : MallocngSvcValid Syscall.standard := by
  intro s
  refine ⟨standard_eq_execBrk s, standard_eq_execMunmap s, standard_eq_execMmap s,
    fun h8 _ => standard_eq_execMprotect s h8, ?_⟩
  intro h8 hflags hal holdPos hnewPos hnewMax hfit hperm hanon
  rw [standard_eq_execMremap s h8]
  have hflags' : s.readReg64 Reg.x3 = MREMAP_MAYMOVE := hflags
  have holdNe : s.readReg64 Reg.x1 ≠ 0#64 := by
    intro hz; rw [hz] at holdPos; contradiction
  have hnewNe : s.readReg64 Reg.x2 ≠ 0#64 := by
    intro hz; rw [hz] at hnewPos; contradiction
  cases hmf : s.oracle.mremapFail s.oracleIdx with
  | true =>
    exact Or.inl (execMremap_enomem_of_fail s hflags' hal holdNe hnewNe hnewMax hfit hperm hanon (Or.inl hmf))
  | false =>
    cases hsan : sanitizeMmapAddr
        (s.mem.unmapNonFrozen (s.readReg64 Reg.x0) (pageAlignUp (s.readReg64 Reg.x1).toNat))
        (s.oracle.mmap s.oracleIdx)
        (pageAlignUp (s.readReg64 Reg.x2).toNat) with
    | none =>
      exact Or.inl (execMremap_enomem_of_fail s hflags' hal holdNe hnewNe hnewMax hfit hperm hanon (Or.inr hsan))
    | some newBase =>
      obtain ⟨hne, hnbAl, hnbFit, hnbMap⟩ := sanitizeMmapAddr_spec hsan
      by_cases hphys : pageAlignUp (s.readReg64 Reg.x2).toNat ≤
          s.physMemAvail + pageAlignUp (s.readReg64 Reg.x1).toNat
      · refine Or.inr (Or.inr ⟨newBase, hne, hnbAl, hnbFit, hnbMap, ?_⟩)
        rw [mallocngRemapRw_eq_remapRw]
        exact execMremap_ok s hflags' hal holdNe hnewNe hnewMax hfit hperm hanon hmf hsan hphys
      · refine Or.inr (Or.inl ⟨by omega, ?_⟩)
        exact execMremap_oom s hflags' hal holdNe hnewNe hnewMax hfit hperm hanon hmf hsan (by omega)

theorem mallocngSanitizedSvc_standard : MallocngSanitizedSvc Syscall.standard := by
  intro s hrun h8 hprot hflags hoff hlen hoom
  by_cases hgap : MallocngHasGap s.mem (pageAlignUp (s.readReg64 Reg.x1).toNat)
  · obtain ⟨gap, hmin, hgapAl, hfit, hmap⟩ := hgap
    rw [standard_eq_execMmap s h8] at hoom
    have hlenNatPos : 0 < (s.readReg64 Reg.x1).toNat := by
      cases Nat.eq_zero_or_pos (s.readReg64 Reg.x1).toNat with
      | inl hz => exact False.elim (hlen (BitVec.eq_of_toNat_eq hz))
      | inr hp => exact hp
    have hszPos : 0 < pageAlignUp (s.readReg64 Reg.x1).toNat :=
      pageAlignUp_pos_of_ne_zero (by omega)
    have hszAl : pageAlignUp (s.readReg64 Reg.x1).toNat % PAGE_SIZE = 0 :=
      pageAlignUp_mod_pageSize _
    obtain ⟨base, hsan⟩ :=
      sanitizeMmapAddr_exists_of_gap (s.oracle.mmap s.oracleIdx) hszPos hszAl hmin hgapAl hfit hmap
    rcases hprot with hp0 | hp3
    · rw [execMmap_protNone_sanitized_ok s hp0 hflags hoff hlen hsan] at hoom
      cases s
      simp [State.setMem, State.nextOracle, State.writeReg64, State.advancePC] at hrun hoom
      rw [hrun] at hoom
      contradiction
    · by_cases hphys : pageAlignUp (s.readReg64 Reg.x1).toNat ≤ s.physMemAvail
      · rw [execMmap_sanitized_ok s hp3 hflags hoff hlen hsan hphys] at hoom
        cases s
        simp [State.setMem, State.setPhysMemAvail, State.nextOracle, State.writeReg64,
          State.advancePC] at hrun hoom
        rw [hrun] at hoom
        contradiction
      · exact Or.inr (by omega)
  · exact Or.inl hgap

theorem MallocngMappedDelta.refl (k b : Nat) (m : Memory) :
    MallocngMappedDelta k b m m :=
  ⟨[], Nat.zero_le k, Nat.zero_le b, fun _ ha => Or.inl ha⟩

theorem MallocngMappedDelta.mono {k1 k2 b1 b2 : Nat} {m0 mf : Memory}
    (hk : k1 ≤ k2) (hb : b1 ≤ b2) (h : MallocngMappedDelta k1 b1 m0 mf) :
    MallocngMappedDelta k2 b2 m0 mf := by
  obtain ⟨ivs, hlen, hsum, hcov⟩ := h
  exact ⟨ivs, Nat.le_trans hlen hk, Nat.le_trans hsum hb, hcov⟩

theorem MallocngMappedDelta.trans {k1 k2 b1 b2 : Nat} {m0 m1 m2 : Memory}
    (h01 : MallocngMappedDelta k1 b1 m0 m1)
    (h12 : MallocngMappedDelta k2 b2 m1 m2) :
    MallocngMappedDelta (k1 + k2) (b1 + b2) m0 m2 := by
  obtain ⟨ivs1, hl1, hs1, hc1⟩ := h01
  obtain ⟨ivs2, hl2, hs2, hc2⟩ := h12
  refine ⟨ivs1 ++ ivs2, ?_, ?_, ?_⟩
  · rw [List.length_append]; omega
  · rw [List.map_append, List.sum_append]; omega
  · intro a hm2
    rcases hc2 a hm2 with hm1 | ⟨iv, hiv2, hin⟩
    · rcases hc1 a hm1 with hm0 | ⟨iv, hiv1, hin⟩
      · exact Or.inl hm0
      · exact Or.inr ⟨iv, List.mem_append_left ivs2 hiv1, hin⟩
    · exact Or.inr ⟨iv, List.mem_append_right ivs1 hiv2, hin⟩

/-! ## Recursion-Depth and Byte-Budget Bounds -/

/-- Exact upper bound on nested `alloc_slot` -> `alloc_group` -> `alloc_slot` recursion depth
    starting from size class `sc < 48`:
    - `sc ≥ 20`: `2 * stride + 16 ≥ 2320 > 2048` (`PGSZ / 2`), so `0` recursive calls;
    - `sc = 19`: `2 * 1008 + 12 = 2028` -> `p_sc = 23 ≥ 20`, so `≤ 1` recursive call;
    - `14 ≤ sc ≤ 18`: `2 * 400 + 12 = 812` -> `p_sc ≥ 19`, so `≤ 2` recursive calls;
    - `0 ≤ sc ≤ 13`: `cnt * stride + 12 ≥ 332` -> `p_sc ≥ 14`, so `≤ 3` recursive calls. -/
def allocSlotDepthBound (sc : Nat) : Nat :=
  if 20 ≤ sc then 0
  else if 19 ≤ sc then 1
  else if 14 ≤ sc then 2
  else 3

theorem allocSlotDepthBound_le_three (sc : Nat) : allocSlotDepthBound sc ≤ 3 := by
  unfold allocSlotDepthBound
  repeat' split
  all_goals omega

/-- Tight per-call newly-mapped byte budget for `__malloc_alloc_meta()` (`4 MiB + 5 * peakCost`). -/
def allocMetaByteBound (peakCost : Nat) : Nat :=
  4 * 1024 * 1024 + 5 * peakCost

/-- Tight inductive newly-mapped byte budget for `alloc_slot(sc, req)` across recursion depth
    `allocSlotDepthBound sc ≤ 3` (`≤ 20 MiB + 20 * peakCost ≤ MallocngBaseOverhead + MallocngLinearFactor * peakCost`). -/
def allocSlotByteBound (sc peakCost : Nat) : Nat :=
  (allocSlotDepthBound sc + 1) * (5 * 1024 * 1024 + 5 * peakCost)

/-- Composable OOM postcondition with explicit interval budget `maxIvs` and byte budget `maxBytes`. -/
def MallocngInternalOomCond (svc : State → State) (maxIvs maxBytes : Nat) (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
  sf.trace = s0.trace ∧
  MallocngMappedDelta maxIvs maxBytes s0.mem sf.mem ∧
  (MallocngSanitizedSvc svc →
    ∃ sz : Nat,
      PAGE_SIZE ≤ sz ∧
      sz % PAGE_SIZE = 0 ∧
      sz ≤ maxBytes ∧
      MallocngNoGapOrPhys sf sz)

theorem allocSlotByteBound_le_overhead (sc peakCost : Nat) :
    allocSlotByteBound sc peakCost ≤ MallocngBaseOverhead + MallocngLinearFactor * peakCost := by
  have hd := allocSlotDepthBound_le_three sc
  unfold allocSlotByteBound MallocngBaseOverhead MallocngLinearFactor
  have hmul : (allocSlotDepthBound sc + 1) * (5 * 1024 * 1024 + 5 * peakCost) ≤
      4 * (5 * 1024 * 1024 + 5 * peakCost) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## Instruction-Word and Relocation Projections -/

def errnoLocation3Words : List (BitVec 32) := [0xd53bd040#32, 0xd1029000#32, 0xd65f03c0#32]

def syscallRetWords : List (BitVec 32) := [
  0xa9be7bfd#32, 0xb140041f#32, 0x910003fd#32, 0xf9000bf3#32, 0xaa0003f3#32, 0x54000088#32, 0xf9400bf3#32, 0xa8c27bfd#32, 0xd65f03c0#32, 0x94000000#32,
  0xaa0003e1#32, 0x4b1303f3#32, 0x92800000#32, 0xb9000033#32, 0x17fffff8#32]

def mallocImplWords : List (BitVec 32) := [
  0xa9bb7bfd#32, 0x92820021#32, 0xf2efffe1#32, 0x910003fd#32, 0xeb01001f#32, 0x54000da8#32, 0xa90153f3#32, 0xaa0003f4#32, 0xd29ffd60#32, 0xa9025bf5#32,
  0xf2a00020#32, 0xeb00029f#32, 0xa90363f7#32, 0xf90023f9#32, 0x54000d48#32, 0x91000e93#32, 0xf1027e7f#32, 0xd344fe73#32, 0x540003c9#32, 0x91000661#32,
  0x529cc524#32, 0x72a0ed64#32, 0x90000003#32, 0x53027c20#32, 0x91000063#32, 0x2a410400#32, 0x90000002#32, 0x91000042#32, 0x2a400800#32, 0x2a401000#32,
  0x2a402000#32, 0x11000405#32, 0x0a2000a0#32, 0x1b047c00#32, 0x531b7c00#32, 0x38604873#32, 0x51000673#32, 0x531e7673#32, 0x11000663#32, 0x11000a60#32,
  0x7863d843#32, 0xeb03003f#32, 0x1a938013#32, 0x93407e75#32, 0x7873d840#32, 0xeb00003f#32, 0x54000069#32, 0x11000673#32, 0x93407e75#32, 0x90000000#32,
  0x91000000#32, 0x90000018#32, 0x39400c00#32, 0x72001c1f#32, 0x54001081#32, 0x91002aa0#32, 0x90000019#32, 0x91000321#32, 0xf8607836#32, 0xf10002df#32,
  0x7a430a64#32, 0x540002ed#32, 0x71007e7f#32, 0x7a46da64#32, 0x54000fa0#32, 0x37000f93#32, 0x9100eab5#32, 0xf8757820#32, 0xb5000f20#32, 0x32000262#32,
  0x93407c40#32, 0x91002803#32, 0x9100e800#32, 0xf8637836#32, 0xf8607820#32, 0xb40000b6#32, 0xb9401ac1#32, 0x35000081#32, 0xb9401ec1#32, 0x35000041#32,
  0x91000c00#32, 0xf100301f#32, 0x54000d68#32, 0x2a0203f3#32, 0xb4000d36#32, 0xb9401ac1#32, 0x4b0103e2#32, 0x6a010042#32, 0x54000ca0#32, 0x4b0203e0#32,
  0x529cc524#32, 0x0a020000#32, 0x72a0ed64#32, 0x90000003#32, 0x91000063#32, 0x91000339#32, 0x4b020021#32, 0x1b047c00#32, 0xb9001ac1#32, 0xb9400f33#32,
  0x531b7c00#32, 0x38604877#32, 0x92401ef5#32, 0x91000300#32, 0x94000000#32, 0x394082c0#32, 0xf240101f#32, 0x54000c01#32, 0xf94012c4#32, 0xf274cc9f#32,
  0x54000ba0#32, 0x9274cc84#32, 0xd1004084#32, 0x14000060#32, 0x94000000#32, 0xaa0003e1#32, 0x52800182#32, 0xd2800000#32, 0xb9000022#32, 0x1400009a#32,
  0x91005295#32, 0xd2800005#32, 0xaa1503e1#32, 0x12800004#32, 0x52800443#32, 0x52800062#32, 0xd2800000#32, 0x94000000#32, 0xaa0003f3#32, 0xb100041f#32,
  0x54000640#32, 0x90000000#32, 0x91000000#32, 0x90000018#32, 0x39400c00#32, 0x72001c1f#32, 0x54000361#32, 0x90000019#32, 0x91000322#32, 0x394e4040#32,
  0x7103fc1f#32, 0x54000320#32, 0x11000400#32, 0x390e4040#32, 0x94000000#32, 0xaa0003f6#32, 0xb40003a0#32, 0x91000320#32, 0xf9000ad3#32, 0xf9000276#32,
  0xd2820261#32, 0x8b010282#32, 0xb9001edf#32, 0xb9400c01#32, 0x9274cc42#32, 0xb27b1842#32, 0xd2800015#32, 0x11000433#32, 0x52800017#32, 0xb9000c13#32,
  0xb9001adf#32, 0xf90012c2#32, 0x17ffffc5#32, 0x91000300#32, 0x94000000#32, 0x17ffffe4#32, 0x910d4041#32, 0x910dc042#32, 0x3800143f#32, 0xeb01005f#32,
  0x54ffffc1#32, 0x91000320#32, 0x52800021#32, 0x390e4001#32, 0x17ffffe2#32, 0x91000300#32, 0x94000000#32, 0xaa1503e1#32, 0xaa1303e0#32, 0x94000000#32,
  0xd2800000#32, 0xa94153f3#32, 0xa9425bf5#32, 0xa94363f7#32, 0xf94023f9#32, 0x14000058#32, 0x91000300#32, 0x94000000#32, 0x17ffff7b#32, 0xaa1403e1#32,
  0x2a1303e0#32, 0x94000000#32, 0x2a0003f7#32, 0x37f800e0#32, 0x91000320#32, 0x93407ef5#32, 0x8b33cc02#32, 0xb9400c13#32, 0xf9402856#32, 0x17ffffa0#32,
  0x91000300#32, 0x94000000#32, 0x17ffffea#32, 0x794042c1#32, 0x90000000#32, 0x91000000#32, 0xd3462c21#32, 0x78617804#32, 0xd37c3c84#32, 0xf9400ac2#32,
  0xcb140083#32, 0xd1001086#32, 0xd1001063#32, 0x91004042#32, 0x12001e61#32, 0xd344fc65#32, 0x9b150880#32, 0x8b060006#32, 0x385fd004#32, 0x34000084#32,
  0x785fe001#32, 0x11000421#32, 0x12001c21#32, 0x385fc004#32, 0x34000084#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0xeb21c0bf#32, 0x54000182#32,
  0xaa4314a3#32, 0x2a2503e7#32, 0xaa430863#32, 0xaa431063#32, 0x0a030028#32, 0x0a030021#32, 0xeb0100bf#32, 0x0b070101#32, 0x1a883021#32, 0xeb21c0bf#32,
  0x54fffe23#32, 0x34000121#32, 0x531c6c22#32, 0x128003e3#32, 0x381fd003#32, 0x781fe001#32, 0x8b22c000#32, 0x381fc01f#32, 0xf9400ac2#32, 0x91004042#32,
  0xcb020002#32, 0x12001ee1#32, 0x381fd001#32, 0xcb0000c3#32, 0xd344fc42#32, 0x781fe002#32, 0x6b140074#32, 0x54000120#32, 0x4b1403e1#32, 0x7100129f#32,
  0x3821c8df#32, 0x540001cd#32, 0x381fb0df#32, 0x52801404#32, 0xb81fc0d4#32, 0x385fd001#32, 0x12001021#32, 0x0b010081#32, 0x381fd001#32, 0xa94153f3#32,
  0xa9425bf5#32, 0xa94363f7#32, 0xf94023f9#32, 0xa8c57bfd#32, 0xd65f03c0#32, 0x385fd001#32, 0x531b0a84#32, 0x17fffff5#32]

abbrev mallocImplRelocs : List Obj.RelocEntry := VerifiedLibraries.mallocng_blk09_libc_malloc_impl.relocs

def vmWaitWords : List (BitVec 32) := [0xd65f03c0#32]

def mmapFnWords : List (BitVec 32) := [
  0xa9bc7bfd#32, 0xf2402cbf#32, 0x910003fd#32, 0x54000381#32, 0xa90153f3#32, 0xaa0003f4#32, 0xb27ff7e0#32, 0xeb00003f#32, 0x540003a8#32, 0xa9025bf5#32,
  0x2a0303f3#32, 0x2a0203f6#32, 0x2a0403f5#32, 0x372003b3#32, 0x93407ec2#32, 0x93407ea4#32, 0xaa1403e0#32, 0x93407e63#32, 0xd2801bc8#32, 0xd4000001#32,
  0xf100029f#32, 0xba410800#32, 0x540000a1#32, 0x121c0673#32, 0x92800160#32, 0x7100827f#32, 0xda9f0000#32, 0xa94153f3#32, 0xa9425bf5#32, 0xa8c47bfd#32,
  0x14000000#32, 0x94000000#32, 0x528002c1#32, 0xb9000001#32, 0x92800000#32, 0xa8c47bfd#32, 0xd65f03c0#32, 0x94000000#32, 0x52800181#32, 0xb9000001#32,
  0xa94153f3#32, 0x17fffff9#32, 0xa90317e1#32, 0x94000000#32, 0xa94317e1#32, 0x17ffffe1#32]

abbrev mmapFnRelocs : List Obj.RelocEntry := VerifiedLibraries.mallocng_blk16_mmap.relocs

def mprotectFnWords : List (BitVec 32) := [
  0xa9bf7bfd#32, 0x90000004#32, 0xaa0003e3#32, 0x910003fd#32, 0xf9400084#32, 0xd2801c48#32, 0x93407c42#32, 0xd1000480#32, 0xcb0403e4#32, 0x8b010001#32,
  0x8a040060#32, 0x8b010063#32, 0x8a040061#32, 0xcb000021#32, 0xd4000001#32, 0x94000000#32, 0xa8c17bfd#32, 0xd65f03c0#32]

def mremapFnWords : List (BitVec 32) := [
  0xa9b97bfd#32, 0x910003fd#32, 0xf9000bf3#32, 0x2a0303f3#32, 0xf90037e4#32, 0xb27ff7e3#32, 0xeb03005f#32, 0x54000148#32, 0xd2800004#32, 0x370801d3#32,
  0x93407e63#32, 0xd2801b08#32, 0xd4000001#32, 0x94000000#32, 0xf9400bf3#32, 0xa8c77bfd#32, 0xd65f03c0#32, 0x94000000#32, 0xaa0003e1#32, 0x52800182#32,
  0x92800000#32, 0xb9000022#32, 0x17fffff8#32, 0xa90287e0#32, 0xf9001fe2#32, 0x94000000#32, 0x9101c3e0#32, 0x910183e5#32, 0x128000e3#32, 0xa90403e0#32,
  0xf9002be5#32, 0x290b7fe3#32, 0xf94017e0#32, 0xa9430be1#32, 0xf94037e4#32, 0x17ffffe7#32]

def munmapFnWords : List (BitVec 32) := [
  0xa9be7bfd#32, 0x910003fd#32, 0xa90153f3#32, 0xaa0003f4#32, 0xaa0103f3#32, 0x94000000#32, 0xaa1403e0#32, 0xaa1303e1#32, 0xd2801ae8#32, 0xd4000001#32,
  0x94000000#32, 0xa94153f3#32, 0xa8c27bfd#32, 0xd65f03c0#32]

def memcpyFnWords : List (BitVec 32) := [
  0x8b020024#32, 0x8b020005#32, 0xf102005f#32, 0x540007a8#32, 0xf100805f#32, 0x540003e8#32, 0xf100405f#32, 0x540000c3#32, 0xa9401c26#32, 0xa97f348c#32,
  0xa9001c06#32, 0xa93f34ac#32, 0xd65f03c0#32, 0x361800e2#32, 0xf9400026#32, 0xf85f8087#32, 0xf9000006#32, 0xf81f80a7#32, 0xd65f03c0#32, 0xd503201f#32,
  0x361000c2#32, 0xb9400026#32, 0xb85fc088#32, 0xb9000006#32, 0xb81fc0a8#32, 0xd65f03c0#32, 0xb4000102#32, 0xd341fc4e#32, 0x39400026#32, 0x385ff08a#32,
  0x386e6828#32, 0x39000006#32, 0x382e6808#32, 0x381ff0aa#32, 0xd65f03c0#32, 0xd503201f#32, 0xa9401c26#32, 0xa9412428#32, 0xa97e2c8a#32, 0xa97f348c#32,
  0xf101005f#32, 0x540000e8#32, 0xa9001c06#32, 0xa9012408#32, 0xa93e2caa#32, 0xa93f34ac#32, 0xd65f03c0#32, 0xd503201f#32, 0xa9423c2e#32, 0xa9434430#32,
  0xf101805f#32, 0x540000a9#32, 0xa97c0c82#32, 0xa97d1081#32, 0xa93c0ca2#32, 0xa93d10a1#32, 0xa9001c06#32, 0xa9012408#32, 0xa9023c0e#32, 0xa9034410#32,
  0xa93e2caa#32, 0xa93f34ac#32, 0xd65f03c0#32, 0xd503201f#32, 0xa940342c#32, 0x92400c0e#32, 0x927cec03#32, 0xcb0e0021#32, 0x8b0e0042#32, 0xa9411c26#32,
  0xa900340c#32, 0xa9422428#32, 0xa9432c2a#32, 0xa9c4342c#32, 0xf1024042#32, 0x54000169#32, 0xa9011c66#32, 0xa9411c26#32, 0xa9022468#32, 0xa9422428#32,
  0xa9032c6a#32, 0xa9432c2a#32, 0xa984346c#32, 0xa9c4342c#32, 0xf1010042#32, 0x54fffee8#32, 0xa97c3c8e#32, 0xa9011c66#32, 0xa97d1c86#32, 0xa9022468#32,
  0xa97e2488#32, 0xa9032c6a#32, 0xa97f2c8a#32, 0xa904346c#32, 0xa93c3cae#32, 0xa93d1ca6#32, 0xa93e24a8#32, 0xa93f2caa#32, 0xd65f03c0#32]

def lockFnWords : List (BitVec 32) := [
  0x90000003#32, 0x91000062#32, 0xaa0003e4#32, 0x320107e1#32, 0x39400c42#32, 0x13001c42#32, 0x34000402#32, 0x885ffc80#32, 0x350000e0#32, 0x8800fc81#32,
  0x35ffffa0#32, 0x36f80362#32, 0x91000063#32, 0x39000c7f#32, 0x14000018#32, 0xd5033bbf#32, 0x37f800a2#32, 0x52800143#32, 0x12b00006#32, 0x320107e5#32,
  0x1400000a#32, 0x91000063#32, 0x39000c7f#32, 0x17fffffa#32, 0x0b060002#32, 0x2a0003e1#32, 0x14000007#32, 0xd5033bbf#32, 0x71000463#32, 0x54000140#32,
  0x37ffff40#32, 0x0b050001#32, 0x2a0003e2#32, 0x885ffc80#32, 0x6b00005f#32, 0x54ffff01#32, 0x8800fc81#32, 0x35ffff80#32, 0xd65f03c0#32, 0x885ffc85#32,
  0x110004a5#32, 0x8800fc85#32, 0x35ffffa0#32, 0x12b00007#32, 0x52b00006#32, 0x14000011#32, 0xaa0403e0#32, 0x93407ca2#32, 0xd2800c48#32, 0xd2801001#32,
  0xd2800003#32, 0xd4000001#32, 0xb100981f#32, 0x54000060#32, 0x0b0700a5#32, 0x14000008#32, 0xaa0403e0#32, 0xd2800001#32, 0xd4000001#32, 0x17fffffb#32,
  0xd5033bbf#32, 0x2a0003e5#32, 0x37fffe05#32, 0x0b0600a1#32, 0x885ffc80#32, 0x6b0000bf#32, 0x54ffff41#32, 0x8800fc81#32, 0x35ffff80#32, 0x17ffffe1#32]

def unlockFnWords : List (BitVec 32) := [
  0xaa0003e3#32, 0xb9400000#32, 0x37f80040#32, 0xd65f03c0#32, 0x12b00004#32, 0x885ffc61#32, 0x0b040020#32, 0x8802fc60#32, 0x35ffffa2#32, 0x320107e0#32,
  0x6b00003f#32, 0x54ffff00#32, 0xaa0303e0#32, 0xd2800c48#32, 0xd2801021#32, 0xd2800022#32, 0xd4000001#32, 0xb100981f#32, 0x54fffe21#32, 0xaa0303e0#32,
  0xaa0203e1#32, 0xd4000001#32, 0x17ffffed#32]

end VerifiedLibraries.Mallocng.Proofs
