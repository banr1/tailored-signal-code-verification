/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedLeavesRuntimeProof
public import VerifiedLibraries.Mallocng.Proofs.GetMetaHelpers
public import VerifiedLibraries.Mallocng.Proofs.InternalPlaced
import VerifiedLibraries.Mallocng.Proofs.SyscallWrappersProof

/-!
# Shared Placed `__libc_free` Contracts and Helpers

Defines the cross-block `nontrivial_free` contract (`nontrivialFreeTopPlacedSpec`),
permission-tracking wrappers for `__unlock` and `__munmap`, and ghost, stack-frame, and sub-word
helpers shared across the placed `__libc_free` proofs.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Placed `nontrivial_free` Contract and Caller Lift -/

def nontrivialFreeTopPlacedSpec [MallocngMultiPlacement]
    (γ : GhostName) (brkStart : BitVec 64) (b : MallocngBudget)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat) : Spec Unit :=
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = g.metaPtr ∧
       s0.readReg64 .x1 = BitVec.ofNat 64 idx ∧
       g ∈ st.groups ∧
       ∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .claimed⌝ ∗
      stackFrame s0 224 ∗
      MallocngRoTablesA maddrs ∗
      MallocngCoreStInflightA 1 γ maddrs brkStart s0.brk b.liveCost b.peakCost st
    post := fun _ s0 sf =>
      ∃∗ st' : MallocngSt,
        ⌜MallocngProcPreserved s0 sf ∧
         sf.brk = s0.brk ∧
         sf.tpidrEl0 = s0.tpidrEl0 ∧
         sf.mem.perm = s0.mem.perm ∧
         MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         totalLiveCount st' ≤ totalLiveCount st ∧
         (dynamicRootRegions st').length ≤ (dynamicRootRegions st).length ∧
         st'.metaAreas.length ≤ st.metaAreas.length ∧
         Cost.GroupsGrpMono st.groups st'.groups⌝ ∗
        stackFrame s0 224 ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStA γ maddrs brkStart s0.brk b.liveCost b.peakCost st' ∗
        if sf.readReg64 .x1 = 0#64 then
          ⌜dynamicRootRegions st' = dynamicRootRegions st⌝
        else
          let miBase := sf.readReg64 .x0
          let miLen := (sf.readReg64 .x1).toNat
          ⌜0 < miLen ∧
           4096 ∣ miBase.toNat ∧
           4096 ∣ miLen ∧
           miBase.toNat + miLen ≤ 2 ^ 48 ∧
           (∀ a : BitVec 64, MallocngInIntervals (dynamicRootRegions st) a →
             InRegion miBase miLen a ∨ MallocngInIntervals (dynamicRootRegions st') a)⌝ ∗
          memRegion miBase miLen ∗
          memMapped miBase miLen
  }

def NontrivialFreeTopPlacedStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (brkStart : BitVec 64) (b : MallocngBudget)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat),
    subroutine_ok (mallocngBlockProg mmpl 5 msvc) (mbase 5)
      (nontrivialFreeTopPlacedSpec γ brkStart b st g idx)

theorem call_placed_nontrivialFree (h : NontrivialFreeTopPlacedStmt) [MallocngMultiPlacement]
    {P : Program} (γ : GhostName) (brkStart : BitVec 64) (b : MallocngBudget)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 5) (nontrivialFreeTopPlacedSpec γ brkStart b st g idx) :=
  subroutine_ok_block_to_block (j := 5) (by decide) (h γ brkStart b st g idx) hext hsvc

/-! ## Permission-Tracking `__unlock` and `__munmap` Wrappers -/

private theorem blk23_unlockNoop_perm [MallocngMultiPlacement] (lk : BitVec 64) :
    subroutine_ok (mallocngBlockProg mmpl 23 msvc) (mbase 23) {
      pre := fun (_ : Unit) s0 => ⌜s0.readReg64 .x0 = lk⌝ ∗ (lk ↦₃₂ 0#32)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm⌝ ∗ (lk ↦₃₂ 0#32)
    } := by
  have _hw := hasWords_blk_relocFree (i := 23) (by decide)
    (ws := unlockFnWords) (by decide +kernel)
  wp_init x s0; subst lk; wp_steps; wp_done

namespace LibcFreeH
/-- `__unlock(lk)` (`blk23`, `0` B stack): fast-path no-op when `*lk = 0#32`, preserving `mem.perm`. -/
theorem placed_unlockNoop_perm_ok [MallocngMultiPlacement] {P : Program} (lk : BitVec 64)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 23) (withCL mmpl {
      pre := fun (_ : Unit) s0 => ⌜s0.readReg64 .x0 = lk⌝ ∗ (lk ↦₃₂ 0#32)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm⌝ ∗ (lk ↦₃₂ 0#32)
    }) :=
  subroutine_ok_block_to_block_plain (j := 23) (by decide) (blk23_unlockNoop_perm lk) hext hsvc
end LibcFreeH
export LibcFreeH (placed_unlockNoop_perm_ok)

private theorem unmapNonFrozen_mapped_imp {m : Memory} {addr : BitVec 64} {len : Nat}
    (hfit : addr.toNat + len ≤ 2 ^ 48)
    (hfrz : m.allPerm (fun p => !p.frozen) addr len = true) :
    ∀ a : BitVec 64, ((m.unmapNonFrozen addr len).perm a).mapped = true →
      (m.perm a).mapped = true ∧ ¬ InRegion addr len a := by
  intro a hmap
  rw [Memory.perm_unmapNonFrozen] at hmap
  split at hmap
  · simp [Option.mapped] at hmap
  · rename_i hnot
    refine ⟨hmap, fun hIn => hnot ?_⟩
    have ⟨hlo, hhi⟩ := (inRegion_iff_toNat (by omega) a).mp hIn
    have hsub : (a - addr).toNat = a.toNat - addr.toNat := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hlo)]
    have hk : a.toNat - addr.toNat < len := by omega
    have ha_eq : addr + BitVec.ofNat 64 (a.toNat - addr.toNat) = a := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
    have hall := (Memory.allPerm_iff m (fun p => !p.frozen) addr len).mp hfrz (a.toNat - addr.toNat) hk
    rw [ha_eq] at hall
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, hall⟩

private theorem step_svc_munmap_rawLen_unmap {prog : Program} {svc : State → State}
    (hSvc : MallocngSvcValid svc) {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc addr : BitVec 64} {rawLen : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 215#64) (haddr : s.readReg64 .x0 = addr)
    (hlen : (s.readReg64 .x1).toNat = rawLen) (hpos : 0 < rawLen)
    (hal : 4096 ∣ addr.toNat) (hfit : addr.toNat + pageAlignUp rawLen ≤ 2 ^ 48)
    (hok : (∀ a : BitVec 64,
        (((s.mem.unmapNonFrozen addr (pageAlignUp rawLen)).perm a).mapped = true →
          (s.mem.perm a).mapped = true ∧ ¬ InRegion addr (pageAlignUp rawLen) a)) →
      SepWP prog target_pc
        ((((s.writeReg64 .x0 0#64).setPC (pc + 4#64)).setMem
          (s.mem.unmapNonFrozen addr (pageAlignUp rawLen))).setPhysMemAvail
          (s.physMemAvail + s.mem.countRw addr (pageAlignUp rawLen)))
        P post oom)
    (hProgSvc : prog.svc = svc := by rfl) :
    SepWP prog target_pc s
      (memRegion addr (pageAlignUp rawLen) ∗ memMapped addr (pageAlignUp rawLen) ∗ P) post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hm_assoc : s.mem ⊨ memRegion addr (pageAlignUp rawLen) ∗
      (memMapped addr (pageAlignUp rawLen) ∗ (P ∗ R)) := by simpa [sepConj_assoc] using hm
  have hfrz : s.mem.allPerm (fun p => !p.frozen) addr (pageAlignUp rawLen) = true :=
    Satisfies.allPerm_not_frozen_of_memRegion hm_assoc
  exact SepWP.to_reaches_pc
    (step_svc_munmap_rawLen hSvc hpc hrun hfetch hx8 haddr hlen hpos hal hfit
      (hok (unmapNonFrozen_mapped_imp hfit hfrz)) hProgSvc) hm

def MallocngUnmappedRange (addr : BitVec 64) (len : Nat) (m0 mf : Memory) : Prop :=
  ∀ a : BitVec 64, (mf.perm a).mapped = true → (m0.perm a).mapped = true ∧ ¬ InRegion addr len a

private theorem unmap_post_step {m0 m1 m2 m3 : Memory} {addr : BitVec 64} {len : Nat}
    (h01 : m1.perm = m0.perm)
    (h12 : ∀ a : BitVec 64, (m2.perm a).mapped = true → (m1.perm a).mapped = true ∧ ¬ InRegion addr len a)
    (h23 : m3.perm = m2.perm) :
    MallocngUnmappedRange addr len m0 m3 := by
  intro a ha
  rw [h23] at ha
  obtain ⟨h1, h2⟩ := h12 a ha
  rw [h01] at h1
  exact ⟨h1, h2⟩

local macro "wp_norm_mbase_pc" : tactic =>
  `(tactic| conv in (mbase _ + _ + _) => rw [BitVec.add_assoc]; simp only [BitVec.reduceAdd])

set_option maxHeartbeats 400000 in
private theorem blk19_munmap_unmap [MallocngMultiPlacement]
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
         sf.readReg32 .x0 = 0#32 ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         MallocngUnmappedRange addr len s0.mem sf.mem⌝ ∗
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
  refine step_svc_munmap_rawLen_unmap MallocngMultiPlacement.svcValid (by wp_norm_lhs)
    (by simp [arm64_norm, *]) (by wp_close_fetch_cl)
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simpa [arm64_norm] using ‹_›) hpos hal hfit ?_
  intro hunmap
  clear hcl0 hcl1 hcl2
  wp_norm_mbase_pc; wp_step
  have hcl4 := hcl3.of_keepsFrozen
    (Memory.keepsFrozen_unmapNonFrozen _ (s0.readReg64 (Reg.gpr 0#5)) len)
  clear hcl3
  wp_call hsys; clear hcl4; wp_steps
  have _hdelta : MallocngMappedDelta 0 0 s0.mem _ :=
    mappedDelta_zero_step (Eq.trans ‹_› (Eq.trans hm2 hm1))
      (mappedDelta_unmapNonFrozen _ (s0.readReg64 (Reg.gpr 0#5)) len) ‹_›
  have _hunmap :=
    unmap_post_step (Eq.trans ‹_› (Eq.trans hm2 hm1)) hunmap ‹_›
  wp_done

/-- `munmap(addr, rawLen)` (`blk19`, `64` B stack), recording that `[addr, addr + pageAlignUp rawLen)`
    is unmapped in `sf.mem`. -/
theorem placed_munmapWrapper_unmap_ok [MallocngMultiPlacement] {P : Program}
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
         sf.readReg32 .x0 = 0#32 ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         MallocngUnmappedRange addr len s0.mem sf.mem⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal)
    }) :=
  subroutine_ok_block_to_block (j := 19) (by decide)
    (blk19_munmap_unmap tp addr errnoVal rawLen hpos hal hfit) hext hsvc

/-! ## Ghost Update, Interval Accounting, and Stack-Frame Bridges -/

namespace LibcFreeH
theorem sepWP_bupd_pre {prog : Program} {tgt : BitVec 64} {s : State} {P Q : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hUpd : P ⊢ |==> Q) (hwp : SepWP prog tgt s Q post oom) :
    SepWP prog tgt s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  exact SepWP.to_reaches_pc hwp (Satisfies.of_bupd_frame_left hUpd hm)

theorem pageAlignUp_of_dvd_4096 {len : Nat} (h : 4096 ∣ len) : pageAlignUp len = len := by
  obtain ⟨k, rfl⟩ := h
  unfold pageAlignUp PAGE_SIZE
  omega

theorem noOrphanMappings_refl_of_perm_eq {ivs : List (BitVec 64 × Nat)} {m0 mf : Memory}
    (hperm : mf.perm = m0.perm) :
    MallocngNoOrphanMappings ivs ivs m0 mf := by
  intro a hmf hor
  rcases hor with hm0 | hivs
  · rw [hperm, hm0] at hmf; cases hmf
  · exact hivs
end LibcFreeH
export LibcFreeH (sepWP_bupd_pre pageAlignUp_of_dvd_4096 noOrphanMappings_refl_of_perm_eq)

theorem noOrphanMappings_of_munmap {ivs0 ivsf : List (BitVec 64 × Nat)}
    {miBase : BitVec 64} {miLen : Nat} {m0 mf : Memory}
    (hUnmap : MallocngUnmappedRange miBase miLen m0 mf)
    (hCov : ∀ a : BitVec 64, MallocngInIntervals ivs0 a →
      InRegion miBase miLen a ∨ MallocngInIntervals ivsf a) :
    MallocngNoOrphanMappings ivs0 ivsf m0 mf := by
  intro a hmf hor
  obtain ⟨hm0_true, hnotIn⟩ := hUnmap a hmf
  rcases hor with hm0_false | hivs0
  · rw [hm0_true] at hm0_false; cases hm0_false
  · rcases hCov a hivs0 with hIn | hivsf
    · exact absurd hIn hnotIn
    · exact hivsf

theorem countIvsWF_of_nontrivialFree {bf : MallocngBudget} {ivs0 : List (BitVec 64 × Nat)}
    {st1 st' : MallocngSt}
    (hCnt1 : MallocngCountIvsWF bf ivs0 st1)
    (hLiveLe : totalLiveCount st' ≤ totalLiveCount st1)
    (hDynLe : (dynamicRootRegions st').length ≤ (dynamicRootRegions st1).length)
    (hMaLe : st'.metaAreas.length ≤ st1.metaAreas.length)
    (hGrp : Cost.GroupsGrpMono st1.groups st'.groups) :
    MallocngCountIvsWF bf (dynamicRootRegions st') st' := by
  refine ⟨hCnt1.1, Nat.le_trans hLiveLe hCnt1.2.1, rfl, ?_,
    Nat.le_trans hMaLe hCnt1.2.2.2.2.1, hGrp _ hCnt1.2.2.2.2.2⟩
  rw [← hCnt1.2.2.1] at hDynLe
  exact Nat.le_trans hDynLe hCnt1.2.2.2.1

theorem stackFrameAt_272_split_48_224 (sp0 : BitVec 64) :
    stackFrameAt sp0 272 =
      (stackFrameAt (sp0 - 48#64) 224 ∗ cells (sp0 - 48#64) 6) := by
  rw [stackFrameAt_eq_memRegion sp0 272, stackFrameAt_eq_memRegion (sp0 - 48#64) 224]
  have hb1 : sp0 - 272#64 + BitVec.ofNat 64 224 = sp0 - 48#64 := by bv_arith
  have ha1 : sp0 - 48#64 - 224#64 = sp0 - 272#64 := by bv_arith
  rw [memRegion_split (sp0 - 272#64) 224 48 (by omega), hb1,
      memRegion_cells (sp0 - 48#64) 6 (by omega), ha1]

theorem stackFrameAt_272_split_48 (sp0 : BitVec 64) :
    stackFrameAt sp0 272 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        stackFrameAt (sp0 - 48#64) 224 ∗
        ((sp0 - 48#64) ↦₆₄ w0) ∗ ((sp0 - 40#64) ↦₆₄ w1) ∗
        ((sp0 - 32#64) ↦₆₄ w2) ∗ ((sp0 - 24#64) ↦₆₄ w3) ∗
        ((sp0 - 16#64) ↦₆₄ w4) ∗ ((sp0 - 8#64) ↦₆₄ w5) := by
  rw [stackFrameAt_272_split_48_224 sp0]; cells_unfold; exact Entails.refl _

theorem stackFrameAt_272_repack_48 (sp0 : BitVec 64) (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (stackFrameAt (sp0 - 48#64) 224 ∗
      ((sp0 - 48#64) ↦₆₄ w0) ∗ ((sp0 - 40#64) ↦₆₄ w1) ∗
      ((sp0 - 32#64) ↦₆₄ w2) ∗ ((sp0 - 24#64) ↦₆₄ w3) ∗
      ((sp0 - 16#64) ↦₆₄ w4) ∗ ((sp0 - 8#64) ↦₆₄ w5)) ⊢ stackFrameAt sp0 272 := by
  rw [stackFrameAt_272_split_48_224 sp0]; cells_unfold; sep_frame

theorem stackFrameAt_224_split_64 (sp : BitVec 64) :
    stackFrameAt sp 224 = (stackFrameAt sp 64 ∗ stackFrameAt (sp - 64#64) 160) :=
  stackFrameAt_split sp 64 160

theorem stackFrameAt_1024_split_272 (sp : BitVec 64) :
    stackFrameAt sp 1024 = (stackFrameAt sp 272 ∗ stackFrameAt (sp - 272#64) 752) :=
  stackFrameAt_split sp 272 752

/-! ## Sub-Word Split and Bitvector Lemmas -/

theorem pointsTo64_split_lo8 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) = ((a ↦₈ w.extractLsb' 0 8) ∗ ((a + 1#64) ↦ₛ (unpack64 w).drop 1)) := by
  have h : unpack64 w = [w.extractLsb' 0 8] ++ (unpack64 w).drop 1 := by simp [unpack64]
  conv => lhs; rw [pointsTo64_eq_pointsToBytes, h]
  simp only [pointsToBytes_append, pointsToBytes_singleton, List.length_cons, List.length_nil, addr_norm]

theorem pointsTo64_split_lo16 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) = ((a ↦₁₆ w.extractLsb' 0 16) ∗ ((a + 2#64) ↦ₛ (unpack64 w).drop 2)) := by
  have h : unpack64 w = [w.extractLsb' 0 8, w.extractLsb' 8 8] ++ (unpack64 w).drop 2 := by simp [unpack64]
  conv => lhs; rw [pointsTo64_eq_pointsToBytes, h]
  rw [pointsToBytes_append, pointsToBytes2_eq_pointsTo16]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, addr_norm]
  rw [show (w.extractLsb' 8 8 ++ w.extractLsb' 0 8) = w.extractLsb' 0 16 by bv_bits]

theorem hdrB_mask64 (b : BitVec 8) {idx : BitVec 32} (h : b.zeroExtend 32 &&& 0x1f#32 = idx) :
    b.zeroExtend 64 &&& 133143986207#64 = idx.zeroExtend 64 := by subst h; bv_robdd

@[simp, arm64_norm, wp_norm] theorem trunc32_zx64_shl4 (x : BitVec 32) :
    (x.zeroExtend 64 <<< 4).truncate 32 = x <<< 4 := by bv_robdd

namespace LibcFreeH
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

theorem ctx_toBytes_split_secret (ctx : BitVec 64) (c : CtxFields) :
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
    ((BitVec.ofNat 64 sc >>> 0 &&& 0xffffffff#64 |||
      (if (BitVec.ofNat 64 sc).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) <<< 1) = BitVec.ofNat 64 (2 * sc) := by
  have h : (BitVec.ofNat 64 sc).ult 48#64 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change sc % (2 ^ 64) < 48; omega
  rw [show BitVec.ofNat 64 (2 * sc) = BitVec.ofNat 64 sc <<< 1 by bv_omega]
  revert h; bv_robdd

theorem madd32_idx_sc {idx scVal : Nat} (hsc : scVal < 65536) :
    0#32 + BitVec.ofNat 32 idx * (BitVec.ofNat 16 scVal).zeroExtend 32 = BitVec.ofNat 32 (idx * scVal) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt hsc, Nat.mul_mod]

theorem add32_sc_madd {idx scVal : Nat} (hsc : scVal < 65536) :
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

theorem maplen_shr4_sub1_ult_false {m tot : Nat} (hm0 : 0 < m) (hm48 : m * 4096 ≤ 2 ^ 48)
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
end LibcFreeH
export LibcFreeH (split_sizeClass_roTablesAt ctx_toBytes_split_secret bv32_toInt_of_lt31
  bv32_slt_iff_of_lt31 bv32_sle_iff_of_lt31 sxtw32_of_lt31 sxtw_lsl1_sc sxtw_sbfm_sc
  madd32_idx_sc add32_sc_madd sc16_ubfiz_shl4 maplen_shr4_sub1_ult_false bv64_ult_of_lt
  packedWord_sc63_mask packedWord_maplen_mask packedWord_byte0_and31)

theorem packedWord_ubfx_sc (g : GroupDesc) (hLast : g.lastIdx ≤ 31)
    (hSc : g.sc < 64) (hMap : g.maplen < 2 ^ 52) :
    (((g.packedWord.extractLsb' 0 16).zeroExtend 64 >>> 6) &&& 0x3f#64) = BitVec.ofNat 64 g.sc := by
  have hL := bv64_ult_of_lt (by omega) (Nat.lt_succ_of_le hLast)
  have hS := bv64_ult_of_lt (by omega) hSc
  have hM := bv64_ult_of_lt (k := 2 ^ 52) (by omega) hMap
  dsimp only [GroupDesc.packedWord]; revert hL hS hM; bv_robdd

theorem free_slotEnd_eq {g : GroupDesc} {idx : Nat} (hStr16 : 16 ≤ g.stride)
    (hEnd48 : (g.slotEnd idx).toNat ≤ 2 ^ 48) (hStrLeEnd : g.stride ≤ (g.slotEnd idx).toNat + 4) :
    (g.mem + 16#64) + ((BitVec.ofNat 64 g.stride - 4#64) + BitVec.ofNat 64 idx * BitVec.ofNat 64 g.stride) =
      g.slotEnd idx := by
  have hSub4 : BitVec.ofNat 64 g.stride - 4#64 = BitVec.ofNat 64 (g.stride - 4) := by
    apply BitVec.eq_of_toNat_eq
    have hLe : (4#64 : BitVec 64) ≤ BitVec.ofNat 64 g.stride := by
      simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
    rw [BitVec.toNat_sub_of_le hLe]; simp only [BitVec.toNat_ofNat]; omega
  unfold GroupDesc.slotEnd GroupDesc.slotStart GroupDesc.storage; rw [← BitVec.ofNat_mul, hSub4]; bv_lin

theorem hdr8_ule_0x9f (b : BitVec 8) :
    (b.zeroExtend 64).ule 0x9f#64 = (b.zeroExtend 32).ule 0x9f#32 ∧
    ((b.zeroExtend 64).truncate 32).ule 0x9f#32 = (b.zeroExtend 32).ule 0x9f#32 ∧
    (((b.zeroExtend 64).truncate 32).zeroExtend 64).ule 0x9f#64 = (b.zeroExtend 32).ule 0x9f#32 ∧
    (b >>> 5).zeroExtend 64 = ((b.zeroExtend 32) >>> 5).zeroExtend 64 :=
  ⟨by bv_robdd, by bv_robdd, by bv_robdd, by bv_robdd⟩

end VerifiedLibraries.Mallocng.Proofs
