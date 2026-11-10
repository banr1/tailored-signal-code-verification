/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedLeavesProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocWfHelpers
import VerifiedLibraries.Mallocng.Proofs.SyscallWrappersProof
import VerifiedLibraries.Mallocng.Proofs.MemcpySym

/-!
# Permission-Preserving Leaf Wrappers and In-Place `set_size` Well-Formedness

Proves permission-preserving placed `subroutine_ok` contracts for `memcpy` (`blk20`) and
`__mremap` (`blk18`). Also proves ghost-token replacement, `.liveUser` pointer uniqueness, and
preservation of `MallocngWF` and `MallocngCountIvsWF` across in-place `set_size` updates in
`__libc_realloc`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

local macro "wp_norm_mbase_pc" : tactic =>
  `(tactic| conv in (mbase _ + _ + _) => rw [BitVec.add_assoc]; simp only [BitVec.reduceAdd])

theorem placed_memcpy_perm_ok [MallocngMultiPlacement] {P : Program}
    (dst src : BitVec 64) (dstBs srcBs : List (BitVec 8)) (n : Nat)
    (hdstLen : dstBs.length = n) (hsrcLen : srcBs.length = n)
    (hn63 : n ≤ 2 ^ 63)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 20) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = n⌝ ∗
        (dst ↦ₛ dstBs) ∗ (src ↦ₛ srcBs)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧
          sf.mem.perm = s0.mem.perm ∧ sf.readReg64 .x0 = dst⌝ ∗
        (dst ↦ₛ srcBs) ∗ (src ↦ₛ srcBs)
    }) := by
  refine subroutine_ok_block_to_block_plain (j := 20) (by decide) ?_ hext hsvc
  have hw := hasWords_blk_relocFree (i := 20) (by decide) (ws := memcpyFnWords) (by decide +kernel)
  have hBvN : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hLift := subroutine_ok_lift_pureWords_process
    (P := mallocngBlockProg mmpl 20 msvc)
    (memcpy_pureWords_ok (mbase 20) dst src dstBs srcBs (BitVec.ofNat 64 n)
      (by omega) (by omega) (by omega))
    (memcpy_allInstrs_noSvc_noMsr _)
    hw
    (fun pc => by simp)
    (h_pre_mem := fun _ _ _ => rfl)
    (h_post_mem := fun _ _ _ _ _ => rfl)
  refine subroutine_ok_outcome_intro fun u R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨
      (⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ s0.readReg64 .x2 = BitVec.ofNat 64 n⌝ ∗
        (dst ↦ₛ dstBs) ∗ (src ↦ₛ srcBs)) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left ?_) hpre
    refine Entails.pure_left fun ⟨hx0, hx1, hx2⟩ => ?_
    have hx2Eq : s0.readReg64 .x2 = BitVec.ofNat 64 n :=
      BitVec.eq_of_toNat_eq (hx2.trans hBvN.symm)
    exact Entails.pure_right ⟨hx0, hx1, hx2Eq⟩ (Entails.refl _)
  refine hLift.mono_outcome u R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hp | he | ho
  · refine Or.inl ⟨hret, hcc, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    refine Entails.pure_left fun hpf => Entails.pure_left fun ⟨horc, hsym, hx0f⟩ => ?_
    rcases hpf with ⟨hfs, htr, htp, hsig, hbrk, hbrks, hperm⟩
    exact Entails.pure_right ⟨⟨hfs, htr, htp, hbrks, horc, hsym, hsig⟩, hbrk, funext hperm.2, hx0f⟩
      (Entails.refl _)
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl he))
  · exact Or.inr (Or.inr (Or.inr ho))

set_option maxHeartbeats 400000 in
private theorem blk18_mremap_perm [MallocngMultiPlacement]
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
          ⌜sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
          ((tp - 0xa4#64) ↦₃₂ 12#32) ∗
          (oldAddr ↦ₛ oldBs) ∗
          memMapped oldAddr oldLen
        else
          ∃∗ newBase : BitVec 64,
            ⌜sf.readReg64 .x0 = newBase ∧ newBase ≠ 0#64 ∧ newBase ≠ BitVec.allOnes 64 ∧
             4096 ∣ newBase.toNat ∧ newBase.toNat + newLen ≤ 2 ^ 48 ∧
             MallocngMappedDelta 1 newLen s0.mem sf.mem ∧
             (∃ m1 : Memory, m1.perm = s0.mem.perm ∧
               sf.mem.perm = (m1.remapRw oldAddr oldLen newBase newLen).perm)⌝ ∗
            ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
            (newBase ↦ₛ (oldBs.take newLen ++ List.replicate (newLen - oldLen) 0#8)) ∗
            memMapped newBase newLen
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         sf.physMemAvail + oldLen < newLen⌝
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
    have hperm_fail : m4.perm = s0.mem.perm :=
      Eq.trans hm4 (Eq.trans ‹_› (Eq.trans hm3 (Eq.trans hm2 hm1)))
    have _hdelta : MallocngMappedDelta 0 0 s0.mem _ := mappedDelta_of_perm_eq hperm_fail
    wp_done
  · have hmaxNew : newRawLen ≤ 2 ^ 64 - 4096 := by
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat] at hhi; omega
    wp_steps
    have hm3Perm : m3.perm = s0.mem.perm := Eq.trans hm3 (Eq.trans hm2 hm1)
    refine SepWP.weaken_pre (P' := ((s0.readReg64 (Reg.gpr 0#5)) ↦ₛ oldBs) ∗
        memMapped (s0.readReg64 (Reg.gpr 0#5)) oldLen ∗ _) (by sep_frame) ?_
    refine step_svc_mremap_tight (oldLen := oldLen) (newRawLen := newRawLen)
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
      have hperm_e : _ = s0.mem.perm := Eq.trans ‹_› hm3Perm
      have _hdelta : MallocngMappedDelta 0 0 s0.mem _ := mappedDelta_of_perm_eq hperm_e
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
      wp_steps; simp only [Reg.x0]; dsimp only [newLen]
      have _hdelta : MallocngMappedDelta 1 (pageAlignUp newRawLen) s0.mem _ :=
        mappedDelta_one_step hm3Perm (mappedDelta_remapRw _ _ oldLen newBase (pageAlignUp newRawLen)) ‹_›
      have _hperm_ex1 : ∃ m1 : Memory, m1.perm = s0.mem.perm ∧
          (m3.remapRw (s0.readReg64 (Reg.gpr 0#5)) oldLen newBase (pageAlignUp newRawLen)).perm =
            (m1.remapRw (s0.readReg64 (Reg.gpr 0#5)) oldLen newBase (pageAlignUp newRawLen)).perm :=
        ⟨m3, hm3Perm, rfl⟩
      have _hperm_ex2 : ∃ m_call : Memory, m_call.perm = s0.mem.perm ∧
          _ = (m_call.remapRw (s0.readReg64 (Reg.gpr 0#5)) oldLen newBase (pageAlignUp newRawLen)).perm :=
        ⟨m3, hm3Perm, ‹_›⟩
      wp_done
    · intro hphys R' hmR
      exact Satisfies.pure_intro
        ⟨rfl, rfl, rfl, hm3Perm, mappedDelta_of_perm_eq hm3Perm, hphys⟩ (Satisfies.drop_left hmR)

theorem placed_mremapWrapper_perm_ok [MallocngMultiPlacement] {P : Program}
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
          ⌜sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
          ((tp - 0xa4#64) ↦₃₂ 12#32) ∗
          (oldAddr ↦ₛ oldBs) ∗
          memMapped oldAddr oldLen
        else
          ∃∗ newBase : BitVec 64,
            ⌜sf.readReg64 .x0 = newBase ∧ newBase ≠ 0#64 ∧ newBase ≠ BitVec.allOnes 64 ∧
             4096 ∣ newBase.toNat ∧ newBase.toNat + newLen ≤ 2 ^ 48 ∧
             MallocngMappedDelta 1 newLen s0.mem sf.mem ∧
             (∃ m1 : Memory, m1.perm = s0.mem.perm ∧
               sf.mem.perm = (m1.remapRw oldAddr oldLen newBase newLen).perm)⌝ ∗
            ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
            (newBase ↦ₛ (oldBs.take newLen ++ List.replicate (newLen - oldLen) 0#8)) ∗
            memMapped newBase newLen
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         sf.physMemAvail + oldLen < newLen⌝
    }) :=
  subroutine_ok_block_to_block (j := 18) (by decide)
    (blk18_mremap_perm tp oldAddr errnoVal oldBs oldLen newRawLen hbs hposOld hdvdOld hdvdAddr holdFit hposNew)
    hext hsvc

theorem mallocngBlock_replace_bupd (γ : GhostName) (L : MallocngLiveMap)
    (p1 : BitVec 64) (n1 : Nat) (p2 : BitVec 64) (n2 : Nat)
    (hwf2 : MallocngBlockWf p2 n2)
    (hFresh : p2 = p1 ∨ L p2 = none) :
    MallocngLiveAuth γ L ∗ MallocngBlockToken γ p1 n1 ⊢
      |==> (MallocngLiveAuth γ ((L.erase p1).insert p2 n2 (L.ov p1)) ∗
            MallocngBlockToken γ p2 n2) :=
  mallocngBlock_replaceOv_bupd γ L p1 n1 p2 n2 hwf2 hFresh

theorem liveUser_ptr_unique {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g x : GroupDesc} (hg : g ∈ st.groups) (hx : x ∈ st.groups)
    {idx j : Nat} (hIdx : idx < g.slots.length) (hj : j < x.slots.length)
    {p : BitVec 64} {sz1 eff1 sz2 eff2 : Nat}
    (hS1 : g.slots[idx]'hIdx = .liveUser p sz1 eff1)
    (hS2 : x.slots[j]'hj = .liveUser p sz2 eff2) :
    x = g ∧ j = idx := by
  have hgw := hwf.groups_wf g hg
  have hxw := hwf.groups_wf x hx
  have hsw1 := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx; rw [hS1] at hsw1
  have hsw2 := hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj; rw [hS2] at hsw2
  have ⟨_, _, hSt1, hSub4_1, hEn1, hEndLe1, h48_1, _, hEndMod1⟩ := group_slot_bounds hgw hIdx
  have ⟨_, _, hSt2, hSub4_2, hEn2, hEndLe2, h48_2, _, hEndMod2⟩ := group_slot_bounds hxw hj
  have hpMod16 : p.toNat % 16 = 0 := Nat.mod_eq_zero_of_dvd hsw1.2.2.2.2.1.2.1
  have hLo1 := hsw1.2.2.2.2.2.1; have hHi1 := hsw1.2.2.2.2.2.2.1
  have hLo2 := hsw2.2.2.2.2.2.1; have hHi2 := hsw2.2.2.2.2.2.2.1
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hSM1 : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hSM2 : (j + 1) * x.stride = j * x.stride + x.stride := Nat.succ_mul j x.stride
  have hIn1 : InRegion (g.slotStart idx - 4#64) g.stride p :=
    (inRegion_iff_toNat (by omega) p).mpr ⟨by omega, by omega⟩
  have hIn2 : InRegion (x.slotStart j - 4#64) x.stride p :=
    (inRegion_iff_toNat (by omega) p).mpr ⟨by omega, by omega⟩
  by_cases hSame : g = x ∧ idx = j
  · exact ⟨hSame.1.symm, hSame.2.symm⟩
  · exfalso
    exact nonNested_slotSlice_disjoint hwf hg hIdx (by rw [hS1]; intro _ h; cases h)
      hx hj (by rw [hS2]; intro _ h; cases h)
      (by by_cases hG : g = x; exact Or.inr fun hI => hSame ⟨hG, hI⟩; exact Or.inl hG) hIn1 hIn2

private theorem extractLsb_list_eq_unpack32 (u : BitVec 32) :
    [u.extractLsb' (8 * 0) 8, u.extractLsb' (8 * 1) 8,
     u.extractLsb' (8 * 2) 8, u.extractLsb' (8 * 3) 8] = unpack32 u := by
  simp only [unpack32]

set_option maxHeartbeats 400000 in
theorem reallocInPlace_wf {base brkStart brk : BitVec 64}
    {b : MallocngBudget} {ivs0 : List (BitVec 64 × Nat)} {st : MallocngSt}
    (hCount : MallocngCountIvsWF b ivs0 st)
    (hwf : MallocngWF base brkStart brk b.liveCost b.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff newSz : Nat} (origBs : List (BitVec 8))
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hNewMax : newSz ≤ 131051)
    (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    (slotBsFinal : List (BitVec 8)) (hFinalLen : slotBsFinal.length = g.stride)
    (hKeepPre : ∀ i, i < p.toNat - (g.slotStart idx).toNat + 4 →
      i ≠ p.toNat - (g.slotStart idx).toNat + 1 →
      slotBsFinal.getD i 0#8 = st.byteVal ((g.slotStart idx - 4#64) + BitVec.ofNat 64 i))
    (hHdrP3 : slotBsFinal.getD (p.toNat - (g.slotStart idx).toNat + 1) 0#8 =
      BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
    (hRes1 : 1 ≤ (g.slotEnd idx).toNat - (p.toNat + newSz) →
      slotBsFinal.getD (p.toNat - (g.slotStart idx).toNat + 4 + newSz) 0#8 = 0#8)
    (hRes5 : 5 ≤ (g.slotEnd idx).toNat - (p.toNat + newSz) →
      slotBsFinal.getD (g.stride - 5) 0#8 = 0#8 ∧
      ∀ j < 4, slotBsFinal.getD (g.stride - 4 + j) 0#8 =
        (BitVec.ofNat 32 ((g.slotEnd idx).toNat - (p.toNat + newSz))).extractLsb' (8 * j) 8) :
    let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
    let g' := { g with slots := g.slots.set idx (.liveUser p newSz newEff) }
    let val' := writeBytesToMap st.byteVal (g.slotStart idx - 4#64) slotBsFinal
    let liveMap' := (st.liveMap.erase p).insert p newSz (st.liveMap.ov p)
    let st' := { st with groups := replaceGroup st.groups g.metaPtr g', byteVal := val', liveMap := liveMap' }
    let bf := mallocngReallocBudget true (some (oldSz, origBs)) newSz b
    MallocngBlockWf p newSz ∧
    MallocngCountIvsWF bf ivs0 st' ∧
    MallocngWF base brkStart brk bf.liveCost bf.peakCost st' ∧
    (∀ a, ¬ InRegion (g.slotStart idx - 4#64) g.stride a →
      (OwnedRwByte st' a ↔ OwnedRwByte st a)) ∧
    (∀ a, InRegion (g.slotStart idx - 4#64) g.stride a →
      a ∈ st.masterDom ∧ (OwnedRwByte st' a ↔ ¬ InRegion p newSz a)) := by
  intro newEff g' val' liveMap' st' bf
  have hgw := hwf.groups_wf g hg
  have hswOld := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx; rw [hSlot] at hswOld
  have ⟨_, hStor, hSt, hSub4, hEn, hEndLe, h48G, _, _⟩ := group_slot_bounds hgw hIdx
  have hStrPos := (group_stride_pos_and_align hgw).1
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hLo : (g.slotStart idx).toNat ≤ p.toNat := hswOld.2.2.2.2.2.1
  have hOldFit : p.toNat + oldSz ≤ (g.slotEnd idx).toNat := hswOld.2.2.2.2.2.2.1
  have hOldEfGe : max oldSz MallocngMinBlockCost ≤ oldEff := hswOld.2.2.2.2.2.2.2.1
  obtain ⟨hOldEfTot, _⟩ := liveUser_cost_count_le_totals hg hIdx hSlot
  have hValIn : ∀ i < g.stride, val' ((g.slotStart idx - 4#64) + BitVec.ofNat 64 i) = slotBsFinal.getD i 0#8 := by
    intro i hi
    have hiL : i < slotBsFinal.length := by omega
    have hW := writeBytesToMap_in st.byteVal (g.slotStart idx - 4#64) slotBsFinal hiL (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL]; exact hW
  have hPreVal : ∀ a : BitVec 64, (g.slotStart idx - 4#64).toNat ≤ a.toNat →
      a.toNat < p.toNat → a ≠ p - 3#64 → val' a = st.byteVal a := by
    intro a haLo haHi haNe
    let i := a.toNat - (g.slotStart idx - 4#64).toNat
    have haEq : (g.slotStart idx - 4#64) + BitVec.ofNat 64 i = a := by
      apply BitVec.eq_of_toNat_eq
      rw [bv64_add_toNat (a := g.slotStart idx - 4#64) (n := i) (by omega)]; omega
    have hSubP3 : (p - 3#64).toNat = p.toNat - 3 := bv64_sub_toNat (by omega)
    have hiNe : i ≠ p.toNat - (g.slotStart idx).toNat + 1 := fun hI => haNe (BitVec.eq_of_toNat_eq (by omega))
    rw [← haEq, hValIn i (by omega), hKeepPre i (by omega) hiNe]
  have hHdrVal : val' (p - 3#64) =
      BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx) := by
    have hSubP3 : (p - 3#64).toNat = p.toNat - 3 := bv64_sub_toNat (by omega)
    have hAddr : (g.slotStart idx - 4#64) + BitVec.ofNat 64 (p.toNat - (g.slotStart idx).toNat + 1) = p - 3#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [bv64_add_toNat (by omega)]; omega
    rw [← hAddr, hValIn _ (by omega), hHdrP3]
  have hRes1Val : 1 ≤ (g.slotEnd idx).toNat - (p.toNat + newSz) →
      val' (p + BitVec.ofNat 64 newSz) = 0#8 := fun h1 => by
    have hAddr : (g.slotStart idx - 4#64) + BitVec.ofNat 64 (p.toNat - (g.slotStart idx).toNat + 4 + newSz) =
        p + BitVec.ofNat 64 newSz := by
      apply BitVec.eq_of_toNat_eq
      rw [bv64_add_toNat (by omega), bv64_add_toNat (by omega)]; omega
    rw [← hAddr, hValIn _ (by omega), hRes1 h1]
  have hRes5Val : 5 ≤ (g.slotEnd idx).toNat - (p.toNat + newSz) →
      val' (g.slotEnd idx - 5#64) = 0#8 ∧
      readBytesFromMap val' (g.slotEnd idx - 4#64) 4 =
        unpack32 (BitVec.ofNat 32 ((g.slotEnd idx).toNat - (p.toNat + newSz))) := fun h5 => by
    obtain ⟨hB5, hB4⟩ := hRes5 h5
    have hSubE5 : (g.slotEnd idx - 5#64).toNat = (g.slotEnd idx).toNat - 5 := bv64_sub_toNat (by omega)
    have hSubE4 : (g.slotEnd idx - 4#64).toNat = (g.slotEnd idx).toNat - 4 := bv64_sub_toNat (by omega)
    have hA5 : (g.slotStart idx - 4#64) + BitVec.ofNat 64 (g.stride - 5) = g.slotEnd idx - 5#64 := by
      apply BitVec.eq_of_toNat_eq; rw [bv64_add_toNat (by omega)]; omega
    have hA4 : ∀ j < 4, (g.slotEnd idx - 4#64) + BitVec.ofNat 64 j =
        (g.slotStart idx - 4#64) + BitVec.ofNat 64 (g.stride - 4 + j) := fun j hj => by
      apply BitVec.eq_of_toNat_eq
      rw [bv64_add_toNat (by omega), bv64_add_toNat (by omega)]; omega
    refine ⟨by rw [← hA5, hValIn _ (by omega), hB5], ?_⟩
    rw [← extractLsb_list_eq_unpack32]
    apply List.ext_getElem
    · rw [readBytesFromMap_length]; rfl
    · intro j hj1 hj2
      have hj4 : j < 4 := by rwa [readBytesFromMap_length] at hj1
      rw [readBytesFromMap_getElem _ _ _ _ hj1, hA4 j hj4, hValIn _ (by omega), hB4 j hj4]
      match j, hj4 with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
      | 3, _ => rfl
  obtain ⟨_, hNewBWf, hTargetSw⟩ :=
    reallocInPlace_slotWf (val' := val') (liveMap' := liveMap') hwf hg hIdx hSlot hNewMax hFit hScLe
      (by simp [liveMap'])
      hPreVal hHdrVal hRes1Val hRes5Val
  have hOutMod : ∀ a, ¬ SlotWriteMod g idx a → val' a = st.byteVal a := fun a hNotMod => by
    by_cases hInS : InRegion (g.slotStart idx - 4#64) g.stride a
    · have haEq0 : a = g.slotStart idx - 4#64 :=
        Classical.byContradiction fun hNe => hNotMod (Or.inr ⟨hInS, hNe⟩)
      subst haEq0
      exact hPreVal _ (Nat.le_refl _) (by omega)
        (fun hE => by have := congrArg BitVec.toNat hE; have := bv64_sub_toNat (a := p) (n := 3) (by omega); omega)
    · exact writeBytesToMap_out _ _ _ (by rwa [hFinalLen])
  obtain ⟨hg'Mem, hGsCases, hGsKeep, hGsMeta, hGsFindSelf, hGsFindNe⟩ :=
    replaceGroup_props st.groups g g' hg hwf.groups_nodup.1 rfl
  obtain ⟨hGsMem, hGsRoots⟩ := replaceGroup_preserves_mem_and_roots st.groups g g' hg hwf.groups_nodup.1 rfl rfl
  obtain ⟨hSetCl, hSetEff, hSetCnt, _⟩ := list_set_liveUser_props g.slots idx hIdx p p oldSz oldEff newSz newEff hSlot
  have hNotN : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm := by rw [hSlot]; intro _ h; cases h
  obtain ⟨hmDisjMa, hmDisjMeta, hmDisjGrpHdr, hmDisjOther⟩ := slotWriteMod_disjoint hwf hg hIdx hNotN
  obtain ⟨hmDisjAp, _⟩ := protNone_disjoint_slotWriteMod hwf hg hIdx
  have hOutRead : ∀ (b0 : BitVec 64) (n : Nat), n ≤ 2 ^ 64 →
      (∀ a, InRegion b0 n a → ¬ SlotWriteMod g idx a) →
      readBytesFromMap st'.byteVal b0 n = readBytesFromMap st.byteVal b0 n :=
    fun b0 n hn hD => (readBytesFromMap_congr_pred (W := SlotWriteMod g idx) hn hD
      (fun a hN => (hOutMod a hN).symm)).symm
  have hDynEq : dynamicRootRegions st' = dynamicRootRegions st := by
    dsimp only [dynamicRootRegions, st']; rw [hGsRoots]
  have hEffEq : totalLiveEffCost st' + oldEff = totalLiveEffCost st + newEff := by
    have hS := replaceGroup_sum_eq st.groups g g' hg hwf.groups_nodup.1 (fun x => (x.slots.map slotEffCost).sum)
    unfold totalLiveEffCost; dsimp only [st', g'] at hS ⊢; omega
  have hCntEq : totalLiveCount st' = totalLiveCount st := by
    have hS := replaceGroup_sum_eq st.groups g g' hg hwf.groups_nodup.1 (fun x => (x.slots.map slotLiveCount).sum)
    unfold totalLiveCount; dsimp only [st', g'] at hS ⊢; omega
  have hMpEq : ∀ a, OwnedMappedByte st' a ↔ OwnedMappedByte st a := by
    intro a; unfold OwnedMappedByte
    have hGrpMp : (∃ x ∈ st'.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a) ↔
        (∃ x ∈ st.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a) :=
      ⟨fun ⟨x, hx, hMp, hIn⟩ => (hGsCases x hx).elim (fun hE => by subst hE; exact ⟨g, hg, hMp, hIn⟩)
          (fun ⟨_, hxO⟩ => ⟨x, hxO, hMp, hIn⟩),
       fun ⟨x, hx, hMp, hIn⟩ => if hE : x.metaPtr = g.metaPtr then
          by have rflX := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE; subst rflX; exact ⟨g', hg'Mem, hMp, hIn⟩
        else ⟨x, hGsKeep x hx hE, hMp, hIn⟩⟩
    dsimp only [st'] at hGrpMp ⊢; rw [hGrpMp]
  have hCarvOut : ∀ a, ¬ InRegion (g.slotStart idx - 4#64) g.stride a →
      (CarvedUserByte st' a ↔ CarvedUserByte st a) := by
    intro a hNotS; unfold CarvedUserByte; constructor
    · rintro ⟨x, hx, s, hs, hSub⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
      rcases hGsCases x hx with rfl | ⟨_, hxOld⟩
      · have hjNe : j ≠ idx := fun hI => by
          subst hI; simp only [g', List.getElem_set_self] at hSub
          have ⟨h1, h2⟩ := (inRegion_iff_toNat (base := p) (n := newSz) (by omega) a).mp hSub
          exact hNotS ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
        have hjO : j < g.slots.length := by simpa [g'] using hj
        simp only [g', List.getElem_set_ne (Ne.symm hjNe)] at hSub ⊢
        exact ⟨g, hg, _, List.getElem_mem hjO, hSub⟩
      · exact ⟨x, hxOld, _, List.getElem_mem hj, hSub⟩
    · rintro ⟨x, hx, s, hs, hSub⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
      by_cases hE : x.metaPtr = g.metaPtr
      · have rflX := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE; subst rflX
        have hjNe : j ≠ idx := fun hI => by
          subst hI; rw [hSlot] at hSub
          have ⟨h1, h2⟩ := (inRegion_iff_toNat (base := p) (n := oldSz) (by omega) a).mp hSub
          exact hNotS ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
        have hj' : j < g'.slots.length := by simpa [g'] using hj
        exact ⟨g', hg'Mem, g'.slots[j]'hj', List.getElem_mem hj',
          by simpa [g', List.getElem_set_ne (Ne.symm hjNe)] using hSub⟩
      · exact ⟨x, hGsKeep x hx hE, _, List.getElem_mem hj, hSub⟩
  have hRwOut : ∀ a, ¬ InRegion (g.slotStart idx - 4#64) g.stride a →
      (OwnedRwByte st' a ↔ OwnedRwByte st a) := by
    intro a hNotS; unfold OwnedRwByte
    have h1 : (∃ x ∈ st'.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a) ↔
        (∃ x ∈ st.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a) :=
      ⟨fun ⟨x, hx, hp, hi⟩ => (hGsCases x hx).elim (fun hE => by subst hE; exact ⟨g, hg, hp, hi⟩)
          (fun ⟨_, hxO⟩ => ⟨x, hxO, hp, hi⟩),
       fun ⟨x, hx, hp, hi⟩ => if hE : x.metaPtr = g.metaPtr then
          by have rflX := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE; subst rflX; exact ⟨g', hg'Mem, hp, hi⟩
        else ⟨x, hGsKeep x hx hE, hp, hi⟩⟩
    dsimp only [st', CarvedMetaByte] at h1 ⊢
    rw [h1, hCarvOut a hNotS]
  have hNoRes : st.reservedMetas = [] := by
    have hInf := hwf.inflight_wf
    cases hL : st.reservedMetas with | nil => rfl | cons _ _ => simp [hL] at hInf
  obtain ⟨rg, hrg, hMpRg, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
  have hRg48 := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
  have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRg]
  have hRwIn : ∀ a, InRegion (g.slotStart idx - 4#64) g.stride a →
      a ∈ st.masterDom ∧ (OwnedRwByte st' a ↔ ¬ InRegion p newSz a) := by
    intro a ha
    have ⟨hALo, hAHi⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    have hInRg : InRegion rg.mem (rg.maplen * 4096) a :=
      (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
    have hDom : a ∈ st.masterDom := hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rg, hrg, hMpRg, hInRg⟩)))))
    have hRgIn' : ∃ x ∈ st'.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a :=
      if hE : rg.metaPtr = g.metaPtr then
        by have rflR := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hrg hg hE; subst rflR; exact ⟨g', hg'Mem, hMpRg, hInRg⟩
      else ⟨rg, hGsKeep rg hrg hE, hMpRg, hInRg⟩
    have hIdx' : idx < g'.slots.length := by simpa [g'] using hIdx
    refine ⟨hDom, ⟨fun hRw hInU => hRw.2.1 ⟨g', hg'Mem, .liveUser p newSz newEff, ?_, hInU⟩, fun hNotU => ?_⟩⟩
    · have hS' : g'.slots[idx]'hIdx' = .liveUser p newSz newEff := by simp [g']
      rw [← hS']; exact List.getElem_mem hIdx'
    · refine ⟨Or.inr hRgIn', ?_, by simp [st', CarvedMetaByte, hNoRes]⟩
      rintro ⟨x, hx, s, hs, hSub⟩
      obtain ⟨j, hj, hEqS⟩ := List.getElem_of_mem hs
      cases hS : s with
      | freeAvail | freeInactive | claimed | liveNested _ => simp [hS] at hSub
      | liveUser u' r' c' =>
        simp only [hS] at hSub
        have hSlX : x.slots[j]'hj = .liveUser u' r' c' := hEqS.trans hS
        rcases hGsCases x hx with rfl | ⟨hNeM, hxOld⟩
        · by_cases hji : j = idx
          · subst hji; simp only [g', List.getElem_set_self] at hSlX
            injection hSlX with h1 h2 _; subst h1 h2; exact hNotU hSub
          · have hjO : j < g.slots.length := by simpa [g'] using hj
            simp only [g', List.getElem_set_ne (Ne.symm hji)] at hSlX
            have hSWf' := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hjO; rw [hSlX] at hSWf'
            have ⟨_, _, hSt', hSub4', hEn', _, h48', _, _⟩ := group_slot_bounds hgw hjO
            have hSM' : (j + 1) * g.stride = j * g.stride + g.stride := Nat.succ_mul j g.stride
            have hUFit' := hSWf'.2.2.2.2.2.2.1
            have ⟨hULo, hUHi⟩ := (inRegion_iff_toNat (by omega) a).mp hSub
            have ha' : InRegion (g.slotStart j - 4#64) g.stride a :=
              (inRegion_iff_toNat (by omega) a).mpr ⟨by have := hSWf'.2.2.2.2.2.1; omega, by omega⟩
            exact nonNested_slotSlice_disjoint hwf hg hIdx hNotN hg hjO (by rw [hSlX]; intro _ h; cases h)
              (Or.inr (Ne.symm hji)) ha ha'
        · have hxw := hwf.groups_wf x hxOld
          have hSWf' := hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj; rw [hSlX] at hSWf'
          have ⟨_, _, hSt', hSub4', hEn', _, h48', _, _⟩ := group_slot_bounds hxw hj
          have hSM' : (j + 1) * x.stride = j * x.stride + x.stride := Nat.succ_mul j x.stride
          have hUFit' := hSWf'.2.2.2.2.2.2.1
          have ⟨hULo, hUHi⟩ := (inRegion_iff_toNat (by omega) a).mp hSub
          have ha' : InRegion (x.slotStart j - 4#64) x.stride a :=
            (inRegion_iff_toNat (by omega) a).mpr ⟨by have := hSWf'.2.2.2.2.2.1; omega, by omega⟩
          exact nonNested_slotSlice_disjoint hwf hg hIdx hNotN hxOld hj (by rw [hSlX]; intro _ h; cases h)
            (Or.inl (fun hE => hNeM (congrArg GroupDesc.metaPtr hE.symm))) ha ha'
  have hGroupsMap : ∀ cg ∈ st.groups, ∃ cg' ∈ st'.groups,
      cg'.metaPtr = cg.metaPtr ∧ cg'.parentMeta = cg.parentMeta ∧
      cg'.mem = cg.mem ∧ cg'.nestedCap = cg.nestedCap := fun cg hcg =>
    if hE : cg.metaPtr = g.metaPtr then
      by have rflC := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg hg hE; subst rflC; exact ⟨g', hg'Mem, rfl, rfl, rfl, rfl⟩
    else ⟨cg, hGsKeep cg hcg hE, rfl, rfl, rfl, rfl⟩
  have hParLift : ∀ x ∈ st.groups, x.maplen = 0 →
      1 ≤ x.lastIdx ∧ ∃ pg ∈ st'.groups, ∃ pIdx : Nat, ∃ hp : pIdx < pg.slots.length,
        x.parentMeta = some pg.metaPtr ∧ pg.sc < 48 ∧ x.sc < pg.sc ∧ pg.sc ≤ 24 ∧
        pg.slots[pIdx]'hp = .liveNested x.metaPtr ∧
        (pg.slotStart pIdx).toNat ≤ x.mem.toNat ∧ x.mem.toNat + x.nestedCap ≤ (pg.slotEnd pIdx).toNat ∧
        x.nestedCap = slotStride pg.sc - 4 := by
    intro x hx hM0
    obtain ⟨hL1, pg, hpg, pIdx, hp, hPM, h1, h2, h3, hPS, hLoP, hHiP, hNC⟩ :=
      (hwf.groups_wf x hx).2.2.2.2.2.2.2.2.2.2.2.2.1 hM0
    refine ⟨hL1, ?_⟩
    by_cases hE : pg.metaPtr = g.metaPtr
    · have rflP := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hg hE; subst rflP
      have hpNe : pIdx ≠ idx := fun hI => by subst hI; rw [hSlot] at hPS; cases hPS
      have hp' : pIdx < g'.slots.length := by simpa [g'] using hp
      exact ⟨g', hg'Mem, pIdx, hp', hPM, h1, h2, h3,
        by simpa [g', List.getElem_set_ne (Ne.symm hpNe)] using hPS, hLoP, hHiP, hNC⟩
    · exact ⟨pg, hGsKeep pg hpg hE, pIdx, hp, hPM, h1, h2, h3, hPS, hLoP, hHiP, hNC⟩
  have hCount' : MallocngCountIvsWF bf ivs0 st' := by
    obtain ⟨hC1, hC2, hC3, hC4, hC5, hC6⟩ := hCount
    have hGrp' : Cost.GroupsGrpBound (b.peakCount + 6) st'.groups :=
      hC6.of_subset fun x hx _ _ => by
        rcases hGsCases x hx with hxe | ⟨_, hx0⟩
        · rw [hxe]; exact ⟨g, hg, rfl, Nat.le_refl _⟩
        · exact ⟨x, hx0, rfl, Nat.le_refl _⟩
    simp only [MallocngCountIvsWF, bf, mallocngReallocBudget, ↓reduceIte]
    exact ⟨by omega, by omega, hC3.trans hDynEq.symm, by omega,
      Nat.le_trans hC5 (Nat.add_le_add_left (Nat.div_le_div_right (by omega)) 1),
      hGrp'.mono (by omega)⟩
  refine ⟨hNewBWf, hCount', ?_, hRwOut, hRwIn⟩
  refine {
    base_wf := hwf.base_wf
    brk_bounds := hwf.brk_bounds
    ctx_lens := hwf.ctx_lens
    initDone_wf := hwf.initDone_wf
    initZero_wf := fun h0 => by exfalso; rw [(hwf.initZero_wf h0).2.2.2.2.2.2.2.2.2.1] at hg; cases hg
    bounces_wf := hwf.bounces_wf
    usage_wf := fun sc hsc => by
      dsimp only [st']
      rw [replaceGroup_filter_sc_cnt_sum st.groups g g' hg hwf.groups_nodup.1 rfl rfl sc]
      exact hwf.usage_wf sc hsc
    brk_mode_wf := hwf.brk_mode_wf
    metaAreas_wf := ⟨hwf.metaAreas_wf.1, fun ma hma => by
      obtain ⟨h1, h2, h3, h4⟩ := hwf.metaAreas_wf.2.1 ma hma
      exact ⟨h1, h2, h3, (hOutRead ma.base 24 (by decide) (hmDisjMa ma hma)).trans h4⟩,
      hwf.metaAreas_wf.2.2⟩
    guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1,
      fun ap hap => by
        obtain ⟨h1, h2, h3, h4⟩ := hwf.guard_avail_wf.2.2.2 ap hap
        exact ⟨h1, h2, h3, (hOutRead ap 4096 (by decide) (hmDisjAp ap hap)).trans h4⟩⟩
    inflight_wf := by
      have hS := replaceGroup_sum_eq st.groups g g' hg hwf.groups_nodup.1
        (fun x => (x.slots.filter SlotState.isClaimed).length)
      have := hwf.inflight_wf
      unfold totalClaimedSlots at this ⊢; dsimp only [st', g'] at hS ⊢; omega
    free_bump_metas_wf := by
      obtain ⟨hDll, hFmB, hBumpC, hBmB, hUFNd, hUFIff⟩ := hwf.free_bump_metas_wf
      have hNd12 := (List.nodup_append.mp hUFNd).1
      have hNd1 := (List.nodup_append.mp hNd12).1
      refine ⟨hDll, fun fm hfm => ?_, hBumpC, fun bm hbm => ?_,
        by dsimp only [st']; rw [hGsMeta]; exact hUFNd,
        fun m => by dsimp only [st', allMetaSlots]; rw [hGsMeta]; exact hUFIff m⟩
      · have hNe : fm.ptr ≠ g.metaPtr := fun hE =>
          (List.nodup_append.mp hNd1).2.2 g.metaPtr (List.mem_map_of_mem hg) fm.ptr (List.mem_map_of_mem hfm) hE.symm
        have hAll := (hUFIff fm.ptr).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hfm))))
        exact (hOutRead fm.ptr 40 (by decide) (hmDisjMeta fm.ptr hAll hNe)).trans (hFmB fm hfm)
      · have hNe : bm ≠ g.metaPtr := fun hE =>
          (List.nodup_append.mp hNd12).2.2 g.metaPtr (List.mem_append_left _ (List.mem_map_of_mem hg)) bm hbm hE.symm
        have hAll := (hUFIff bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm))
        exact (hOutRead bm 40 (by decide) (hmDisjMeta bm hAll hNe)).trans (hBmB bm hbm)
    groups_nodup := ⟨by dsimp only [st']; rw [hGsMeta]; exact hwf.groups_nodup.1,
      by dsimp only [st']; rw [hGsMem]; exact hwf.groups_nodup.2⟩
    groups_wf := fun x' hx' => by
      have hMemOut : ∀ h ∈ st.groups,
          st'.byteVal (h.slotEnd h.lastIdx) = st.byteVal (h.slotEnd h.lastIdx) ∧
          readBytesFromMap st'.byteVal h.mem 8 = readBytesFromMap st.byteVal h.mem 8 ∧
          st'.byteVal (h.mem + 8#64) = st.byteVal (h.mem + 8#64) := fun h hh => by
        have hhw := hwf.groups_wf h hh
        have hGe12 : 12 ≤ h.totalBytes := by have := hhw.2.2.2.2.2.2.2.1; omega
        have hH48 := hhw.2.2.2.2.2.2.1
        have hAdd8 : (h.mem + 8#64).toNat = h.mem.toNat + 8 := bv64_add_toNat (by omega)
        obtain ⟨hHdr9, hEndLast⟩ := hmDisjGrpHdr h hh
        exact ⟨hOutMod _ hEndLast,
          hOutRead h.mem 8 (by decide) (fun a ha => by
            have haN := (inRegion_iff_toNat (base := h.mem) (n := 8) (by omega) a).mp ha
            exact hHdr9 a ((inRegion_iff_toNat (base := h.mem) (n := 9) (by omega) a).mpr ⟨by omega, by omega⟩)),
          hOutMod _ (hHdr9 _ ((inRegion_iff_toNat (base := h.mem) (n := 9) (by omega) _).mpr ⟨by omega, by omega⟩))⟩
      rcases hGsCases x' hx' with rfl | ⟨hNeM, hxOld⟩
      · obtain ⟨hEndEq, hMem8Eq, hAct8Eq⟩ := hMemOut g hg
        have hMetaSelf : readBytesFromMap st'.byteVal g.metaPtr 40 = g.metaBytes :=
          (readBytesFromMap_congr_pred (W := InRegion (g.slotStart idx - 4#64) slotBsFinal.length)
            (by decide)
            (fun a ha hS => by
              rw [hFinalLen] at hS
              obtain ⟨maG, hmaG, _, _, _, hMN, hMFit, hMa48⟩ :=
                metaSlot_in_metaArea hwf ((hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
                  (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg)))))
              have ⟨hM1, hM2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
              have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hS
              exact not_both_inRegion_of_disjointRegions (metaArea_disjoint_root_group hwf hmaG hrg hMpRg)
                ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
                ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩))
            (fun a hNot => writeBytesToMap_out st.byteVal _ slotBsFinal hNot)).trans
            hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        refine ⟨hgw.1, hgw.2.1, by simp [g', hgw.2.2.1], hgw.2.2.2.1,
          hgw.2.2.2.2.1, hgw.2.2.2.2.2.1, hgw.2.2.2.2.2.2.1, hgw.2.2.2.2.2.2.2.1,
          hgw.2.2.2.2.2.2.2.2.1, hEndEq.trans hgw.2.2.2.2.2.2.2.2.2.1,
          hgw.2.2.2.2.2.2.2.2.2.2.1, hgw.2.2.2.2.2.2.2.2.2.2.2.1, hParLift g hg,
          hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hMetaSelf,
          hMem8Eq.trans hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hAct8Eq.trans hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, fun j hj' => ?_⟩
        by_cases hji : j = idx
        · subst hji; simp only [g', List.getElem_set_self]; exact hTargetSw
        · have hj : j < g.slots.length := by simpa [g'] using hj'
          have hSetNe : g'.slots[j]'hj' = g.slots[j]'hj := by simp [g', List.getElem_set_ne (Ne.symm hji)]
          obtain ⟨hNonN, hNest⟩ := hmDisjOther g hg j hj (Or.inr hji)
          rw [hSetNe]
          exact slotWf_congr_local hwf hg hj rfl rfl rfl rfl rfl rfl rfl rfl hGroupsMap
            (fun hNN a ha => hOutMod a (hNonN hNN a ha))
            (fun cm cg hS hcg hCm hPm => ⟨hOutMod _ (hNest cm cg hS hcg hCm hPm).1,
              fun a ha => hOutMod a ((hNest cm cg hS hcg hCm hPm).2 a ha)⟩)
            (hOv := fun u _ _ _ => by
              dsimp only [st', liveMap']; rw [MallocngLiveMap.insert_ov, MallocngLiveMap.erase_ov]
              by_cases hup : u = p <;> simp only [hup, ↓reduceIte])
      · have hxw := hwf.groups_wf x' hxOld
        obtain ⟨hEndEq, hMem8Eq, hAct8Eq⟩ := hMemOut x' hxOld
        have hAll := (hwf.free_bump_metas_wf.2.2.2.2.2 x'.metaPtr).mp
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hxOld))))
        refine ⟨hxw.1, hxw.2.1, hxw.2.2.1, hxw.2.2.2.1, hxw.2.2.2.2.1, hxw.2.2.2.2.2.1,
          hxw.2.2.2.2.2.2.1, hxw.2.2.2.2.2.2.2.1, hxw.2.2.2.2.2.2.2.2.1,
          hEndEq.trans hxw.2.2.2.2.2.2.2.2.2.1, hxw.2.2.2.2.2.2.2.2.2.2.1,
          hxw.2.2.2.2.2.2.2.2.2.2.2.1, hParLift x' hxOld,
          hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          (hOutRead x'.metaPtr 40 (by decide) (hmDisjMeta x'.metaPtr hAll hNeM)).trans
            hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hMem8Eq.trans hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hAct8Eq.trans hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, fun j hj => ?_⟩
        obtain ⟨hNonN, hNest⟩ := hmDisjOther x' hxOld j hj (Or.inl hNeM)
        exact slotWf_congr_local hwf hxOld hj rfl rfl rfl rfl rfl rfl rfl rfl hGroupsMap
          (fun hNN a ha => hOutMod a (hNonN hNN a ha))
          (fun cm cg hS hcg hCm hPm => ⟨hOutMod _ (hNest cm cg hS hcg hCm hPm).1,
            fun a ha => hOutMod a ((hNest cm cg hS hcg hCm hPm).2 a ha)⟩)
          (hOv := fun u _ _ _ => by
            dsimp only [st', liveMap']; rw [MallocngLiveMap.insert_ov, MallocngLiveMap.erase_ov]
            by_cases hup : u = p <;> simp only [hup, ↓reduceIte])
    regions_disjoint := by rw [hDynEq]; exact hwf.regions_disjoint
    active_wf := fun sc h1 h2 => by
      have haw := hwf.active_wf sc h1 h2
      have hFmEq : ∀ ms : List (BitVec 64),
          ms.filterMap (fun m => (findGroupByMeta st' m).map fun x => (x.metaPtr, x.prev, x.next)) =
          ms.filterMap (fun m => (findGroupByMeta st m).map fun x => (x.metaPtr, x.prev, x.next)) := by
        intro ms; induction ms with
        | nil => rfl
        | cons m tl ih =>
          simp only [List.filterMap]
          by_cases hmE : m = g.metaPtr
          · subst hmE
            have hFOld := findGroupByMeta_of_mem hwf.groups_nodup.1 hg
            have hFNew : findGroupByMeta st' g.metaPtr = some g' := hGsFindSelf
            rw [hFNew, hFOld, ih]; rfl
          · have hFNe : findGroupByMeta st' m = findGroupByMeta st m := hGsFindNe m hmE
            rw [hFNe, ih]
      have hToOld : ∀ x ∈ st'.groups, ∃ y ∈ st.groups,
          y.metaPtr = x.metaPtr ∧ y.sc = x.sc ∧ y.activeIdx = x.activeIdx ∧ y.lastIdx = x.lastIdx := fun x hx =>
        (hGsCases x hx).elim (fun hE => by subst hE; exact ⟨g, hg, rfl, rfl, rfl, rfl⟩)
          (fun ⟨_, hxO⟩ => ⟨x, hxO, rfl, rfl, rfl, rfl⟩)
      refine ⟨fun m hm => ?_, by rw [hFmEq]; exact haw.2.1, by rw [hFmEq]; exact haw.2.2.1,
        fun x hx hSc => (hGsCases x hx).elim (fun hE => by subst hE; exact haw.2.2.2.1 g hg hSc)
          (fun ⟨_, hxO⟩ => haw.2.2.2.1 x hxO hSc),
        fun i hi hPos x hx hM => (hGsCases x hx).elim (fun hE => by subst hE; exact haw.2.2.2.2.1 i hi hPos g hg hM)
          (fun ⟨_, hxO⟩ => haw.2.2.2.2.1 i hi hPos x hxO hM),
        fun x1 hx1 x2 hx2 hS1 hS2 hA1 hA2 => ?_, fun x hx hSc hA => ?_⟩
      · obtain ⟨x, hx, rfl, rfl⟩ := haw.1 m hm
        exact if hE : x.metaPtr = g.metaPtr then
          ⟨g', hg'Mem, (congrArg GroupDesc.metaPtr (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE)).symm,
            (congrArg GroupDesc.sc (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE)).symm⟩
        else ⟨x, hGsKeep x hx hE, rfl, rfl⟩
      · obtain ⟨y1, hy1, hM1, hY1S, hY1A, hY1L⟩ := hToOld x1 hx1
        obtain ⟨y2, hy2, hM2, hY2S, hY2A, hY2L⟩ := hToOld x2 hx2
        exact hM1.symm.trans ((haw.2.2.2.2.2.1 y1 hy1 y2 hy2 (hY1S.trans hS1) (hY2S.trans hS2)
          (by omega) (by omega)).trans hM2)
      · obtain ⟨y, hy, hM, hYS, hYA, hYL⟩ := hToOld x hx
        rw [← hM]; exact haw.2.2.2.2.2.2 y hy (hYS.trans hSc) (by omega)
    liveMap_wf := fun q m => by
      dsimp only [st', liveMap', MallocngLiveMap.insert, MallocngLiveMap.erase]
      by_cases hqp : q = p
      · subst hqp; simp only [↓reduceIte, Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨g', hg'Mem, idx, by simpa [g'] using hIdx, newEff, by simp [g']⟩
        · rintro ⟨x, hx, j, hj, ef, hSl⟩
          rcases hGsCases x hx with rfl | ⟨hNeM, hxOld⟩
          · by_cases hji : j = idx
            · subst hji; simp only [g', List.getElem_set_self] at hSl; cases hSl; rfl
            · have hjO : j < g.slots.length := by simpa [g'] using hj
              simp only [g', List.getElem_set_ne (Ne.symm hji)] at hSl
              exact False.elim (hji (liveUser_ptr_unique hwf hg hg hIdx hjO hSlot hSl).2)
          · exact False.elim (hNeM (congrArg GroupDesc.metaPtr
              (liveUser_ptr_unique hwf hg hxOld hIdx hj hSlot hSl).1))
      · simp only [hqp, ↓reduceIte]; rw [hwf.liveMap_wf q m]
        constructor
        · rintro ⟨x, hx, j, hj, ef, hSl⟩
          by_cases hE : x.metaPtr = g.metaPtr
          · have rflX := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE; subst rflX
            have hjNe : j ≠ idx := fun hI => by subst hI; rw [hSlot] at hSl; injection hSl with h1 _ _; exact hqp h1.symm
            exact ⟨g', hg'Mem, j, by simpa [g'] using hj, ef,
              by simpa [g', List.getElem_set_ne (Ne.symm hjNe)] using hSl⟩
          · exact ⟨x, hGsKeep x hx hE, j, hj, ef, hSl⟩
        · rintro ⟨x, hx, j, hj, ef, hSl⟩
          rcases hGsCases x hx with rfl | ⟨_, hxOld⟩
          · have hjNe : j ≠ idx := fun hI => by
              subst hI; simp only [g', List.getElem_set_self] at hSl; injection hSl with h1 _ _; exact hqp h1.symm
            have hjO : j < g.slots.length := by simpa [g'] using hj
            exact ⟨g, hg, j, hjO, ef, by simpa [g', List.getElem_set_ne (Ne.symm hjNe)] using hSl⟩
          · exact ⟨x, hxOld, j, hj, ef, hSl⟩
    live_le_peak := by simp only [bf, mallocngReallocBudget, ↓reduceIte, MallocngMinBlockCost]; omega
    effCost_le_live := by
      have := hwf.effCost_le_live
      simp only [bf, mallocngReallocBudget, ↓reduceIte, MallocngMinBlockCost] at hEffEq hOldEfGe hOldEfTot this ⊢
      dsimp only [newEff] at hEffEq; simp only [MallocngMinBlockCost] at hEffEq; omega
    meta_pages_bound := ⟨Nat.le_trans hwf.meta_pages_bound.1
      (Nat.add_le_add_left (Nat.div_le_div_right (by simp [bf, mallocngReallocBudget]; omega)) 2),
      hwf.meta_pages_bound.2.1, hwf.meta_pages_bound.2.2⟩
    empty_groups_bound := by
      have hNE : ¬ g'.isEmpty = true := fun hE => by
        have hI : idx < g'.slots.length := by simpa [g'] using hIdx
        have hA := List.all_eq_true.mp hE (g'.slots[idx]'hI) (List.getElem_mem hI); simp [g', SlotState.isFree] at hA
      intro x hx hEmp; rcases hGsCases x hx with rfl | ⟨_, hxO⟩
      · exact False.elim (hNE hEmp)
      · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hwf.empty_groups_bound x hxO hEmp
        exact ⟨e1, e2, e3, e4, e5, fun y hy hEy hSc => (hGsCases y hy).elim
          (fun r => False.elim (hNE (r ▸ hEy))) (fun ⟨_, hyO⟩ => e6 y hyO hEy hSc), e7⟩
    masterDom_wf := ⟨hwf.masterDom_wf.1,
      fun a h => by
        rcases h with h1 | h2 | h3
        · by_cases hS : InRegion (g.slotStart idx - 4#64) g.stride a
          · exact (hRwIn a hS).1
          · exact hwf.masterDom_wf.2.1 a (Or.inl ((hRwOut a hS).mp h1))
        · exact hwf.masterDom_wf.2.1 a (Or.inr (Or.inl h2))
        · exact hwf.masterDom_wf.2.1 a (Or.inr (Or.inr ((hMpEq a).mp h3))),
      fun a ha => by rw [hDynEq]; exact hwf.masterDom_wf.2.2 a ha⟩
  }

end VerifiedLibraries.Mallocng.Proofs
