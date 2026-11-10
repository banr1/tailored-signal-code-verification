/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.NontrivialFreeFine5
public import LibsignalBinary.Heap.Fine.VendorFree.PlacedLibcFreeProof

/-!
# Raw Placed `__libc_free` Verification

Proves `placed_libcFree_raw_ok` and `call_placed_libcFree_raw` for `libcFreeRaw272Spec` (`blk06`,
272-byte stack), exporting `LibcFreeRawPostRel p n st st'` (`SameLiveUserSub` on released `st` when
`p ≠ 0#64`, and `st' = st` when `p = 0#64`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open LibsignalBinary.Heap.Fine.VendorFree

/-! ## Raw `__libc_free` Specification -/

/-- Exact raw witness connecting entry state `st` (`MallocngWF`) and exit state `st'` (`MallocngWF`)
    across `__libc_free(p)` on `(p, n)`. -/
def LibcFreeRawPostRel (p : BitVec 64) (n : Nat) (st st' : MallocngSt) : Prop :=
  if p = 0#64 then
    st' = st
  else
    ∃ (g : GroupDesc) (idx effCost : Nat) (hIdx : idx < g.slots.length) (bs : List (BitVec 8)),
      g ∈ st.groups ∧
      g.slots[idx]'hIdx = .liveUser p n effCost ∧
      bs.length = n ∧
      SameLiveUserSub st' (VendorFree.mkReleasedSt st g idx p bs)

noncomputable def libcFreeRaw272Spec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p : BitVec 64) (n liveCost peakCost : Nat)
    (st : MallocngSt) : Spec Unit :=
  { pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = p ∧ s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
      stackFrame s0 272 ∗
      MallocngRoTablesA maddrs ∗
      MallocngCoreStA γ maddrs brkStart s0.brk liveCost peakCost st ∗
      MallocngRuntime maddrs tp ∗
      if p = 0#64 then emp else memRegion p n ∗ MallocngBlockToken γ p n
    post := fun (_ : Unit) s0 sf =>
      ∃∗ st' : MallocngSt,
      ∃∗ liveCost' : Nat,
        ⌜MallocngProcPreserved s0 sf ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         sf.brk = s0.brk ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
         liveCost' ≤ peakCost ∧
         MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem ∧
         LibcFreeRawPostRel p n st st'⌝ ∗
        stackFrame s0 272 ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStA γ maddrs brkStart sf.brk liveCost' peakCost st' ∗
        MallocngRuntime maddrs tp }

/-! ## Spatial Focus and Postcondition Packing Helpers -/

private theorem mappedDelta_zero_of_perm_eq {m0 mf : Memory} (h : mf.perm = m0.perm) :
    MallocngMappedDelta 0 0 m0 mf :=
  ⟨[], Nat.le_refl 0, Nat.le_refl 0, fun _ ha => Or.inl (h ▸ ha)⟩

private theorem mappedDelta_zero_congr {m0 m1 m2 m3 : Memory}
    (h01 : m1.perm = m0.perm) (hd : MallocngMappedDelta 0 0 m1 m2) (h32 : m3.perm = m2.perm) :
    MallocngMappedDelta 0 0 m0 m3 := by
  obtain ⟨ivs, hl, hs, hc⟩ := hd
  refine ⟨ivs, hl, hs, fun a ha => ?_⟩
  rw [h32] at ha
  rcases hc a ha with hm1 | hiv
  · exact Or.inl (h01 ▸ hm1)
  · exact Or.inr hiv

private theorem unmappedRange_congr {addr : BitVec 64} {len : Nat} {m0 m1 m2 m3 : Memory}
    (h01 : m1.perm = m0.perm) (hu : MallocngUnmappedRange addr len m1 m2) (h32 : m3.perm = m2.perm) :
    MallocngUnmappedRange addr len m0 m3 := by
  intro a ha; rw [h32] at ha; obtain ⟨hm1, hn⟩ := hu a ha; exact ⟨h01 ▸ hm1, hn⟩

private theorem pointsTo_metaBytes_eq (g : GroupDesc) :
    (g.metaPtr ↦ₛ g.metaBytes) =
      ((g.metaPtr ↦₆₄ g.prev) ∗ ((g.metaPtr + 8#64) ↦₆₄ g.next) ∗
       ((g.metaPtr + 16#64) ↦₆₄ g.mem) ∗ ((g.metaPtr + 24#64) ↦₃₂ g.availMask) ∗
       ((g.metaPtr + 28#64) ↦₃₂ g.freedMask) ∗ ((g.metaPtr + 32#64) ↦₆₄ g.packedWord)) := by
  simp only [GroupDesc.metaBytes, List.append_assoc, pointsToBytes_append,
    unpack64_length, unpack32_length, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo32_eq_pointsToBytes, addr_norm]

private theorem focus_meta_of_mem_groups {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) :
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      (((g.metaPtr ↦₆₄ g.prev) ∗ ((g.metaPtr + 8#64) ↦₆₄ g.next) ∗
        ((g.metaPtr + 16#64) ↦₆₄ g.mem) ∗ ((g.metaPtr + 24#64) ↦₃₂ g.availMask) ∗
        ((g.metaPtr + 28#64) ↦₃₂ g.freedMask) ∗ ((g.metaPtr + 32#64) ↦₆₄ g.packedWord)) ∗
       ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal) := by
  have hOwn := (meta_ownedRw_of_mem_groups hwf hg).2.2.2.2
  have hBytes : readBytesFromMap st.byteVal g.metaPtr 40 = g.metaBytes :=
    (hwf.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ByteMap_extract_slice hwf.masterDom_wf.1 st.byteVal g.metaPtr (by decide : 40 ≤ 2 ^ 64)
      (fun a ha => (hOwn a ha).2) (fun a ha => (hOwn a ha).1),
    hBytes, pointsTo_metaBytes_eq]

private theorem calleeSaved22_28_of_preserved {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    CalleeSaved22_28 s1 s2 :=
  ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem pack_libcFree_raw_post [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p sp0 : BitVec 64)
    (n liveCost liveCost' peakCost : Nat)
    (st stf : MallocngSt) (s0 sf : State)
    (hproc : MallocngProcPreserved s0 sf)
    (hdelta : MallocngMappedDelta 0 0 s0.mem sf.mem)
    (hbrk : sf.brk = s0.brk)
    (hsp0 : s0.sp = sp0)
    (htp : sf.tpidrEl0 = tp) (hbrks : sf.brkStart = brkStart)
    (hliveLe : liveCost' ≤ peakCost)
    (hno : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions stf) s0.mem sf.mem)
    (hrel : LibcFreeRawPostRel p n st stf) :
    ((MallocngRoTablesA maddrs ∗
      MallocngCoreStA γ maddrs brkStart sf.brk liveCost' peakCost stf ∗
      MallocngRuntime maddrs tp) ∗ stackFrameAt sp0 272) ⊢
      (libcFreeRaw272Spec γ tp brkStart p n liveCost peakCost st).post () s0 sf := by
  dsimp only [libcFreeRaw272Spec]
  refine Entails.trans ?_ (Entails.sepExists_intro stf)
  refine Entails.trans ?_ (Entails.sepExists_intro liveCost')
  refine Entails.pure_right ⟨hproc, hdelta, hbrk, htp, hbrks, hliveLe, hno, hrel⟩ ?_
  have hsf_eq : stackFrame s0 272 = stackFrameAt sp0 272 := by
    rw [stackFrameAt_eq_memRegion sp0 272]; simp [stackFrame, hsp0]
  rw [hsf_eq]
  sep_frame

/-! ## Slow Path and Fast/Slow Dispatch -/

set_option maxHeartbeats 400000 in
private theorem libcFree_munmap_tail_raw_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 6 b)
    (γ : GhostName) (tp brkStart p sp0 w5 miBase miLenBv : BitVec 64)
    (n liveCost liveCost' peakCost : Nat)
    {st st1 st' : MallocngSt}
    (hDyn1 : dynamicRootRegions st1 = dynamicRootRegions st)
    (hliveLe : liveCost' ≤ peakCost)
    (hRel : LibcFreeRawPostRel p n st st')
    (hPos : 0 < miLenBv.toNat) (hAlBase : 4096 ∣ miBase.toNat) (hAlLen : 4096 ∣ miLenBv.toNat)
    (hFit : miBase.toNat + miLenBv.toNat ≤ 2 ^ 48)
    (hCov : ∀ a : BitVec 64, MallocngInIntervals (dynamicRootRegions st1) a →
      InRegion miBase miLenBv.toNat a ∨ MallocngInIntervals (dynamicRootRegions st') a)
    (s0 se : State)
    (hcl_e : VerifiedLibraries.mallocngLib.CodeLoaded mmpl se.mem)
    (hpc_e : se.pc = b + 0x2dc#64) (hrun_e : se.status = .Running)
    (hsp_e : se.sp = sp0 - 48#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hbrk0e : se.brk = s0.brk)
    (htp_e : se.tpidrEl0 = tp) (hbrks_e : se.brkStart = brkStart)
    (hperm0e : se.mem.perm = s0.mem.perm) (hproc0e : MallocngProcPreserved s0 se)
    (hcs0e : CalleeSaved22_28 s0 se)
    (hx0_e : se.readReg64 (.gpr 0#5) = tp - 0xa4#64)
    (hx19_e : se.readReg64 (.gpr 19#5) = miLenBv)
    (hx20_e : se.readReg64 (.gpr 20#5) = miBase) :
    SepWP (blkPC_b06.rebase b (fun _ => none)) (s0.readReg64 .lr) se
      (MallocngRoTablesA maddrs ∗
       MallocngCoreStA γ maddrs brkStart se.brk liveCost' peakCost st' ∗
       MallocngRuntime maddrs tp ∗
       stackFrameAt (sp0 - 48#64) 224 ∗ LibcFreeSpillSlots sp0 s0 w5 ∗
       memRegion miBase miLenBv.toNat ∗ memMapped miBase miLenBv.toNat)
      (fun sf Pf =>
        (Pf ⊢ (libcFreeRaw272Spec γ tp brkStart p n liveCost peakCost st).post () s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  have _ := hb
  have hspAl0' : (sp0 &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp0] using hspAl0
  have hspAl48 : ((sp0 - 48#64) &&& 15#64 == 0#64) = true := by revert hspAl0'; bv_robdd
  have hspAl_e : se.spAligned = true := by simpa [State.spAligned, hsp_e] using hspAl48
  conv =>
    arg 4
    dsimp only [MallocngRuntime]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro errnoVal
  wp_step; wp_step; wp_step; wp_step; wp_step
  have hPA : pageAlignUp miLenBv.toNat = miLenBv.toNat := pageAlignUp_of_dvd_4096 hAlLen
  have hMuSub := placed_munmapWrapper_unmap_ok (P := blkPC_b06.rebase b (fun _ => none))
    tp miBase errnoVal miLenBv.toNat hPos hAlBase (by rw [hPA]; exact hFit)
  let FrameMu := MallocngRoTablesA maddrs ∗
    MallocngCoreStA γ maddrs brkStart se.brk liveCost' peakCost st' ∗
    ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
    stackFrameAt (sp0 - 48#64 - 64#64) 160 ∗ LibcFreeSpillSlots sp0 s0 w5
  refine SepWP.call_subroutine_frame (F := FrameMu) (x := ()) (ret_pc := b + 0x2f0#64) hMuSub
    (by simp only [arm64_norm]; rw [hb]; bv_arith)
    (by simp [arm64_norm, hrun_e])
    (by simpa [State.spAligned, arm64_norm, hsp_e] using hspAl_e)
    (by simp [arm64_norm])
    (fun R' hm => by
      rw [← sepConj_assoc]; refine Satisfies.mono (sepConj_mono_left ?_) hm
      dsimp only [withCL, FrameMu]
      rw [hPA, pure_sepConj_of_true ⟨by simp [arm64_norm, htp_e], by simp [arm64_norm], by simp [arm64_norm]⟩,
        sepConj_comm (Q := ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl _⌝),
        pure_sepConj_of_true (by simpa [arm64_norm] using hcl_e),
        show stackFrame _ 64 = stackFrameAt (sp0 - 48#64) 64 by
          rw [stackFrameAt_eq_memRegion (sp0 - 48#64) 64]; simp [stackFrame, arm64_norm, hsp_e],
        stackFrameAt_224_split_64 (sp0 - 48#64)]
      sep_frame)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun smu hpc_mu hrun_mu hsp_mu hcs_mu => ?_)
    (fun _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
  (conv => arg 4; dsimp only [withCL]); wp_focus_pure
  rintro ⟨hproc_mu, hbrk_mu, _, hdelta_mu, hunmap_mu⟩
  wp_focus_pure; intro hcl_mu
  have hx21_mu : smu.readReg64 (.gpr 21#5) = tp - 0xa4#64 := by simpa [arm64_norm] using hcs_mu.2.2.1
  have hx19_mu : smu.readReg32 (.gpr 19#5) = errnoVal := by simp [hcs_mu.1, arm64_norm]
  have hsp_mu' : smu.sp = sp0 - 48#64 := by simpa [arm64_norm, hsp_e] using hsp_mu
  have hspAl_mu : smu.spAligned = true := by simpa [State.spAligned, hsp_mu'] using hspAl48
  apply step_str32_perm_kf (ea := tp - 0xa4#64) (wb := none) (val := errnoVal)
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_close_fetch_cl
  · first | wp_norm_lhs | wp_norm_goal
  · simp only [evalAddrMode, arm64_norm, hx21_mu]
  · exact hx19_mu
  · wp_sep_access
  · wp_norm_lhs
  intro m_str hm_str hkf_str
  have _hcl_str := hcl_mu.of_keepsFrozen hkf_str; clear hkf_str
  try wp_norm_state
  wp_step
  let RestF := MallocngRoTablesA maddrs ∗
    MallocngCoreStA γ maddrs brkStart se.brk liveCost' peakCost st' ∗
    MallocngRuntime maddrs tp
  refine SepWP.weaken_pre (P' := RestF ∗ stackFrameAt (sp0 - 48#64) 224 ∗ LibcFreeSpillSlots sp0 s0 w5) ?_ ?_
  · have hMR64 : ∀ a : BitVec 64, a = sp0 - 48#64 - 64#64 →
        memRegion a 64 = stackFrameAt (sp0 - 48#64) 64 := by
      intro a ha; rw [ha, stackFrameAt_eq_memRegion (sp0 - 48#64) 64]
    have hStk : stackFrameAt (sp0 - 48#64) 64 ∗ stackFrameAt (sp0 - 48#64 - 64#64) 160 ⊢
        stackFrameAt (sp0 - 48#64) 224 := by
      rw [← stackFrameAt_224_split_64 (sp0 - 48#64)]; exact Entails.refl _
    let Mid := ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
      MallocngRoTablesA maddrs ∗
      MallocngCoreStA γ maddrs brkStart se.brk liveCost' peakCost st' ∗
      ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
      LibcFreeSpillSlots sp0 s0 w5
    refine Entails.trans (Q := (stackFrameAt (sp0 - 48#64) 64 ∗ stackFrameAt (sp0 - 48#64 - 64#64) 160) ∗ Mid)
      (by dsimp only [FrameMu, Mid]; rw [hMR64 _ (by simp [arm64_norm, hsp_e])]; sep_frame) ?_
    refine Entails.trans (sepConj_mono_left hStk) ?_
    dsimp only [RestF, MallocngRuntime, Mid]
    sep_frame
  · refine SepWP.mono (libcFree_epilogue_ok hb sp0 w5 RestF s0 _
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun_mu])
      (by simp [arm64_norm, hsp_mu']) hsp0 hspAl0 ?_) ?_
    · have hcs0mu : CalleeSaved22_28 s0 smu :=
        calleeSaved22_28_trans hcs0e (calleeSaved22_28_trans
          ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
           by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩
          (calleeSaved22_28_of_preserved hcs_mu))
      exact ⟨by simpa [arm64_norm] using hcs0mu.1, by simpa [arm64_norm] using hcs0mu.2.1,
             by simpa [arm64_norm] using hcs0mu.2.2.1, by simpa [arm64_norm] using hcs0mu.2.2.2.1,
             by simpa [arm64_norm] using hcs0mu.2.2.2.2.1, by simpa [arm64_norm] using hcs0mu.2.2.2.2.2.1,
             by simpa [arm64_norm] using hcs0mu.2.2.2.2.2.2.1, by simpa [calleeSavedVRegs] using hcs0mu.2.2.2.2.2.2.2⟩
    · rintro sf Pf _ _ ⟨hent, hmem_sf, hbrk_sf, hproc_sf, hsp_sf, hcs_sf⟩
      have hperm_sf : sf.mem.perm = smu.mem.perm := by
        rw [hmem_sf]; simp only [arm64_norm] at hm_str ⊢; exact hm_str
      have hbrk_sf' : sf.brk = se.brk := by
        rw [hbrk_sf]; simp only [arm64_norm] at hbrk_mu ⊢; exact hbrk_mu
      have hproc0f : MallocngProcPreserved s0 sf :=
        procPreserved_trans' hproc0e (procPreserved_trans'
          ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
           by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
          (procPreserved_trans' hproc_mu (procPreserved_trans'
            ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
             by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
             by simp [arm64_norm]⟩ hproc_sf)))
      have htp_sf : sf.tpidrEl0 = tp := hproc0f.2.2.1.trans (hproc0e.2.2.1.symm.trans htp_e)
      have hbrks_sf : sf.brkStart = brkStart := hproc0f.2.2.2.1.trans (hproc0e.2.2.2.1.symm.trans hbrks_e)
      have hUnmap0f : MallocngUnmappedRange miBase miLenBv.toNat s0.mem sf.mem :=
        unmappedRange_congr (by simp only [arm64_norm]; exact hperm0e) (hPA ▸ hunmap_mu) hperm_sf
      have hDelta0f : MallocngMappedDelta 0 0 s0.mem sf.mem :=
        mappedDelta_zero_congr (by simp only [arm64_norm]; exact hperm0e) hdelta_mu hperm_sf
      have hNoOrph : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem :=
        noOrphanMappings_of_munmap hUnmap0f (fun a ha => hCov a (hDyn1.symm ▸ ha))
      refine ⟨Entails.trans hent ?_, hsp_sf, hcs_sf⟩
      dsimp only [RestF]; rw [← hbrk_sf']
      exact pack_libcFree_raw_post γ tp brkStart p sp0 n liveCost liveCost' peakCost st st' s0 sf
        hproc0f hDelta0f (hbrk_sf'.trans hbrk0e) hsp0 htp_sf hbrks_sf hliveLe hNoOrph hRel

set_option maxHeartbeats 400000 in
private theorem libcFree_after_unlock_raw_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 6 b)
    (γ : GhostName) (tp brkStart p sp0 w5 miBase miLenBv : BitVec 64)
    (n liveCost liveCost' peakCost : Nat)
    {st st1 st' : MallocngSt}
    (hDyn1 : dynamicRootRegions st1 = dynamicRootRegions st)
    (hliveLe : liveCost' ≤ peakCost)
    (hRel : LibcFreeRawPostRel p n st st')
    (s0 su : State)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl su.mem)
    (hpc : su.pc = b + 0x2d4#64) (hrun : su.status = .Running)
    (hsp : su.sp = sp0 - 48#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hbrk0u : su.brk = s0.brk)
    (htp : su.tpidrEl0 = tp) (hbrks : su.brkStart = brkStart)
    (hperm0u : su.mem.perm = s0.mem.perm) (hproc0u : MallocngProcPreserved s0 su)
    (hcs0u : CalleeSaved22_28 s0 su)
    (hx19 : su.readReg64 (.gpr 19#5) = miLenBv)
    (hx20 : su.readReg64 (.gpr 20#5) = miBase) :
    SepWP (blkPC_b06.rebase b (fun _ => none)) (s0.readReg64 .lr) su
      (MallocngRoTablesA maddrs ∗
       MallocngCoreStA γ maddrs brkStart su.brk liveCost' peakCost st' ∗
       MallocngRuntime maddrs tp ∗
       stackFrameAt (sp0 - 48#64) 224 ∗ LibcFreeSpillSlots sp0 s0 w5 ∗
       NfRetSep st1 st' miBase miLenBv)
      (fun sf Pf =>
        (Pf ⊢ (libcFreeRaw272Spec γ tp brkStart p n liveCost peakCost st).post () s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  have _ := hb
  have hspAl0' : (sp0 &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp0] using hspAl0
  have hspAl : su.spAligned = true := by rw [State.spAligned, hsp]; revert hspAl0'; bv_robdd
  dsimp only [NfRetSep]
  by_cases hZero : miLenBv = 0#64
  · simp only [hZero, ↓reduceIte]
    wp_focus_pure; intro hDynEq
    wp_step
    let Rest := MallocngRoTablesA maddrs ∗
      MallocngCoreStA γ maddrs brkStart su.brk liveCost' peakCost st' ∗
      MallocngRuntime maddrs tp
    refine SepWP.weaken_pre (P' := Rest ∗ stackFrameAt (sp0 - 48#64) 224 ∗ LibcFreeSpillSlots sp0 s0 w5)
      (by dsimp only [Rest]; sep_frame) ?_
    refine SepWP.mono (libcFree_epilogue_ok hb sp0 w5 Rest s0 _
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hsp]) hsp0 hspAl0
      ⟨by simpa [arm64_norm] using hcs0u.1, by simpa [arm64_norm] using hcs0u.2.1,
       by simpa [arm64_norm] using hcs0u.2.2.1, by simpa [arm64_norm] using hcs0u.2.2.2.1,
       by simpa [arm64_norm] using hcs0u.2.2.2.2.1, by simpa [arm64_norm] using hcs0u.2.2.2.2.2.1,
       by simpa [arm64_norm] using hcs0u.2.2.2.2.2.2.1, by simpa [calleeSavedVRegs] using hcs0u.2.2.2.2.2.2.2⟩) ?_
    rintro sf Pf _ _ ⟨hent, hmem_sf, hbrk_sf, hproc_sf, hsp_sf, hcs_sf⟩
    have hperm_sf : sf.mem.perm = s0.mem.perm := by simp [hmem_sf, arm64_norm, hperm0u]
    have hbrk_sf' : sf.brk = su.brk := by simp [hbrk_sf, arm64_norm]
    have hproc0f : MallocngProcPreserved s0 sf :=
      procPreserved_trans' hproc0u (procPreserved_trans'
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩ hproc_sf)
    have htp_sf : sf.tpidrEl0 = tp := by simpa [arm64_norm, htp] using hproc_sf.2.2.1
    have hbrks_sf : sf.brkStart = brkStart := by simpa [arm64_norm, hbrks] using hproc_sf.2.2.2.1
    have hDynSt : dynamicRootRegions st' = dynamicRootRegions st := hDynEq.trans hDyn1
    refine ⟨Entails.trans hent ?_, hsp_sf, hcs_sf⟩
    dsimp only [Rest]; rw [← hbrk_sf']
    exact pack_libcFree_raw_post γ tp brkStart p sp0 n liveCost liveCost' peakCost st st' s0 sf
      hproc0f (mappedDelta_zero_of_perm_eq hperm_sf) (hbrk_sf'.trans hbrk0u) hsp0 htp_sf hbrks_sf
      hliveLe (hDynSt.symm ▸ noOrphanMappings_refl_of_perm_eq hperm_sf) hRel
  · simp only [hZero, ↓reduceIte]
    conv => arg 4; dsimp only []
    wp_focus_pure; rintro ⟨hPos, hAlBase, hAlLen, hFit, hCov⟩
    have hNe0 : (miLenBv == 0#64) = false := beq_false_of_ne hZero
    wp_step
    conv in State.setPC _ _ => simp only [hx19, hNe0, Bool.false_eq_true, ↓reduceIte]
    wp_step
    let FrameE := MallocngRoTablesA maddrs ∗
      MallocngCoreStA γ maddrs brkStart su.brk liveCost' peakCost st' ∗
      MallocngRuntime maddrs tp ∗
      stackFrameAt (sp0 - 48#64) 224 ∗ LibcFreeSpillSlots sp0 s0 w5 ∗
      memRegion miBase miLenBv.toNat ∗ memMapped miBase miLenBv.toNat
    have hErrSub := placed_errnoLocation_perm_ok (P := blkPC_b06.rebase b (fun _ => none))
    refine SepWP.call_subroutine_frame (F := FrameE) (x := ()) (ret_pc := b + 0x2dc#64) hErrSub
      (by simp only [arm64_norm]; rw [hb]; bv_arith)
      (by simp [arm64_norm, hrun])
      (by simpa [State.spAligned, arm64_norm, hsp] using hspAl)
      (by simp [arm64_norm])
      (fun R' hm => by
        rw [← sepConj_assoc]; refine Satisfies.mono (sepConj_mono_left ?_) hm
        dsimp only [withCL, FrameE]
        rw [emp_sepConj, pure_sepConj_of_true (by simpa [arm64_norm] using hcl)]
        sep_frame)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun se hpc_e hrun_e hsp_e hcs_e => ?_)
      (fun _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
    (conv => arg 4; dsimp only [withCL]); wp_focus_pure; rintro ⟨hproc_e, hbrk_e, hperm_e, hx0_e⟩
    wp_focus_pure; intro hcl_e
    have hx0_e' : se.readReg64 (.gpr 0#5) = tp - 0xa4#64 := by simpa [arm64_norm, htp] using hx0_e
    have hx19_e : se.readReg64 (.gpr 19#5) = miLenBv := by simpa [arm64_norm, hx19] using hcs_e.1
    have hx20_e : se.readReg64 (.gpr 20#5) = miBase := by simpa [arm64_norm, hx20] using hcs_e.2.1
    have hsp_e' : se.sp = sp0 - 48#64 := by simpa [arm64_norm, hsp] using hsp_e
    have htp_e : se.tpidrEl0 = tp := by simpa [arm64_norm, htp] using hproc_e.2.2.1
    have hbrks_e : se.brkStart = brkStart := by simpa [arm64_norm, hbrks] using hproc_e.2.2.2.1
    have hbrk_e' : se.brk = su.brk := by simpa [arm64_norm] using hbrk_e
    have hperm0e : se.mem.perm = s0.mem.perm := by simpa [arm64_norm, hperm0u] using hperm_e
    have hproc0e : MallocngProcPreserved s0 se :=
      procPreserved_trans' hproc0u (procPreserved_trans'
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩ hproc_e)
    have hcs0e : CalleeSaved22_28 s0 se :=
      calleeSaved22_28_trans hcs0u (calleeSaved22_28_trans
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩
        (calleeSaved22_28_of_preserved hcs_e))
    refine SepWP.weaken_pre ?_
      (libcFree_munmap_tail_raw_ok hb γ tp brkStart p sp0 w5 miBase miLenBv n liveCost liveCost' peakCost
        hDyn1 hliveLe hRel hPos hAlBase hAlLen hFit hCov s0 se hcl_e hpc_e hrun_e hsp_e' hsp0 hspAl0
        (hbrk_e'.trans hbrk0u) htp_e hbrks_e hperm0e hproc0e hcs0e hx0_e' hx19_e hx20_e)
    dsimp only [FrameE]
    rw [← hbrk_e']
    sep_frame

private noncomputable def CoreWithoutLock [MallocngMultiPlacement] (γ : GhostName) (st : MallocngSt) : SepProp :=
  MallocngLiveAuth γ st.liveMap ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
  (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
  ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
  ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
  ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
  MappedSet st.masterDom (OwnedMappedByte st)

set_option maxHeartbeats 400000 in
private theorem libcFree_slow_raw_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 6 b)
    (γ : GhostName) (tp brkStart p sp0 w5 : BitVec 64)
    (n liveCost liveCost' peakCost : Nat)
    {st st1 : MallocngSt} {g1 : GroupDesc} {idx : Nat}
    (hg1 : g1 ∈ st1.groups) (hIdx1 : idx < g1.slots.length)
    (hSlot1 : g1.slots[idx]'hIdx1 = .claimed)
    (hIdx31 : idx ≤ 31)
    (hDyn1 : dynamicRootRegions st1 = dynamicRootRegions st)
    (hMkRel : ∀ st', SameLiveUserSub st' st1 → LibcFreeRawPostRel p n st st')
    (s0 s : State)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hpc : s.pc = b + 0x2a0#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 48#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hbrk0s : s.brk = s0.brk)
    (htp : s.tpidrEl0 = tp) (hbrks : s.brkStart = brkStart)
    (hperm0s : s.mem.perm = s0.mem.perm) (hproc0s : MallocngProcPreserved s0 s)
    (hcs0s : CalleeSaved22_28 s0 s)
    (hx19 : s.readReg64 (.gpr 19#5) = g1.metaPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = (BitVec.ofNat 32 idx).zeroExtend 64) :
    SepWP (blkPC_b06.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA 1 γ maddrs brkStart s.brk liveCost' peakCost st1 ∗
       MallocngRuntime maddrs tp ∗
       stackFrameAt (sp0 - 48#64) 224 ∗ LibcFreeSpillSlots sp0 s0 w5)
      (fun sf Pf =>
        (Pf ⊢ (libcFreeRaw272Spec γ tp brkStart p n liveCost peakCost st).post () s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  have _ := hb
  have hspAl0' : (sp0 &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp0] using hspAl0
  have hspAl48 : ((sp0 - 48#64) &&& 15#64 == 0#64) = true := by revert hspAl0'; bv_robdd
  have hspAl : s.spAligned = true := by simpa [State.spAligned, hsp] using hspAl48
  have hIdx64 : BitVec.setWidth 64 (BitVec.ofNat 32 idx) = BitVec.ofNat 64 idx := by bv_omega
  conv => arg 4; dsimp only [MallocngRuntime]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  conv => arg 4; change MallocngRoTablesA maddrs ∗
    MallocngCoreStInflightA 1 γ maddrs brkStart s.brk liveCost' peakCost st1 ∗
    MallocngRuntime maddrs tp ∗
    stackFrameAt (sp0 - 48#64) 224 ∗ LibcFreeSpillSlots sp0 s0 w5
  let FrameNt := MallocngRuntime maddrs tp ∗ LibcFreeSpillSlots sp0 s0 w5
  have hNtSub := call_placed_nontrivialFree_fine (P := blkPC_b06.rebase b (fun _ => none))
    γ brkStart liveCost' peakCost st1 g1 idx
  refine SepWP.call_subroutine_frame (F := FrameNt) (x := ()) (ret_pc := b + 0x2c4#64) hNtSub
    (by simp only [arm64_norm]; rw [hb]; bv_arith)
    (by simp [arm64_norm, hrun])
    (by simpa [State.spAligned, arm64_norm, hsp] using hspAl)
    (by simp [arm64_norm])
    (fun R' hm => by
      rw [← sepConj_assoc]; refine Satisfies.mono (sepConj_mono_left ?_) hm
      dsimp only [nontrivialFreeFinePlacedSpec, withCL, FrameNt]
      rw [pure_sepConj_of_true ⟨by simp [arm64_norm], by simp [arm64_norm, hIdx64], hg1, hIdx1, hSlot1⟩,
          sepConj_comm (Q := ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl _⌝),
          pure_sepConj_of_true (by simpa [arm64_norm] using hcl),
          show stackFrame _ 224 = stackFrameAt (sp0 - 48#64) 224 by
            rw [stackFrameAt_eq_memRegion (sp0 - 48#64) 224]; simp [stackFrame, arm64_norm, hsp],
          show (_ : State).brk = s.brk by simp [arm64_norm]]
      sep_frame)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sm hpc_m hrun_m hsp_m hcs_m => ?_)
    (fun _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
  conv => arg 4; dsimp only [nontrivialFreeFinePlacedSpec, withCL]
  wp_focus_pure; intro hcl_m
  conv => arg 4; simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro st'
  wp_focus_pure
  rintro ⟨hproc_m, hbrk_m, htp_m, hperm_m, _hdelta_m, hSubSt, _hLiveLe, _hDynLe⟩
  (conv => arg 4; dsimp only [MallocngCoreStA, MallocngCoreStInflightA]); wp_focus_pure; intro hwf'
  have hwf'_s : MallocngWFInflight 0 maddrs.base brkStart s.brk liveCost' peakCost st' := by
    simpa [arm64_norm] using hwf'
  let miBase := sm.readReg64 (.gpr 0#5)
  let miLenBv := sm.readReg64 (.gpr 1#5)
  have hx21_m : sm.readReg64 (.gpr 21#5) = pageOf maddrs.lock := by simpa [arm64_norm] using hcs_m.2.2.1
  have hsp_m' : sm.sp = sp0 - 48#64 := by simpa [arm64_norm, hsp] using hsp_m
  have hspAl_m : sm.spAligned = true := by simpa [State.spAligned, hsp_m'] using hspAl48
  have hbrk_m' : sm.brk = s.brk := by simpa [arm64_norm] using hbrk_m
  have htp_m' : sm.tpidrEl0 = tp := by simpa [arm64_norm, htp] using htp_m
  have hbrks_m' : sm.brkStart = brkStart := by simpa [arm64_norm, hbrks] using hproc_m.2.2.2.1
  have hperm0m : sm.mem.perm = s0.mem.perm := by simpa [arm64_norm, hperm0s] using hperm_m
  have hproc0m : MallocngProcPreserved s0 sm :=
    procPreserved_trans' hproc0s (procPreserved_trans'
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩ hproc_m)
  have hcs0m : CalleeSaved22_28 s0 sm :=
    calleeSaved22_28_trans hcs0s (calleeSaved22_28_trans
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩
      (calleeSaved22_28_of_preserved hcs_m))
  wp_step; wp_step; wp_step; wp_step
  let PostRem := NfRetSep st1 st' miBase miLenBv
  let FrameU := MallocngRoTablesA maddrs ∗ CoreWithoutLock γ st' ∗
    FrameNt ∗ stackFrameAt (sp0 - 48#64) 224 ∗ PostRem
  have hUnlSub := placed_unlockNoop_perm_ok (P := blkPC_b06.rebase b (fun _ => none)) maddrs.lock
  refine SepWP.call_subroutine_frame (F := FrameU) (x := ()) (ret_pc := b + 0x2d4#64) hUnlSub
    (by simp only [arm64_norm]; rw [hb]; bv_arith)
    (by simp [arm64_norm, hrun_m])
    (by simpa [State.spAligned, arm64_norm, hsp_m'] using hspAl_m)
    (by simp [arm64_norm])
    (fun R' hm => by
      have hMR224 : ∀ a : BitVec 64, a = sp0 - 48#64 - 224#64 →
          memRegion a 224 = stackFrameAt (sp0 - 48#64) 224 := by
        intro a ha; rw [ha, stackFrameAt_eq_memRegion (sp0 - 48#64) 224]
      rw [← sepConj_assoc]; refine Satisfies.mono (sepConj_mono_left ?_) hm
      dsimp only [withCL, FrameU, MallocngCoreStA, MallocngCoreStInflightA, CoreWithoutLock, PostRem, miBase, miLenBv]
      rw [hMR224 _ (by simp [arm64_norm, hsp])]
      conv =>
        rhs
        rw [pure_sepConj_of_true (by simp [arm64_norm]),
            sepConj_comm (Q := ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl _⌝),
            pure_sepConj_of_true (by simpa [arm64_norm] using hcl_m)]
      sep_frame)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun su hpc_u hrun_u hsp_u hcs_u => ?_)
    (fun _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
  (conv => arg 4; dsimp only [withCL]); wp_focus_pure; rintro ⟨hproc_u, hbrk_u, hperm_u⟩
  wp_focus_pure; intro hcl_u
  have hbrk_u' : su.brk = s.brk := by simp only [arm64_norm] at hbrk_u; exact hbrk_u.trans hbrk_m'
  have hsp_u' : su.sp = sp0 - 48#64 := by simpa [arm64_norm, hsp_m'] using hsp_u
  have htp_u : su.tpidrEl0 = tp := by simpa [arm64_norm, htp_m'] using hproc_u.2.2.1
  have hbrks_u : su.brkStart = brkStart := by simpa [arm64_norm, hbrks_m'] using hproc_u.2.2.2.1
  have hperm0u : su.mem.perm = s0.mem.perm := by simpa [arm64_norm, hperm0m] using hperm_u
  have hproc0u : MallocngProcPreserved s0 su :=
    procPreserved_trans' hproc0m (procPreserved_trans'
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩ hproc_u)
  have hcs0u : CalleeSaved22_28 s0 su :=
    calleeSaved22_28_trans hcs0m (calleeSaved22_28_trans
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩
      (calleeSaved22_28_of_preserved hcs_u))
  have hx19_u : su.readReg64 (.gpr 19#5) = miLenBv := by simpa [arm64_norm, miLenBv] using hcs_u.1
  have hx20_u : su.readReg64 (.gpr 20#5) = miBase := by simpa [arm64_norm, miBase] using hcs_u.2.1
  refine SepWP.weaken_pre ?_
    (libcFree_after_unlock_raw_ok hb γ tp brkStart p sp0 w5 miBase miLenBv n liveCost liveCost' peakCost
      hDyn1 hwf'_s.live_le_peak (hMkRel st' hSubSt) s0 su
      hcl_u hpc_u hrun_u hsp_u' hsp0 hspAl0 (hbrk_u'.trans hbrk0s) htp_u hbrks_u hperm0u hproc0u hcs0u hx19_u hx20_u)
  dsimp only [FrameU, FrameNt, MallocngCoreStA, MallocngCoreStInflightA, CoreWithoutLock, PostRem]
  rw [hbrk_u', pure_sepConj_of_true hwf'_s]
  sep_frame

set_option maxHeartbeats 400000 in
private theorem libcFree_fast_or_slow_raw_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 6 b)
    (γ : GhostName) (tp brkStart p sp0 w5 : BitVec 64)
    (n liveCost : Nat) (bf : MallocngBudget)
    {st st1 : MallocngSt} {g1 : GroupDesc} {idx : Nat}
    (hg1 : g1 ∈ st1.groups) (hIdx1 : idx < g1.slots.length)
    (hSlot1 : g1.slots[idx]'hIdx1 = .claimed)
    (hIdx31 : idx ≤ 31)
    (hScCases : g1.sc < 48 ∨ g1.sc = 63)
    (hSc63Last0 : g1.sc = 63 → g1.lastIdx = 0)
    (hCnt1 : MallocngCountIvsWF bf (dynamicRootRegions st) st1)
    (hMkRel : ∀ st', SameLiveUserSub st' st1 → LibcFreeRawPostRel p n st st')
    (s0 s : State)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hpc : s.pc = b + 0x228#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 48#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hbrk0s : s.brk = s0.brk)
    (htp : s.tpidrEl0 = tp) (hbrks : s.brkStart = brkStart)
    (hperm0s : s.mem.perm = s0.mem.perm) (hproc0s : MallocngProcPreserved s0 s)
    (hcs0s : CalleeSaved22_28 s0 s)
    (hw5_reg : s.readReg32 .x5 = 1#32 <<< idx)
    (hw6_reg : s.readReg32 .x6 = (2#32 <<< g1.lastIdx) - 1#32)
    (hx7_reg : s.readReg64 .x7 = maddrs.libc)
    (hx19_reg : s.readReg64 .x19 = g1.metaPtr)
    (hx20_reg : s.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) :
    SepWP (blkPC_b06.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA 1 γ maddrs brkStart s.brk bf.liveCost bf.peakCost st1 ∗
       MallocngRuntime maddrs tp ∗
       stackFrameAt (sp0 - 48#64) 224 ∗ LibcFreeSpillSlots sp0 s0 w5)
      (fun sf Pf =>
        (Pf ⊢ (libcFreeRaw272Spec γ tp brkStart p n liveCost bf.peakCost st).post () s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  have _ := hb
  have hw5 : (s.readReg64 (.gpr 5#5)).truncate 32 = 1#32 <<< idx := hw5_reg
  have hw6 : (s.readReg64 (.gpr 6#5)).truncate 32 = (2#32 <<< g1.lastIdx) - 1#32 := hw6_reg
  have hx7 : s.readReg64 (.gpr 7#5) = maddrs.libc := hx7_reg
  have hx19 : s.readReg64 (.gpr 19#5) = g1.metaPtr := hx19_reg
  have hx20 : s.readReg64 (.gpr 20#5) = (BitVec.ofNat 32 idx).zeroExtend 64 := hx20_reg
  (conv => arg 4; dsimp only [MallocngCoreStInflightA]); wp_focus_pure; intro hwf1
  have hGWf := hwf1.groups_wf g1 hg1
  have hSWf := hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx1
  rw [hSlot1] at hSWf
  have hIdxLe : idx ≤ g1.lastIdx := by have := hGWf.2.2.1; unfold GroupDesc.cnt at this; omega
  have hAv0 : g1.availMask.getLsbD idx = false :=
    Bool.eq_false_iff.mpr fun h => by have := hSWf.2.1.mp h; cases this
  have hFr0 : g1.freedMask.getLsbD idx = false :=
    Bool.eq_false_iff.mpr fun h => by have := hSWf.2.2.1.mp h; cases this
  have hMP := freeSlot_mask_props hIdxLe hGWf.2.1
    hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hAv0 hFr0
  have hAnd0 : (1#32 <<< idx) &&& (g1.availMask ||| g1.freedMask) = 0#32 := by
    rw [BitVec.and_comm]; exact hMP.2.1
  conv => arg 4; rw [focus_meta_of_mem_groups hwf1 hg1]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_if hFrZero
  · refine SepWP.weaken_pre ?_
      (libcFree_slow_raw_ok hb γ tp brkStart p sp0 w5 n liveCost bf.liveCost bf.peakCost
        hg1 hIdx1 hSlot1 hIdx31 hCnt1.2.2.1.symm hMkRel s0 _
        hcl (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp])
        hsp0 hspAl0 (by simp [arm64_norm, hbrk0s]) (by simp [arm64_norm, htp]) (by simp [arm64_norm, hbrks])
        (by simp [arm64_norm, hperm0s])
        (procPreserved_trans' hproc0s ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩)
        (calleeSaved22_28_trans hcs0s
          ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
           by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩)
        (by simp [arm64_norm, hx19]) (by simp [arm64_norm, hx20]))
    dsimp only [MallocngCoreStInflightA]
    rw [← focus_meta_of_mem_groups hwf1 hg1, show (_ : State).brk = s.brk by rfl,
        pure_sepConj_of_true hwf1]
    sep_frame
  · wp_step; wp_step; wp_step
    wp_if hAllEq
    · refine SepWP.weaken_pre ?_
        (libcFree_slow_raw_ok hb γ tp brkStart p sp0 w5 n liveCost bf.liveCost bf.peakCost
          hg1 hIdx1 hSlot1 hIdx31 hCnt1.2.2.1.symm hMkRel s0 _
          hcl (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp])
          hsp0 hspAl0 (by simp [arm64_norm, hbrk0s]) (by simp [arm64_norm, htp]) (by simp [arm64_norm, hbrks])
          (by simp [arm64_norm, hperm0s])
          (procPreserved_trans' hproc0s ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩)
          (calleeSaved22_28_trans hcs0s
            ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
             by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩)
          (by simp [arm64_norm, hx19]) (by simp [arm64_norm, hx20]))
      dsimp only [MallocngCoreStInflightA]
      rw [← focus_meta_of_mem_groups hwf1 hg1, show (_ : State).brk = s.brk by rfl,
          pure_sepConj_of_true hwf1]
      sep_frame
    · have hFrNe0 : g1.freedMask ≠ 0#32 := by
        intro hEq; rw [hEq] at hFrZero; simp [arm64_norm] at hFrZero
      have hNotAll : (g1.availMask ||| g1.freedMask) + (1#32 <<< idx) ≠
          (2#32 <<< g1.lastIdx) - 1#32 := by
        intro hEq; rw [BitVec.add_comm] at hEq
        exact hAllEq hEq
      have hFast := free_set_freedMask_fast hwf1 hCnt1 hg1 hIdx1 hSlot1 hScCases hSc63Last0 hFrNe0 hNotAll
      let g2 := mkFreedKeepGroup g1 idx
      let bv2 := writeBytesToMap st1.byteVal g1.metaPtr g2.metaBytes
      let st2 : MallocngSt := { st1 with groups := replaceGroupByMeta st1.groups g1.metaPtr g2, byteVal := bv2 }
      have hSub2 : SameLiveUserSub st2 st1 :=
        sameLiveUserSub_mkFreedKeepGroup hwf1.groups_nodup.1 hg1 hIdx1 hSlot1 bv2
      conv => arg 4; dsimp only [MallocngRuntime]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro _errnoVal
      wp_step; wp_step; wp_step; wp_step
      apply step_str32_perm_kf (ea := g1.metaPtr + 28#64) (wb := none) (val := g2.freedMask)
      · wp_norm_lhs
      · wp_norm_lhs
      · wp_close_fetch_cl
      · first | wp_norm_lhs | wp_norm_goal
      · simp only [evalAddrMode, arm64_norm, hx19]
      · simp only [arm64_norm]; exact hFast.1
      · wp_sep_access
      · wp_norm_lhs
      intro m1 hm1 hkf1
      have _hcl9 := hcl.of_keepsFrozen hkf1; clear hkf1
      try wp_norm_state
      wp_step
      let RestEp := MallocngRoTablesA maddrs ∗
        MallocngCoreStA γ maddrs brkStart s.brk bf.liveCost bf.peakCost st2 ∗
        MallocngRuntime maddrs tp
      refine SepWP.weaken_pre (P' := RestEp ∗ stackFrameAt (sp0 - 48#64) 224 ∗ LibcFreeSpillSlots sp0 s0 w5) ?_ ?_
      · dsimp only [RestEp, MallocngCoreStA, MallocngCoreStInflightA, MallocngRuntime]
        rw [pure_sepConj_of_true hFast.2.2.2.2.2, hFast.2.1, hFast.2.2.1, ← hFast.2.2.2.1]
        dsimp only [st2]
        sep_frame
      · refine SepWP.mono (libcFree_epilogue_ok hb sp0 w5 RestEp s0 _
          (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) hsp0 hspAl0
          (calleeSaved22_28_trans hcs0s
            ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
             by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩)) ?_
        rintro sf Pf _ _ ⟨hPf, hmem_f, hbrk_f, hproc_f, hsp_f, hcs_f⟩
        have hbrk_sf : sf.brk = s.brk := by simpa [arm64_norm] using hbrk_f
        have hperm_sf : sf.mem.perm = s0.mem.perm := by
          rw [hmem_f]; simp only [arm64_norm]; exact hm1.trans hperm0s
        have hproc0_sf : MallocngProcPreserved s0 sf :=
          procPreserved_trans' hproc0s (procPreserved_trans' ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩ hproc_f)
        have htp_sf : sf.tpidrEl0 = tp := by rw [hproc_f.2.2.1]; simpa [arm64_norm] using htp
        have hbrks_sf : sf.brkStart = brkStart := by rw [hproc_f.2.2.2.1]; simpa [arm64_norm] using hbrks
        have hDyn2 : dynamicRootRegions st2 = dynamicRootRegions st := (hFast.2.2.2.2.1).2.2.1.symm
        refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f⟩
        dsimp only [RestEp]
        rw [← hbrk_sf]
        exact pack_libcFree_raw_post γ tp brkStart p sp0 n liveCost bf.liveCost bf.peakCost st st2 s0 sf
          hproc0_sf (mappedDelta_zero_of_perm_eq hperm_sf) (hbrk_sf.trans hbrk0s) hsp0 htp_sf hbrks_sf
          (hFast.2.2.2.2.2).live_le_peak (hDyn2.symm ▸ noOrphanMappings_refl_of_perm_eq hperm_sf)
          (hMkRel st2 hSub2)

/-! ## Placed Raw `__libc_free` Theorem and Caller Lift -/

set_option maxHeartbeats 400000 in
theorem placed_libcFree_raw_ok [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p : BitVec 64) (n liveCost peakCost : Nat)
    (st : MallocngSt) (hGrp : Cost.GroupsGrpBound 128 st.groups) :
    subroutine_ok (mallocngBlockProg mmpl 6 msvc) (mbase 6)
      (withCL mmpl (libcFreeRaw272Spec γ tp brkStart p n liveCost peakCost st)) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have hfn : ∀ c, (blkPC_b06.rebase c (fun _ => none)).fnAddr "__libc_free" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase, Program.fnOff, Program.findSymbol?, blkPC_b06, PlacedLib.program]
    rw [blkSymsEq_b06]
    have hf : (ProofLib.ProgramReflection.toStringSymbols blkSymChars_b06).find? (·.1 == "__libc_free") =
        some ("__libc_free", 0) := by decide
    rw [hf]; exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b06 (hfn (mbase 6)) fun b hb => ?_
  have _ := hb
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre hspAl0; rw [hfn b] at hpc
  let sp0 := s0.sp
  let P0 := stackFrame s0 272 ∗
    MallocngRoTablesA maddrs ∗
    MallocngCoreStA γ maddrs brkStart s0.brk liveCost peakCost st ∗
    MallocngRuntime maddrs tp ∗
    if p = 0#64 then emp else memRegion p n ∗ MallocngBlockToken γ p n
  have hpre' : s0.mem ⊨ ⌜s0.mem = m0⌝ ∗ ⌜s0.readReg64 .x0 = p ∧ s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗ P0 ∗ R := by
    simpa [libcFreeRaw272Spec, P0, sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hm0, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, htp0, hbrks0⟩, hmem0⟩ := hpre'
  have hcl_s0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem := hm0 ▸ hcl0
  refine ⟨P0, hmem0, ?_⟩
  refine SepWP.mono
    (post := fun sf Pf =>
      (Pf ⊢ (libcFreeRaw272Spec γ tp brkStart p n liveCost peakCost st).post () s0 sf) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (oom := fun _ => ⌜False⌝)
    ?_ (fun sf Pf _ _ ⟨hent, hsp_f, hcs_f⟩ =>
      ⟨Satisfies.mono (sepConj_mono_left hent), hsp_f, hcs_f⟩)
  dsimp only [P0]
  conv =>
    arg 4
    unfold stackFrame
    rw [← stackFrameAt_eq_memRegion s0.sp 272]
  (conv => arg 4; dsimp only [MallocngCoreStA, MallocngCoreStInflightA]); wp_focus_pure; intro hwf
  by_cases hp0 : p = 0#64
  · subst hp0
    wp_step; wp_step
    refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      ⟨?_, by simp [arm64_norm],
       ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
        by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
        by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩⟩
    conv => lhs; simp only [↓reduceIte, sepConj_emp]
    refine Entails.trans ?_
      (pack_libcFree_raw_post γ tp brkStart 0#64 sp0 n liveCost liveCost peakCost st st s0
        (s0.setPC (s0.readReg64 (.gpr 30#5)))
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩
        (mappedDelta_zero_of_perm_eq rfl) rfl rfl htp0 hbrks0 hwf.live_le_peak
        (noOrphanMappings_refl_of_perm_eq rfl) (by simp [LibcFreeRawPostRel]))
    dsimp only [MallocngCoreStA, MallocngCoreStInflightA]
    rw [show (s0.setPC (s0.readReg64 (.gpr 30#5))).brk = s0.brk by rfl, pure_sepConj_of_true hwf]
    sep_frame
  · conv => arg 4; simp only [hp0, ↓reduceIte]
    refine SepWP.weaken_pre (P' := (MallocngLiveAuth γ st.liveMap ∗ MallocngBlockToken γ p n) ∗
      (stackFrameAt sp0 272 ∗ MallocngRoTablesA maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
       ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
       MappedSet st.masterDom (OwnedMappedByte st) ∗ MallocngRuntime maddrs tp ∗ memRegion p n))
      (by sep_frame) ?_
    refine SepWP.weaken_pre (sepConj_mono_left (mallocngBlock_lookup γ st.liveMap p n)) ?_
    wp_focus_pure; rintro ⟨_hBlkWf, hLive⟩
    obtain ⟨g, hg, idx, hIdx, effCost, hSlot⟩ := (hwf.liveMap_wf p n).mp hLive
    have hF := liveUserBlockFacts_of hwf hg hIdx hSlot
    have hn64 : n ≤ 2 ^ 64 := by have := hF.p_add_n_48; omega
    conv => arg 4; rw [memRegion_eq_exists_bytes p n hn64]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro bs
    wp_focus_pure; intro hBsLen
    let bud := synthCoarseFreeBudget liveCost peakCost st
    have hCnt : MallocngCountIvsWF bud (dynamicRootRegions st) st :=
      synthCoarseFreeBudget_countIvsWF liveCost peakCost st hGrp
    let RestStage1 := MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
      (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
      ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
      MappedSet st.masterDom (OwnedMappedByte st) ∗ MallocngRuntime maddrs tp ∗
      (p ↦ₛ bs) ∗ mallocngIface.Block γ p n
    refine SepWP.weaken_pre
      (P' := (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ RestStage1) ∗ stackFrameAt sp0 272)
      (by dsimp only [RestStage1, MallocngRoTablesA, mallocngIface]; sep_frame) ?_
    refine SepWP.seq (libcFree_stage1_ok hb hF RestStage1 hcl_s0 hpc hrun hx0 rfl hspAl0) ?_
    rintro s7 P7 hpc7 hrun7 ⟨w5, hP7, hcl7, hperm7, hbrk7, hproc7, hsp7, _hspAl7, hcs7, hx0_7, hx9_7, hx19_7, hx20_7⟩
    let RestStage2 := MallocngRuntime maddrs tp ∗ stackFrameAt (sp0 - 48#64) 224 ∗ LibcFreeSpillSlots sp0 s0 w5
    refine SepWP.weaken_pre
      (P' := MallocngRoTablesA maddrs ∗
        MallocngCoreStA γ maddrs brkStart s7.brk bud.liveCost bud.peakCost st ∗
        (p ↦ₛ bs) ∗ mallocngIface.Block γ p n ∗ RestStage2)
      (Entails.trans hP7 (by
        rw [hbrk7]
        dsimp only [RestStage1, RestStage2, MallocngRoTablesA, MallocngCoreStA, MallocngCoreStInflightA, mallocngIface, bud]
        rw [synthCoarseFreeBudget_liveCost, synthCoarseFreeBudget_peakCost, pure_sepConj_of_true hwf]; sep_frame)) ?_
    refine SepWP.seq (libcFree_release_ib_ok hb γ brkStart p n effCost idx bud (dynamicRootRegions st)
      (hbrk7 ▸ hwf) hCnt hg hIdx hSlot hBsLen hF.last_le_31 hF.idx_le_last RestStage2
      hcl7 hpc7 hrun7 hx0_7 hx9_7 hx19_7 hx20_7) ?_
    rintro s8 P8 hpc8 hrun8 ⟨hIdx1, hg1, hSlot1, hCnt1, hP8, hcl8, hperm8, hbrk8, hproc8, hsp8, _hspAl8, hcs8, hw5_8, hw6_8, hx7_8, hx19_8, hx20_8⟩
    have hproc08 := procPreserved_trans' hproc7 hproc8
    have htp8 : s8.tpidrEl0 = tp := hproc08.2.2.1.trans htp0
    have hbrks8 : s8.brkStart = brkStart := hproc08.2.2.2.1.trans hbrks0
    have hMkRel : ∀ st', SameLiveUserSub st' (mkReleasedSt st g idx p bs) → LibcFreeRawPostRel p n st st' := by
      intro st' hSub'
      simp only [LibcFreeRawPostRel, hp0, ↓reduceIte]
      exact ⟨g, idx, effCost, hIdx, bs, hg, hSlot, hBsLen, hSub'⟩
    have hPeakEq : (mallocngFreeBudget false n bud).peakCost = peakCost := rfl
    refine SepWP.weaken_pre (Entails.trans hP8 (by dsimp only [RestStage2]; sep_frame)) ?_
    rw [← hPeakEq]
    exact libcFree_fast_or_slow_raw_ok hb γ tp brkStart p sp0 w5 n liveCost (mallocngFreeBudget false n bud)
      hg1 hIdx1 hSlot1 (Nat.le_trans hF.idx_le_last hF.last_le_31)
      hF.sc_cases (fun h => (hF.sc_63_props h).1) hCnt1 hMkRel s0 s8
      hcl8 hpc8 hrun8 (hsp8.trans hsp7) rfl hspAl0 (hbrk8.trans hbrk7) htp8 hbrks8
      (hperm8.trans hperm7) hproc08 (calleeSaved22_28_trans hcs7 hcs8)
      hw5_8 hw6_8 hx7_8 hx19_8 hx20_8

theorem call_placed_libcFree_raw [MallocngMultiPlacement]
    {P : Program} (γ : GhostName) (tp brkStart p : BitVec 64) (n liveCost peakCost : Nat)
    (st : MallocngSt) (hGrp : Cost.GroupsGrpBound 128 st.groups)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = (mallocngBlockProg mmpl 6 msvc).svc := by rfl) :
    subroutine_ok P (mbase 6)
      (withCL mmpl (libcFreeRaw272Spec γ tp brkStart p n liveCost peakCost st)) :=
  subroutine_ok_block_to_block (j := 6) (by decide)
    (placed_libcFree_raw_ok γ tp brkStart p n liveCost peakCost st hGrp) hext hsvc

end LibsignalBinary.Heap.Fine
