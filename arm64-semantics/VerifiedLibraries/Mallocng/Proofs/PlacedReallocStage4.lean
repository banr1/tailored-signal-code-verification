/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocStage3
public import VerifiedLibraries.Mallocng.Proofs.InternalPlaced

/-!
# Placed `__libc_realloc` Out-of-Place and `ENOMEM` Paths

Proves the `__libc_realloc` `ENOMEM` overflow branch (`realloc_enomem_ok`, `+0x2b8` to `ret`) and
the out-of-place `malloc + memcpy + free` path (`realloc_stage4_oop_ok`, `+0x260` to `ret`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Arithmetic, Budget, and Stack Helpers -/

theorem sepWP_bind_state {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ s', s' = s → SepWP prog target s' P post oom) :
    SepWP prog target s P post oom := h s rfl

theorem mallocngProcPreserved_trans {s0 s1 s2 : State}
    (h1 : MallocngProcPreserved s0 s1) (h2 : MallocngProcPreserved s1 s2) :
    MallocngProcPreserved s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2⟩

theorem rdlRealloc_tightOom_congr {svc : State → State} {req1 req2 peak : Nat}
    {s0 sPre sf : State}
    (hle : req1 ≤ req2)
    (hfs : sPre.fs = s0.fs) (htr : sPre.trace = s0.trace)
    (hsig : sPre.sigActions = s0.sigActions) (hperm : sPre.mem.perm = s0.mem.perm)
    (hoom : MallocngTightOomCond svc req1 peak sPre sf) :
    MallocngTightOomCond svc req2 peak s0 sf := by
  rcases hoom with ⟨h1, h2, h3, ivs, hlen, hsum, hcov, hgap⟩
  have hsb : MallocngTightStepBound req1 peak ≤ MallocngTightStepBound req2 peak :=
    MallocngTightStepBound_mono hle
  have htb : MallocngTightTotalBound req1 peak ≤ MallocngTightTotalBound req2 peak :=
    MallocngTightTotalBound_mono hle
  refine ⟨h1.trans hfs, h2.trans htr, h3.trans hsig, ivs, hlen, Nat.le_trans hsum hsb,
    fun a hm => ?_, fun hsan => ?_⟩
  · rcases hcov a hm with hmPre | hin
    · exact Or.inl (by rwa [← hperm])
    · exact Or.inr hin
  · obtain ⟨sz, hmin, hmod, hszLe, htotLe, hng⟩ := hgap hsan
    exact ⟨sz, hmin, hmod, Nat.le_trans hszLe hsb, Nat.le_trans htotLe htb, hng⟩

theorem spAligned_of_sub80 {s : State} {sp0 : BitVec 64}
    (hsp : s.sp = sp0 - 80#64) (h0 : sp0 &&& 15#64 = 0#64) : s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]; revert h0; bv_robdd

theorem stackFrame_eq_stackFrameAt_720 {s : State} {sp1 : BitVec 64} (k : Nat)
    (hk : k ≤ 720) (hsp : s.sp = sp1) : stackFrame s k = stackFrameAt sp1 k := by
  unfold stackFrame; rw [hsp, ← stackFrameAt_eq_memRegion sp1 k (by omega)]

theorem stackFrameAt_720_split (sp1 : BitVec 64) (k m : Nat) (h : k + m = 720) :
    stackFrameAt sp1 720 = (stackFrameAt sp1 k ∗ stackFrameAt (sp1 - BitVec.ofNat 64 k) m) := by
  rw [← h]; exact stackFrameAt_split sp1 k m (by omega)

theorem realloc_oop_budget {oldSz newSz : Nat} {origBs : List (BitVec 8)} {bgt : MallocngBudget}
    (hCostGe : max oldSz MallocngMinBlockCost ≤ bgt.liveCost) :
    mallocngFreeBudget false oldSz (mallocngAllocBudget true newSz bgt) =
      mallocngReallocBudget true (some (oldSz, origBs)) newSz bgt := by
  unfold mallocngFreeBudget mallocngAllocBudget mallocngReallocBudget
  simp only [↓reduceIte, Bool.false_eq_true]; congr 1 <;> omega

theorem pack_mallocImpl_env [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (bf : MallocngBudget)
    (st' : MallocngSt) (sf : State)
    (htp : sf.tpidrEl0 = tp) (hbrks : sf.brkStart = brkStart)
    (hCount : MallocngCountIvsWF bf (dynamicRootRegions st') st') :
    MallocngRoTablesA maddrs ∗
    MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
    MallocngRuntime maddrs tp ⊢
      MallocngEnv mallocngIface γ maddrs tp brkStart bf (dynamicRootRegions st') sf := by
  unfold MallocngEnv
  refine Entails.pure_right ⟨htp, hbrks⟩ ?_
  rw [mallocngHeap_split_runtime]
  change _ ⊢ MallocngCoreImpl γ maddrs brkStart sf.brk bf (dynamicRootRegions st') ∗ MallocngRuntime maddrs tp
  rw [MallocngCoreImpl_eq, ← sepConj_assoc]
  refine sepConj_mono_left (sepConj_mono_right ?_)
  exact Entails.sepExists_right st' (Entails.pure_right hCount (Entails.refl _))

theorem shrink_init_prefix (p : BitVec 64) (origBs : List (BitVec 8)) (oldSz newSz : Nat)
    (hOrigLe : origBs.length ≤ oldSz) (hOld48 : p.toNat + oldSz ≤ 2 ^ 48) :
    let keptBs := origBs.take newSz
    (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ⊢
      (p ↦ₛ keptBs) ∗ memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) := by
  intro keptBs
  have hEq : origBs = keptBs ++ origBs.drop newSz := (List.take_append_drop newSz origBs).symm
  have hKeptLe : keptBs.length ≤ origBs.length := List.length_take_le' newSz origBs
  have hDropLen : (origBs.drop newSz).length = origBs.length - keptBs.length := by
    simp [keptBs, List.length_drop, List.length_take]; omega
  conv => lhs; arg 1; rw [hEq, pointsToBytes_append]
  rw [sepConj_assoc]
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_left (IsBlock.pointsToBytes _ _).entails_memRegion) ?_
  rw [hDropLen]
  have hSplit := memRegion_split_le (p + BitVec.ofNat 64 keptBs.length)
    (origBs.length - keptBs.length) (oldSz - keptBs.length) (by omega) (by omega)
  have hAdd : p + BitVec.ofNat 64 keptBs.length + BitVec.ofNat 64 (origBs.length - keptBs.length) =
      p + BitVec.ofNat 64 origBs.length := by
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hSub : oldSz - keptBs.length - (origBs.length - keptBs.length) = oldSz - origBs.length := by omega
  rw [hAdd, hSub] at hSplit
  rw [← hSplit]
  exact Entails.refl _

theorem cond_ls_subs64_eq_ule (a b : BitVec 64) :
    ConditionHolds .LS (subsPState64 a b) = a.ule b := by
  unfold subsPState64; bv_robdd

theorem ule_ite_toNat_eq_min (a b : BitVec 64) :
    (if a.ule b then a else b).toNat = min a.toNat b.toNat := by
  by_cases h : a.ule b = true
  · simp only [h, ↓reduceIte]; simp only [BitVec.ule, decide_eq_true_eq] at h; omega
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    simp only [BitVec.ule, decide_eq_true_eq] at h; omega

/-! ## `ENOMEM` Overflow Path -/

theorem realloc_enomem_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) {Rest : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x2b8#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hbrk : s.brk = s0.brk)
    (hproc : MallocngProcPreserved s0 s)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23) (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hcs : ReallocUntouchedCS s0 s)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem) :
    let sp1 := s0.sp - 80#64
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗
       (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
        memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
       stackFrameAt sp1 720 ∗
       MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s ∗
       Rest)
      (fun sf Pf =>
        sf.mem.perm = s0.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢ stackFrame s0 800 ∗
          MallocngPostEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 sf ∗ Rest)) oom := by
  intro sp1; have _ := hb
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (mallocngEnv_focus_errno γ maddrs tp brkStart bgt ivs0 s))))) ?_
  refine SepWP.weaken_pre (P' :=
      ⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
      ∃∗ errnoVal : BitVec 32,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (ReallocSavedLo s0 sp1 ∗
         (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
          memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
         stackFrameAt sp1 720 ∗
         (mallocngIface.MallocngCore γ maddrs brkStart s.brk bgt ivs0 ∗
          ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ∗
         Rest))
    (by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_mono fun ev => Entails.of_eq ?_
      generalize (mallocngIface.MallocngCore γ maddrs brkStart s.brk bgt ivs0) = PCore
      generalize (s.tpidrEl0 = tp ∧ s.brkStart = brkStart) = PureE
      ac_rfl) ?_
  apply SepWP.pure_elim; rintro ⟨htp, hbrks⟩
  apply SepWP.exists_left; intro errnoVal
  wp_step
  have hErr := placed_errnoLocation_perm_ok (P := blkPC_b14.rebase b (fun _ => none))
    (by intro pc; simp) rfl
  refine SepWP.call_subroutine_frame hErr (x := ())
    (F := ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
      (ReallocSavedLo s0 sp1 ∗
       (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
        memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
       stackFrameAt sp1 720 ∗
       (mallocngIface.MallocngCore γ maddrs brkStart s.brk bgt ivs0 ∗
        ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ∗
       Rest))
    (ret_pc := b + 0x2bc#64)
    (by simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by simp [hrun])
    (by simpa [State.spAligned] using hal)
    (by simp)
    (fun R' hm => by
      dsimp only [withCL]
      rw [emp_sepConj, satisfies_pure_sepConj]
      exact ⟨hcl, hm⟩)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_
    (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  intro s1 hpc1 hrun1 hsp1 hcs1
  dsimp only [withCL]
  refine SepWP.weaken_pre (P' :=
      ⌜(MallocngProcPreserved s s1 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
        s1.readReg64 .x0 = tp - 0xa4#64) ∧
       VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem⌝ ∗
      (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
       (ReallocSavedLo s0 sp1 ∗
        (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
         memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
        stackFrameAt sp1 720 ∗
        (mallocngIface.MallocngCore γ maddrs brkStart s.brk bgt ivs0 ∗
         ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ∗
        Rest)))
    (by
      rw [sepConj_assoc]
      refine Entails.pure_left fun ⟨hp1, hb1, hm1, hx0_1⟩ => Entails.pure_left fun hcl1 => ?_
      exact Entails.pure_right ⟨⟨⟨hp1.1, hp1.2.1, hp1.2.2.1, hp1.2.2.2.1, hp1.2.2.2.2.1,
        hp1.2.2.2.2.2.1, hp1.2.2.2.2.2.2⟩, hb1, hm1,
        by simpa [htp] using hx0_1⟩, hcl1⟩ (Entails.refl _)) ?_
  apply SepWP.pure_elim; rintro ⟨⟨hproc1, hbrk1, hperm1, hx0_1⟩, hcl1⟩
  have hsp1Eq : s1.sp = s0.sp - 80#64 := by simpa [hsp] using hsp1
  have hal1 : s1.spAligned = true := spAligned_of_sub80 hsp1Eq hsp0
  have _ := hpc1; have _ := hx0_1
  wp_step; wp_step
  wp_str32_cl m2 hm2Perm hcl1 _hcl2
  wp_step
  apply sepWP_bind_state; intro sFin hsFin
  have hpcF : sFin.pc = b + 0x294#64 := by rw [hsFin]; simp
  have hrunF : sFin.status = .Running := by rw [hsFin]; simp [hrun1]
  have hspF : sFin.sp = s0.sp - 80#64 := by rw [hsFin]; simp [hsp1Eq]
  have halF : sFin.spAligned = true := by rw [hsFin]; simpa [State.spAligned] using hal1
  have hPermF : sFin.mem.perm = s0.mem.perm := by
    rw [hsFin]; exact hm2Perm.trans (hperm1.trans hPerm)
  have hbrkF : sFin.brk = s0.brk := by rw [hsFin]; exact hbrk1.trans hbrk
  have hprocF : MallocngProcPreserved s0 sFin := by
    have h01 := mallocngProcPreserved_trans hproc hproc1
    rw [hsFin]
    exact ⟨by simp [h01.1], by simp [h01.2.1], by simp [h01.2.2.1], by simp [h01.2.2.2.1],
           by simp [h01.2.2.2.2.1], by simp [h01.2.2.2.2.2.1], by simp [h01.2.2.2.2.2.2]⟩
  obtain ⟨_, _, _, _, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _hfp1, hv_1⟩ := hcs1
  have hx20F : sFin.readReg64 .x20 = 0#64 := by rw [hsFin]; simp
  have hx23F : sFin.readReg64 .x23 = s0.readReg64 .x23 := by
    rw [hsFin]; simp [Reg.x23] at hx23_1 hx23 ⊢; exact hx23_1.trans hx23
  have hx24F : sFin.readReg64 .x24 = s0.readReg64 .x24 := by
    rw [hsFin]; simp [Reg.x24] at hx24_1 hx24 ⊢; exact hx24_1.trans hx24
  have hx25F : sFin.readReg64 .x25 = s0.readReg64 .x25 := by
    rw [hsFin]; simp [Reg.x25] at hx25_1 hx25 ⊢; exact hx25_1.trans hx25
  have hx26F : sFin.readReg64 .x26 = s0.readReg64 .x26 := by
    rw [hsFin]; simp [Reg.x26] at hx26_1 hx26 ⊢; exact hx26_1.trans hx26
  have hcsF : ReallocUntouchedCS s0 sFin := by
    rw [hsFin]
    exact ⟨by simp [Reg.x27] at hx27_1 ⊢; exact hx27_1.trans hcs.1,
           by simp [Reg.x28] at hx28_1 ⊢; exact hx28_1.trans hcs.2.1,
           by simpa [calleeSavedVRegs] using hv_1.trans hcs.2.2⟩
  clear hsFin
  refine SepWP.weaken_pre (P' :=
      ReallocSavedLo s0 sp1 ∗
      (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
       memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
      stackFrameAt sp1 720 ∗
      (MallocngPostEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 sFin ∗ Rest))
    (by
      have htp0 : s0.tpidrEl0 = tp := hproc.2.2.1.symm.trans htp
      have hbrks0 : s0.brkStart = brkStart := hproc.2.2.2.1.symm.trans hbrks
      have hUnf := mallocngEnv_unfocus_errno γ maddrs tp brkStart bgt ivs0 (s0 := s0) (sf := sFin)
        12#32 hPermF hbrkF (hprocF.2.2.1.trans htp0) (hprocF.2.2.2.1.trans hbrks0)
      rw [← hbrk] at hUnf
      refine Entails.trans (Q := ReallocSavedLo s0 sp1 ∗
          (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
           memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
          stackFrameAt sp1 720 ∗
          ((((tp - 0xa4#64) ↦₃₂ 12#32) ∗
            (mallocngIface.MallocngCore γ maddrs brkStart s.brk bgt ivs0 ∗
             ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) ∗ Rest))
        (Entails.of_eq (by
          generalize (mallocngIface.MallocngCore γ maddrs brkStart s.brk bgt ivs0) = PCore
          ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hUnf)))) ?_
  refine SepWP.mono (realloc_epilogue_ok hb hpcF hrunF hspF halF hsp0 hx20F
    hx23F hx24F hx25F hx26F hcsF) ?_
  intro sf Pf _ _ ⟨hmemEq, hbrkEq, hprocE, hspE, hcsE, hx0E, hPf⟩
  refine ⟨by rw [hmemEq]; exact hPermF, hbrkEq.trans hbrkF,
    mallocngProcPreserved_trans hprocF hprocE, hspE, hcsE, hx0E, ?_⟩
  have hPostCongr := mallocngPostEnv_congr_state (J := mallocngIface) (γ := γ) (A := maddrs)
    (tp := tp) (brkStart := brkStart) (bf := bgt) (ivs0 := ivs0) (s0 := s0)
    hmemEq hbrkEq hprocE.2.2.1 hprocE.2.2.2.1
  rw [hPostCongr] at hPf
  exact Entails.trans hPf (Entails.of_eq (by ac_rfl))

/-! ## Out-of-Place `malloc + memcpy + free` Path -/

private theorem realloc_s4_free_ok [MallocngMultiPlacement]
    (hFree : LibcFreePlacedStmt) {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget)
    (ivs0 ivs1 : List (BitVec 64 × Nat))
    (s0 s3 : State) {p q : BitVec 64} {oldSz newSz al : Nat} (origBs : List (BitVec 8))
    {Frame : SepProp}
    (hpNe : p ≠ 0#64) (hqNe : q ≠ 0#64) (hq16 : 16 ∣ q.toNat) (hq48 : q.toNat + newSz ≤ 2 ^ 48)
    (hCostGe : max oldSz MallocngMinBlockCost ≤ bgt.liveCost)
    (hpc3 : s3.pc = b + 0x284#64) (hrun3 : s3.status = .Running)
    (hsp3Eq : s3.sp = s0.sp - 80#64) (hal3 : s3.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx19_s3 : s3.readReg64 .x19 = p) (hx20_s3 : s3.readReg64 .x20 = q)
    (hcs3 : ReallocUntouchedCS s0 s3) (hcl3 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s3.mem)
    (hProc03 : MallocngProcPreserved s0 s3)
    (hDelta03 : MallocngMappedDelta 16 (MallocngTightStepBound newSz bgt.peakCount) s0.mem s3.mem)
    (hNoOrph03 : MallocngNoOrphanMappings ivs0 ivs1 s0.mem s3.mem) :
    let sp1 := s0.sp - 80#64
    let bf1 := mallocngAllocBudget true newSz bgt
    let bf := mallocngReallocBudget true (some (oldSz, origBs)) newSz bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s3
      (MallocngEnv mallocngIface γ maddrs tp brkStart bf1 ivs1 s3 ∗
       memRegion p oldSz ∗ mallocngIface.Block γ p oldSz ∗
       stackFrameAt sp1 720 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
       MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
       memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame)
      (fun sf Pf =>
        ∃ q' : BitVec 64,
          MallocngCallAccounting 16
            (MallocngTightStepBound (mallocngReallocRes al newSz) bgt.peakCount) s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q' ∧
          (Pf ⊢ stackFrame s0 800 ∗
            MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngTightInitBlock γ al).pureWf q' (newSz, keptBs)⌝ ∗
            (MallocngTightInitBlock γ al).interp q' (newSz, keptBs) ∗ Frame))
      (fun sf => ⌜MallocngTightOomCond msvc newSz bgt.peakCount s0 sf⌝) := by
  intro sp1 bf1 bf keptBs; have _ := hb; have _ := hpc3; have _ := hx19_s3
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  wp_step; wp_step
  apply sepWP_bind_state; intro s4 hs4
  have hsp4Eq : s4.sp = sp1 := by rw [hs4]; simpa using hsp3Eq
  have hmem4Eq : s4.mem = s3.mem := by rw [hs4]; rfl
  have hFreeCall := call_placed_libcFree hFree (P := blkPC_b14.rebase b (fun _ => none))
    γ tp brkStart p oldSz bf1 ivs1 (by intro pc; simp) rfl
  have hEnvS4 : MallocngEnv mallocngIface γ maddrs tp brkStart bf1 ivs1 s3 =
      MallocngEnv mallocngIface γ maddrs tp brkStart bf1 ivs1 s4 := by rw [hs4]; rfl
  have hSf272 : stackFrameAt sp1 720 = (stackFrame s4 272 ∗ stackFrameAt (sp1 - 272#64) 448) := by
    rw [stackFrameAt_720_split sp1 272 448 (by decide),
        ← stackFrame_eq_stackFrameAt_720 272 (by decide) hsp4Eq]
  refine SepWP.call_subroutine_frame hFreeCall (x := ())
    (F := stackFrameAt (sp1 - 272#64) 448 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
      MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
      memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame)
    (ret_pc := b + 0x28c#64)
    (by rw [hs4]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by rw [hs4]; simp [hrun3]) (by rw [hs4]; simpa [State.spAligned] using hal3)
    (by rw [hs4]; simp)
    (fun R' hm => by
      dsimp only [libcFreePlacedSpec, withCL]; simp only [hpNe, ↓reduceIte]
      have hx0_s4 : s4.readReg64 .x0 = p := by rw [hs4]; simp
      have hcl_s4 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem := by rwa [hmem4Eq]
      refine Satisfies.mono ?_ hm; rw [hSf272, hEnvS4]
      refine Entails.trans (Q :=
          (stackFrame s4 272 ∗ MallocngEnv mallocngIface γ maddrs tp brkStart bf1 ivs1 s4 ∗
            (memRegion p oldSz ∗ mallocngIface.Block γ p oldSz)) ∗
          (stackFrameAt (sp1 - 272#64) 448 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
           MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
           memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame) ∗ R')
        (Entails.of_eq (by
          generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bf1 ivs1 s4) = PEnv4
          ac_rfl)) ?_
      refine sepConj_mono_left ?_; rw [sepConj_comm _ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem⌝]
      exact Entails.pure_right hcl_s4 (Entails.pure_right hx0_s4 (Entails.refl _)))
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_
    (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  intro s5 hpc5 hrun5 hsp5 hcs45
  dsimp only [libcFreePlacedSpec, withCL]
  have hBfEq : mallocngFreeBudget (p == 0#64) oldSz bf1 = bf := by
    rw [beq_false_of_ne hpNe]; exact realloc_oop_budget hCostGe
  rw [hBfEq]
  have hsp5Eq : s5.sp = sp1 := by simpa [hsp4Eq] using hsp5
  have hal5 : s5.spAligned = true := spAligned_of_sub80 hsp5Eq hsp0
  refine SepWP.weaken_pre (P' :=
      ⌜MallocngProcPreserved s4 s5 ∧ MallocngMappedDelta 0 0 s4.mem s5.mem⌝ ∗
      ((((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x26)) ∗
       ReallocSavedLo s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs1 s4 s5 ∗
       MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
       memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame))
    (by
      refine Entails.trans (Q :=
          ⌜MallocngProcPreserved s4 s5 ∧ MallocngMappedDelta 0 0 s4.mem s5.mem⌝ ∗
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s5.mem⌝ ∗
          ((stackFrame s4 272 ∗ stackFrameAt (sp1 - 272#64) 448) ∗
           ReallocSavedHi s0 sp1 ∗ ReallocSavedLo s0 sp1 ∗
           MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs1 s4 s5 ∗
           MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
           memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame))
        (Entails.of_eq (by
          generalize (MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs1 s4 s5) = PPost5
          generalize (MallocngProcPreserved s4 s5 ∧ MallocngMappedDelta 0 0 s4.mem s5.mem) = Pure5
          ac_rfl)) ?_
      refine Entails.pure_left fun hP5 => Entails.pure_left fun _hcl5 => Entails.pure_right hP5 ?_
      rw [hSf272.symm, ← reallocSavedHi_eq s0]
      exact Entails.of_eq (by
        generalize (MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs1 s4 s5) = PPost5
        ac_rfl)) ?_
  apply SepWP.pure_elim; rintro ⟨hProc45, hDelta45⟩
  have _ := hpc5; wp_step; wp_step
  obtain ⟨_, hx20_5, _, _, _, _, _, _, hx27_5, hx28_5, _hfp5, hv_5⟩ := hcs45
  have hx20_s5 : s5.readReg64 .x20 = q := by
    rw [hs4] at hx20_5; simp [Reg.x20] at hx20_5 ⊢; exact hx20_5.trans hx20_s3
  apply sepWP_bind_state; intro sFin hsFin
  have hpcF : sFin.pc = b + 0x294#64 := by rw [hsFin]; simp
  have hrunF : sFin.status = .Running := by rw [hsFin]; simp [hrun5]
  have hspF : sFin.sp = s0.sp - 80#64 := by rw [hsFin]; simp [hsp5Eq, sp1]
  have halF : sFin.spAligned = true := by rw [hsFin]; simpa [State.spAligned] using hal5
  have hx20F : sFin.readReg64 .x20 = q := by rw [hsFin]; simp [hx20_s5]
  have hx23F : sFin.readReg64 .x23 = s0.readReg64 .x23 := by rw [hsFin]; simp
  have hx24F : sFin.readReg64 .x24 = s0.readReg64 .x24 := by rw [hsFin]; simp
  have hx25F : sFin.readReg64 .x25 = s0.readReg64 .x25 := by rw [hsFin]; simp
  have hx26F : sFin.readReg64 .x26 = s0.readReg64 .x26 := by rw [hsFin]; simp
  have hcsF : ReallocUntouchedCS s0 sFin := by
    rw [hs4] at hx27_5 hx28_5 hv_5; rw [hsFin]
    exact ⟨by simp [Reg.x27] at hx27_5 ⊢; exact hx27_5.trans hcs3.1,
           by simp [Reg.x28] at hx28_5 ⊢; exact hx28_5.trans hcs3.2.1,
           by simpa [calleeSavedVRegs] using hv_5.trans hcs3.2.2⟩
  have hmemF : sFin.mem = s5.mem := by rw [hsFin]; rfl
  have hbrkF : sFin.brk = s5.brk := by rw [hsFin]; rfl
  have hProc35 : MallocngProcPreserved s3 s5 := by rw [hs4] at hProc45; exact hProc45
  have hProc05 : MallocngProcPreserved s0 s5 := mallocngProcPreserved_trans hProc03 hProc35
  have hProc0F : MallocngProcPreserved s0 sFin := by
    rw [hsFin]
    exact ⟨by simp [hProc05.1], by simp [hProc05.2.1], by simp [hProc05.2.2.1],
           by simp [hProc05.2.2.2.1], by simp [hProc05.2.2.2.2.1],
           by simp [hProc05.2.2.2.2.2.1], by simp [hProc05.2.2.2.2.2.2]⟩
  clear hsFin; rw [hmem4Eq] at hDelta45
  have hPostTrans : MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs1 s4 s5 ⊢
      MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sFin := by
    unfold MallocngPostEnv
    refine Entails.sepExists_elim fun ivsf => Entails.pure_left fun hNoOrph45 => ?_
    rw [hmem4Eq] at hNoOrph45
    have hNoOrph05 : MallocngNoOrphanMappings ivs0 ivsf s0.mem sFin.mem := by
      rw [hmemF]; exact noOrphanMappings_chain_alloc_free hNoOrph03 rfl hDelta45 hNoOrph45
    refine Entails.sepExists_right ivsf (Entails.pure_right hNoOrph05 ?_)
    unfold MallocngEnv
    rw [hbrkF, show sFin.tpidrEl0 = s5.tpidrEl0 from hProc0F.2.2.1.trans hProc05.2.2.1.symm,
        show sFin.brkStart = s5.brkStart from hProc0F.2.2.2.1.trans hProc05.2.2.2.1.symm]
    exact Entails.refl _
  have hInitInterp : (MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
      memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length)) ⊢
      ⌜(MallocngTightInitBlock γ al).pureWf q (newSz, keptBs)⌝ ∗
      (MallocngTightInitBlock γ al).interp q (newSz, keptBs) :=
    Entails.pure_right ⟨hqNe, hq16, by omega, by simp [keptBs]; omega⟩ (Entails.refl _)
  refine SepWP.weaken_pre (P' :=
      ReallocSavedLo s0 sp1 ∗
      (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
       memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
      stackFrameAt sp1 720 ∗
      (MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sFin ∗
       ⌜(MallocngTightInitBlock γ al).pureWf q (newSz, keptBs)⌝ ∗
       (MallocngTightInitBlock γ al).interp q (newSz, keptBs) ∗ Frame))
    (by
      rw [← reallocSavedHi_eq s0]
      refine Entails.trans (sepConj_mono_left (reallocSavedHi_entails_memRegions s0 sp1)) ?_
      refine Entails.trans (Q := ReallocSavedLo s0 sp1 ∗
          (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
           memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
          stackFrameAt sp1 720 ∗
          (MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs1 s4 s5 ∗
           ((MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
             memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length)) ∗ Frame)))
        (Entails.of_eq (by
          generalize (MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs1 s4 s5) = PPost5
          ac_rfl)) ?_
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono hPostTrans ?_)))
      exact Entails.trans (sepConj_mono_left hInitInterp) (Entails.of_eq (by ac_rfl))) ?_
  refine SepWP.mono (realloc_epilogue_ok hb hpcF hrunF hspF halF hsp0 hx20F
    hx23F hx24F hx25F hx26F hcsF) ?_
  intro sf Pf _ _ ⟨hmemEq, hbrkEq, hprocE, hspE, hcsE, hx0E, hPf⟩
  have hDelta0Sf : MallocngMappedDelta 16
      (MallocngTightStepBound (mallocngReallocRes al newSz) bgt.peakCount) s0.mem sf.mem := by
    rw [hmemEq, hmemF]
    exact mappedDelta_mono_bounds (Nat.le_refl 16)
      (MallocngTightStepBound_mono (le_mallocngReallocRes al newSz))
      (mappedDelta_trans_zero_right hDelta03 hDelta45)
  refine ⟨q, ⟨mallocngProcPreserved_trans hProc0F hprocE, hDelta0Sf⟩, hspE, hcsE, hx0E, ?_⟩
  rw [mallocngPostEnv_congr_state (J := mallocngIface) (γ := γ) (A := maddrs)
    (tp := tp) (brkStart := brkStart) (bf := bf) (ivs0 := ivs0) (s0 := s0)
    hmemEq hbrkEq hprocE.2.2.1 hprocE.2.2.2.1] at hPf
  dsimp only [MallocngTightInitBlock] at hPf ⊢
  exact Entails.trans hPf (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 400000 in
theorem realloc_stage4_oop_ok [MallocngMultiPlacement]
    (hImpl : LibcMallocImplPlacedTightKStmt) (hFree : LibcFreePlacedStmt)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) {p : BitVec 64} {oldSz newSz al : Nat} (origBs : List (BitVec 8))
    {Frame : SepProp}
    (hpNe : p ≠ 0#64) (hpOld48 : p.toNat + oldSz ≤ 2 ^ 48)
    (hOrigLe : origBs.length ≤ oldSz) (hNewMax : newSz ≤ MallocngMaxAllocSize)
    (hpc : s.pc = b + 0x260#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hproc : MallocngProcPreserved s0 s)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = p) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hx23 : s.readReg64 .x23 = p + BitVec.ofNat 64 oldSz)
    (hcs : ReallocUntouchedCS s0 s) (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem) :
    let sp1 := s0.sp - 80#64
    let bf := mallocngReallocBudget true (some (oldSz, origBs)) newSz bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s ∗
       MallocngTightBlock γ p oldSz al ∗
       (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ∗
       Frame)
      (fun sf Pf =>
        ∃ q : BitVec 64,
          MallocngCallAccounting 16
            (MallocngTightStepBound (mallocngReallocRes al newSz) bgt.peakCount) s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
          (Pf ⊢ stackFrame s0 800 ∗
            MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngTightInitBlock γ al).pureWf q (newSz, keptBs)⌝ ∗
            (MallocngTightInitBlock γ al).interp q (newSz, keptBs) ∗
            Frame))
      (fun sf => ⌜MallocngTightOomCond msvc newSz bgt.peakCount s0 sf⌝) := by
  intro sp1 bf keptBs; have _ := hb
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (mallocngTightBlock_to_token γ p oldSz al)))))) ?_
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMaxLt64 : MallocngMaxAllocSize < 2 ^ 64 := maxAllocSize_lt_pow64
  apply sepWP_pure_of_sat (φ := max oldSz MallocngMinBlockCost ≤ bgt.liveCost) (fun R hm =>
    liveCost_ge_of_env_block γ maddrs tp brkStart bgt ivs0 s p oldSz
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ∗
       Frame ∗ R)
      (Satisfies.mono (Entails.of_eq (by
        generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s) = PEnv
        ac_rfl)) hm))
  intro hCostGe
  have hNewBvNat : (BitVec.ofNat 64 newSz).toNat = newSz := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (shrink_init_prefix p origBs oldSz newSz hOrigLe hpOld48))))))) ?_
  have _ := hx21
  wp_step; wp_step
  apply sepWP_bind_state; intro s1 hs1
  have hsp1Eq : s1.sp = sp1 := by rw [hs1]; simpa using hsp
  have hmem1Eq : s1.mem = s.mem := by rw [hs1]; rfl
  have hMalloc := call_placed_libcMallocImpl_tightK hImpl (P := blkPC_b14.rebase b (fun _ => none))
    γ tp brkStart bgt ivs0 newSz (by intro pc; simp) rfl
  have hEnvS1 : MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s =
      MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s1 := by rw [hs1]; rfl
  have hSf704 : stackFrameAt sp1 720 = (stackFrame s1 704 ∗ stackFrameAt (sp1 - 704#64) 16) := by
    rw [stackFrameAt_720_split sp1 704 16 (by decide),
        ← stackFrame_eq_stackFrameAt_720 704 (by decide) hsp1Eq]
  refine SepWP.call_subroutine_frame hMalloc (x := ())
    (F := stackFrameAt (sp1 - 704#64) 16 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
      mallocngIface.Block γ p oldSz ∗ (p ↦ₛ keptBs) ∗
      memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗ Frame)
    (ret_pc := b + 0x268#64)
    (by rw [hs1]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by rw [hs1]; simp [hrun]) (by rw [hs1]; simpa [State.spAligned] using hal)
    (by rw [hs1]; simp)
    (fun R' hm => by
      dsimp only [libcMallocImplPlacedTightKSpec, withCL]
      have hx0_s1 : (s1.readReg64 .x0).toNat = newSz := by
        rw [hs1]; simp only [wp_norm, arm64_norm, hNewBvNat]
      have hcl_s1 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem := by rwa [hmem1Eq]
      refine Satisfies.mono ?_ hm; rw [hSf704, hEnvS1]
      refine Entails.trans (Q :=
          (stackFrame s1 704 ∗ MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s1) ∗
          (stackFrameAt (sp1 - 704#64) 16 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
           mallocngIface.Block γ p oldSz ∗ (p ↦ₛ keptBs) ∗
           memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗ Frame) ∗ R')
        (Entails.of_eq (by
          dsimp only [keptBs]
          generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s1) = PEnv
          ac_rfl)) ?_
      refine sepConj_mono_left ?_; rw [sepConj_comm _ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem⌝]
      exact Entails.pure_right hcl_s1 (Entails.pure_right hx0_s1 (Entails.refl _)))
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_
    (fun R' sf _ ho => by
      have ho' := Satisfies.drop_mid ho
      dsimp only [libcMallocImplPlacedTightKSpec, withCL] at ho'; rw [satisfies_pure_sepConj] at ho' ⊢
      obtain ⟨ho1, hR'⟩ := ho'; simp only [hNewMax, decide_true, ↓reduceIte] at ho1
      have hfs1 : s1.fs = s0.fs := by rw [hs1]; exact hproc.1
      have htr1 : s1.trace = s0.trace := by rw [hs1]; exact hproc.2.1
      have hsig1 : s1.sigActions = s0.sigActions := by rw [hs1]; exact hproc.2.2.2.2.2.2
      have hp1 : s1.mem.perm = s0.mem.perm := by rw [hmem1Eq]; exact hPerm
      exact ⟨rdlRealloc_tightOom_congr (Nat.le_refl newSz)
        hfs1 htr1 hsig1 hp1 ho1, hR'⟩)
  intro s2 hpc2 hrun2 hsp2 hcs12
  let bf1 := mallocngAllocBudget true newSz bgt
  dsimp only [libcMallocImplPlacedTightKSpec, withCL]; simp only [hNewMax, decide_true, ↓reduceIte]
  refine SepWP.weaken_pre (P' :=
      ∃∗ q : BitVec 64, ∃∗ bsNew : List (BitVec 8), ∃∗ st' : MallocngSt,
        ⌜MallocngProcPreserved s1 s2 ∧
         MallocngMappedDelta 16 (MallocngTightStepBound newSz bgt.peakCount) s1.mem s2.mem ∧
         VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem ∧
         s2.readReg64 .x0 = q ∧ s2.tpidrEl0 = tp ∧ s2.brkStart = brkStart ∧
         MallocngBlockWf q newSz ∧ bsNew.length = newSz ∧
         MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s1.mem s2.mem ∧
         MallocngCountIvsWF bf1 (dynamicRootRegions st') st'⌝ ∗
        (MallocngEnv mallocngIface γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
         memRegion q newSz ∗ MallocngTightBlock γ q newSz al ∗
         stackFrameAt sp1 720 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
         mallocngIface.Block γ p oldSz ∗
         (p ↦ₛ keptBs) ∗ memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗
         Frame))
    (by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_mono fun q => Entails.sepExists_mono fun bsNew =>
        Entails.sepExists_mono fun st' => ?_
      have hPackEnv := pack_mallocImpl_env γ tp brkStart bf1 st' s2
      refine Entails.trans (Q :=
          ⌜MallocngProcPreserved s1 s2 ∧
            MallocngMappedDelta 16 (MallocngTightStepBound newSz bgt.peakCount) s1.mem s2.mem⌝ ∗
          ⌜s2.readReg64 .x0 = q ∧ s2.tpidrEl0 = tp ∧ s2.brkStart = brkStart ∧
            MallocngBlockWf q newSz ∧ bsNew.length = newSz ∧
            MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s1.mem s2.mem ∧
            MallocngCountIvsWF bf1 (dynamicRootRegions st') st' ∧
            ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
              g'.slots[idx]'hIdx = .liveUser q newSz (max newSz MallocngMinBlockCost) ∧
              q.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
              (g'.isMmapped = true → bsNew = List.replicate newSz 0#8)⌝ ∗
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem⌝ ∗
          ((MallocngRoTablesA maddrs ∗
            MallocngCoreStA γ maddrs brkStart s2.brk bf1.liveCost bf1.peakCost st' ∗
            MallocngRuntime maddrs tp) ∗ (q ↦ₛ bsNew) ∗ MallocngBlockTokenK γ q newSz 0 ∗
           (stackFrame s1 704 ∗ stackFrameAt (sp1 - 704#64) 16) ∗
           ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
           mallocngIface.Block γ p oldSz ∗ (p ↦ₛ keptBs) ∗
           memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗ Frame))
        (Entails.of_eq (by
          dsimp only [bf1, keptBs]
          generalize (MallocngRoTablesA maddrs) = PRo
          generalize (MallocngCoreStA γ maddrs brkStart s2.brk
            (mallocngAllocBudget true newSz bgt).liveCost
            (mallocngAllocBudget true newSz bgt).peakCost st') = PSt
          generalize (MallocngRuntime maddrs tp) = PRt
          ac_rfl)) ?_
      refine Entails.pure_left fun ⟨hProc2, hDelta2⟩ =>
        Entails.pure_left fun ⟨hx0_2, htp2, hbrks2, hWfQ, hbsLen, hNoOrph2, hCnt2, _⟩ =>
        Entails.pure_left fun hcl2 => ?_
      refine Entails.pure_right ⟨hProc2, hDelta2, hcl2, hx0_2,
        htp2, hbrks2, hWfQ, hbsLen, hNoOrph2, hCnt2⟩ ?_
      rw [hSf704.symm]
      have hRegQ' : (q ↦ₛ bsNew) ⊢ memRegion q newSz := by
        rw [← hbsLen]; exact (IsBlock.pointsToBytes q bsNew).entails_memRegion
      exact sepConj_mono (hPackEnv htp2 hbrks2 hCnt2) (sepConj_mono hRegQ' (sepConj_mono_left (mallocngBlockTokenK_to_tight γ q newSz 0 al (Nat.zero_le _))))) ?_
  apply SepWP.exists_left; intro q; apply SepWP.exists_left; intro _bsNew
  apply SepWP.exists_left; intro st'; apply SepWP.pure_elim
  rintro ⟨hProc12, hDelta12, hcl2, hx0_2, _htp2, _hbrks2, ⟨hqNe, hq16, hq48, _⟩, _hbsLen, hNoOrph12, _hCnt2⟩
  have hsp2Eq : s2.sp = sp1 := by simpa [hsp1Eq] using hsp2
  have hal2 : s2.spAligned = true := spAligned_of_sub80 hsp2Eq hsp0
  obtain ⟨hx19_2, _, hx21_2, _, hx23_2, _, _, _, hx27_2, hx28_2, _hfp2, hv_2⟩ := hcs12
  have hx19_s2 : s2.readReg64 .x19 = p := by
    rw [hs1] at hx19_2; simp [Reg.x19] at hx19_2 ⊢; exact hx19_2.trans hx19
  have hx21_s2 : s2.readReg64 .x21 = BitVec.ofNat 64 newSz := by
    rw [hs1] at hx21_2; simp [Reg.x21] at hx21_2 ⊢; exact hx21_2.trans hx21
  have hx23_s2 : s2.readReg64 .x23 = p + BitVec.ofNat 64 oldSz := by
    rw [hs1] at hx23_2; simp [Reg.x23] at hx23_2 ⊢; exact hx23_2.trans hx23
  have _ := hpc2; have _ := hx19_s2; have _ := hx21_s2; have _ := hx23_s2
  wp_step; wp_step
  wp_if hzQ
  · exact absurd hzQ hqNe
  ·
    wp_step; wp_step; wp_step; wp_step; wp_step
    let copyLen := min oldSz newSz
    have hKeptLenLe : keptBs.length ≤ copyLen := by
      dsimp only [keptBs, copyLen]; rw [List.length_take]; omega
    refine SepWP.weaken_pre (P' :=
        ∃∗ dstBs : List (BitVec 8), ∃∗ midBs : List (BitVec 8),
          ⌜dstBs.length = copyLen ∧ (keptBs ++ midBs).length = copyLen⌝ ∗
          (((q ↦ₛ dstBs) ∗ (p ↦ₛ (keptBs ++ midBs))) ∗
           (memRegion (p + BitVec.ofNat 64 copyLen) (oldSz - copyLen) ∗
            memRegion (q + BitVec.ofNat 64 copyLen) (newSz - copyLen) ∗
            MallocngEnv mallocngIface γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
            MallocngTightBlock γ q newSz al ∗
            stackFrameAt sp1 720 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
            mallocngIface.Block γ p oldSz ∗ Frame)))
      (by
        have hPrep := copyPrep_entails p q keptBs oldSz newSz copyLen
          hKeptLenLe (Nat.min_le_left _ _) (Nat.min_le_right _ _) (by omega) (by omega)
        refine Entails.trans (Q :=
            ((p ↦ₛ keptBs) ∗ memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗
              memRegion q newSz) ∗
            (MallocngEnv mallocngIface γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
             MallocngTightBlock γ q newSz al ∗ stackFrameAt sp1 720 ∗
             ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ mallocngIface.Block γ p oldSz ∗ Frame))
          (Entails.of_eq (by
            generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2) = PEnv2
            ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left hPrep) ?_
        simp only [sepExists_sepConj_left]
        refine Entails.sepExists_mono fun dstBs => Entails.sepExists_mono fun midBs => Entails.of_eq ?_
        generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2) = PEnv2
        generalize (dstBs.length = copyLen ∧ (keptBs ++ midBs).length = copyLen) = PurePrep
        ac_rfl) ?_
    apply SepWP.exists_left; intro dstBs; apply SepWP.exists_left; intro midBs
    apply SepWP.pure_elim; rintro ⟨hDstLen, hMidLen⟩
    have hMemcpy := placed_memcpy_perm_ok (P := blkPC_b14.rebase b (fun _ => none))
      q p dstBs (keptBs ++ midBs) copyLen hDstLen hMidLen (by dsimp only [copyLen]; omega)
      (by intro pc; simp) rfl
    have hSubOld : (p + BitVec.ofNat 64 oldSz) - p = BitVec.ofNat 64 oldSz := by bv_lin
    have hOldBvNat : (BitVec.ofNat 64 oldSz).toNat = oldSz := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    apply sepWP_bind_state; intro s2c hs2c
    refine SepWP.call_subroutine_frame hMemcpy (x := ())
      (F := memRegion (p + BitVec.ofNat 64 copyLen) (oldSz - copyLen) ∗
            memRegion (q + BitVec.ofNat 64 copyLen) (newSz - copyLen) ∗
            MallocngEnv mallocngIface γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
            MallocngTightBlock γ q newSz al ∗ stackFrameAt sp1 720 ∗
            ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ mallocngIface.Block γ p oldSz ∗ Frame)
      (ret_pc := b + 0x284#64)
      (by rw [hs2c]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
      (by rw [hs2c]; simp [hrun2]) (by rw [hs2c]; simpa [State.spAligned] using hal2)
      (by rw [hs2c]; simp)
      (fun R' hm => by
        dsimp only [withCL]
        have hcl_2c : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2c.mem := by rw [hs2c]; exact hcl2
        have hArgs : s2c.readReg64 .x0 = q ∧ s2c.readReg64 .x1 = p ∧ (s2c.readReg64 .x2).toNat = copyLen := by
          rw [hs2c]; refine ⟨by simp [hx0_2], by simp, ?_⟩
          simp only [wp_norm, arm64_norm, hSubOld]; rw [ule_ite_toNat_eq_min, hOldBvNat, hNewBvNat]
        rw [sepConj_assoc] at hm
        refine Satisfies.mono (sepConj_mono_left ?_) hm
        rw [sepConj_comm _ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2c.mem⌝]
        exact Entails.pure_right hcl_2c (Entails.pure_right hArgs (Entails.of_eq (by ac_rfl))))
      (fun _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      ?_
      (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
    intro s3 hpc3 hrun3 hsp3 hcs23
    dsimp only [withCL]
    refine SepWP.weaken_pre (P' :=
        ⌜(MallocngProcPreserved s2 s3 ∧ s3.brk = s2.brk ∧ s3.mem.perm = s2.mem.perm) ∧
         VerifiedLibraries.mallocngLib.CodeLoaded mmpl s3.mem⌝ ∗
        (MallocngEnv mallocngIface γ maddrs tp brkStart bf1 (dynamicRootRegions st') s3 ∗
         memRegion p oldSz ∗ mallocngIface.Block γ p oldSz ∗
         stackFrameAt sp1 720 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
         MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
         memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame))
      (by
        have hFin := copyFinish_entails p q keptBs midBs oldSz newSz copyLen
          hMidLen (Nat.min_le_left _ _) (Nat.min_le_right _ _) (by omega) (by omega)
        refine Entails.trans (Q :=
            ⌜MallocngProcPreserved s2c s3 ∧ s3.brk = s2c.brk ∧
              s3.mem.perm = s2c.mem.perm ∧ s3.readReg64 .x0 = q⌝ ∗
            ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s3.mem⌝ ∗
            (((q ↦ₛ (keptBs ++ midBs)) ∗ (p ↦ₛ (keptBs ++ midBs)) ∗
              memRegion (p + BitVec.ofNat 64 copyLen) (oldSz - copyLen) ∗
              memRegion (q + BitVec.ofNat 64 copyLen) (newSz - copyLen)) ∗
             MallocngEnv mallocngIface γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
             MallocngTightBlock γ q newSz al ∗ stackFrameAt sp1 720 ∗
             ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ mallocngIface.Block γ p oldSz ∗ Frame))
          (Entails.of_eq (by
            generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2) = PEnv2
            generalize (MallocngProcPreserved s2c s3 ∧ s3.brk = s2c.brk ∧
              s3.mem.perm = s2c.mem.perm ∧ s3.readReg64 .x0 = q) = Pure3
            ac_rfl)) ?_
        refine Entails.pure_left fun ⟨hp3, hbrk3, hperm3, _⟩ => Entails.pure_left fun hcl3 => ?_
        have hp3' : MallocngProcPreserved s2 s3 := by rw [hs2c] at hp3; exact hp3
        have hbrk3' : s3.brk = s2.brk := by rw [hs2c] at hbrk3; exact hbrk3
        have hperm3' : s3.mem.perm = s2.mem.perm := by rw [hs2c] at hperm3; exact hperm3
        have hEnv23 : MallocngEnv mallocngIface γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 =
            MallocngEnv mallocngIface γ maddrs tp brkStart bf1 (dynamicRootRegions st') s3 := by
          unfold MallocngEnv; rw [hbrk3', hp3'.2.2.1, hp3'.2.2.2.1]
        rw [hEnv23]
        refine Entails.pure_right ⟨⟨hp3', hbrk3', hperm3'⟩, hcl3⟩ ?_
        refine Entails.trans (sepConj_mono_left hFin) ?_
        exact Entails.of_eq (by
          generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bf1 (dynamicRootRegions st') s3) = PEnv3
          ac_rfl)) ?_
    apply SepWP.pure_elim; rintro ⟨⟨hProc23, _hbrk23, hperm23⟩, hcl3⟩
    have hsp3Eq : s3.sp = sp1 := by rw [hs2c] at hsp3; simpa [hsp2Eq] using hsp3
    have hal3 : s3.spAligned = true := spAligned_of_sub80 hsp3Eq hsp0
    obtain ⟨hx19_3, hx20_3, _, _, _, _, _, _, hx27_3, hx28_3, _hfp3, hv_3⟩ := hcs23
    have hx19_s3 : s3.readReg64 .x19 = p := by
      rw [hs2c] at hx19_3; simp [Reg.x19] at hx19_3 ⊢; exact hx19_3.trans hx19_s2
    have hx20_s3 : s3.readReg64 .x20 = q := by
      rw [hs2c] at hx20_3; simpa [Reg.x20] using hx20_3
    have hcs3 : ReallocUntouchedCS s0 s3 := by
      rw [hs2c] at hx27_3 hx28_3 hv_3; rw [hs1] at hx27_2 hx28_2 hv_2
      exact ⟨by simp [Reg.x27] at hx27_3 hx27_2 ⊢; exact hx27_3.trans (hx27_2.trans hcs.1),
             by simp [Reg.x28] at hx28_3 hx28_2 ⊢; exact hx28_3.trans (hx28_2.trans hcs.2.1),
             by simpa [calleeSavedVRegs] using hv_3.trans (hv_2.trans hcs.2.2)⟩
    have hProcS2 : MallocngProcPreserved s s2 := by rw [hs1] at hProc12; exact hProc12
    have hProc03 : MallocngProcPreserved s0 s3 :=
      mallocngProcPreserved_trans hproc (mallocngProcPreserved_trans hProcS2 hProc23)
    have hDelta03 : MallocngMappedDelta 16 (MallocngTightStepBound newSz bgt.peakCount) s0.mem s3.mem := by
      rw [hmem1Eq] at hDelta12
      have h0s : MallocngMappedDelta 0 0 s0.mem s.mem :=
        ⟨[], by decide, by decide, fun _ hm => Or.inl (by rwa [hPerm] at hm)⟩
      have h23 : MallocngMappedDelta 0 0 s2.mem s3.mem :=
        ⟨[], by decide, by decide, fun _ hm => Or.inl (by rwa [hperm23] at hm)⟩
      exact mappedDelta_trans_zero_right (mappedDelta_zero_trans_left h0s hDelta12) h23
    have hNoOrph03 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem s3.mem := by
      intro a hm3 hor0
      exact hNoOrph12 a (by rwa [← hperm23]) (hor0.imp (fun h0 => by rwa [hmem1Eq, hPerm]) id)
    exact realloc_s4_free_ok (al := al) hFree hb γ tp brkStart bgt ivs0 (dynamicRootRegions st') s0 s3 origBs
      hpNe hqNe hq16 hq48 hCostGe hpc3 hrun3 hsp3Eq hal3 hsp0 hx19_s3 hx20_s3
      hcs3 hcl3 hProc03 hDelta03 hNoOrph03

end VerifiedLibraries.Mallocng.Proofs
