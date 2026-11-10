/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.FreeFineInst
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocNullPath
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocStage4

/-!
# Fine-Grained `__libc_realloc` Stage 4 Helpers

Provides `__libc_malloc_impl` cross-block lifts, `FineStepBound` monotonicity and `errno` focus
helpers, raw `malloc` commit into `FineBudget.stepReallocAdd`, and the Stage 4 `free` + epilogue
tail (`+0x284 → ret`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## `__libc_malloc_impl` Lifts and `FineStepBound` Helpers -/

theorem call_placed_libcMallocImpl_fine [MallocngMultiPlacement]
    (h : LibcMallocImplFineStmt) {P : Program}
    (γ : GhostName) (tp brkStart : BitVec 64) (b : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = (mallocngBlockProg mmpl 9 msvc).svc := by rfl) :
    subroutine_ok P (mbase 9) (libcMallocImplFineSpec γ tp brkStart b ivs0 req) :=
  subroutine_ok_block_to_block (j := 9) (by decide) (h γ tp brkStart b ivs0 req) hext hsvc

theorem call_placed_libcMallocImpl_raw_fine [MallocngMultiPlacement]
    (h : LibcMallocImplFineRawStmt) {P : Program}
    (γ : GhostName) (tp brkStart : BitVec 64) (b : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = (mallocngBlockProg mmpl 9 msvc).svc := by rfl) :
    subroutine_ok P (mbase 9) (libcMallocImplFineRawSpec γ tp brkStart b ivs0 req) :=
  subroutine_ok_block_to_block (j := 9) (by decide) (h γ tp brkStart b ivs0 req) hext hsvc

theorem FineStepBound_alloc_le (req align m : Nat) :
    FineStepBound req 16 m ≤ FineStepBound req align m := by
  unfold FineStepBound
  have hMono : pageAlignUp (req + (max 16 16 - 16) + 8192) ≤
      pageAlignUp (req + (max align 16 - 16) + 8192) := by
    unfold pageAlignUp
    exact Nat.mul_le_mul_right _ (Nat.div_le_div_right (by omega))
  omega

theorem fineStepReserve_alloc_le_realloc (req align oldSz : Nat) (b : FineBudget) :
    fineStepReserve (.alloc req) b ≤ fineStepReserve (.realloc align oldSz req) b :=
  FineStepBound_alloc_le req align (fineMaxMetaAreas b)

theorem fineStepReserve_null_eq (ok : Bool) (req : Nat) (b : FineBudget) :
    fineStepReserve (if ok then .alloc req else .alloc 0) b =
      if ok then fineStepReserve (.realloc 16 0 req) b else fineStepReserve (.alloc 0) b := by
  cases ok <;> rfl

theorem fineMaxMetaAreas_le_stepReallocAdd (align newSz : Nat) (b : FineBudget) :
    fineMaxMetaAreas b ≤ fineMaxMetaAreas (FineBudget.stepReallocAdd align newSz b) := by
  have hMono := fineMaxMetaAreas_mono (.realloc align 0 newSz) b
  have hEq : fineMaxMetaAreas (FineBudget.step (.realloc align 0 newSz) b) =
      fineMaxMetaAreas (FineBudget.stepReallocAdd align newSz b) := by
    unfold FineBudget.step FineBudget.stepRealloc fineMaxMetaAreas fineMaxGroups
    unfold FineBudget.stepFree finePeak63Count
    dsimp only
    split <;> simp
  rwa [hEq] at hMono

theorem fineStepOomCond_congr {svc : State → State} {b1 b2 : Nat}
    {s0 sPre sf : State}
    (hb : b1 ≤ b2)
    (hfs : sPre.fs = s0.fs) (htr : sPre.trace = s0.trace)
    (hsig : sPre.sigActions = s0.sigActions) (hperm : sPre.mem.perm = s0.mem.perm)
    (hoom : FineStepOomCond svc b1 sPre sf) :
    FineStepOomCond svc b2 s0 sf := by
  obtain ⟨hf1, ht1, hs1, hdelta, hgap⟩ := hoom
  refine ⟨hf1.trans hfs, ht1.trans htr, hs1.trans hsig, ?_, fun hsan => ?_⟩
  · obtain ⟨ivs, hlen, hsum, hcov⟩ := hdelta
    refine ⟨ivs, hlen, Nat.le_trans hsum hb, fun a hm => ?_⟩
    rcases hcov a hm with hmPre | hin
    · exact Or.inl (by rwa [← hperm])
    · exact Or.inr hin
  · obtain ⟨sz, hlo, hmod, hhi, hng⟩ := hgap hsan
    exact ⟨sz, hlo, hmod, Nat.le_trans hhi hb, hng⟩

theorem fineEnv_focus_errno (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (b : FineBudget) (ivs : List (BitVec 64 × Nat)) (s : State) :
    FineEnv γ A tp brkStart b ivs s ⊢
      ⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
      ∃∗ errnoVal : BitVec 32,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (FineCoreImpl γ A brkStart s.brk b ivs ∗
         ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) := by
  unfold FineEnv
  rw [FineHeapImpl_eq]
  unfold MallocngRuntime
  refine sepConj_mono_right ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_mono fun _ => Entails.of_eq (by
    generalize (FineCoreImpl γ A brkStart s.brk b ivs) = PCore
    ac_rfl)

theorem fineEnv_unfocus_errno (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (b : FineBudget) (ivs : List (BitVec 64 × Nat))
    {s0 sf : State} (errnoVal' : BitVec 32)
    (hPerm : sf.mem.perm = s0.mem.perm) (hBrk : sf.brk = s0.brk)
    (hTp : sf.tpidrEl0 = tp) (hBrkS : sf.brkStart = brkStart) :
    ((tp - 0xa4#64) ↦₃₂ errnoVal') ∗
    (FineCoreImpl γ A brkStart s0.brk b ivs ∗
     ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) ⊢
      FinePostEnv γ A tp brkStart b ivs s0 sf := by
  unfold FinePostEnv
  have hNoOrph : MallocngNoOrphanMappings ivs ivs s0.mem sf.mem := by
    intro a hm hor
    rcases hor with hnot | hin
    · rw [hPerm, hnot] at hm; cases hm
    · exact hin
  refine Entails.sepExists_right ivs (Entails.pure_right hNoOrph ?_)
  unfold FineEnv
  refine Entails.pure_right ⟨hTp, hBrkS⟩ ?_
  rw [hBrk, FineHeapImpl_eq]
  unfold MallocngRuntime
  refine Entails.trans (sepConj_mono_left
    (Entails.sepExists_intro (P := fun ev => (tp - 0xa4#64) ↦₃₂ ev) errnoVal')) ?_
  exact Entails.of_eq (by ac_rfl)

theorem finePostEnv_congr_state {γ : GhostName} {A : MallocngAddrs}
    {tp brkStart : BitVec 64} {bf : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {s0 s1 s2 : State}
    (hmem : s2.mem = s1.mem) (hbrk : s2.brk = s1.brk)
    (htp : s2.tpidrEl0 = s1.tpidrEl0) (hbrks : s2.brkStart = s1.brkStart) :
    FinePostEnv γ A tp brkStart bf ivs0 s0 s1 =
      FinePostEnv γ A tp brkStart bf ivs0 s0 s2 := by
  unfold FinePostEnv FineEnv
  simp only [hmem, hbrk, htp, hbrks]

theorem fineMallocBlock_to_initBlock_nil (γ : GhostName) (q : BitVec 64)
    (bs : List (BitVec 8)) (req : Nat)
    (hwf : MallocngBlockWf q req) (hlen : bs.length = req) :
    (FineInitBlockSem γ).pureWf q (req, 16, []) ∧
    ((q ↦ₛ bs) ∗ FineBlock γ q req 16 ⊢
      (FineInitBlockSem γ).interp q (req, 16, [])) := by
  obtain ⟨hne, h16, h48, _⟩ := hwf
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by decide
  refine ⟨⟨hne, h16, by omega, Nat.zero_le req⟩, ?_⟩
  dsimp only [FineInitBlockSem, List.length_nil, Nat.sub_zero]
  have hMax16 : max 16 16 = 16 := rfl
  rw [hMax16, pointsToBytes_nil, emp_sepConj,
      show q + BitVec.ofNat 64 0 = q from BitVec.add_zero q,
      sepConj_comm (q ↦ₛ bs)]
  refine sepConj_mono_right ?_
  simpa [hlen] using (IsBlock.pointsToBytes q bs).entails_memRegion

theorem pack_fineImpl_postEnv [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bf : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (alignMap' : BitVec 64 → Option Nat) (live' peak' : Nat)
    (st' : MallocngSt) (s0 sf : State)
    (htp : sf.tpidrEl0 = tp) (hbrks : sf.brkStart = brkStart)
    (hNoOrph : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem) :
    MallocngRoTablesA maddrs ∗
    FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
      (dynamicRootRegions st') alignMap' live' peak' st' ∗
    MallocngRuntime maddrs tp ⊢
      FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf := by
  unfold FinePostEnv FineEnv
  refine Entails.sepExists_right (dynamicRootRegions st') (Entails.pure_right hNoOrph ?_)
  refine Entails.pure_right ⟨htp, hbrks⟩ ?_
  rw [FineHeapImpl_eq, FineCoreImpl_eq]
  have hCoreEnt :
      FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
        (dynamicRootRegions st') alignMap' live' peak' st' ⊢
        ∃∗ st1 : MallocngSt, ∃∗ am1 : BitVec 64 → Option Nat,
        ∃∗ lc1 : Nat, ∃∗ pc1 : Nat,
          FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
            (dynamicRootRegions st') am1 lc1 pc1 st1 :=
    Entails.sepExists_right st' (Entails.sepExists_right alignMap'
      (Entails.sepExists_right live' (Entails.sepExists_right peak' (Entails.refl _))))
  refine Entails.trans (Q :=
      (MallocngRoTablesA maddrs ∗
       FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
         (dynamicRootRegions st') alignMap' live' peak' st') ∗
      MallocngRuntime maddrs tp)
    (Entails.of_eq (by
      generalize (FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
        (dynamicRootRegions st') alignMap' live' peak' st') = PCore
      ac_rfl)) ?_
  exact sepConj_mono_left (sepConj_mono_right hCoreEnt)

/-! ## Stage 4 Raw `malloc` Commit and `free` Tail -/

theorem commit_stage4_malloc_raw [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (alignMap0 : BitVec 64 → Option Nat) (st0 st' : MallocngSt)
    (g' : GroupDesc) (idx align newSz : Nat) (q : BitVec 64)
    (bCoarse : MallocngBudget) (bsNew : List (BitVec 8)) (s2 : State)
    (htp2 : s2.tpidrEl0 = tp) (hbrks2 : s2.brkStart = brkStart)
    (hbsLen : bsNew.length = newSz)
    (hwf' : MallocngWF maddrs.base brkStart s2.brk bCoarse.liveCost bCoarse.peakCost st')
    (hRaw : MallocImplFineRawRel maddrs.base brkStart bgt ivs0 alignMap0 st0 st' g' idx newSz q) :
    let bf1 := FineBudget.stepReallocAdd align newSz bgt
    MallocngRoTablesA maddrs ∗
    ghostMapAuth (fineAlignGam γ) alignMap0 ∗
    MallocngCoreStA (fineBaseGam γ) maddrs brkStart s2.brk bCoarse.liveCost bCoarse.peakCost st' ∗
    MallocngRuntime maddrs tp ∗
    (q ↦ₛ bsNew) ∗
    MallocngBlockToken (fineBaseGam γ) q newSz ⊢
      |==> (FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
            memRegion q newSz ∗
            FineBlock γ q newSz (max align 16)) := by
  intro bf1
  obtain ⟨hInv0, hFresh0, hLiveMap', hMetaLe0, _, _, _, _, _, hBranch⟩ := hRaw
  have hAlignNone : alignMap0 q = none := by
    cases hAq : alignMap0 q with
    | none => rfl
    | some al =>
      obtain ⟨req0, hLq⟩ := (hInv0.alignMap_wf.1 q al hAq).2
      rw [hFresh0] at hLq
      cases hLq
  have hMetaLe' : st'.metaAreas.length ≤ fineMaxMetaAreas bf1 :=
    Nat.le_trans hMetaLe0 (fineMaxMetaAreas_le_stepReallocAdd align newSz bgt)
  let alignMap1 : BitVec 64 → Option Nat :=
    fun k => if k = q then some (max align 16) else alignMap0 k
  have hInv' : MallocngFineInv 0 bf1 (dynamicRootRegions st') alignMap1 st' := by
    by_cases hSmall : newSz ≤ MmapThresholdReq
    · simp only [hSmall, ↓reduceDIte] at hBranch
      obtain ⟨sc, pk, pkSC, pkSB, st1, g1, brk1, live1, peak1,
        hsc, hAlt, hPk, hPres, hwf1, hg1Mem, hg1Sc, ⟨hIdx1, hClaimed1⟩,
        hgSame, hgSlots, hGroups'⟩ := hBranch
      exact commit_claimed_slab_slot_reallocAdd hsc hSmall hAlt hFresh0 hInv0 hPk hPres
        hwf1 hwf' hg1Mem hg1Sc hIdx1 hClaimed1 hgSame hgSlots hGroups'
        (fun k => by change st'.liveMap.req k = _; rw [hLiveMap', MallocngLiveMap.insert_req]) hMetaLe'
    · simp only [hSmall, ↓reduceDIte] at hBranch
      obtain ⟨st1, _, hSame1, hGroups', hg'Sc, hg'Slots, hg'Map⟩ := hBranch
      have hMapDecl : g'.maplen * 4096 ≤ declCost63 newSz (max align 16) := by
        unfold declCost63; omega
      exact commit_mmap63_group_reallocAdd hFresh0 hInv0 hSame1 hGroups'
        hg'Sc hg'Slots (by omega) hMapDecl
        (fun k => by change st'.liveMap.req k = _; rw [hLiveMap', MallocngLiveMap.insert_req]) hMetaLe'
  let RestSpatial :=
    MallocngRoTablesA maddrs ∗
    MallocngCoreStA (fineBaseGam γ) maddrs brkStart s2.brk bCoarse.liveCost bCoarse.peakCost st' ∗
    MallocngRuntime maddrs tp ∗
    (q ↦ₛ bsNew) ∗
    MallocngBlockToken (fineBaseGam γ) q newSz
  refine Entails.trans (Q := ghostMapAuth (fineAlignGam γ) alignMap0 ∗ RestSpatial)
    (Entails.of_eq (by dsimp only [RestSpatial]; ac_rfl)) ?_
  refine Entails.trans
    (Entails.trans
      (sepConj_mono_left (ghostMap_alloc (fineAlignGam γ) alignMap0 q (max align 16) hAlignNone))
      (bupd_frame_r _ RestSpatial)) ?_
  refine bupd_mono ?_
  dsimp only [RestSpatial]
  have hCoreEnt :
      ghostMapAuth (fineAlignGam γ) alignMap1 ∗
      MallocngCoreStA (fineBaseGam γ) maddrs brkStart s2.brk bCoarse.liveCost bCoarse.peakCost st' ⊢
        ∃∗ stx : MallocngSt, ∃∗ amx : BitVec 64 → Option Nat,
        ∃∗ lcx : Nat, ∃∗ pcx : Nat,
          FineCoreStInflightA 0 γ maddrs brkStart s2.brk bf1
            (dynamicRootRegions st') amx lcx pcx stx :=
    Entails.sepExists_right st' (Entails.sepExists_right alignMap1
      (Entails.sepExists_right bCoarse.liveCost (Entails.sepExists_right bCoarse.peakCost
        (by unfold FineCoreStInflightA MallocngCoreStA
            exact Entails.pure_right hInv' (Entails.refl _)))))
  have hEnvEnt :
      (MallocngRoTablesA maddrs ∗
       (ghostMapAuth (fineAlignGam γ) alignMap1 ∗
        MallocngCoreStA (fineBaseGam γ) maddrs brkStart s2.brk bCoarse.liveCost bCoarse.peakCost st')) ∗
      MallocngRuntime maddrs tp ⊢
        FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 := by
    unfold FineEnv
    refine Entails.pure_right ⟨htp2, hbrks2⟩ ?_
    rw [FineHeapImpl_eq, FineCoreImpl_eq]
    exact sepConj_mono_left (sepConj_mono_right hCoreEnt)
  have hRegEnt : (q ↦ₛ bsNew) ⊢ memRegion q newSz := by
    rw [← hbsLen]; exact (IsBlock.pointsToBytes q bsNew).entails_memRegion
  have hBlkEnt :
      MallocngBlockToken (fineBaseGam γ) q newSz ∗
      ghostMapElem (fineAlignGam γ) q (max align 16) ⊢
        FineBlock γ q newSz (max align 16) := by
    unfold FineBlock
    exact Entails.pure_right (Nat.le_max_right align 16) (Entails.refl _)
  refine Entails.trans (Q :=
      ((MallocngRoTablesA maddrs ∗
        (ghostMapAuth (fineAlignGam γ) alignMap1 ∗
         MallocngCoreStA (fineBaseGam γ) maddrs brkStart s2.brk bCoarse.liveCost bCoarse.peakCost st')) ∗
       MallocngRuntime maddrs tp) ∗
      ((q ↦ₛ bsNew) ∗
       (MallocngBlockToken (fineBaseGam γ) q newSz ∗
        ghostMapElem (fineAlignGam γ) q (max align 16))))
    (Entails.of_eq (by
      change (ghostMapAuth (fineAlignGam γ) alignMap1 ∗
          ghostMapElem (fineAlignGam γ) q (max align 16)) ∗
          (MallocngRoTablesA maddrs ∗
           MallocngCoreStA (fineBaseGam γ) maddrs brkStart s2.brk bCoarse.liveCost bCoarse.peakCost st' ∗
           MallocngRuntime maddrs tp ∗ (q ↦ₛ bsNew) ∗
           MallocngBlockToken (fineBaseGam γ) q newSz) = _
      ac_rfl)) ?_
  exact sepConj_mono hEnvEnt (sepConj_mono hRegEnt hBlkEnt)

theorem realloc_s4_free_fine_ok [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget)
    (ivs0 ivs1 : List (BitVec 64 × Nat))
    (s0 s3 : State) {p q : BitVec 64} {oldSz align newSz : Nat} (origBs : List (BitVec 8))
    {Frame : SepProp}
    (hpNe : p ≠ 0#64) (hqNe : q ≠ 0#64) (hq16 : 16 ∣ q.toNat) (hq48 : q.toNat + newSz ≤ 2 ^ 48)
    (hpc3 : s3.pc = b + 0x284#64) (hrun3 : s3.status = .Running)
    (hsp3Eq : s3.sp = s0.sp - 80#64) (hal3 : s3.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx19_s3 : s3.readReg64 .x19 = p) (hx20_s3 : s3.readReg64 .x20 = q)
    (hcs3 : ReallocUntouchedCS s0 s3) (hcl3 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s3.mem)
    (hProc03 : MallocngProcPreserved s0 s3)
    (hDelta03 : MallocngMappedDelta 16 (fineStepReserve (.alloc newSz) bgt) s0.mem s3.mem)
    (hNoOrph03 : MallocngNoOrphanMappings ivs0 ivs1 s0.mem s3.mem) :
    let sp1 := s0.sp - 80#64
    let bf1 := FineBudget.stepReallocAdd align newSz bgt
    let bf := FineBudget.stepRealloc align oldSz newSz bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s3
      (FineEnv γ maddrs tp brkStart bf1 ivs1 s3 ∗
       memRegion p oldSz ∗ FineBlock γ p oldSz (max align 16) ∗
       stackFrameAt sp1 720 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
       FineBlock γ q newSz (max align 16) ∗ (q ↦ₛ keptBs) ∗
       memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame)
      (fun sf Pf =>
        ∃ q' : BitVec 64,
          MallocngCallAccounting 16
            (fineStepReserve (.realloc align oldSz newSz) bgt) s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q' ∧
          (Pf ⊢ stackFrame s0 800 ∗
            FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(FineInitBlockSem γ).pureWf q' (newSz, max align 16, keptBs)⌝ ∗
            (FineInitBlockSem γ).interp q' (newSz, max align 16, keptBs) ∗ Frame))
      (fun sf => ⌜FineStepOomCond msvc (fineStepReserve (.realloc align oldSz newSz) bgt) s0 sf⌝) := by
  intro sp1 bf1 bf keptBs; have _ := hb; have _ := hpc3; have _ := hx19_s3
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMaxIdem : max (max align 16) 16 = max align 16 := by omega
  wp_step; wp_step
  apply sepWP_bind_state; intro s4 hs4
  have hsp4Eq : s4.sp = sp1 := by rw [hs4]; simpa using hsp3Eq
  have hmem4Eq : s4.mem = s3.mem := by rw [hs4]; rfl
  have hFreeCall := call_placed_libcFree_fine_272 (P := blkPC_b14.rebase b (fun _ => none))
    γ tp brkStart p oldSz align bf1 ivs1 (by intro pc; simp) rfl
  have hEnvS4 : FineEnv γ maddrs tp brkStart bf1 ivs1 s3 =
      FineEnv γ maddrs tp brkStart bf1 ivs1 s4 := by rw [hs4]; rfl
  have hSf272 : stackFrameAt sp1 720 = (stackFrame s4 272 ∗ stackFrameAt (sp1 - 272#64) 448) := by
    rw [stackFrameAt_720_split sp1 272 448 (by decide),
        ← stackFrame_eq_stackFrameAt_720 272 (by decide) hsp4Eq]
  refine SepWP.call_subroutine_frame hFreeCall (x := ())
    (F := stackFrameAt (sp1 - 272#64) 448 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
      FineBlock γ q newSz (max align 16) ∗ (q ↦ₛ keptBs) ∗
      memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame)
    (ret_pc := b + 0x28c#64)
    (by rw [hs4]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by rw [hs4]; simp [hrun3]) (by rw [hs4]; simpa [State.spAligned] using hal3)
    (by rw [hs4]; simp)
    (fun R' hm => by
      dsimp only [libcFreeFine272Spec, withCL]; simp only [hpNe, ↓reduceIte]
      have hx0_s4 : s4.readReg64 .x0 = p := by rw [hs4]; simp
      have hcl_s4 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem := by rwa [hmem4Eq]
      refine Satisfies.mono ?_ hm; rw [hSf272, hEnvS4]
      refine Entails.trans (Q :=
          (stackFrame s4 272 ∗ FineEnv γ maddrs tp brkStart bf1 ivs1 s4 ∗
            (memRegion p oldSz ∗ FineBlock γ p oldSz (max align 16))) ∗
          (stackFrameAt (sp1 - 272#64) 448 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
           FineBlock γ q newSz (max align 16) ∗ (q ↦ₛ keptBs) ∗
           memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame) ∗ R')
        (Entails.of_eq (by
          generalize (FineEnv γ maddrs tp brkStart bf1 ivs1 s4) = PEnv4
          generalize (FineBlock γ p oldSz (max align 16)) = PBlkP
          generalize (FineBlock γ q newSz (max align 16)) = PBlkQ
          ac_rfl)) ?_
      refine sepConj_mono_left ?_; rw [sepConj_comm _ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem⌝]
      exact Entails.pure_right hcl_s4 (Entails.pure_right hx0_s4 (Entails.refl _)))
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_
    (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  intro s5 hpc5 hrun5 hsp5 hcs45
  dsimp only [libcFreeFine272Spec, withCL]
  have hBfEq : (if p == 0#64 then bf1 else FineBudget.stepFree align oldSz bf1) = bf := by
    rw [beq_false_of_ne hpNe]; rfl
  rw [hBfEq]
  have hsp5Eq : s5.sp = sp1 := by simpa [hsp4Eq] using hsp5
  have hal5 : s5.spAligned = true := spAligned_of_sub80 hsp5Eq hsp0
  refine SepWP.weaken_pre (P' :=
      ⌜MallocngProcPreserved s4 s5 ∧ MallocngMappedDelta 0 0 s4.mem s5.mem⌝ ∗
      ((((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x26)) ∗
       ReallocSavedLo s0 sp1 ∗ stackFrameAt sp1 720 ∗
       FinePostEnv γ maddrs tp brkStart bf ivs1 s4 s5 ∗
       FineBlock γ q newSz (max align 16) ∗ (q ↦ₛ keptBs) ∗
       memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame))
    (by
      refine Entails.trans (Q :=
          ⌜MallocngProcPreserved s4 s5 ∧ MallocngMappedDelta 0 0 s4.mem s5.mem⌝ ∗
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s5.mem⌝ ∗
          ((stackFrame s4 272 ∗ stackFrameAt (sp1 - 272#64) 448) ∗
           ReallocSavedHi s0 sp1 ∗ ReallocSavedLo s0 sp1 ∗
           FinePostEnv γ maddrs tp brkStart bf ivs1 s4 s5 ∗
           FineBlock γ q newSz (max align 16) ∗ (q ↦ₛ keptBs) ∗
           memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame))
        (Entails.of_eq (by
          generalize (FinePostEnv γ maddrs tp brkStart bf ivs1 s4 s5) = PPost5
          generalize (FineBlock γ q newSz (max align 16)) = PBlkQ
          generalize (MallocngProcPreserved s4 s5 ∧ MallocngMappedDelta 0 0 s4.mem s5.mem) = Pure5
          ac_rfl)) ?_
      refine Entails.pure_left fun hP5 => Entails.pure_left fun _hcl5 => Entails.pure_right hP5 ?_
      rw [hSf272.symm, ← reallocSavedHi_eq s0]
      exact Entails.of_eq (by
        generalize (FinePostEnv γ maddrs tp brkStart bf ivs1 s4 s5) = PPost5
        generalize (FineBlock γ q newSz (max align 16)) = PBlkQ
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
  have hPostTrans : FinePostEnv γ maddrs tp brkStart bf ivs1 s4 s5 ⊢
      FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sFin := by
    unfold FinePostEnv
    refine Entails.sepExists_elim fun ivsf => Entails.pure_left fun hNoOrph45 => ?_
    rw [hmem4Eq] at hNoOrph45
    have hNoOrph05 : MallocngNoOrphanMappings ivs0 ivsf s0.mem sFin.mem := by
      rw [hmemF]; exact noOrphanMappings_chain_alloc_free hNoOrph03 rfl hDelta45 hNoOrph45
    refine Entails.sepExists_right ivsf (Entails.pure_right hNoOrph05 ?_)
    unfold FineEnv
    rw [hbrkF, show sFin.tpidrEl0 = s5.tpidrEl0 from hProc0F.2.2.1.trans hProc05.2.2.1.symm,
        show sFin.brkStart = s5.brkStart from hProc0F.2.2.2.1.trans hProc05.2.2.2.1.symm]
    exact Entails.refl _
  have hInitInterp : (FineBlock γ q newSz (max align 16) ∗ (q ↦ₛ keptBs) ∗
      memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length)) ⊢
      ⌜(FineInitBlockSem γ).pureWf q (newSz, max align 16, keptBs)⌝ ∗
      (FineInitBlockSem γ).interp q (newSz, max align 16, keptBs) := by
    dsimp only [FineInitBlockSem]
    rw [hMaxIdem]
    exact Entails.pure_right ⟨hqNe, hq16, by omega, by simp [keptBs]; omega⟩ (Entails.refl _)
  refine SepWP.weaken_pre (P' :=
      ReallocSavedLo s0 sp1 ∗
      (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
       memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
      stackFrameAt sp1 720 ∗
      (FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sFin ∗
       ⌜(FineInitBlockSem γ).pureWf q (newSz, max align 16, keptBs)⌝ ∗
       (FineInitBlockSem γ).interp q (newSz, max align 16, keptBs) ∗ Frame))
    (by
      rw [← reallocSavedHi_eq s0]
      refine Entails.trans (sepConj_mono_left (reallocSavedHi_entails_memRegions s0 sp1)) ?_
      refine Entails.trans (Q := ReallocSavedLo s0 sp1 ∗
          (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
           memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
          stackFrameAt sp1 720 ∗
          (FinePostEnv γ maddrs tp brkStart bf ivs1 s4 s5 ∗
           ((FineBlock γ q newSz (max align 16) ∗ (q ↦ₛ keptBs) ∗
             memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length)) ∗ Frame)))
        (Entails.of_eq (by
          generalize (FinePostEnv γ maddrs tp brkStart bf ivs1 s4 s5) = PPost5
          generalize (FineBlock γ q newSz (max align 16)) = PBlkQ
          ac_rfl)) ?_
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono hPostTrans ?_)))
      exact Entails.trans (sepConj_mono_left hInitInterp) (Entails.of_eq (by ac_rfl))) ?_
  refine SepWP.mono (realloc_epilogue_ok hb hpcF hrunF hspF halF hsp0 hx20F
    hx23F hx24F hx25F hx26F hcsF) ?_
  intro sf Pf _ _ ⟨hmemEq, hbrkEq, hprocE, hspE, hcsE, hx0E, hPf⟩
  have hDelta0Sf : MallocngMappedDelta 16
      (fineStepReserve (.realloc align oldSz newSz) bgt) s0.mem sf.mem := by
    rw [hmemEq, hmemF]
    exact mappedDelta_mono_bounds (Nat.le_refl 16)
      (fineStepReserve_alloc_le_realloc newSz align oldSz bgt)
      (mappedDelta_trans_zero_right hDelta03 hDelta45)
  refine ⟨q, ⟨mallocngProcPreserved_trans hProc0F hprocE, hDelta0Sf⟩, hspE, hcsE, hx0E, ?_⟩
  rw [finePostEnv_congr_state (γ := γ) (A := maddrs)
    (tp := tp) (brkStart := brkStart) (bf := bf) (ivs0 := ivs0) (s0 := s0)
    hmemEq hbrkEq hprocE.2.2.1 hprocE.2.2.2.1] at hPf
  dsimp only [FineInitBlockSem] at hPf ⊢
  exact Entails.trans hPf (Entails.of_eq (by
    generalize (FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf) = PPost
    generalize (FineBlock γ q newSz (max (max align 16) 16)) = PBlkQ
    ac_rfl))

end LibsignalBinary.Heap.Fine
