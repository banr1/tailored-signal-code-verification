/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.FineSpecs
public import LibsignalBinary.Heap.Fine.LibcFreeFineRaw

/-!
# Fine-Grained Placed `__libc_free` and `free` Instantiation

Combines `placed_libcFree_raw_ok` with `FineBlock` ghost-map deletion (`ghostMap_delete` and
`fineBlock_lookup`) and `free_preserves_fineInv` to verify placed `__libc_free` (`blk06`) and the
exported `free` (`blk03`) entrypoint against `fineFreeSpec`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## `FineEnv`-Based `__libc_free` (`blk06`) Specification -/

noncomputable def libcFreeFine272Spec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p : BitVec 64) (n align : Nat)
    (b : FineBudget) (ivs0 : List (BitVec 64 × Nat)) : Spec Unit :=
  let bf := if p == 0#64 then b else FineBudget.stepFree align n b
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = p⌝ ∗
      stackFrame s0 272 ∗
      FineEnv γ maddrs tp brkStart b ivs0 s0 ∗
      if p = 0#64 then emp
      else memRegion p n ∗ FineBlock γ p n (max align 16)
    post := fun _ s0 sf =>
      ⌜MallocngProcPreserved s0 sf ∧
       MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
      stackFrame s0 272 ∗
      FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf
  }

private theorem pack_finePostEnv [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bf : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (alignMap' : BitVec 64 → Option Nat) (live' peak' : Nat)
    (st' : MallocngSt) (s0 sf : State)
    (htp : sf.tpidrEl0 = tp) (hbrks : sf.brkStart = brkStart)
    (hNoOrph : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem)
    (hInv' : MallocngFineInv 0 bf (dynamicRootRegions st') alignMap' st') :
    MallocngRoTablesA maddrs ∗
    ghostMapAuth (fineAlignGam γ) alignMap' ∗
    MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st' ∗
    MallocngRuntime maddrs tp ⊢
      FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf := by
  unfold FinePostEnv FineEnv
  refine Entails.sepExists_right (dynamicRootRegions st') (Entails.pure_right hNoOrph ?_)
  refine Entails.pure_right ⟨htp, hbrks⟩ ?_
  rw [FineHeapImpl_eq, FineCoreImpl_eq]
  have hCoreEnt :
      ghostMapAuth (fineAlignGam γ) alignMap' ∗
      MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st' ⊢
        ∃∗ st1 : MallocngSt, ∃∗ am1 : BitVec 64 → Option Nat,
        ∃∗ lc1 : Nat, ∃∗ pc1 : Nat,
          FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
            (dynamicRootRegions st') am1 lc1 pc1 st1 :=
    Entails.sepExists_right st' (Entails.sepExists_right alignMap'
      (Entails.sepExists_right live' (Entails.sepExists_right peak'
        (by unfold FineCoreStInflightA MallocngCoreStA
            exact Entails.pure_right hInv' (Entails.refl _)))))
  refine Entails.trans (Q :=
      (MallocngRoTablesA maddrs ∗
       (ghostMapAuth (fineAlignGam γ) alignMap' ∗
        MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st')) ∗
      MallocngRuntime maddrs tp)
    (Entails.of_eq (by ac_rfl)) ?_
  exact sepConj_mono_left (sepConj_mono_right hCoreEnt)

/-! ## Placed `__libc_free` Verification -/

set_option maxHeartbeats 400000 in
theorem placed_libcFree_fine_272_ok [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p : BitVec 64) (n align : Nat)
    (b : FineBudget) (ivs0 : List (BitVec 64 × Nat)) :
    subroutine_ok (mallocngBlockProg mmpl 6 msvc) (mbase 6)
      (libcFreeFine272Spec γ tp brkStart p n align b ivs0) := by
  unfold libcFreeFine272Spec
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre hspAl0
  dsimp only [FineEnv] at hpre
  rw [FineHeapImpl_eq, FineCoreImpl_eq] at hpre
  have hpre1 : s0.mem ⊨
      ⌜s0.mem = m0⌝ ∗
      ⌜s0.readReg64 .x0 = p⌝ ∗
      ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
      (∃∗ st0 : MallocngSt, ∃∗ alignMap0 : BitVec 64 → Option Nat,
       ∃∗ live0 : Nat, ∃∗ peak0 : Nat,
        FineCoreStInflightA 0 γ maddrs brkStart s0.brk b ivs0 alignMap0 live0 peak0 st0) ∗
      (stackFrame s0 272 ∗ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗
       (if p = 0#64 then emp else memRegion p n ∗ FineBlock γ p n (max align 16))) ∗ R := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    ac_rfl
  rw [satisfies_pure_sepConj] at hpre1; obtain ⟨hm0, hpre1⟩ := hpre1
  rw [satisfies_pure_sepConj] at hpre1; obtain ⟨hx0, hpre1⟩ := hpre1
  rw [satisfies_pure_sepConj] at hpre1; obtain ⟨⟨htp0, hbrks0⟩, hpre1⟩ := hpre1
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hpre1
  obtain ⟨st0, alignMap0, live0, peak0, hpre1⟩ := hpre1
  dsimp only [FineCoreStInflightA, MallocngCoreStInflightA] at hpre1
  have hpre2 : s0.mem ⊨
      ⌜MallocngFineInv 0 b ivs0 alignMap0 st0⌝ ∗
      ⌜MallocngWFInflight 0 maddrs.base brkStart s0.brk live0 peak0 st0⌝ ∗
      (stackFrame s0 272 ∗ MallocngRoTablesA maddrs ∗
       ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       MallocngCoreStA (fineBaseGam γ) maddrs brkStart s0.brk live0 peak0 st0 ∗
       MallocngRuntime maddrs tp ∗
       (if p = 0#64 then emp else memRegion p n ∗ FineBlock γ p n (max align 16))) ∗ R := by
    refine Satisfies.mono ?_ hpre1
    dsimp only [MallocngCoreStA, MallocngCoreStInflightA]
    refine Entails.trans (Q :=
        ⌜MallocngFineInv 0 b ivs0 alignMap0 st0⌝ ∗
        ⌜MallocngWFInflight 0 maddrs.base brkStart s0.brk live0 peak0 st0⌝ ∗
        (stackFrame s0 272 ∗ MallocngRoTablesA maddrs ∗
         ghostMapAuth (fineAlignGam γ) alignMap0 ∗
         (MallocngLiveAuth (fineBaseGam γ) st0.liveMap ∗
          (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
          (maddrs.lock ↦₃₂ 0#32) ∗
          (maddrs.replaced ↦₃₂ 0#32) ∗
          (maddrs.aaReplaced ↦₃₂ 0#32) ∗
          ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗
          MallocngAuxvState (fineBaseGam γ) st0.auxvPtr st0.auxvSnap ∗
          ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗
          ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∗
          MappedSet st0.masterDom (OwnedMappedByte st0)) ∗
         MallocngRuntime maddrs tp ∗
         (if p = 0#64 then emp else memRegion p n ∗ FineBlock γ p n (max align 16))) ∗ R)
      (Entails.of_eq (by ac_rfl)) ?_
    refine Entails.pure_left fun hInv => Entails.pure_left fun hwf => ?_
    refine Entails.pure_right hInv (Entails.pure_right hwf ?_)
    rw [pure_sepConj_of_true hwf]
    exact Entails.of_eq (by ac_rfl)
  rw [satisfies_pure_sepConj] at hpre2; obtain ⟨hInv0, hpre2⟩ := hpre2
  rw [satisfies_pure_sepConj] at hpre2; obtain ⟨hwf0, hmem0⟩ := hpre2
  have hcl_s0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem := hm0 ▸ hcl0
  have hIvs0 : ivs0 = dynamicRootRegions st0 := hInv0.ivs_eq rfl
  let P0 := stackFrame s0 272 ∗ MallocngRoTablesA maddrs ∗
    ghostMapAuth (fineAlignGam γ) alignMap0 ∗
    MallocngCoreStA (fineBaseGam γ) maddrs brkStart s0.brk live0 peak0 st0 ∗
    MallocngRuntime maddrs tp ∗
    (if p = 0#64 then emp else memRegion p n ∗ FineBlock γ p n (max align 16))
  have hRaw := placed_libcFree_raw_ok (fineBaseGam γ) tp brkStart p n live0 peak0 st0
    (groupsGrpBound_128_of_geom hInv0.groups_geom)
  by_cases hp0 : p = 0#64
  · refine ⟨P0, hmem0, ?_⟩
    subst hp0
    simp only [beq_self_eq_true, ↓reduceIte]
    refine SepWP.call_subroutine_frame (F := ghostMapAuth (fineAlignGam γ) alignMap0)
      (x := ()) (ret_pc := s0.readReg64 .lr) hRaw hpc hrun hspAl0 rfl
      (fun R' hm => by
        dsimp only [P0, libcFreeRaw272Spec, withCL] at hm ⊢
        simp only [↓reduceIte, sepConj_emp] at hm ⊢
        rw [← sepConj_assoc]
        refine Satisfies.mono (sepConj_mono_left ?_) hm
        have hPrePure : s0.readReg64 .x0 = 0#64 ∧ s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart :=
          ⟨hx0, htp0, hbrks0⟩
        refine Entails.trans (Q :=
            ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ ∗
            ⌜s0.readReg64 .x0 = 0#64 ∧ s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
            (stackFrame s0 272 ∗ MallocngRoTablesA maddrs ∗
             MallocngCoreStA (fineBaseGam γ) maddrs brkStart s0.brk live0 peak0 st0 ∗
             MallocngRuntime maddrs tp) ∗
            ghostMapAuth (fineAlignGam γ) alignMap0)
          ?_ (Entails.of_eq (by ac_rfl))
        refine Entails.pure_right hcl_s0 (Entails.pure_right hPrePure ?_)
        exact Entails.of_eq (by ac_rfl))
      (fun _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
      (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
    refine SepWP.done hpc_f hrun_f ⟨fun hsat => ?_, hsp_f, hcs_f⟩
    dsimp only [libcFreeRaw272Spec, withCL] at hsat
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hsat
    obtain ⟨st', liveCost', hsat⟩ := hsat
    have hsat1 : sf.mem ⊨
        ⌜MallocngProcPreserved s0 sf ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         sf.brk = s0.brk ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
         liveCost' ≤ peak0 ∧
         MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st') s0.mem sf.mem ∧
         LibcFreeRawPostRel 0#64 n st0 st'⌝ ∗
        ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
        (stackFrame s0 272 ∗
         (MallocngRoTablesA maddrs ∗
          ghostMapAuth (fineAlignGam γ) alignMap0 ∗
          MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk liveCost' peak0 st' ∗
          MallocngRuntime maddrs tp)) ∗ R := by
      refine Satisfies.mono (Entails.of_eq ?_) hsat
      ac_rfl
    rw [satisfies_pure_sepConj] at hsat1
    obtain ⟨⟨hproc_f, hdelta_f, _hbrk_f, htp_f, hbrks_f, _hliveLe, hNoOrph, hRel⟩, hsat1⟩ := hsat1
    rw [satisfies_pure_sepConj] at hsat1; obtain ⟨_hcl_f, hsat1⟩ := hsat1
    have hstEq : st' = st0 := by simpa [LibcFreeRawPostRel] using hRel
    subst st'
    have hNoOrph0 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st0) s0.mem sf.mem :=
      hIvs0 ▸ hNoOrph
    have hInv0' : MallocngFineInv 0 b (dynamicRootRegions st0) alignMap0 st0 :=
      hIvs0 ▸ hInv0
    refine Satisfies.mono (sepConj_mono_left ?_) hsat1
    have hPack := pack_finePostEnv γ tp brkStart b ivs0 alignMap0 liveCost' peak0 st0 s0 sf
      htp_f hbrks_f hNoOrph0 hInv0'
    have hPostPure : MallocngProcPreserved s0 sf ∧ MallocngMappedDelta 0 0 s0.mem sf.mem :=
      ⟨hproc_f, hdelta_f⟩
    refine Entails.trans (sepConj_mono_right hPack) ?_
    refine Entails.trans (Q :=
        ⌜MallocngProcPreserved s0 sf ∧ MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
        (stackFrame s0 272 ∗ FinePostEnv γ maddrs tp brkStart b ivs0 s0 sf))
      (Entails.pure_right hPostPure (Entails.refl _)) ?_
    exact Entails.of_eq (by ac_rfl)
  ·
    have hAlign0 : alignMap0 p = some (max align 16) := by
      have hLk : s0.mem ⊨
          (ghostMapAuth (fineAlignGam γ) alignMap0 ∗
           MallocngLiveAuth (fineBaseGam γ) st0.liveMap ∗
           FineBlock γ p n (max align 16)) ∗
          (stackFrame s0 272 ∗ MallocngRoTablesA maddrs ∗
           ⌜MallocngWFInflight 0 maddrs.base brkStart s0.brk live0 peak0 st0⌝ ∗
           (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
           (maddrs.lock ↦₃₂ 0#32) ∗
           (maddrs.replaced ↦₃₂ 0#32) ∗
           (maddrs.aaReplaced ↦₃₂ 0#32) ∗
           ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗
           MallocngAuxvState (fineBaseGam γ) st0.auxvPtr st0.auxvSnap ∗
           ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗
           ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∗
           MappedSet st0.masterDom (OwnedMappedByte st0) ∗
           MallocngRuntime maddrs tp ∗ memRegion p n ∗ R) := by
        dsimp only [P0, MallocngCoreStA, MallocngCoreStInflightA] at hmem0
        simp only [hp0, ↓reduceIte] at hmem0
        refine Satisfies.mono (Entails.of_eq ?_) hmem0
        ac_rfl
      have hLk2 := Satisfies.mono (sepConj_mono_left
        (fineBlock_lookup γ st0.liveMap alignMap0 p n (max align 16))) hLk
      rw [sepConj_assoc, satisfies_pure_sepConj] at hLk2
      exact hLk2.1.2.2.2
    refine ⟨P0, hmem0, ?_⟩
    simp only [beq_false_of_ne hp0, Bool.false_eq_true, ↓reduceIte]
    let alignMap' : BitVec 64 → Option Nat := fun k => if k = p then none else alignMap0 k
    let RawPre := stackFrame s0 272 ∗ MallocngRoTablesA maddrs ∗
      MallocngCoreStA (fineBaseGam γ) maddrs brkStart s0.brk live0 peak0 st0 ∗
      MallocngRuntime maddrs tp ∗ memRegion p n ∗ MallocngBlockToken (fineBaseGam γ) p n
    have hBupd : P0 ⊢ |==> (ghostMapAuth (fineAlignGam γ) alignMap' ∗ RawPre) := by
      dsimp only [P0, RawPre, FineBlock]
      simp only [hp0, ↓reduceIte]
      have hRearr :
          stackFrame s0 272 ∗ MallocngRoTablesA maddrs ∗
          ghostMapAuth (fineAlignGam γ) alignMap0 ∗
          MallocngCoreStA (fineBaseGam γ) maddrs brkStart s0.brk live0 peak0 st0 ∗
          MallocngRuntime maddrs tp ∗
          (memRegion p n ∗ ⌜16 ≤ max align 16⌝ ∗ MallocngBlockToken (fineBaseGam γ) p n ∗
           ghostMapElem (fineAlignGam γ) p (max align 16)) ⊢
          (ghostMapAuth (fineAlignGam γ) alignMap0 ∗ ghostMapElem (fineAlignGam γ) p (max align 16)) ∗
          RawPre := by
        dsimp only [RawPre]
        rw [pure_sepConj_of_true (Nat.le_max_right align 16)]
        exact Entails.of_eq (by ac_rfl)
      exact Entails.trans hRearr (Entails.trans
        (sepConj_mono_left (ghostMap_delete (fineAlignGam γ) alignMap0 p (max align 16)))
        (bupd_frame_r _ _))
    apply SepWP.bupd_pre hBupd
    refine SepWP.call_subroutine_frame (F := ghostMapAuth (fineAlignGam γ) alignMap')
      (x := ()) (ret_pc := s0.readReg64 .lr) hRaw hpc hrun hspAl0 rfl
      (fun R' hm => by
        dsimp only [RawPre, libcFreeRaw272Spec, withCL] at hm ⊢
        simp only [hp0, ↓reduceIte]
        rw [← sepConj_assoc]
        refine Satisfies.mono (sepConj_mono_left ?_) hm
        have hPrePure : s0.readReg64 .x0 = p ∧ s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart :=
          ⟨hx0, htp0, hbrks0⟩
        refine Entails.trans (Q :=
            ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ ∗
            ⌜s0.readReg64 .x0 = p ∧ s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
            RawPre ∗
            ghostMapAuth (fineAlignGam γ) alignMap')
          ?_ (Entails.of_eq (by dsimp only [RawPre]; ac_rfl))
        refine Entails.pure_right hcl_s0 (Entails.pure_right hPrePure ?_)
        exact Entails.of_eq (by dsimp only [RawPre]; ac_rfl))
      (fun _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
      (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
    refine SepWP.done hpc_f hrun_f ⟨fun hsat => ?_, hsp_f, hcs_f⟩
    dsimp only [libcFreeRaw272Spec, withCL] at hsat
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hsat
    obtain ⟨st', liveCost', hsat⟩ := hsat
    have hsat1 : sf.mem ⊨
        ⌜MallocngProcPreserved s0 sf ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         sf.brk = s0.brk ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
         liveCost' ≤ peak0 ∧
         MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st') s0.mem sf.mem ∧
         LibcFreeRawPostRel p n st0 st'⌝ ∗
        ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
        ⌜MallocngWFInflight 0 maddrs.base brkStart sf.brk liveCost' peak0 st'⌝ ∗
        (stackFrame s0 272 ∗
         (MallocngRoTablesA maddrs ∗
          ghostMapAuth (fineAlignGam γ) alignMap' ∗
          MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk liveCost' peak0 st' ∗
          MallocngRuntime maddrs tp)) ∗ R := by
      refine Satisfies.mono ?_ hsat
      dsimp only [MallocngCoreStA, MallocngCoreStInflightA]
      refine Entails.trans (Q :=
          ⌜MallocngProcPreserved s0 sf ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧
            sf.brk = s0.brk ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
            liveCost' ≤ peak0 ∧
            MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st') s0.mem sf.mem ∧
            LibcFreeRawPostRel p n st0 st'⌝ ∗
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
          ⌜MallocngWFInflight 0 maddrs.base brkStart sf.brk liveCost' peak0 st'⌝ ∗
          (stackFrame s0 272 ∗
           MallocngRoTablesA maddrs ∗
           ghostMapAuth (fineAlignGam γ) alignMap' ∗
           (MallocngLiveAuth (fineBaseGam γ) st'.liveMap ∗
            (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗
            (maddrs.lock ↦₃₂ 0#32) ∗
            (maddrs.replaced ↦₃₂ 0#32) ∗
            (maddrs.aaReplaced ↦₃₂ 0#32) ∗
            ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗
            MallocngAuxvState (fineBaseGam γ) st'.auxvPtr st'.auxvSnap ∗
            ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
            ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
            MappedSet st'.masterDom (OwnedMappedByte st')) ∗
           MallocngRuntime maddrs tp) ∗ R)
        (Entails.of_eq (by ac_rfl)) ?_
      refine Entails.pure_left fun hP => Entails.pure_left fun hCL => Entails.pure_left fun hWF => ?_
      refine Entails.pure_right hP (Entails.pure_right hCL (Entails.pure_right hWF ?_))
      rw [pure_sepConj_of_true hWF]
      exact Entails.of_eq (by ac_rfl)
    rw [satisfies_pure_sepConj] at hsat1
    obtain ⟨⟨hproc_f, hdelta_f, _hbrk_f, htp_f, hbrks_f, _hliveLe, hNoOrph, hRel⟩, hsat1⟩ := hsat1
    rw [satisfies_pure_sepConj] at hsat1; obtain ⟨_hcl_f, hsat1⟩ := hsat1
    rw [satisfies_pure_sepConj] at hsat1; obtain ⟨hwf', hsat1⟩ := hsat1
    simp only [LibcFreeRawPostRel, hp0, ↓reduceIte] at hRel
    obtain ⟨g, idx, effCost, hIdx, bs, hg, hSlot, hBsLen, hSub⟩ := hRel
    have hInv' : MallocngFineInv 0 (FineBudget.stepFree align n b)
        (dynamicRootRegions st') alignMap' st' :=
      free_preserves_fineInv hInv0 hwf0 hwf' hg hIdx hSlot hBsLen hAlign0 hSub
    have hNoOrph0 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem :=
      hIvs0 ▸ hNoOrph
    refine Satisfies.mono (sepConj_mono_left ?_) hsat1
    have hPack := pack_finePostEnv γ tp brkStart (FineBudget.stepFree align n b) ivs0
      alignMap' liveCost' peak0 st' s0 sf htp_f hbrks_f hNoOrph0 hInv'
    have hPostPure : MallocngProcPreserved s0 sf ∧ MallocngMappedDelta 0 0 s0.mem sf.mem :=
      ⟨hproc_f, hdelta_f⟩
    refine Entails.trans (sepConj_mono_right hPack) ?_
    refine Entails.trans (Q :=
        ⌜MallocngProcPreserved s0 sf ∧ MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
        (stackFrame s0 272 ∗ FinePostEnv γ maddrs tp brkStart (FineBudget.stepFree align n b) ivs0 s0 sf))
      (Entails.pure_right hPostPure (Entails.refl _)) ?_
    exact Entails.of_eq (by ac_rfl)

theorem call_placed_libcFree_fine_272 [MallocngMultiPlacement]
    {P : Program} (γ : GhostName) (tp brkStart p : BitVec 64) (n align : Nat)
    (b : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = (mallocngBlockProg mmpl 6 msvc).svc := by rfl) :
    subroutine_ok P (mbase 6)
      (libcFreeFine272Spec γ tp brkStart p n align b ivs0) :=
  subroutine_ok_block_to_block (j := 6) (by decide)
    (placed_libcFree_fine_272_ok γ tp brkStart p n align b ivs0) hext hsvc

/-! ## Public `free` (`blk03`) Entrypoint Verification -/

private theorem fineFreeableBlock_comm (γ : GhostName) (p : BitVec 64) (n align : Nat) :
    (if p = 0#64 then emp else FineBlock γ p n (max align 16) ∗ memRegion p n) =
      if p = 0#64 then emp else memRegion p n ∗ FineBlock γ p n (max align 16) := by
  split
  · rfl
  · exact sepConj_comm _ _

private theorem blk03_free_fine_ok [MallocngMultiPlacement] (γ : GhostName) :
    subroutine_ok (mallocngBlockProg mmpl 3 msvc) (mbase 3)
      (withCL mmpl (ToBaseSpec.toSpec (fineFreeSpec γ maddrs) (mbase 3))) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have hfn : ∀ c, (blkPC_b03.rebase c (fun _ => none)).fnAddr "free" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase, Program.fnOff, Program.findSymbol?, blkPC_b03, PlacedLib.program]
    rw [blkSymsEq_b03]
    have hf : (ProofLib.ProgramReflection.toStringSymbols blkSymChars_b03).find? (·.1 == "free") =
        some ("free", 0) := by decide
    rw [hf]; exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b03 (hfn (mbase 3)) fun b hb => ?_
  have _ := hb
  apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hpre hspAl0; rw [hfn b] at hpc
  rcases x with ⟨p, sp0, n, align, tp, brkStart, bud, ivs0⟩
  let P0 := (FineFreeableBlockSem γ).interp p (n, align) ∗
    FineEnv γ maddrs tp brkStart bud ivs0 s0 ∗
    stackFrameAt sp0 1024
  have hpre' : s0.mem ⊨ ⌜s0.mem = m0⌝ ∗
      ⌜s0.readReg64 .x0 = p ∧ s0.sp = sp0 ∧ (FineFreeableBlockSem γ).pureWf p (n, align)⌝ ∗
      P0 ∗ R := by
    simpa [ToBaseSpec.toSpec, fineFreeSpec, mallocngStackBytes, P0, sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hm0, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hsp0, _hpWf⟩, hmem0⟩ := hpre'
  have hcl_s0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem := hm0 ▸ hcl0
  refine ⟨P0, hmem0, ?_⟩
  wp_step
  let FrameF := stackFrameAt (sp0 - 272#64) 752
  have hSub := call_placed_libcFree_fine_272
    (P := blkPC_b03.rebase b (fun _ => none)) γ tp brkStart p n align bud ivs0
  refine SepWP.call_subroutine_frame (F := FrameF) (x := ()) (ret_pc := s0.readReg64 .lr) hSub
    (by simp only [arm64_norm]; rw [hb]; bv_arith)
    (by simp [arm64_norm, hrun])
    (by simpa [State.spAligned, arm64_norm] using hspAl0)
    (by simp [arm64_norm])
    (fun R' hm => by
      have hSF272 : ∀ s' : State, s'.sp = sp0 → stackFrame s' 272 = stackFrameAt sp0 272 := by
        intro s' hs; rw [stackFrameAt_eq_memRegion sp0 272]; simp [stackFrame, hs]
      have hEnvEq : ∀ pc', FineEnv γ maddrs tp brkStart bud ivs0 (s0.setPC pc') =
          FineEnv γ maddrs tp brkStart bud ivs0 s0 := fun _ => rfl
      rw [← sepConj_assoc]; refine Satisfies.mono (sepConj_mono_left ?_) hm
      dsimp only [P0, FrameF, libcFreeFine272Spec, withCL, FineFreeableBlockSem]
      rw [fineFreeableBlock_comm, stackFrameAt_1024_split_272 sp0,
          hSF272 _ (by simp [arm64_norm, hsp0]), hEnvEq]
      conv =>
        rhs
        rw [pure_sepConj_of_true (by simpa [arm64_norm] using hx0),
            sepConj_comm (Q := ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl _⌝),
            pure_sepConj_of_true (by simpa [arm64_norm] using hcl_s0)]
      sep_frame)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
  have hsp_f' : sf.sp = s0.sp := by simpa [arm64_norm] using hsp_f
  have hcs_f' : CalleeSavedPreserved s0 sf :=
    ⟨by simpa [arm64_norm] using hcs_f.1,
     by simpa [arm64_norm] using hcs_f.2.1,
     by simpa [arm64_norm] using hcs_f.2.2.1,
     by simpa [arm64_norm] using hcs_f.2.2.2.1,
     by simpa [arm64_norm] using hcs_f.2.2.2.2.1,
     by simpa [arm64_norm] using hcs_f.2.2.2.2.2.1,
     by simpa [arm64_norm] using hcs_f.2.2.2.2.2.2.1,
     by simpa [arm64_norm] using hcs_f.2.2.2.2.2.2.2.1,
     by simpa [arm64_norm] using hcs_f.2.2.2.2.2.2.2.2.1,
     by simpa [arm64_norm] using hcs_f.2.2.2.2.2.2.2.2.2.1,
     by simpa [arm64_norm] using hcs_f.2.2.2.2.2.2.2.2.2.2.1,
     by simpa [calleeSavedVRegs] using hcs_f.2.2.2.2.2.2.2.2.2.2.2⟩
  refine SepWP.done hpc_f hrun_f ⟨fun hsat => ?_, hsp_f', hcs_f'⟩
  have hSF272 : ∀ s' : State, s'.sp = sp0 → stackFrame s' 272 = stackFrameAt sp0 272 := by
    intro s' hs; rw [stackFrameAt_eq_memRegion sp0 272]; simp [stackFrame, hs]
  dsimp only [libcFreeFine272Spec, withCL, FrameF] at hsat
  simp only [sepConj_assoc] at hsat
  rw [satisfies_pure_sepConj] at hsat
  obtain ⟨⟨hproc_f, hdelta_f⟩, hsat⟩ := hsat
  have hStripCL : ∀ (B C E R' : SepProp) (φ : Prop),
      B ∗ C ∗ ⌜φ⌝ ∗ E ∗ R' ⊢ (B ∗ C ∗ E) ∗ R' := by
    intro B C E R' φ
    rw [← sepConj_assoc, ← sepConj_assoc, sepConj_comm (Q := ⌜φ⌝)]
    simp only [sepConj_assoc]
    exact Entails.pure_left fun _ => Entails.refl _
  have hPostEnvEq : ∀ bud' pc',
      FinePostEnv γ maddrs tp brkStart bud' ivs0 (s0.setPC pc') sf =
      FinePostEnv γ maddrs tp brkStart bud' ivs0 s0 sf := fun _ _ => rfl
  have hsat' := Satisfies.mono (hStripCL _ _ _ _ _) hsat
  rw [hSF272 _ (by simp [arm64_norm, hsp0]), hPostEnvEq] at hsat'
  refine Satisfies.mono (sepConj_mono_left ?_) hsat'
  dsimp only [ToBaseSpec.toSpec, fineFreeSpec, mallocngStackBytes, FineBudget.step]
  have hAcc : MallocngCallAccounting 0 0 s0 sf :=
    ⟨procPreserved_trans' ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩ hproc_f, hdelta_f⟩
  refine Entails.pure_right hAcc ?_
  rw [stackFrameAt_1024_split_272 sp0]
  sep_frame

/-- Multi-block placed `free(p)` (`blk03`) satisfies `fineFreeSpec`. -/
theorem placed_free_fine_entry_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "free"
      (fineFreeSpec γ (mallocngAddrsOfPlacement mpl)) := by
  let inst : MallocngMultiPlacement := { mpl := mpl, svc := svc, placeable := hPlace, svcValid := hSvc }
  refine ⟨by decide, 3, 0, by decide +kernel, ?_⟩
  rw [fnAddr_free]
  exact withCL_to_withCodeLoaded (@blk03_free_fine_ok inst γ)

end LibsignalBinary.Heap.Fine
