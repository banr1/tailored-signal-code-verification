/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ReallocStage4HelpersFine

/-!
# Fine-Grained Placed `__libc_realloc` Null, `ENOMEM`, and Stage 4 Paths

Verifies the null-pointer tail branch (`p = 0#64 → __libc_malloc_impl`), the `ENOMEM` overflow exit
(`newSize > MallocngMaxAllocSize`), and the Stage 4 out-of-place `malloc + memcpy + free` path of
placed `__libc_realloc` (`blk14`) over `FineBudget`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Null-Pointer Path -/

set_option maxHeartbeats 400000 in
theorem realloc_null_path_fine_ok [MallocngMultiPlacement]
    (hImpl : LibcMallocImplFineStmt)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart newSize : BitVec 64)
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 : State) (R : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = 0#64) (hx1 : s0.readReg64 .x1 = newSize)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem) :
    let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
    let bf := if ok then FineBudget.step (.alloc newSize.toNat) bgt else bgt
    let stepB :=
      if ok then fineStepReserve (.realloc 16 0 newSize.toNat) bgt
      else fineStepReserve (.alloc 0) bgt
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) s0
      (stackFrame s0 800 ∗ FineEnv γ maddrs tp brkStart bgt ivs0 s0)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R →
          sf.mem ⊨
            ((⌜MallocngCallAccounting 16 stepB s0 sf⌝ ∗
              stackFrame s0 800 ∗
              FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
              if ok then
                ∃∗ q : BitVec 64,
                  ⌜sf.readReg64 .x0 = q ∧
                   (FineInitBlockSem γ).pureWf q (newSize.toNat, 16, [])⌝ ∗
                  (FineInitBlockSem γ).interp q (newSize.toNat, 16, [])
              else
                ⌜sf.readReg64 .x0 = 0#64⌝ ∗ emp) ∗
             ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜FineStepOomCond msvc stepB s0 sf⌝) := by
  intro ok bf stepB; have _ := hb; have _ := hx0; have _ := hx1
  have hspMask0 : s0.sp &&& 15#64 = 0#64 := of_decide_eq_true hsp0
  have hspAlign80 : (s0.sp - 80#64) &&& 15#64 = 0#64 := by revert hspMask0; bv_robdd
  refine SepWP.weaken_pre (sepConj_mono_left (stackFrame800_entails_exists_cells s0)) ?_
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro v0; apply SepWP.exists_left; intro v1
  apply SepWP.exists_left; intro v2; apply SepWP.exists_left; intro v3
  apply SepWP.exists_left; intro v4; apply SepWP.exists_left; intro v5
  apply SepWP.exists_left; intro v6; apply SepWP.exists_left; intro v7
  apply SepWP.exists_left; intro v8; apply SepWP.exists_left; intro v9
  wp_stp64_cl m1 hm1 hcl0 hcl1
  wp_step
  wp_stp64_cl m2 hm2 hcl1 hcl2
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply sepWP_bind_state; intro sTail hsTail
  have hPermTail : sTail.mem.perm = s0.mem.perm := by
    have hmEq : sTail.mem = m2 := by rw [hsTail]; rfl
    rw [hmEq, hm2, hm1]
  have hclTail : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sTail.mem := by
    have hmEq : sTail.mem = m2 := by rw [hsTail]; rfl
    rwa [hmEq]
  have hspTail : sTail.sp = s0.sp := by rw [hsTail]; simp
  have hspAlignTail : sTail.spAligned = true := by
    unfold State.spAligned at hsp0 ⊢; rwa [hspTail]
  have hEnvTail : FineEnv γ maddrs tp brkStart bgt ivs0 s0 =
      FineEnv γ maddrs tp brkStart bgt ivs0 sTail := by
    unfold FineEnv
    have htpT : sTail.tpidrEl0 = s0.tpidrEl0 := by rw [hsTail]; rfl
    have hbrksT : sTail.brkStart = s0.brkStart := by rw [hsTail]; rfl
    have hbrkT : sTail.brk = s0.brk := by rw [hsTail]; rfl
    rw [htpT, hbrksT, hbrkT]
  refine SepWP.weaken_pre (sepConj_mono_left
    (stack80_cells_to_stackFrame800 s0 (s0.readReg64 .x29) (s0.readReg64 .x30)
      v2 v3 (s0.readReg64 .x21) (s0.readReg64 .x22) v6 v7 v8 v9)) ?_
  have hSplit704 : stackFrame s0 800 = (stackFrame sTail 704 ∗ stackFrameAt (s0.sp - 704#64) 96) := by
    unfold stackFrame
    rw [hspTail, ← stackFrameAt_eq_memRegion s0.sp 800, ← stackFrameAt_eq_memRegion s0.sp 704,
        show (800 : Nat) = 704 + 96 from rfl, stackFrameAt_split s0.sp 704 96]
  rw [hSplit704, hEnvTail]
  have hMalloc := call_placed_libcMallocImpl_fine hImpl (P := blkPC_b14.rebase b (fun _ => none))
    γ tp brkStart bgt ivs0 newSize.toNat (by intro pc; simp) rfl
  have hlrTail : sTail.readReg64 Reg.lr = s0.readReg64 Reg.lr := by rw [hsTail]; simp
  refine SepWP.call_subroutine_frame hMalloc (x := ())
    (F := stackFrameAt (s0.sp - 704#64) 96)
    (ret_pc := s0.readReg64 Reg.lr)
    (by rw [hsTail]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by rw [hsTail]; simp [hrun])
    hspAlignTail
    hlrTail
    (fun R' hm => by
      have hx0T : (sTail.readReg64 .x0).toNat = newSize.toNat := by
        rw [hsTail]; simp
      refine Satisfies.mono ?_ hm
      dsimp only [libcMallocImplFineSpec, withCL]
      refine Entails.trans (Q :=
          (stackFrame sTail 704 ∗ FineEnv γ maddrs tp brkStart bgt ivs0 sTail) ∗
          stackFrameAt (s0.sp - 704#64) 96 ∗ R')
        (Entails.of_eq (by
          generalize (FineEnv γ maddrs tp brkStart bgt ivs0 sTail) = PEnv
          ac_rfl)) ?_
      refine sepConj_mono_left ?_
      rw [sepConj_comm _ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sTail.mem⌝]
      exact Entails.pure_right hclTail (Entails.pure_right hx0T (Entails.refl _)))
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpcSf hrunSf hspSf hcsSf => ?_)
    (fun R' sf _ hOom => ?_)
  ·
    have hspSf0 : sf.sp = s0.sp := hspSf.trans hspTail
    have hcsSf0 : CalleeSavedPreserved s0 sf := by
      have hcsT : CalleeSavedPreserved s0 sTail := by
        rw [hsTail]
        refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
          by simp, by simp, by simp, by simp [calleeSavedVRegs]⟩
      exact CalleeSavedPreserved.trans hcsT hcsSf
    refine SepWP.done hpcSf hrunSf ⟨fun hm => ?_, hspSf0, hcsSf0⟩
    dsimp only [libcMallocImplFineSpec, withCL] at hm
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
    obtain ⟨⟨hProcTSf, hDeltaTSf⟩, hm⟩ := hm
    have hProc0T : MallocngProcPreserved s0 sTail := by
      rw [hsTail]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hProc0Sf : MallocngProcPreserved s0 sf := mallocngProcPreserved_trans hProc0T hProcTSf
    have hStepEq : fineStepReserve (if ok then .alloc newSize.toNat else .alloc 0) bgt = stepB :=
      fineStepReserve_null_eq ok newSize.toNat bgt
    have hDelta0Sf : MallocngMappedDelta 16 stepB s0.mem sf.mem := by
      rw [hStepEq] at hDeltaTSf
      obtain ⟨ivs, hlen, hsum, hcov⟩ := hDeltaTSf
      refine ⟨ivs, hlen, hsum, fun a ha => ?_⟩
      rcases hcov a ha with hmT | hin
      · exact Or.inl (by rwa [← hPermTail])
      · exact Or.inr hin
    have hAcc0Sf : MallocngCallAccounting 16 stepB s0 sf := ⟨hProc0Sf, hDelta0Sf⟩
    by_cases hLeMax : newSize.toNat ≤ MallocngMaxAllocSize
    · have hOkTrue : ok = true := decide_eq_true hLeMax
      have hBfEq : FineBudget.stepAlloc newSize.toNat bgt = bf := by
        dsimp only [bf]; simp only [hOkTrue, ↓reduceIte]; rfl
      simp only [hLeMax, decide_true, hOkTrue, ↓reduceIte] at hm ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
      obtain ⟨q, bs, st', alignMap', live', peak', hm⟩ := hm
      rw [← sepConj_assoc (stackFrame sTail 704) ⌜_⌝,
          sepConj_comm (stackFrame sTail 704) ⌜_⌝,
          sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
      obtain ⟨⟨hx0Q, htpSf, hbrksSf, hWfQ, hBsLen, hNoOrphT, _⟩, hm⟩ := hm
      rw [hBfEq] at hm
      have hm' : sf.mem ⊨
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
          (stackFrame sTail 704 ∗ stackFrameAt (s0.sp - 704#64) 96) ∗
          (MallocngRoTablesA maddrs ∗
           FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
             (dynamicRootRegions st') alignMap' live' peak' st' ∗
           MallocngRuntime maddrs tp) ∗
          ((q ↦ₛ bs) ∗ FineBlock γ q newSize.toNat 16) ∗ R := by
        refine Satisfies.mono (Entails.of_eq ?_) hm
        generalize (MallocngRoTablesA maddrs) = PRo
        generalize (FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
          (dynamicRootRegions st') alignMap' live' peak' st') = PCore
        generalize (MallocngRuntime maddrs tp) = PRt
        generalize (FineBlock γ q newSize.toNat 16) = PBlk
        ac_rfl
      rw [← hSplit704, satisfies_pure_sepConj] at hm'
      obtain ⟨hclSf, hm'⟩ := hm'
      have hNoOrph0 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem := by
        intro a hmA hor0
        rcases hor0 with hnot0 | hin0
        · exact hNoOrphT a hmA (Or.inl (by rwa [hPermTail]))
        · exact hNoOrphT a hmA (Or.inr hin0)
      have ⟨hPureInit, hEntInit⟩ := fineMallocBlock_to_initBlock_nil γ q bs newSize.toNat hWfQ hBsLen
      have hPostEnvEnt :
          MallocngRoTablesA maddrs ∗
          FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
            (dynamicRootRegions st') alignMap' live' peak' st' ∗
          MallocngRuntime maddrs tp ⊢
            FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf :=
        pack_fineImpl_postEnv γ tp brkStart bf ivs0 alignMap' live' peak' st' s0 sf
          htpSf hbrksSf hNoOrph0
      have hBlkEnt :
          ((q ↦ₛ bs) ∗ FineBlock γ q newSize.toNat 16) ⊢
          ∃∗ q' : BitVec 64,
            ⌜sf.readReg64 .x0 = q' ∧
             (FineInitBlockSem γ).pureWf q' (newSize.toNat, 16, [])⌝ ∗
            (FineInitBlockSem γ).interp q' (newSize.toNat, 16, []) :=
        Entails.trans hEntInit
          (Entails.sepExists_right q (Entails.pure_right ⟨hx0Q, hPureInit⟩ (Entails.refl _)))
      rw [← hSplit704,
          sepConj_comm (_ : SepProp) ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝,
          sepConj_assoc ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ _ R,
          sepConj_assoc ⌜MallocngCallAccounting 16 stepB s0 sf⌝ _ R,
          sepConj_assoc (stackFrame s0 800) _ R,
          sepConj_assoc (FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf) _ R]
      refine Satisfies.mono ?_ hm'
      refine Entails.pure_right hclSf (Entails.pure_right hAcc0Sf ?_)
      exact sepConj_mono_right (sepConj_mono hPostEnvEnt (sepConj_mono_left hBlkEnt))
    · have hOkFalse : ok = false := decide_eq_false hLeMax
      have hBfEq : bgt = bf := by
        dsimp only [bf]; simp only [hOkFalse, Bool.false_eq_true, ↓reduceIte]
      simp only [hLeMax, decide_false, hOkFalse, Bool.false_eq_true, ↓reduceIte] at hm ⊢
      rw [← sepConj_assoc (stackFrame sTail 704) ⌜_⌝,
          sepConj_comm (stackFrame sTail 704) ⌜_⌝,
          sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
      obtain ⟨hx0_0, hm⟩ := hm
      rw [hBfEq] at hm
      have hm' : sf.mem ⊨
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
          (stackFrame sTail 704 ∗ stackFrameAt (s0.sp - 704#64) 96) ∗
          FinePostEnv γ maddrs tp brkStart bf ivs0 sTail sf ∗ R := by
        refine Satisfies.mono (Entails.of_eq ?_) hm
        generalize (FinePostEnv γ maddrs tp brkStart bf ivs0 sTail sf) = PPost
        ac_rfl
      rw [← hSplit704, satisfies_pure_sepConj] at hm'
      obtain ⟨hclSf, hm'⟩ := hm'
      have hPostCongr :
          FinePostEnv γ maddrs tp brkStart bf ivs0 sTail sf ⊢
          FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf := by
        unfold FinePostEnv
        refine Entails.sepExists_mono fun ivsf => Entails.pure_left fun hNoT => ?_
        refine Entails.pure_right (fun a hmA hor0 => ?_) (Entails.refl _)
        rcases hor0 with hnot0 | hin0
        · exact hNoT a hmA (Or.inl (by rwa [hPermTail]))
        · exact hNoT a hmA (Or.inr hin0)
      rw [← hSplit704, sepConj_emp,
          sepConj_comm (_ : SepProp) ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝,
          sepConj_assoc ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ _ R,
          sepConj_assoc ⌜MallocngCallAccounting 16 stepB s0 sf⌝ _ R,
          sepConj_assoc (stackFrame s0 800) _ R,
          sepConj_assoc (FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf) _ R]
      refine Satisfies.mono ?_ hm'
      refine Entails.pure_right hclSf (Entails.pure_right hAcc0Sf ?_)
      exact sepConj_mono_right
        (sepConj_mono hPostCongr (Entails.pure_right hx0_0 (Entails.refl R)))
  ·
    have hOom' := Satisfies.drop_mid hOom
    dsimp only [libcMallocImplFineSpec, withCL] at hOom' ⊢
    rw [satisfies_pure_sepConj] at hOom' ⊢
    obtain ⟨hOomT, hR'⟩ := hOom'
    have hStepLe : fineStepReserve (if decide (newSize.toNat ≤ MallocngMaxAllocSize)
        then .alloc newSize.toNat else .alloc 0) bgt ≤ stepB := by
      rw [fineStepReserve_null_eq (decide (newSize.toNat ≤ MallocngMaxAllocSize)) newSize.toNat bgt]
      exact Nat.le_refl _
    refine ⟨?_, hR'⟩
    exact fineStepOomCond_congr hStepLe
      (by rw [hsTail]; rfl) (by rw [hsTail]; rfl) (by rw [hsTail]; rfl) hPermTail hOomT

/-! ## `ENOMEM` Overflow Path -/

/-- At `+0x2b8`, calls `___errno_location`, stores `12#32` (`ENOMEM`), sets `x20 := 0#64`,
    and jumps to `+0x294` (`realloc_epilogue_ok`). -/
theorem realloc_enomem_fine_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
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
       FineEnv γ maddrs tp brkStart bgt ivs0 s ∗
       Rest)
      (fun sf Pf =>
        sf.mem.perm = s0.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢ stackFrame s0 800 ∗
          FinePostEnv γ maddrs tp brkStart bgt ivs0 s0 sf ∗ Rest)) oom := by
  intro sp1; have _ := hb
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (fineEnv_focus_errno γ maddrs tp brkStart bgt ivs0 s))))) ?_
  refine SepWP.weaken_pre (P' :=
      ⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
      ∃∗ errnoVal : BitVec 32,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (ReallocSavedLo s0 sp1 ∗
         (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
          memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
         stackFrameAt sp1 720 ∗
         (FineCoreImpl γ maddrs brkStart s.brk bgt ivs0 ∗
          ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ∗
         Rest))
    (by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_mono fun ev => Entails.of_eq ?_
      generalize (FineCoreImpl γ maddrs brkStart s.brk bgt ivs0) = PCore
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
       (FineCoreImpl γ maddrs brkStart s.brk bgt ivs0 ∗
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
        (FineCoreImpl γ maddrs brkStart s.brk bgt ivs0 ∗
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
      (FinePostEnv γ maddrs tp brkStart bgt ivs0 s0 sFin ∗ Rest))
    (by
      have htp0 : s0.tpidrEl0 = tp := hproc.2.2.1.symm.trans htp
      have hbrks0 : s0.brkStart = brkStart := hproc.2.2.2.1.symm.trans hbrks
      have hUnf := fineEnv_unfocus_errno γ maddrs tp brkStart bgt ivs0 (s0 := s0) (sf := sFin)
        12#32 hPermF hbrkF (hprocF.2.2.1.trans htp0) (hprocF.2.2.2.1.trans hbrks0)
      rw [← hbrk] at hUnf
      refine Entails.trans (Q := ReallocSavedLo s0 sp1 ∗
          (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
           memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
          stackFrameAt sp1 720 ∗
          ((((tp - 0xa4#64) ↦₃₂ 12#32) ∗
            (FineCoreImpl γ maddrs brkStart s.brk bgt ivs0 ∗
             ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) ∗ Rest))
        (Entails.of_eq (by
          generalize (FineCoreImpl γ maddrs brkStart s.brk bgt ivs0) = PCore
          ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hUnf)))) ?_
  refine SepWP.mono (realloc_epilogue_ok hb hpcF hrunF hspF halF hsp0 hx20F
    hx23F hx24F hx25F hx26F hcsF) ?_
  intro sf Pf _ _ ⟨hmemEq, hbrkEq, hprocE, hspE, hcsE, hx0E, hPf⟩
  refine ⟨by rw [hmemEq]; exact hPermF, hbrkEq.trans hbrkF,
    mallocngProcPreserved_trans hprocF hprocE, hspE, hcsE, hx0E, ?_⟩
  have hPostCongr := finePostEnv_congr_state (γ := γ) (A := maddrs)
    (tp := tp) (brkStart := brkStart) (bf := bgt) (ivs0 := ivs0) (s0 := s0)
    hmemEq hbrkEq hprocE.2.2.1 hprocE.2.2.2.1
  rw [hPostCongr] at hPf
  exact Entails.trans hPf (Entails.of_eq (by ac_rfl))

/-! ## Stage 4 Out-of-Place `malloc + memcpy + free` -/

set_option maxHeartbeats 400000 in
/-- Out-of-place `malloc(newSz) + commit stepReallocAdd + memcpy(q, p, min oldSz newSz) + free(p)`
    (`+0x260` → `ret`). -/
theorem realloc_stage4_oop_fine_ok [MallocngMultiPlacement]
    (hImplRaw : LibcMallocImplFineRawStmt)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) {p : BitVec 64} {oldSz align newSz : Nat} (origBs : List (BitVec 8))
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
    let bf := FineBudget.stepRealloc align oldSz newSz bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       FineEnv γ maddrs tp brkStart bgt ivs0 s ∗
       FineBlock γ p oldSz (max align 16) ∗
       (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ∗
       Frame)
      (fun sf Pf =>
        ∃ q : BitVec 64,
          MallocngCallAccounting 16
            (fineStepReserve (.realloc align oldSz newSz) bgt) s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
          (Pf ⊢ stackFrame s0 800 ∗
            FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(FineInitBlockSem γ).pureWf q (newSz, max align 16, keptBs)⌝ ∗
            (FineInitBlockSem γ).interp q (newSz, max align 16, keptBs) ∗
            Frame))
      (fun sf => ⌜FineStepOomCond msvc (fineStepReserve (.realloc align oldSz newSz) bgt) s0 sf⌝) := by
  intro sp1 bf keptBs; have _ := hb
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMaxLt64 : MallocngMaxAllocSize < 2 ^ 64 := maxAllocSize_lt_pow64
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
  have hMalloc := call_placed_libcMallocImpl_raw_fine hImplRaw (P := blkPC_b14.rebase b (fun _ => none))
    γ tp brkStart bgt ivs0 newSz (by intro pc; simp) rfl
  have hEnvS1 : FineEnv γ maddrs tp brkStart bgt ivs0 s =
      FineEnv γ maddrs tp brkStart bgt ivs0 s1 := by rw [hs1]; rfl
  have hSf704 : stackFrameAt sp1 720 = (stackFrame s1 704 ∗ stackFrameAt (sp1 - 704#64) 16) := by
    rw [stackFrameAt_720_split sp1 704 16 (by decide),
        ← stackFrame_eq_stackFrameAt_720 704 (by decide) hsp1Eq]
  refine SepWP.call_subroutine_frame hMalloc (x := ())
    (F := stackFrameAt (sp1 - 704#64) 16 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
      FineBlock γ p oldSz (max align 16) ∗ (p ↦ₛ keptBs) ∗
      memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗ Frame)
    (ret_pc := b + 0x268#64)
    (by rw [hs1]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by rw [hs1]; simp [hrun]) (by rw [hs1]; simpa [State.spAligned] using hal)
    (by rw [hs1]; simp)
    (fun R' hm => by
      dsimp only [libcMallocImplFineRawSpec, withCL]
      have hx0_s1 : (s1.readReg64 .x0).toNat = newSz := by
        rw [hs1]; simp only [wp_norm, arm64_norm, hNewBvNat]
      have hcl_s1 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem := by rwa [hmem1Eq]
      refine Satisfies.mono ?_ hm; rw [hSf704, hEnvS1]
      refine Entails.trans (Q :=
          (stackFrame s1 704 ∗ FineEnv γ maddrs tp brkStart bgt ivs0 s1) ∗
          (stackFrameAt (sp1 - 704#64) 16 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
           FineBlock γ p oldSz (max align 16) ∗ (p ↦ₛ keptBs) ∗
           memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗ Frame) ∗ R')
        (Entails.of_eq (by
          dsimp only [keptBs]
          generalize (FineEnv γ maddrs tp brkStart bgt ivs0 s1) = PEnv
          generalize (FineBlock γ p oldSz (max align 16)) = PBlkP
          ac_rfl)) ?_
      refine sepConj_mono_left ?_; rw [sepConj_comm _ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem⌝]
      exact Entails.pure_right hcl_s1 (Entails.pure_right hx0_s1 (Entails.refl _)))
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_
    (fun R' sf _ ho => by
      have ho' := Satisfies.drop_mid ho
      dsimp only [libcMallocImplFineRawSpec, withCL] at ho'; rw [satisfies_pure_sepConj] at ho' ⊢
      obtain ⟨ho1, hR'⟩ := ho'; simp only [hNewMax, decide_true, ↓reduceIte] at ho1
      have hfs1 : s1.fs = s0.fs := by rw [hs1]; exact hproc.1
      have htr1 : s1.trace = s0.trace := by rw [hs1]; exact hproc.2.1
      have hsig1 : s1.sigActions = s0.sigActions := by rw [hs1]; exact hproc.2.2.2.2.2.2
      have hp1 : s1.mem.perm = s0.mem.perm := by rw [hmem1Eq]; exact hPerm
      exact ⟨fineStepOomCond_congr (fineStepReserve_alloc_le_realloc newSz align oldSz bgt)
        hfs1 htr1 hsig1 hp1 ho1, hR'⟩)
  intro s2 hpc2 hrun2 hsp2 hcs12
  let bf1 := FineBudget.stepReallocAdd align newSz bgt
  dsimp only [libcMallocImplFineRawSpec, withCL]; simp only [hNewMax, decide_true, ↓reduceIte]
  refine SepWP.weaken_pre (P' :=
      ∃∗ q : BitVec 64, ∃∗ bsNew : List (BitVec 8), ∃∗ st0 : MallocngSt,
      ∃∗ alignMap0 : BitVec 64 → Option Nat, ∃∗ st' : MallocngSt,
      ∃∗ g' : GroupDesc, ∃∗ idx : Nat, ∃∗ bCoarse : MallocngBudget,
        ⌜MallocngProcPreserved s1 s2 ∧
         MallocngMappedDelta 16 (fineStepReserve (.alloc newSz) bgt) s1.mem s2.mem ∧
         VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem ∧
         s2.readReg64 .x0 = q ∧ s2.tpidrEl0 = tp ∧ s2.brkStart = brkStart ∧
         MallocngBlockWf q newSz ∧ bsNew.length = newSz ∧
         MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s1.mem s2.mem ∧
         MallocngWF maddrs.base brkStart s2.brk bCoarse.liveCost bCoarse.peakCost st' ∧
         MallocImplFineRawRel maddrs.base brkStart bgt ivs0 alignMap0 st0 st' g' idx newSz q⌝ ∗
        ((MallocngRoTablesA maddrs ∗
          ghostMapAuth (fineAlignGam γ) alignMap0 ∗
          MallocngCoreStA (fineBaseGam γ) maddrs brkStart s2.brk bCoarse.liveCost bCoarse.peakCost st' ∗
          MallocngRuntime maddrs tp ∗
          (q ↦ₛ bsNew) ∗
          MallocngBlockToken (fineBaseGam γ) q newSz) ∗
         (stackFrameAt sp1 720 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
          FineBlock γ p oldSz (max align 16) ∗
          (p ↦ₛ keptBs) ∗ memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗
          Frame)))
    (by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_mono fun q => Entails.sepExists_mono fun bsNew =>
        Entails.sepExists_mono fun st0 => Entails.sepExists_mono fun alignMap0 =>
        Entails.sepExists_mono fun st' => Entails.sepExists_mono fun g' =>
        Entails.sepExists_mono fun idx => Entails.sepExists_mono fun bCoarse => ?_
      refine Entails.trans (Q :=
          ⌜MallocngProcPreserved s1 s2 ∧
            MallocngMappedDelta 16 (fineStepReserve (.alloc newSz) bgt) s1.mem s2.mem⌝ ∗
          ⌜s2.readReg64 .x0 = q ∧ s2.tpidrEl0 = tp ∧ s2.brkStart = brkStart ∧
            MallocngBlockWf q newSz ∧ bsNew.length = newSz ∧
            MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s1.mem s2.mem ∧
            MallocngWF maddrs.base brkStart s2.brk bCoarse.liveCost bCoarse.peakCost st' ∧
            MallocngCountIvsWF bCoarse (dynamicRootRegions st') st' ∧
            MallocImplFineRawRel maddrs.base brkStart bgt ivs0 alignMap0 st0 st' g' idx newSz q ∧
            (g'.isMmapped = true → bsNew = List.replicate newSz 0#8)⌝ ∗
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem⌝ ∗
          ((MallocngRoTablesA maddrs ∗
            ghostMapAuth (fineAlignGam γ) alignMap0 ∗
            MallocngCoreStA (fineBaseGam γ) maddrs brkStart s2.brk bCoarse.liveCost bCoarse.peakCost st' ∗
            MallocngRuntime maddrs tp ∗ (q ↦ₛ bsNew) ∗
            MallocngBlockToken (fineBaseGam γ) q newSz) ∗
           ((stackFrame s1 704 ∗ stackFrameAt (sp1 - 704#64) 16) ∗
            ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
            FineBlock γ p oldSz (max align 16) ∗ (p ↦ₛ keptBs) ∗
            memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗ Frame)))
        (Entails.of_eq (by
          dsimp only [keptBs]
          generalize (MallocngRoTablesA maddrs) = PRo
          generalize (ghostMapAuth (fineAlignGam γ) alignMap0) = PGh
          generalize (MallocngCoreStA (fineBaseGam γ) maddrs brkStart s2.brk
            bCoarse.liveCost bCoarse.peakCost st') = PSt
          generalize (MallocngRuntime maddrs tp) = PRt
          generalize (FineBlock γ p oldSz (max align 16)) = PBlkP
          ac_rfl)) ?_
      refine Entails.pure_left fun ⟨hProc2, hDelta2⟩ =>
        Entails.pure_left fun ⟨hx0_2, htp2, hbrks2, hWfQ, hbsLen, hNoOrph2, hwf2, _, hRaw2, _⟩ =>
        Entails.pure_left fun hcl2 => ?_
      refine Entails.pure_right
        ⟨hProc2, hDelta2, hcl2, hx0_2, htp2, hbrks2, hWfQ, hbsLen, hNoOrph2, hwf2, hRaw2⟩ ?_
      rw [hSf704.symm]
      exact Entails.refl _) ?_
  apply SepWP.exists_left; intro q; apply SepWP.exists_left; intro bsNew
  apply SepWP.exists_left; intro st0; apply SepWP.exists_left; intro alignMap0
  apply SepWP.exists_left; intro st'; apply SepWP.exists_left; intro g'
  apply SepWP.exists_left; intro idx; apply SepWP.exists_left; intro bCoarse
  apply SepWP.pure_elim
  rintro ⟨hProc12, hDelta12, hcl2, hx0_2, htp2, hbrks2,
    ⟨hqNe, hq16, hq48, _⟩, hbsLen, hNoOrph12, hwf2, hRaw2⟩
  refine VerifiedLibraries.Mallocng.Proofs.sepWP_bupd_pre (Q :=
      FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
      memRegion q newSz ∗ FineBlock γ q newSz (max align 16) ∗
      stackFrameAt sp1 720 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
      FineBlock γ p oldSz (max align 16) ∗
      (p ↦ₛ keptBs) ∗ memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗
      Frame)
    (by
      have hCommit := commit_stage4_malloc_raw γ tp brkStart bgt ivs0 alignMap0 st0 st'
        g' idx align newSz q bCoarse bsNew s2 htp2 hbrks2 hbsLen hwf2 hRaw2
      refine Entails.trans
        (Entails.trans (sepConj_mono_left hCommit) (bupd_frame_r _ _)) ?_
      exact bupd_mono (Entails.of_eq (by
        generalize (FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2) = PEnv2
        generalize (FineBlock γ q newSz (max align 16)) = PBlkQ
        generalize (FineBlock γ p oldSz (max align 16)) = PBlkP
        ac_rfl))) ?_
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
            FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
            FineBlock γ q newSz (max align 16) ∗
            stackFrameAt sp1 720 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
            FineBlock γ p oldSz (max align 16) ∗ Frame)))
      (by
        have hPrep := copyPrep_entails p q keptBs oldSz newSz copyLen
          hKeptLenLe (Nat.min_le_left _ _) (Nat.min_le_right _ _) (by omega) (by omega)
        refine Entails.trans (Q :=
            ((p ↦ₛ keptBs) ∗ memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗
              memRegion q newSz) ∗
            (FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
             FineBlock γ q newSz (max align 16) ∗ stackFrameAt sp1 720 ∗
             ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
             FineBlock γ p oldSz (max align 16) ∗ Frame))
          (Entails.of_eq (by
            generalize (FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2) = PEnv2
            generalize (FineBlock γ q newSz (max align 16)) = PBlkQ
            generalize (FineBlock γ p oldSz (max align 16)) = PBlkP
            ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left hPrep) ?_
        simp only [sepExists_sepConj_left]
        refine Entails.sepExists_mono fun dstBs => Entails.sepExists_mono fun midBs => Entails.of_eq ?_
        generalize (FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2) = PEnv2
        generalize (FineBlock γ q newSz (max align 16)) = PBlkQ
        generalize (FineBlock γ p oldSz (max align 16)) = PBlkP
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
            FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
            FineBlock γ q newSz (max align 16) ∗ stackFrameAt sp1 720 ∗
            ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
            FineBlock γ p oldSz (max align 16) ∗ Frame)
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
        (FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s3 ∗
         memRegion p oldSz ∗ FineBlock γ p oldSz (max align 16) ∗
         stackFrameAt sp1 720 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
         FineBlock γ q newSz (max align 16) ∗ (q ↦ₛ keptBs) ∗
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
             FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
             FineBlock γ q newSz (max align 16) ∗ stackFrameAt sp1 720 ∗
             ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
             FineBlock γ p oldSz (max align 16) ∗ Frame))
          (Entails.of_eq (by
            generalize (FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2) = PEnv2
            generalize (FineBlock γ q newSz (max align 16)) = PBlkQ
            generalize (FineBlock γ p oldSz (max align 16)) = PBlkP
            generalize (MallocngProcPreserved s2c s3 ∧ s3.brk = s2c.brk ∧
              s3.mem.perm = s2c.mem.perm ∧ s3.readReg64 .x0 = q) = Pure3
            ac_rfl)) ?_
        refine Entails.pure_left fun ⟨hp3, hbrk3, hperm3, _⟩ => Entails.pure_left fun hcl3 => ?_
        have hp3' : MallocngProcPreserved s2 s3 := by rw [hs2c] at hp3; exact hp3
        have hbrk3' : s3.brk = s2.brk := by rw [hs2c] at hbrk3; exact hbrk3
        have hperm3' : s3.mem.perm = s2.mem.perm := by rw [hs2c] at hperm3; exact hperm3
        have hEnv23 : FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 =
            FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s3 := by
          unfold FineEnv; rw [hbrk3', hp3'.2.2.1, hp3'.2.2.2.1]
        rw [hEnv23]
        refine Entails.pure_right ⟨⟨hp3', hbrk3', hperm3'⟩, hcl3⟩ ?_
        refine Entails.trans (sepConj_mono_left hFin) ?_
        exact Entails.of_eq (by
          generalize (FineEnv γ maddrs tp brkStart bf1 (dynamicRootRegions st') s3) = PEnv3
          generalize (FineBlock γ q newSz (max align 16)) = PBlkQ
          generalize (FineBlock γ p oldSz (max align 16)) = PBlkP
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
    have hDelta03 : MallocngMappedDelta 16 (fineStepReserve (.alloc newSz) bgt) s0.mem s3.mem := by
      rw [hmem1Eq] at hDelta12
      have h0s : MallocngMappedDelta 0 0 s0.mem s.mem :=
        ⟨[], by decide, by decide, fun _ hm => Or.inl (by rwa [hPerm] at hm)⟩
      have h23 : MallocngMappedDelta 0 0 s2.mem s3.mem :=
        ⟨[], by decide, by decide, fun _ hm => Or.inl (by rwa [hperm23] at hm)⟩
      exact mappedDelta_trans_zero_right (mappedDelta_zero_trans_left h0s hDelta12) h23
    have hNoOrph03 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem s3.mem := by
      intro a hm3 hor0
      exact hNoOrph12 a (by rwa [← hperm23]) (hor0.imp (fun h0 => by rwa [hmem1Eq, hPerm]) id)
    exact realloc_s4_free_fine_ok hb γ tp brkStart bgt ivs0 (dynamicRootRegions st') s0 s3 origBs
      hpNe hqNe hq16 hq48 hpc3 hrun3 hsp3Eq hal3 hsp0 hx19_s3 hx20_s3
      hcs3 hcl3 hProc03 hDelta03 hNoOrph03

end LibsignalBinary.Heap.Fine
