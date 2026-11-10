/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ReallocNonNullFine

/-!
# Fine-Grained Placed `__libc_realloc` and `realloc` Verification

Verifies placed `__libc_realloc` (`blk14`, 800-byte stack) by dispatching `oldBlk = none` to the
null path and `oldBlk = some _` to the non-null path, and lifts the result across the 1-instruction
`realloc` (`blk13`) tail branch to `fineReallocSpec`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Placed `__libc_realloc` Contract and Caller Lift -/

/-- Fine-model placed `__libc_realloc(p, newSize)` (`blk14`, `800` B stack) contract. -/
def libcReallocFineSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p newSize : BitVec 64)
    (oldBlk : Option (Nat × Nat × List (BitVec 8)))
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat)) : Spec Unit :=
  let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
  let keptBs := ((oldBlk.map fun (_, _, bs) => bs).getD []).take newSize.toNat
  let ev : FineEvent := match oldBlk with
    | none => .alloc newSize.toNat
    | some (oldSize, align, _) => .realloc align oldSize newSize.toNat
  let evRes : FineEvent := match oldBlk with
    | none => .realloc 16 0 newSize.toNat
    | some (oldSize, align, _) => .realloc align oldSize newSize.toNat
  let outAlign : Nat := match oldBlk with
    | none => 16
    | some (_, align, _) => max align 16
  let bf := if ok then FineBudget.step ev bgt else bgt
  let stepB := if ok then fineStepReserve evRes bgt else fineStepReserve (.alloc 0) bgt
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧
       (OptOwn (FineInitBlockSem γ)).pureWf p oldBlk⌝ ∗
      stackFrame s0 800 ∗
      FineEnv γ maddrs tp brkStart bgt ivs0 s0 ∗
      (OptOwn (FineInitBlockSem γ)).interp p oldBlk
    post := fun _ s0 sf =>
      ⌜MallocngCallAccounting 16 stepB s0 sf⌝ ∗
      stackFrame s0 800 ∗
      FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
      if ok then
        ∃∗ q : BitVec 64,
          ⌜sf.readReg64 .x0 = q ∧
           (FineInitBlockSem γ).pureWf q (newSize.toNat, outAlign, keptBs)⌝ ∗
          (FineInitBlockSem γ).interp q (newSize.toNat, outAlign, keptBs)
      else
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        (OptOwn (FineInitBlockSem γ)).interp p oldBlk
    onOom := fun _ s0 sf =>
      ⌜FineStepOomCond msvc stepB s0 sf⌝
  }

def LibcReallocFineStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p newSize : BitVec 64)
    (oldBlk : Option (Nat × Nat × List (BitVec 8)))
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat)),
    subroutine_ok (mallocngBlockProg mmpl 14 msvc) (mbase 14)
      (libcReallocFineSpec γ tp brkStart p newSize oldBlk bgt ivs0)

theorem call_placed_libcRealloc_fine [MallocngMultiPlacement]
    (h : LibcReallocFineStmt) {P : Program}
    (γ : GhostName) (tp brkStart p newSize : BitVec 64)
    (oldBlk : Option (Nat × Nat × List (BitVec 8)))
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 14)
      (libcReallocFineSpec γ tp brkStart p newSize oldBlk bgt ivs0) :=
  subroutine_ok_block_to_block (j := 14) (by decide)
    (h γ tp brkStart p newSize oldBlk bgt ivs0) hext hsvc

/-! ## Placed `__libc_realloc` and Exported `realloc` -/

/-- Placed `__libc_realloc(p, newSize)` (`blk14`, `800` B stack) over `FineBudget`,
    parameterized only over `ReallocStage2FineStmt` and `ReallocStage3FineStmt`. -/
theorem placed_libcRealloc_fine_ok
    (hStage2 : ReallocStage2FineStmt) (hStage3 : ReallocStage3FineStmt) :
    LibcReallocFineStmt := by
  intro _ γ tp brkStart p newSize oldBlk bgt ivs0
  open ProofLib.ProgramReflection in
  have hfn : ∀ c, (blkPC_b14.rebase c (fun _ => none)).fnAddr "__libc_realloc" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase, Program.fnOff, Program.findSymbol?, blkPC_b14, PlacedLib.program]
    rw [blkSymsEq_b14]
    have hf : (toStringSymbols blkSymChars_b14).find? (·.1 == "__libc_realloc") =
        some ("__libc_realloc", 0) := by decide
    rw [hf]; exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b14 (hfn (mbase 14)) fun b hb => ?_
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre hsp
  rw [hfn b] at hpc
  have hpre' : s0.mem ⊨
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ ∗
      ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧
       (OptOwn (FineInitBlockSem γ)).pureWf p oldBlk⌝ ∗
      (stackFrame s0 800 ∗ FineEnv γ maddrs tp brkStart bgt ivs0 s0 ∗
       (OptOwn (FineInitBlockSem γ)).interp p oldBlk) ∗ R := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    dsimp only [libcReallocFineSpec, withCL]
    generalize (FineEnv γ maddrs tp brkStart bgt ivs0 s0) = PEnv
    generalize ((OptOwn (FineInitBlockSem γ)).interp p oldBlk) = POld
    ac_rfl
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcl0, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx1, hpWf⟩, hpre'⟩ := hpre'
  cases oldBlk with
  | none =>
    rw [OptOwn_interp_none] at hpre'
    have hpre'' : s0.mem ⊨ ⌜p = 0#64⌝ ∗
        (stackFrame s0 800 ∗ FineEnv γ maddrs tp brkStart bgt ivs0 s0) ∗ R :=
      Satisfies.mono (Entails.of_eq (by
        generalize (FineEnv γ maddrs tp brkStart bgt ivs0 s0) = PEnv
        ac_rfl)) hpre'
    rw [satisfies_pure_sepConj] at hpre''; obtain ⟨hp0, hpre''⟩ := hpre''; subst hp0
    refine ⟨stackFrame s0 800 ∗ FineEnv γ maddrs tp brkStart bgt ivs0 s0, hpre'',
      SepWP.mono (realloc_null_path_fine_ok placed_libcMallocImpl_fine_ok hb
        γ tp brkStart newSize bgt ivs0 s0 R hpc hrun hsp hx0 hx1 hcl0)
        fun sf Pf _ _ ⟨hq, hspF, hcsF⟩ => ⟨fun hm => Satisfies.mono ?_ (hq hm), hspF, hcsF⟩⟩
    dsimp only [libcReallocFineSpec, withCL, Option.map, Option.getD]
    simp only [List.take_nil]
    refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))))
    split
    · exact Entails.refl _
    · refine sepConj_mono_right ?_
      rw [OptOwn_interp_none, ← sepConj_emp ⌜(0#64 : BitVec 64) = 0#64⌝]
      exact Entails.pure_right rfl (Entails.refl emp)
  | some blk =>
    rcases blk with ⟨oldSz, align, origBs⟩
    exact ⟨stackFrame s0 800 ∗ FineEnv γ maddrs tp brkStart bgt ivs0 s0 ∗
      (FineInitBlockSem γ).interp p (oldSz, align, origBs), hpre',
      realloc_nonnull_path_fine_ok hStage2 hStage3 hb γ tp brkStart p newSize oldSz align origBs
        bgt ivs0 s0 R hpWf.2 hpc hrun hsp hx0 hx1 hcl0⟩

/-- Exported `"realloc"` (`blk13`, 1-instruction `b __libc_realloc` tail-call) over `FineBudget`,
    parameterized only over `ReallocStage2FineStmt` and `ReallocStage3FineStmt`. -/
theorem placed_realloc_fine_entry_of_stages
    (hStage2 : ReallocStage2FineStmt) (hStage3 : ReallocStage3FineStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "realloc"
      (fineReallocSpec svc γ (mallocngAddrsOfPlacement mpl)) := by
  let _ : MallocngMultiPlacement := ⟨mpl, svc, hPlace, hSvc⟩
  refine ⟨by decide, 13, 0, by decide +kernel, ?_⟩
  rw [fnAddr_realloc mpl]
  apply withCL_to_withCodeLoaded
  open ProofLib.ProgramReflection in
  have hfn : ∀ c, (blkPC_b13.rebase c (fun _ => none)).fnAddr "realloc" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase, Program.fnOff, Program.findSymbol?, blkPC_b13, PlacedLib.program]
    rw [blkSymsEq_b13]
    have hf : (toStringSymbols blkSymChars_b13).find? (·.1 == "realloc") =
        some ("realloc", 0) := by decide
    rw [hf]; exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b13 (hfn (mbase 13)) fun b hb => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, newSize, sp, oldBlk, tp, brkStart, bgt, ivs0⟩
  let outAlign : Nat := match oldBlk with
    | none => 16
    | some (_, align, _) => max align 16
  let keptBs := ((oldBlk.map fun (_, _, bs) => bs).getD []).take newSize.toNat
  let ev : FineEvent := match oldBlk with
    | none => .alloc newSize.toNat
    | some (oldSize, align, _) => .realloc align oldSize newSize.toNat
  let evRes : FineEvent := match oldBlk with
    | none => .realloc 16 0 newSize.toNat
    | some (oldSize, align, _) => .realloc align oldSize newSize.toNat
  intro R s0 hpc hrun hpre hsp
  rw [hfn b] at hpc
  have _ := hb
  have hpre' : s0.mem ⊨
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ ∗
      ⌜s0.sp = sp ∧ s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧
       (OptOwn (FineInitBlockSem γ)).pureWf p oldBlk⌝ ∗
      (stackFrameAt sp 1024 ∗ FineEnv γ maddrs tp brkStart bgt ivs0 s0 ∗
       (OptOwn (FineInitBlockSem γ)).interp p oldBlk) ∗ R := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    dsimp only [withCL, fineReallocSpec, ToBaseSpec.toSpec, CType.CondOwn, mallocngStackBytes]
    generalize (FineEnv γ maddrs tp brkStart bgt ivs0 s0) = PEnv
    generalize ((OptOwn (FineInitBlockSem γ)).interp p oldBlk) = POld
    ac_rfl
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcl0, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hspEq, hx0, hx1, hpWf⟩, hpre'⟩ := hpre'
  have hSf1024 : stackFrameAt sp 1024 = (stackFrame s0 800 ∗ stackFrameAt (sp - 800#64) 224) := by
    rw [show (1024 : Nat) = 800 + 224 from rfl, stackFrameAt_split sp 800 224]
    congr 1; unfold stackFrame; rw [hspEq, stackFrameAt_eq_memRegion sp 800]
  rw [hSf1024] at hpre'
  refine ⟨(stackFrame s0 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
    FineEnv γ maddrs tp brkStart bgt ivs0 s0 ∗
    (OptOwn (FineInitBlockSem γ)).interp p oldBlk, hpre', ?_⟩
  wp_step
  apply sepWP_bind_state; intro s1 hs1
  have hRealloc := call_placed_libcRealloc_fine (placed_libcRealloc_fine_ok hStage2 hStage3)
    (P := blkPC_b13.rebase b (fun _ => none))
    γ tp brkStart p newSize oldBlk bgt ivs0 (by intro pc; simp) rfl
  have hEnv1 : FineEnv γ maddrs tp brkStart bgt ivs0 s0 =
      FineEnv γ maddrs tp brkStart bgt ivs0 s1 := by
    unfold FineEnv; rw [hs1]; rfl
  have hSf1 : stackFrame s0 800 = stackFrame s1 800 := by unfold stackFrame; rw [hs1]; simp
  rw [hEnv1, hSf1]
  refine SepWP.call_subroutine_frame hRealloc (x := ()) (F := stackFrameAt (sp - 800#64) 224)
    (ret_pc := s0.readReg64 Reg.lr)
    (by rw [hs1]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by rw [hs1]; simp [hrun])
    (by unfold State.spAligned at hsp ⊢; rw [hs1]; simpa using hsp)
    (by rw [hs1]; simp)
    (fun R' hm => by
      have hcl1 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem := by rw [hs1]; exact hcl0
      have hPure1 : s1.readReg64 .x0 = p ∧ s1.readReg64 .x1 = newSize ∧
          (OptOwn (FineInitBlockSem γ)).pureWf p oldBlk :=
        ⟨by rw [hs1]; simpa using hx0, by rw [hs1]; simpa using hx1, hpWf⟩
      refine Satisfies.mono ?_ hm
      dsimp only [libcReallocFineSpec, withCL]
      refine Entails.trans (Entails.pure_right hcl1 (Entails.pure_right hPure1 (Entails.refl _))) ?_
      exact Entails.of_eq (by
        generalize (FineEnv γ maddrs tp brkStart bgt ivs0 s1) = PEnv
        generalize ((OptOwn (FineInitBlockSem γ)).interp p oldBlk) = POld
        ac_rfl))
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpcSf hrunSf hspSf hcsSf => ?_)
    (fun R' sf _ hOom => ?_)
  · have hspSf0 : sf.sp = s0.sp := hspSf.trans (by rw [hs1]; simp)
    have hcsSf0 : CalleeSavedPreserved s0 sf := CalleeSavedPreserved.trans (by
      rw [hs1]; exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp [calleeSavedVRegs]⟩) hcsSf
    refine SepWP.done hpcSf hrunSf ⟨fun hm => ?_, hspSf0, hcsSf0⟩
    dsimp only [libcReallocFineSpec, withCL] at hm
    have hs1Mem : s1.mem = s0.mem := by rw [hs1]; rfl
    have hAccCongr : ∀ k m, MallocngCallAccounting k m s1 sf → MallocngCallAccounting k m s0 sf := by
      intro k m ⟨hPr, hDl⟩
      exact ⟨mallocngProcPreserved_trans (by rw [hs1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hPr,
        by rwa [hs1Mem] at hDl⟩
    have hPostCongr : ∀ bf', FinePostEnv γ maddrs tp brkStart bf' ivs0 s1 sf =
        FinePostEnv γ maddrs tp brkStart bf' ivs0 s0 sf := fun bf' => by
      unfold FinePostEnv MallocngNoOrphanMappings; rw [hs1Mem]
    have hSfCombine : stackFrame s1 800 ∗ stackFrameAt (sp - 800#64) 224 = stackFrameAt sp 1024 := by
      rw [← hSf1, ← hSf1024]
    rw [hPostCongr] at hm
    dsimp only [withCL, fineReallocSpec, ToBaseSpec.toSpec, CType.CondOwn, mallocngStackBytes]
    by_cases hLe : newSize.toNat ≤ MallocngMaxAllocSize
    · simp only [decide_eq_true hLe, ↓reduceIte] at hm ⊢
      have hm' : sf.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
          ⌜MallocngCallAccounting 16 (fineStepReserve evRes bgt) s1 sf⌝ ∗
          (∃∗ q : BitVec 64, ⌜sf.readReg64 .x0 = q ∧
             (FineInitBlockSem γ).pureWf q (newSize.toNat, outAlign, keptBs)⌝ ∗
            (FineInitBlockSem γ).interp q (newSize.toNat, outAlign, keptBs)) ∗
          (stackFrame s1 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
          FinePostEnv γ maddrs tp brkStart (FineBudget.step ev bgt) ivs0 s0 sf ∗ R := by
        refine Satisfies.mono (Entails.of_eq ?_) hm; dsimp only [FineInitBlockSem, outAlign, keptBs, ev, evRes]
        generalize (∃∗ q : BitVec 64, _) = PRet
        generalize (FinePostEnv γ maddrs tp brkStart _ ivs0 s0 sf) = PPost; ac_rfl
      rw [hSfCombine, satisfies_pure_sepConj] at hm'; obtain ⟨hclSf, hm'⟩ := hm'
      rw [satisfies_pure_sepConj] at hm'; obtain ⟨hAcc1, hm'⟩ := hm'
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm'; obtain ⟨q, hm'⟩ := hm'
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm'; obtain ⟨⟨hx0Q, hWfQ⟩, hm'⟩ := hm'
      have hAcc0 := hAccCongr _ _ hAcc1; rw [← hx0Q] at hWfQ hm'
      have hPurePost : (True : Prop) ∧
          (OptOwn (FineInitBlockSem γ)).pureWf (sf.readReg64 .x0)
            (some (newSize.toNat, outAlign, keptBs)) ∧
          MallocngCallAccounting 16 (fineStepReserve evRes bgt) s0 sf :=
        ⟨trivial, ⟨hWfQ.1, hWfQ⟩, hAcc0⟩
      refine Satisfies.mono (Entails.trans
        (Entails.pure_right hclSf (Entails.pure_right hPurePost (Entails.refl _))) ?_) hm'
      exact Entails.of_eq (by
        dsimp only [OptOwn, FineInitBlockSem, outAlign, keptBs, ev, evRes]
        generalize (FinePostEnv γ maddrs tp brkStart _ ivs0 s0 sf) = PPost
        generalize (FineBlock γ (sf.readReg64 .x0) newSize.toNat _) = PBlk
        simp only [emp_sepConj]; ac_rfl)
    · simp only [decide_eq_false hLe, Bool.false_eq_true, ↓reduceIte] at hm ⊢
      have hm' : sf.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
          ⌜MallocngCallAccounting 16 (fineStepReserve (.alloc 0) bgt) s1 sf⌝ ∗
          ⌜sf.readReg64 .x0 = 0#64⌝ ∗ (OptOwn (FineInitBlockSem γ)).interp p oldBlk ∗
          (stackFrame s1 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
          FinePostEnv γ maddrs tp brkStart bgt ivs0 s0 sf ∗ R := by
        refine Satisfies.mono (Entails.of_eq ?_) hm
        generalize ((OptOwn (FineInitBlockSem γ)).interp p oldBlk) = POld
        generalize (FinePostEnv γ maddrs tp brkStart bgt ivs0 s0 sf) = PPost; ac_rfl
      rw [hSfCombine, satisfies_pure_sepConj] at hm'; obtain ⟨hclSf, hm'⟩ := hm'
      rw [satisfies_pure_sepConj] at hm'; obtain ⟨hAcc1, hm'⟩ := hm'
      have hPurePost : (OptOwn (FineInitBlockSem γ)).pureWf p oldBlk ∧
          (OptOwn (FineInitBlockSem γ)).pureWf (sf.readReg64 .x0) none ∧
          MallocngCallAccounting 16 (fineStepReserve (.alloc 0) bgt) s0 sf :=
        ⟨hpWf, trivial, hAccCongr _ _ hAcc1⟩
      refine Satisfies.mono (Entails.trans
        (Entails.pure_right hclSf (Entails.pure_right hPurePost (Entails.refl _))) ?_) hm'
      exact Entails.of_eq (by
        dsimp only [OptOwn]
        generalize ((OptOwn (FineInitBlockSem γ)).interp p oldBlk) = POld
        generalize (FinePostEnv γ maddrs tp brkStart bgt ivs0 s0 sf) = PPost; ac_rfl)
  · have hOom' := Satisfies.drop_mid hOom
    dsimp only [libcReallocFineSpec, withCL, fineReallocSpec, ToBaseSpec.toSpec] at hOom' ⊢
    rw [satisfies_pure_sepConj] at hOom' ⊢; obtain ⟨hOom1, hR'⟩ := hOom'
    exact ⟨fineStepOomCond_congr (Nat.le_refl _)
      (by rw [hs1]; rfl) (by rw [hs1]; rfl) (by rw [hs1]; rfl) (by rw [hs1]; rfl) hOom1, hR'⟩

end LibsignalBinary.Heap.Fine
