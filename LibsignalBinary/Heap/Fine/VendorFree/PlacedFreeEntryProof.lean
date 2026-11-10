/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch0
public import LibsignalBinary.Heap.Fine.VendorFree.PlacedLibcFreeProof

/-!
# Placed `free` Public Entry Verification

Proves `freePlaced_entry_ok`: placed `free(p)` (`blk03`, tail branch `b __libc_free`) satisfies
`mallocngFreeSpec` given `NontrivialFreeTopPlacedStmt`.
-/

set_option autoImplicit false

section

namespace LibsignalBinary.Heap.Fine.VendorFree
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

@[expose] public section

private theorem freeableBlock_comm (γ : GhostName) (p : BitVec 64) (n : Nat) :
    (if p = 0#64 then emp else mallocngIface.Block γ p n ∗ memRegion p n) =
      if p = 0#64 then emp else memRegion p n ∗ mallocngIface.Block γ p n := by
  split
  · rfl
  · exact sepConj_comm _ _

private theorem blk03_free_ok (hNt : NontrivialFreeTopPlacedStmt)
    [MallocngMultiPlacement] (γ : GhostName) :
    subroutine_ok (mallocngBlockProg mmpl 3 msvc) (mbase 3)
      (withCL mmpl (ToBaseSpec.toSpec (mallocngFreeSpec mallocngIface γ maddrs) (mbase 3))) := by
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
  rcases x with ⟨p, sp0, n, tp, brkStart, bud, ivs0⟩
  let P0 := (MallocngFreeableBlock mallocngIface γ).interp p n ∗
    MallocngEnv mallocngIface γ maddrs tp brkStart bud ivs0 s0 ∗
    stackFrameAt sp0 1024
  have hpre' : s0.mem ⊨ ⌜s0.mem = m0⌝ ∗
      ⌜s0.readReg64 .x0 = p ∧ s0.sp = sp0 ∧ (MallocngFreeableBlock mallocngIface γ).pureWf p n⌝ ∗
      P0 ∗ R := by
    simpa [ToBaseSpec.toSpec, mallocngFreeSpec, mallocngStackBytes, P0, sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hm0, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hsp0, _hpWf⟩, hmem0⟩ := hpre'
  have hcl_s0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem := hm0 ▸ hcl0
  refine ⟨P0, hmem0, ?_⟩
  wp_step
  let FrameF := stackFrameAt (sp0 - 272#64) 752
  have hSub := call_placed_libcFree_272 (placed_libcFree_272_ok hNt)
    (P := blkPC_b03.rebase b (fun _ => none)) γ tp brkStart p n bud ivs0
  refine SepWP.call_subroutine_frame (F := FrameF) (x := ()) (ret_pc := s0.readReg64 .lr) hSub
    (by simp only [arm64_norm]; rw [hb]; bv_arith)
    (by simp [arm64_norm, hrun])
    (by simpa [State.spAligned, arm64_norm] using hspAl0)
    (by simp [arm64_norm])
    (fun R' hm => by
      have hSF272 : ∀ s' : State, s'.sp = sp0 → stackFrame s' 272 = stackFrameAt sp0 272 := by
        intro s' hs; rw [stackFrameAt_eq_memRegion sp0 272]; simp [stackFrame, hs]
      have hEnvEq : ∀ pc', MallocngEnv mallocngIface γ maddrs tp brkStart bud ivs0 (s0.setPC pc') =
          MallocngEnv mallocngIface γ maddrs tp brkStart bud ivs0 s0 := fun _ => rfl
      rw [← sepConj_assoc]; refine Satisfies.mono (sepConj_mono_left ?_) hm
      dsimp only [P0, FrameF, libcFreePlaced272Spec, withCL]
      rw [freeableBlock_comm, stackFrameAt_1024_split_272 sp0,
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
  dsimp only [libcFreePlaced272Spec, withCL, FrameF] at hsat
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
      MallocngPostEnv mallocngIface γ maddrs tp brkStart bud' ivs0 (s0.setPC pc') sf =
      MallocngPostEnv mallocngIface γ maddrs tp brkStart bud' ivs0 s0 sf := fun _ _ => rfl
  have hsat' := Satisfies.mono (hStripCL _ _ _ _ _) hsat
  rw [hSF272 _ (by simp [arm64_norm, hsp0]), hPostEnvEq] at hsat'
  refine Satisfies.mono (sepConj_mono_left ?_) hsat'
  dsimp only [ToBaseSpec.toSpec, mallocngFreeSpec, mallocngStackBytes]
  have hAcc : MallocngCallAccounting 0 0 s0 sf :=
    ⟨procPreserved_trans' ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩ hproc_f, hdelta_f⟩
  refine Entails.pure_right hAcc ?_
  rw [stackFrameAt_1024_split_272 sp0]
  sep_frame

/-- Multi-block placed `free(p)` (`b03`) satisfies `mallocngFreeSpec`. -/
theorem freePlaced_entry_ok (hNt : NontrivialFreeTopPlacedStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "free"
      (mallocngFreeSpec mallocngIface γ (mallocngAddrsOfPlacement mpl)) := by
  letI : MallocngMultiPlacement := { mpl := mpl, svc := svc, placeable := hPlace, svcValid := hSvc }
  refine ⟨by decide, 3, 0, by decide +kernel, ?_⟩
  rw [fnAddr_free]
  exact withCL_to_withCodeLoaded (blk03_free_ok hNt γ)

end

end LibsignalBinary.Heap.Fine.VendorFree
