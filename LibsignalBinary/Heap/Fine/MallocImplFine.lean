/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.MallocImplSmallFine
public import LibsignalBinary.Heap.Fine.MallocLargeTraceRaw
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplProof
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch0
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Fine-Grained Placed `__libc_malloc_impl` and `default_malloc`

Establishes the raw uncommitted contract (`placed_libcMallocImpl_raw_fine_ok`), pure budget commit
lemmas (`stepAlloc` and `stepReallocAdd`), and committed `align = 16` contracts for placed
`__libc_malloc_impl` (`blk09`) and `default_malloc` / `malloc` (`blk04`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic ProofLib.ProgramReflection
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Prologue, Stack-Frame, and `ENOMEM` Branch Helpers -/

private theorem ult_ofNat_iff_fine {c req : Nat} (hc : c < 2 ^ 64) (hr : req < 2 ^ 64) :
    ((BitVec.ofNat 64 c).ult (BitVec.ofNat 64 req) = true) ↔ c < req := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hr,
    decide_eq_true_eq]

private theorem stackFrame_704_split_prologue_fine (s0 : State) :
    stackFrame s0 704 =
      ((∃∗ v29 : BitVec 64, (s0.sp - 80#64) ↦₆₄ v29) ∗
       (∃∗ v30 : BitVec 64, ((s0.sp - 80#64) + 8#64) ↦₆₄ v30) ∗
       memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
       stackFrameAt (s0.sp - 80#64) 624) := by
  let sp1 := s0.sp - 80#64
  have hSplit : stackFrame s0 704 = (memRegion sp1 80 ∗ stackFrameAt sp1 624) := by
    unfold stackFrame
    rw [← stackFrameAt_eq_memRegion s0.sp 704, show (704 : Nat) = 80 + 624 from rfl,
        stackFrameAt_split s0.sp 80 624, stackFrameAt_eq_memRegion s0.sp 80]
  rw [hSplit,
      memRegion_split' (b := sp1) (b' := sp1 + 8#64) (n := 8) (k := 72) rfl rfl (by decide),
      memRegion_split' (b := sp1 + 8#64) (b' := sp1 + 16#64) (n := 8) (k := 64) rfl (by bv_lin) (by decide),
      memRegion_eight sp1, memRegion_eight (sp1 + 8#64)]
  simp only [sepConj_assoc]; rfl

private theorem enomem_repack_stackFrame_fine (s0 : State) :
    (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
     (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
     memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
     stackFrameAt (s0.sp - 80#64) 624) ⊢ stackFrame s0 704 := by
  rw [stackFrame_704_split_prologue_fine s0]
  exact sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _) (Entails.refl _))

private theorem memRegion_64_unpack_fine (sp1 : BitVec 64) :
    memRegion (sp1 + 16#64) 64 =
      ((∃∗ v19 : BitVec 64, (sp1 + 16#64) ↦₆₄ v19) ∗
       (∃∗ v20 : BitVec 64, (sp1 + 24#64) ↦₆₄ v20) ∗
       (∃∗ v21 : BitVec 64, (sp1 + 32#64) ↦₆₄ v21) ∗
       (∃∗ v22 : BitVec 64, (sp1 + 40#64) ↦₆₄ v22) ∗
       (∃∗ v23 : BitVec 64, (sp1 + 48#64) ↦₆₄ v23) ∗
       (∃∗ v24 : BitVec 64, (sp1 + 56#64) ↦₆₄ v24) ∗
       (∃∗ v25 : BitVec 64, (sp1 + 64#64) ↦₆₄ v25) ∗
       (∃∗ vPad : BitVec 64, (sp1 + 72#64) ↦₆₄ vPad)) := by
  rw [memRegion_split' (b := sp1 + 16#64) (b' := sp1 + 24#64) (n := 8) (k := 56) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 24#64) (b' := sp1 + 32#64) (n := 8) (k := 48) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 32#64) (b' := sp1 + 40#64) (n := 8) (k := 40) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 40#64) (b' := sp1 + 48#64) (n := 8) (k := 32) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 48#64) (b' := sp1 + 56#64) (n := 8) (k := 24) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 56#64) (b' := sp1 + 64#64) (n := 8) (k := 16) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 64#64) (b' := sp1 + 72#64) (n := 8) (k := 8) rfl (by bv_lin) (by decide),
      memRegion_eight (sp1 + 16#64), memRegion_eight (sp1 + 24#64),
      memRegion_eight (sp1 + 32#64), memRegion_eight (sp1 + 40#64),
      memRegion_eight (sp1 + 48#64), memRegion_eight (sp1 + 56#64),
      memRegion_eight (sp1 + 64#64), memRegion_eight (sp1 + 72#64)]

private structure AllGprCSPreservedFine (s0 s : State) : Prop where
  x19 : s.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5)
  x20 : s.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5)
  x21 : s.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5)
  x22 : s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5)
  x23 : s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5)
  x24 : s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5)
  x25 : s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5)
  x26 : s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  x27 : s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  x28 : s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5)
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0

private theorem allGprCS_of_calleeSaved_fine {s0 s1 s2 : State}
    (h1 : AllGprCSPreservedFine s0 s1) (h2 : CalleeSavedPreserved s1 s2) :
    AllGprCSPreservedFine s0 s2 := by
  obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, _, cv⟩ := h2
  exact ⟨c19.trans h1.x19, c20.trans h1.x20, c21.trans h1.x21, c22.trans h1.x22,
    c23.trans h1.x23, c24.trans h1.x24, c25.trans h1.x25, c26.trans h1.x26,
    c27.trans h1.x27, c28.trans h1.x28, cv.trans h1.vregs⟩

set_option maxHeartbeats 400000 in
private theorem mallocImpl_enomem_branch_fine [MallocngMultiPlacement]
    {b9 : BitVec 64} (hb : BlkBase 9 b9)
    {γ : GhostName} {tp brkStart : BitVec 64} {b : FineBudget}
    {ivs0 : List (BitVec 64 × Nat)} {s0 s : State}
    {oom : State → SepProp}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hpc : s.pc = b9 + miOff_call_errno) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hbrk : s.brk = s0.brk) (hperm : s.mem.perm = s0.mem.perm)
    (hProc : MallocngProcPreserved s0 s) (hcs : AllGprCSPreservedFine s0 s) :
    SepWP (blkPC_b09.rebase b9 (fun _ => none)) (s0.readReg64 (.gpr 30#5)) s
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
       (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
       memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
       stackFrameAt (s0.sp - 80#64) 624 ∗
       FineHeapImpl γ maddrs tp brkStart s0.brk b ivs0)
      (fun sf P_f =>
        (P_f ⊢
          ⌜MallocngProcPreserved s0 sf ∧
           MallocngMappedDelta 16 (fineStepReserve (.alloc 0) b) s0.mem sf.mem⌝ ∗
          stackFrame s0 704 ∗
          ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          FinePostEnv γ maddrs tp brkStart b ivs0 s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      oom := by
  have hUnpack :
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
       (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
       memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
       stackFrameAt (s0.sp - 80#64) 624 ∗
       FineHeapImpl γ maddrs tp brkStart s0.brk b ivs0) =
      (∃∗ errnoVal : BitVec 32,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗
         FineCoreImpl γ maddrs brkStart s0.brk b ivs0 ∗
         ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) := by
    rw [FineHeapImpl_eq]
    unfold MallocngRuntime
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepExists_congr fun errnoVal => ?_
    generalize ((tp - 0xa4#64) ↦₃₂ errnoVal) = pEr,
      ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
      ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48,
      FineCoreImpl γ maddrs brkStart s0.brk b ivs0 = pCr,
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) = p29,
      (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) = p30,
      memRegion ((s0.sp - 80#64) + 16#64) 64 = pMid,
      stackFrameAt (s0.sp - 80#64) 624 = pSf
    ac_rfl
  rw [hUnpack]
  apply SepWP.exists_elim; intro errnoVal
  let errRest :=
    ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
    (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
    memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
    stackFrameAt (s0.sp - 80#64) 624 ∗
    FineCoreImpl γ maddrs brkStart s0.brk b ivs0 ∗
    ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
  change SepWP _ _ _ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ errRest) _ _
  have hSpAl : s.spAligned = true := by
    dsimp [State.spAligned]; rw [hsp]; exact sp_sub_80_aligned hsp_align
  dsimp only [miOff_call_errno] at hpc
  wp_step
  have herr := placed_errnoLocation_perm_ok (P := blkPC_b09.rebase b9 (fun _ => none))
  let errnoFrame := ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ errRest
  have hPreErr : (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ errRest) ⊢
      (emp ∗ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem⌝) ∗ errnoFrame := by
    rw [emp_sepConj]
    exact Entails.pure_right hcl (Entails.refl _)
  apply SepWP.weaken_pre hPreErr
  refine SepWP.call_subroutine_frame (F := errnoFrame) (x := ()) (ret_pc := b9 + miOff_after_errno)
    herr (by subst hb; simp [arm64_norm]; bv_arith)
    (by simp [arm64_norm, hrun])
    (by simpa [State.spAligned, arm64_norm] using hSpAl)
    (by dsimp only [miOff_after_errno]; simp [arm64_norm])
    (fun R' hm => by simpa [withCL, sepConj_assoc, arm64_norm] using hm)
    (fun R' sf _ hp => not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => not_satisfies_false_sepConj he)
    ?_
    (fun R' sf _ ho => False.elim (not_satisfies_false_sepConj ho))
  intro s_e hpc_e hrun_e hsp_e hcs_e
  dsimp only [withCL]
  rw [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hProc_e, hbrk_e, hperm_e, hx0_e⟩
  apply SepWP.pure_elim; intro _hcl_e
  have hsp_se : s_e.sp = s0.sp - 80#64 := by simpa [arm64_norm] using hsp_e.trans hsp
  have hbrk_se : s_e.brk = s0.brk := by simpa [arm64_norm] using hbrk_e.trans hbrk
  have hperm_se : s_e.mem.perm = s0.mem.perm := by simpa [arm64_norm] using hperm_e.trans hperm
  have hProc_se : MallocngProcPreserved s0 s_e :=
    procPres_trans (procPres_setPC (procPres_writeReg64 hProc)) hProc_e
  have hcs_bl : AllGprCSPreservedFine s0 ((s.writeReg64 (.gpr 30#5) (b9 + 460#64)).setPC
      (b9 + 456#64 + (mbase 0 - mbase 9 - 456#64))) :=
    ⟨by simpa using hcs.x19, by simpa using hcs.x20, by simpa using hcs.x21,
     by simpa using hcs.x22, by simpa using hcs.x23, by simpa using hcs.x24,
     by simpa using hcs.x25, by simpa using hcs.x26, by simpa using hcs.x27,
     by simpa using hcs.x28, by simpa [calleeSavedVRegs] using hcs.vregs⟩
  have hcs_se : AllGprCSPreservedFine s0 s_e := allGprCS_of_calleeSaved_fine hcs_bl hcs_e
  have hx0_tp : s_e.readReg64 (.gpr 0#5) = tp - 0xa4#64 := by
    have htp_s : s.tpidrEl0 = tp := hProc.2.2.1.trans htp0
    simpa [Reg.x0, htp_s] using hx0_e
  clear hx0_e
  dsimp only [errnoFrame, errRest]
  dsimp only [miOff_after_errno] at hpc_e
  wp_steps 3
  wp_str32_perm m_er hm_er
  have hSpAl_se : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := sp_sub_80_aligned hsp_align
  generalize hsp1_eq : s0.sp - 80#64 = sp1 at hsp_se hSpAl_se ⊢
  wp_steps 3
  subst hsp1_eq
  have hSpAdd : (s0.sp - 80#64) + 80#64 = s0.sp := by bv_lin
  apply SepWP.done
  · simp [arm64_norm]
  · simp [arm64_norm, hrun_e]
  · refine ⟨?_, by simp [arm64_norm, hSpAdd], ?_⟩
    · have hPermF : m_er.perm = s0.mem.perm := hm_er.trans hperm_se
      have hDeltaF : MallocngMappedDelta 16 (fineStepReserve (.alloc 0) b) s0.mem m_er :=
        ⟨[], Nat.zero_le _, Nat.zero_le _, fun a ha => Or.inl (hPermF ▸ ha)⟩
      have hNoOrphF : MallocngNoOrphanMappings ivs0 ivs0 s0.mem m_er :=
        mallocngNoOrphanMappings_of_perm_eq rfl hPermF
      refine Entails.pure_right ⟨by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [arm64_norm, hProc_se.1, hProc_se.2.1, hProc_se.2.2.1, hProc_se.2.2.2.1,
            hProc_se.2.2.2.2.1, hProc_se.2.2.2.2.2.1, hProc_se.2.2.2.2.2.2], hDeltaF⟩ ?_
      have hRearr :
          (((tp - 0xa4#64) ↦₃₂ 12#32) ∗
           (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
            stackFrameAt (s0.sp - 80#64) 624 ∗
            FineCoreImpl γ maddrs brkStart s0.brk b ivs0 ∗
            ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) =
          ((((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
            stackFrameAt (s0.sp - 80#64) 624) ∗
           (FineCoreImpl γ maddrs brkStart s0.brk b ivs0 ∗
            (((tp - 0xa4#64) ↦₃₂ 12#32) ∗
             ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)))) := by
        generalize ((tp - 0xa4#64) ↦₃₂ 12#32) = pEr,
          ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
          ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48,
          FineCoreImpl γ maddrs brkStart s0.brk b ivs0 = pCr,
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) = p29,
          (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) = p30,
          memRegion ((s0.sp - 80#64) + 16#64) 64 = pMid,
          stackFrameAt (s0.sp - 80#64) 624 = pSf
        ac_rfl
      rw [hRearr]
      refine sepConj_mono (enomem_repack_stackFrame_fine s0) ?_
      refine Entails.pure_right (by simp [arm64_norm]) ?_
      unfold FinePostEnv FineEnv
      refine Entails.trans ?_ (Entails.sepExists_intro ivs0)
      refine Entails.pure_right hNoOrphF ?_
      refine Entails.pure_right
        ⟨by simp [arm64_norm, hProc_se.2.2.1, htp0],
         by simp [arm64_norm, hProc_se.2.2.2.1, hbrkS0]⟩ ?_
      (try simp only [arm64_norm, hbrk_se])
      rw [FineHeapImpl_eq]
      refine sepConj_mono (Entails.refl _) ?_
      unfold MallocngRuntime
      exact sepConj_mono (Entails.sepExists_intro 12#32) (Entails.refl _)
    · exact ⟨by simpa [arm64_norm] using hcs_se.x19,
        by simpa [arm64_norm] using hcs_se.x20,
        by simpa [arm64_norm] using hcs_se.x21,
        by simpa [arm64_norm] using hcs_se.x22,
        by simpa [arm64_norm] using hcs_se.x23,
        by simpa [arm64_norm] using hcs_se.x24,
        by simpa [arm64_norm] using hcs_se.x25,
        by simpa [arm64_norm] using hcs_se.x26,
        by simpa [arm64_norm] using hcs_se.x27,
        by simpa [arm64_norm] using hcs_se.x28,
        by simp [arm64_norm],
        by simpa [calleeSavedVRegs] using hcs_se.vregs⟩

/-! ## Large `mmap` Branch Adapter and Size Dispatch -/

set_option maxHeartbeats 400000 in
/-- Adapts `placed_mallocImpl_large_raw_ok` (`131051 < req ≤ MallocngMaxAllocSize`) to
    `MallocImplFineRawSuccessPost`. -/
theorem mallocImpl_large_raw_fine_ok [MallocngMultiPlacement]
    {γ : GhostName} {tp brkStart : BitVec 64} {b : FineBudget} {liveCost peakCost : Nat}
    {ivs0 : List (BitVec 64 × Nat)} {alignMap0 : BitVec 64 → Option Nat}
    {req : Nat} {st0 : MallocngSt} {s0 s : State}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s.brk liveCost peakCost st0)
    (hGt : 131051 < req) (hReqMax : req ≤ MallocngMaxAllocSize)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hPerm0 : s.mem.perm = s0.mem.perm)
    (hpc : s.pc = mbase 9 + miOff_large_entry) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s.brk liveCost peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ MallocImplFineRawSuccessPost γ tp brkStart b ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜FineStepOomCond msvc (fineStepReserve (.alloc req) b) s0 sf⌝) := by
  have hGroups0 : st0.groups.length ≤ fineMaxGroups b := groups_fine_length_le hwf0 hInv0
  have hMeta0 : st0.metaAreas.length ≤ fineMaxMetaAreas b := hInv0.metaAreas_le
  have hMetaStep : 1 + (7 + fineMaxGroups b) / 101 ≤ fineMaxMetaAreas b := Nat.le_refl _
  let maxBytes := ((req + 20 + 4095) / 4096) * 4096 + 131072 * fineMaxMetaAreas b
  have hMaxLe : maxBytes ≤ fineStepReserve (.alloc req) b := by
    dsimp only [maxBytes, fineStepReserve, FineStepBound, pageAlignUp, PAGE_SIZE]
    have h1 : (req + 20 + 4095) / 4096 ≤ (req + (max 16 16 - 16) + 8192 + 4095) / 4096 := by
      apply Nat.div_le_div_right; omega
    have := Nat.mul_le_mul_right 4096 h1
    omega
  have hPreFrame :
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s.brk liveCost peakCost st0 ∗
       MallocngRuntime maddrs tp) =
      ((MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s.brk liveCost peakCost st0 ∗
        MallocngRuntime maddrs tp) ∗
       ghostMapAuth (fineAlignGam γ) alignMap0) := by
    generalize MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      stackFrameAt (s0.sp - 80#64) 624 = pSf,
      MallocngRoTablesA maddrs = pRo,
      ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
      MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s.brk liveCost peakCost st0 = pCr,
      MallocngRuntime maddrs tp = pRt
    ac_rfl
  rw [hPreFrame]
  apply SepWP.of_reaches_pc; intro R hm
  rw [sepConj_assoc] at hm
  refine reaches_pc_mono
    (SepWP.to_reaches_pc
      (placed_mallocImpl_large_raw_ok (γ := fineBaseGam γ)
        hcl hwf0 hGroups0 hMeta0 hMetaStep hGt hReqMax
        htp0 hbrkS0 hPerm0 hpc hrun hsp hsp_align hProc hcsHi hx20) hm)
    ?_
    (fun sf _hOom ho => by
      have ho' := Satisfies.drop_mid ho
      rw [satisfies_pure_sepConj] at ho' ⊢
      exact ⟨fineStepOomCond_of_placed (Nat.le_refl 16) hMaxLe ho'.1, ho'.2⟩)
  rintro sf _hpc_f _hrun_f ⟨P_inner, hmf, st', cg, p, live', peak',
    hsp_f, hcs_f, hProc_f, hx0_f, _hcl_f, hAcc_f, hNoOrph_f, hEntInner,
    hGroups', ⟨st1_w, hGroups1, hSame1⟩, hCgSc, _hCgParent, _hCgCap, _hCgLast, _hCgMapPos,
    hCgMapEq, hCgSlots, hFresh0, hLiveMap', hMetaLe', hBlkWf, _hpNe0, _hpAlign, _hp48⟩
  refine ⟨P_inner ∗ ghostMapAuth (fineAlignGam γ) alignMap0, by rw [sepConj_assoc]; exact hmf,
    Entails.trans (sepConj_mono_left hEntInner) ?_, hsp_f, hcs_f⟩
  have hDelta_f : MallocngMappedDelta 16 (fineStepReserve (.alloc req) b) s0.mem sf.mem :=
    MallocngMappedDelta.mono (Nat.le_refl 16) hMaxLe hAcc_f.2
  have hIvs0Eq : ivs0 = dynamicRootRegions st0 := hInv0.ivs_eq rfl
  have hNoOrph' : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem :=
    hIvs0Eq ▸ hNoOrph_f
  unfold MallocImplFineRawSuccessPost
  refine Entails.pure_right ⟨hProc_f, hDelta_f⟩ ?_
  have hPullWf :
      (MallocngRoTablesA maddrs ∗
        MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st' ∗
        MallocngRuntime maddrs tp ∗ stackFrame s0 704 ∗
        (p ↦ₛ List.replicate req 0#8) ∗ MallocngBlockToken (fineBaseGam γ) p req) ∗
       ghostMapAuth (fineAlignGam γ) alignMap0 ⊢
      ⌜MallocngWF maddrs.base brkStart sf.brk live' peak' st'⌝ ∗
      (stackFrame s0 704 ∗
       (MallocngRoTablesA maddrs ∗
        ghostMapAuth (fineAlignGam γ) alignMap0 ∗
        MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st' ∗
        MallocngRuntime maddrs tp ∗
        (p ↦ₛ List.replicate req 0#8) ∗
        MallocngBlockToken (fineBaseGam γ) p req)) := by
    have hDup :
        MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st' ⊢
          ⌜MallocngWF maddrs.base brkStart sf.brk live' peak' st'⌝ ∗
          MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st' := by
      dsimp only [MallocngCoreStA, MallocngCoreStInflightA]
      apply Entails.pure_left; intro hwf'
      exact Entails.pure_right hwf' (Entails.pure_right hwf' (Entails.refl _))
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hDup))) ?_
    generalize ⌜MallocngWF maddrs.base brkStart sf.brk live' peak' st'⌝ = pWf,
      MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st' = pCr,
      MallocngRoTablesA maddrs = pRo,
      MallocngRuntime maddrs tp = pRt,
      stackFrame s0 704 = pSf,
      (p ↦ₛ List.replicate req 0#8) = pBs,
      MallocngBlockToken (fineBaseGam γ) p req = pTok,
      ghostMapAuth (fineAlignGam γ) alignMap0 = pGa
    exact Entails.of_eq (by ac_rfl)
  refine Entails.trans hPullWf ?_
  apply Entails.pure_left; intro hwf'
  unfold MallocImplFineRawSuccessBody
  refine sepConj_mono_right ?_
  let bCoarse := synthCoarseBudget live' peak' st'
  refine Entails.trans ?_ (Entails.sepExists_intro p)
  refine Entails.trans ?_ (Entails.sepExists_intro (List.replicate req 0#8))
  refine Entails.trans ?_ (Entails.sepExists_intro st0)
  refine Entails.trans ?_ (Entails.sepExists_intro alignMap0)
  refine Entails.trans ?_ (Entails.sepExists_intro st')
  refine Entails.trans ?_ (Entails.sepExists_intro cg)
  refine Entails.trans ?_ (Entails.sepExists_intro 0)
  refine Entails.trans ?_ (Entails.sepExists_intro bCoarse)
  have hCgMem : cg ∈ st'.groups := by simp [hGroups']
  have hIdx0 : 0 < cg.slots.length := by simp [hCgSlots]
  have hSlot0 : cg.slots[0]'hIdx0 = .liveUser p req (max req MallocngMinBlockCost) := by
    simp [hCgSlots]
  have hPOffLe : p.toNat - (cg.slotStart 0).toNat ≤ 255 * 16 := by
    have hgw := hwf'.groups_wf cg hCgMem
    have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 hIdx0
    rw [hSlot0] at hsw
    dsimp only [SlotWf] at hsw
    have hOff := hsw.2.2.2.2.2.2.2.2.1.1
    omega
  have hCgMap4115 : cg.maplen * 4096 ≤ req + 4115 := by
    rw [hCgMapEq]
    have := Nat.div_mul_le_self (req + 20 + 4095) 4096
    omega
  have hNotSmall : ¬ req ≤ MmapThresholdReq := by
    dsimp only [MmapThresholdReq]; omega
  have hRawRel : MallocImplFineRawRel maddrs.base brkStart b ivs0 alignMap0 st0 st' cg 0 req p := by
    refine ⟨hInv0, hFresh0, hLiveMap', hMetaLe', hCgMem, ⟨hIdx0, hSlot0⟩,
      hPOffLe, fun h => by rw [hCgSc] at h; omega, fun _ => hCgMap4115, ?_⟩
    rw [dite_eq_right hNotSmall]
    exact ⟨st1_w, rfl, hSame1, hGroups1, hCgSc, hCgSlots, hCgMap4115⟩
  have hGrp' : Cost.GroupsGrpBound 128 st'.groups := by
    rw [hGroups']
    exact (groupsGrpBound_128_of_geom hInv0.groups_geom).cons (fun _ hs => by rw [hCgSc] at hs; omega)
  exact Entails.pure_right
    ⟨hx0_f, hProc_f.2.2.1.trans htp0, hProc_f.2.2.2.1.trans hbrkS0,
     hBlkWf, List.length_replicate, hNoOrph', hwf', synthCoarseBudget_countIvsWF st' hGrp',
     hRawRel, fun _ => rfl⟩
    (Entails.refl _)

set_option maxHeartbeats 400000 in
private theorem mallocImpl_save_cs_dispatch_fine [MallocngMultiPlacement]
    {b9 : BitVec 64} (hb : BlkBase 9 b9)
    {γ : GhostName} {tp brkStart : BitVec 64} {b : FineBudget} {liveCost peakCost : Nat}
    {ivs0 : List (BitVec 64 × Nat)} {alignMap0 : BitVec 64 → Option Nat}
    {req : Nat} {st0 : MallocngSt} {s0 s1 : State}
    (hcl1 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem)
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s1.brk liveCost peakCost st0)
    (hReqMax : req ≤ MallocngMaxAllocSize)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hPerm1 : s1.mem.perm = s0.mem.perm)
    (hpc1 : s1.pc = b9 + miOff_save_cs) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hx0_1 : s1.readReg64 (.gpr 0#5) = BitVec.ofNat 64 req)
    (hProc1 : MallocngProcPreserved s0 s1) (hcs1 : AllGprCSPreservedFine s0 s1) :
    SepWP (blkPC_b09.rebase b9 (fun _ => none)) (s0.readReg64 (.gpr 30#5)) s1
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
       (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
       memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
       stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s1.brk liveCost peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ MallocImplFineRawSuccessPost γ tp brkStart b ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜FineStepOomCond msvc (fineStepReserve (.alloc req) b) s0 sf⌝) := by
  have _ := hb
  have hReq2_64 : req < 2 ^ 64 := by
    have := mallocngMaxAllocSize_eq; omega
  have hSpAl1 : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := sp_sub_80_aligned hsp_align
  generalize hsp1_eq : s0.sp - 80#64 = sp1 at hsp1 hSpAl1 ⊢
  rw [memRegion_64_unpack_fine sp1]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v20
  apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v22
  apply SepWP.exists_elim; intro v23
  apply SepWP.exists_elim; intro v24
  apply SepWP.exists_elim; intro v25
  apply SepWP.exists_elim; intro vPad
  dsimp only [miOff_save_cs] at hpc1
  wp_stp64_cl m2 hm2 hcl1 hcl2
  wp_steps 2
  wp_stp64_cl m3 hm3 hcl2 hcl3
  wp_steps 2
  wp_stp64_cl m4 hm4 hcl3 hcl4
  wp_str64_cl m5 hm5 hcl4 hcl5
  wp_step
  have hPerm5 : m5.perm = s0.mem.perm :=
    hm5.trans (hm4.trans (hm3.trans (hm2.trans hPerm1)))
  refine SepWP.weaken_pre (?_ : _ ⊢
      MallocImplSavedRegs s0 sp1 ∗ stackFrameAt sp1 624 ∗
      MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
      MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s1.brk liveCost peakCost st0 ∗
      MallocngRuntime maddrs tp) ?_
  · generalize stackFrameAt sp1 624 = pSf,
      MallocngRoTablesA maddrs = pRo,
      ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
      MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s1.brk liveCost peakCost st0 = pCr,
      MallocngRuntime maddrs tp = pRt
    rw [hcs1.x19, hcs1.x20, hcs1.x21, hcs1.x22, hcs1.x23, hcs1.x24, hcs1.x25]
    unfold MallocImplSavedRegs
    simp only [sepConj_assoc]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro _))))))))))
  subst hsp1_eq
  have hb_eq : mbase 9 = b9 := hb.symm
  subst hb_eq
  wp_if hHiLarge
  · have hGt131 : 131051 < req := by
      rw [ult_ofNat_iff_fine (by decide) hReq2_64] at hHiLarge
      exact hHiLarge
    rw [← mallocngBlockProg_eq_b09]
    exact mallocImpl_large_raw_fine_ok hcl5 hInv0 hwf0 hGt131 hReqMax
      htp0 hbrkS0 hPerm5 (by dsimp only [miOff_large_entry]; rfl)
      (by simp [arm64_norm, hrun1]) (by simpa [arm64_norm] using hsp1) hsp_align
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [arm64_norm, hProc1.1, hProc1.2.1, hProc1.2.2.1, hProc1.2.2.2.1,
              hProc1.2.2.2.2.1, hProc1.2.2.2.2.2.1, hProc1.2.2.2.2.2.2])
      ⟨by simpa [arm64_norm] using hcs1.x26, by simpa [arm64_norm] using hcs1.x27,
       by simpa [arm64_norm] using hcs1.x28, by simpa [calleeSavedVRegs] using hcs1.vregs⟩
      (by simp only [arm64_norm]; try exact hx0_1)
  · have hLe131 : req ≤ 131051 := by
      have hF : ¬ 131051 < req := fun hLt =>
        hHiLarge ((ult_ofNat_iff_fine (by decide) hReq2_64).mpr hLt)
      omega
    rw [← mallocngBlockProg_eq_b09]
    let bud0 : MallocngBudget := synthCoarseBudget liveCost peakCost st0
    exact mallocImpl_small_med_raw_fine_ok (bud := bud0) hcl5 hInv0 hwf0 hLe131
      htp0 hbrkS0 hPerm5 (by dsimp only [miOff_small_entry]; rfl)
      (by simp [arm64_norm, hrun1]) (by simpa [arm64_norm] using hsp1) hsp_align
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [arm64_norm, hProc1.1, hProc1.2.1, hProc1.2.2.1, hProc1.2.2.2.1,
              hProc1.2.2.2.2.1, hProc1.2.2.2.2.2.1, hProc1.2.2.2.2.2.2])
      ⟨by simpa [arm64_norm] using hcs1.x26, by simpa [arm64_norm] using hcs1.x27,
       by simpa [arm64_norm] using hcs1.x28, by simpa [calleeSavedVRegs] using hcs1.vregs⟩
      (by simp only [arm64_norm]; try exact hx0_1)

/-! ## Raw `__libc_malloc_impl` Contract -/

set_option maxHeartbeats 400000 in
theorem placed_libcMallocImpl_raw_fine_ok : LibcMallocImplFineRawStmt := by
  intro _ γ tp brkStart b ivs0 req
  dsimp only [libcMallocImplFineRawSpec]
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre hspAl0
  have hsp_align : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hspAl0
  have hpre1 : s0.mem ⊨
      ⌜s0.mem = m0 ∧ (s0.readReg64 .x0).toNat = req ∧
       s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
      ((stackFrame s0 704 ∗ FineHeapImpl γ maddrs tp brkStart s0.brk b ivs0) ∗ R) := by
    refine Satisfies.mono ?_ hpre
    unfold FineEnv
    change (⌜s0.mem = m0⌝ ∗ (⌜(s0.readReg64 .x0).toNat = req⌝ ∗ stackFrame s0 704 ∗
        (⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
         FineHeapImpl γ maddrs tp brkStart s0.brk b ivs0))) ∗ R ⊢ _
    refine Entails.trans (Entails.of_eq (by ac_rfl) :
      _ ⊢ ⌜s0.mem = m0⌝ ∗ ⌜(s0.readReg64 .x0).toNat = req⌝ ∗
          ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
          ((stackFrame s0 704 ∗ FineHeapImpl γ maddrs tp brkStart s0.brk b ivs0) ∗ R)) ?_
    apply Entails.pure_left; intro hm0
    apply Entails.pure_left; intro hx0
    apply Entails.pure_left; rintro ⟨htp0, hbrkS0⟩
    exact Entails.pure_right ⟨hm0, hx0, htp0, hbrkS0⟩ (Entails.refl _)
  rw [satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨hm0, hx0_nat, htp0, hbrkS0⟩, hpre_sp⟩ := hpre1
  have hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem := hm0 ▸ hcl0
  have hReq2_64 : req < 2 ^ 64 := hx0_nat ▸ (s0.readReg64 .x0).isLt
  have hx0_bv : s0.readReg64 (.gpr 0#5) = BitVec.ofNat 64 req := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hReq2_64]
    simpa [Reg.x0] using hx0_nat
  refine ⟨stackFrame s0 704 ∗ FineHeapImpl γ maddrs tp brkStart s0.brk b ivs0, hpre_sp, ?_⟩
  rw [stackFrame_704_split_prologue_fine s0]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v29
  apply SepWP.exists_elim; intro v30
  rw [mallocngBlockProg_eq_b09]
  have hpc0 : s0.pc = mbase 9 + 0#64 := by rw [hpc, BitVec.add_zero]
  generalize hb_eq : mbase 9 = b9 at hpc0 ⊢
  have hb : BlkBase 9 b9 := hb_eq.symm
  wp_stp64_cl m1 hm1 hcl hcl1
  wp_steps 5
  have hMaxVal : (9223372036854771710#64 : BitVec 64) = BitVec.ofNat 64 MallocngMaxAllocSize := by
    rw [mallocngMaxAllocSize_eq]
  have hMax2_64 : MallocngMaxAllocSize < 2 ^ 64 := by
    rw [mallocngMaxAllocSize_eq]; decide
  wp_if hHiMax
  · have hGtMax : MallocngMaxAllocSize < req := by
      rw [hMaxVal, ult_ofNat_iff_fine hMax2_64 hReq2_64] at hHiMax
      exact hHiMax
    have hNotLe : ¬ req ≤ MallocngMaxAllocSize := by omega
    have hOkFalse : decide (req ≤ MallocngMaxAllocSize) = false := decide_eq_false hNotLe
    conv => arg 6; ext sf; rw [hOkFalse]; dsimp only [Bool.false_eq_true, ↓reduceIte]
    refine SepWP.mono
      (mallocImpl_enomem_branch_fine
        (oom := fun sf => ⌜FineStepOomCond msvc (fineStepReserve (.alloc 0) b) s0 sf⌝)
        hb hcl1 htp0 hbrkS0
        (by dsimp only [miOff_call_errno]; rfl)
        (by simp [arm64_norm, hrun])
        (by simp [arm64_norm])
        hsp_align
        (by simp [arm64_norm])
        (by simpa [arm64_norm] using hm1)
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩) ?_
    rintro sf P_f _ _ ⟨hEnt, hsp_f, hcs_f⟩
    refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, hsp_f, hcs_f⟩
    simp only [hNotLe, ↓reduceIte]
    exact hEnt
  · have hReqMax : req ≤ MallocngMaxAllocSize := by
      have hF : ¬ MallocngMaxAllocSize < req := fun hLt =>
        hHiMax (by rw [hMaxVal]; exact (ult_ofNat_iff_fine hMax2_64 hReq2_64).mpr hLt)
      omega
    have hOkTrue : decide (req ≤ MallocngMaxAllocSize) = true := decide_eq_true hReqMax
    have hHeapUnpack :
        (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗
         FineHeapImpl γ maddrs tp brkStart s0.brk b ivs0) ⊢
        (∃∗ st0 : MallocngSt,
         ∃∗ alignMap0 : BitVec 64 → Option Nat,
         ∃∗ liveCost : Nat,
         ∃∗ peakCost : Nat,
           ⌜MallocngFineInv 0 b ivs0 alignMap0 st0⌝ ∗
           ⌜MallocngWF maddrs.base brkStart s0.brk liveCost peakCost st0⌝ ∗
           (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
            stackFrameAt (s0.sp - 80#64) 624 ∗
            MallocngRoTablesA maddrs ∗
            ghostMapAuth (fineAlignGam γ) alignMap0 ∗
            MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s0.brk liveCost peakCost st0 ∗
            MallocngRuntime maddrs tp)) := by
      rw [FineHeapImpl_eq, FineCoreImpl_eq]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro st0
      apply Entails.sepExists_elim; intro alignMap0
      apply Entails.sepExists_elim; intro liveCost
      apply Entails.sepExists_elim; intro peakCost
      refine Entails.trans ?_ (Entails.sepExists_intro st0)
      refine Entails.trans ?_ (Entails.sepExists_intro alignMap0)
      refine Entails.trans ?_ (Entails.sepExists_intro liveCost)
      refine Entails.trans ?_ (Entails.sepExists_intro peakCost)
      dsimp only [FineCoreStInflightA]
      have hDupWf :
          MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s0.brk liveCost peakCost st0 ⊢
            ⌜MallocngWF maddrs.base brkStart s0.brk liveCost peakCost st0⌝ ∗
            MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s0.brk liveCost peakCost st0 := by
        dsimp only [MallocngCoreStInflightA]
        apply Entails.pure_left; intro hwf0
        exact Entails.pure_right hwf0 (Entails.pure_right hwf0 (Entails.refl _))
      have hBringFront :
          (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
           (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
           memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
           stackFrameAt (s0.sp - 80#64) 624 ∗
           ((MallocngRoTablesA maddrs ∗
             (⌜MallocngFineInv 0 b ivs0 alignMap0 st0⌝ ∗
              ghostMapAuth (fineAlignGam γ) alignMap0 ∗
              MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s0.brk liveCost peakCost st0)) ∗
            MallocngRuntime maddrs tp)) =
          (MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s0.brk liveCost peakCost st0 ∗
           (⌜MallocngFineInv 0 b ivs0 alignMap0 st0⌝ ∗
            (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
             (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
             memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
             stackFrameAt (s0.sp - 80#64) 624 ∗
             MallocngRoTablesA maddrs ∗
             ghostMapAuth (fineAlignGam γ) alignMap0 ∗
             MallocngRuntime maddrs tp))) := by
        generalize ⌜MallocngFineInv 0 b ivs0 alignMap0 st0⌝ = pInv,
          MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s0.brk liveCost peakCost st0 = pBody,
          ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) = p29,
          (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) = p30,
          memRegion ((s0.sp - 80#64) + 16#64) 64 = pMid,
          stackFrameAt (s0.sp - 80#64) 624 = pSf,
          MallocngRoTablesA maddrs = pRo,
          MallocngRuntime maddrs tp = pRt
        ac_rfl
      rw [hBringFront]
      refine Entails.trans (sepConj_mono_left hDupWf) ?_
      generalize ⌜MallocngFineInv 0 b ivs0 alignMap0 st0⌝ = pInv,
        ⌜MallocngWF maddrs.base brkStart s0.brk liveCost peakCost st0⌝ = pWf,
        MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s0.brk liveCost peakCost st0 = pBody,
        ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) = p29,
        (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) = p30,
        memRegion ((s0.sp - 80#64) + 16#64) 64 = pMid,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocngRoTablesA maddrs = pRo,
        MallocngRuntime maddrs tp = pRt
      exact Entails.of_eq (by ac_rfl)
    apply SepWP.weaken_pre hHeapUnpack
    apply SepWP.exists_elim; intro st0
    apply SepWP.exists_elim; intro alignMap0
    apply SepWP.exists_elim; intro liveCost
    apply SepWP.exists_elim; intro peakCost
    apply SepWP.pure_elim; intro hInv0
    apply SepWP.pure_elim; intro hwf0
    conv => arg 6; ext sf; rw [hOkTrue]; dsimp only [↓reduceIte]
    refine SepWP.mono
      (mallocImpl_save_cs_dispatch_fine hb hcl1 hInv0
        (by simpa [arm64_norm] using hwf0) hReqMax htp0 hbrkS0
        (by simpa [arm64_norm] using hm1)
        (by dsimp only [miOff_save_cs]; rfl)
        (by simp [arm64_norm, hrun])
        (by simp [arm64_norm])
        hsp_align
        (by simpa [arm64_norm] using hx0_bv)
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩) ?_
    rintro sf P_f _ _ ⟨hEnt, hsp_f, hcs_f⟩
    refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, hsp_f, hcs_f⟩
    simp only [hReqMax, ↓reduceIte]
    unfold MallocImplFineRawSuccessPost MallocImplFineRawSuccessBody at hEnt
    simpa [sepConj_assoc] using hEnt

/-! ## `MallocImplFineRawRel` Commits and Committed `__libc_malloc_impl` -/

/-- Pure commit of `MallocImplFineRawRel` under `FineBudget.stepAlloc req b` (`align = 16`). -/
theorem commit_mallocImplFineRawRel_alloc
    {base brkStart brk' : BitVec 64} {live' peak' : Nat}
    {b : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap0 : BitVec 64 → Option Nat} {st0 st' : MallocngSt}
    {g' : GroupDesc} {idx req : Nat} {p : BitVec 64}
    (hwf' : MallocngWF base brkStart brk' live' peak' st')
    (hRaw : MallocImplFineRawRel base brkStart b ivs0 alignMap0 st0 st' g' idx req p) :
    alignMap0 p = none ∧
    MallocngFineInv 0 (FineBudget.stepAlloc req b) (dynamicRootRegions st')
      (fun k => if k = p then some 16 else alignMap0 k) st' := by
  obtain ⟨hInv0, hFresh0, hLiveMap', hMetaLe, _hg'Mem, _hSlot, _hOff, _hSc24, _hSc63, hBranch⟩ := hRaw
  have hAnone : alignMap0 p = none := by
    cases hAl : alignMap0 p with
    | none => rfl
    | some al =>
      obtain ⟨_, n, hL⟩ := hInv0.alignMap_wf.1 p al hAl
      rw [hFresh0] at hL; cases hL
  refine ⟨hAnone, ?_⟩
  have hMetaLe' : st'.metaAreas.length ≤ fineMaxMetaAreas (FineBudget.stepAligned 16 req b) :=
    Nat.le_trans hMetaLe (fineMaxMetaAreas_mono (.alloc req) b)
  change MallocngFineInv 0 (FineBudget.stepAligned 16 req b) (dynamicRootRegions st')
    (fun k => if k = p then some (max 16 16) else alignMap0 k) st'
  by_cases hSmall : req ≤ MmapThresholdReq
  · rw [dite_eq_left hSmall] at hBranch
    obtain ⟨sc, pk, pkSC, pkSB, st1, g1, brk1, live1, peak1,
      hSc48, hScAlt, hPk, hPres, hwf1, hg1Mem, hg1Sc, ⟨hIdx1, hClaimed⟩,
      hg1Same, hg'Slots, hGroups'⟩ := hBranch
    exact commit_claimed_slab_slot_aligned hSc48 (by simpa using hSmall) (by simpa using hScAlt)
      hFresh0 hInv0 hPk hPres hwf1 hwf' hg1Mem hg1Sc hIdx1 hClaimed hg1Same hg'Slots hGroups'
      (fun k => by change st'.liveMap.req k = _; rw [hLiveMap', MallocngLiveMap.insert_req]) hMetaLe'
  · rw [dite_eq_right hSmall] at hBranch
    obtain ⟨st1, _hIdx0, hSame1, hGroups', hCgSc, hCgSlots, hCgMap⟩ := hBranch
    exact commit_mmap63_group_aligned (by simpa using hSmall) hFresh0 hInv0 hSame1 hGroups'
      hCgSc hCgSlots (by omega) (by unfold declCost63; omega)
      (fun k => by change st'.liveMap.req k = _; rw [hLiveMap', MallocngLiveMap.insert_req]) hMetaLe'

/-- Pure commit of `MallocImplFineRawRel` under `FineBudget.stepReallocAdd align req b`
    (for `realloc` Stage 4 out-of-place `malloc(req)`). -/
theorem commit_mallocImplFineRawRel_reallocAdd
    {base brkStart brk' : BitVec 64} {live' peak' : Nat}
    {b : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap0 : BitVec 64 → Option Nat} {st0 st' : MallocngSt}
    {g' : GroupDesc} {idx align req : Nat} {p : BitVec 64}
    (hwf' : MallocngWF base brkStart brk' live' peak' st')
    (hRaw : MallocImplFineRawRel base brkStart b ivs0 alignMap0 st0 st' g' idx req p) :
    alignMap0 p = none ∧
    MallocngFineInv 0 (FineBudget.stepReallocAdd align req b) (dynamicRootRegions st')
      (fun k => if k = p then some (max align 16) else alignMap0 k) st' := by
  obtain ⟨hInv0, hFresh0, hLiveMap', hMetaLe, _hg'Mem, _hSlot, _hOff, _hSc24, _hSc63, hBranch⟩ := hRaw
  have hAnone : alignMap0 p = none := by
    cases hAl : alignMap0 p with
    | none => rfl
    | some al =>
      obtain ⟨_, n, hL⟩ := hInv0.alignMap_wf.1 p al hAl
      rw [hFresh0] at hL; cases hL
  refine ⟨hAnone, ?_⟩
  have hStepAddMono : fineMaxMetaAreas b ≤ fineMaxMetaAreas (FineBudget.stepReallocAdd align req b) := by
    have hMono := fineMaxMetaAreas_mono (.realloc align 0 req) b
    have hEqFree : fineMaxMetaAreas (FineBudget.step (.realloc align 0 req) b) =
        fineMaxMetaAreas (FineBudget.stepReallocAdd align req b) := by
      have hNot63 : ¬ Guaranteed63Threshold ≤ 0 := by decide
      simp only [FineBudget.step, FineBudget.stepRealloc, FineBudget.stepFree, hNot63, ↓reduceIte,
        fineMaxMetaAreas, fineMaxGroups, finePeak63Count]
      congr 2; congr 1; omega
    rwa [hEqFree] at hMono
  have hMetaLe' : st'.metaAreas.length ≤ fineMaxMetaAreas (FineBudget.stepReallocAdd align req b) :=
    Nat.le_trans hMetaLe hStepAddMono
  by_cases hSmall : req ≤ MmapThresholdReq
  · rw [dite_eq_left hSmall] at hBranch
    obtain ⟨sc, pk, pkSC, pkSB, st1, g1, brk1, live1, peak1,
      hSc48, hScAlt, hPk, hPres, hwf1, hg1Mem, hg1Sc, ⟨hIdx1, hClaimed⟩,
      hg1Same, hg'Slots, hGroups'⟩ := hBranch
    exact commit_claimed_slab_slot_reallocAdd (align := align) hSc48 hSmall hScAlt
      hFresh0 hInv0 hPk hPres hwf1 hwf' hg1Mem hg1Sc hIdx1 hClaimed hg1Same hg'Slots hGroups'
      (fun k => by change st'.liveMap.req k = _; rw [hLiveMap', MallocngLiveMap.insert_req]) hMetaLe'
  · rw [dite_eq_right hSmall] at hBranch
    obtain ⟨st1, _hIdx0, hSame1, hGroups', hCgSc, hCgSlots, hCgMap⟩ := hBranch
    exact commit_mmap63_group_reallocAdd (align := align) hFresh0 hInv0 hSame1 hGroups'
      hCgSc hCgSlots (by omega) (by unfold declCost63; omega)
      (fun k => by change st'.liveMap.req k = _; rw [hLiveMap', MallocngLiveMap.insert_req]) hMetaLe'

private theorem bupd_frame_left_loc {P Q : SepProp} : P ∗ (|==> Q) ⊢ |==> (P ∗ Q) := by
  rw [sepConj_comm]
  exact Entails.trans (bupd_frame_r _ _) (bupd_mono (Entails.of_eq (sepConj_comm _ _)))

theorem placed_libcMallocImpl_fine_ok : LibcMallocImplFineStmt := by
  intro _ γ tp brkStart b ivs0 req
  refine subroutine_ok_mono (placed_libcMallocImpl_raw_fine_ok γ tp brkStart b ivs0 req)
    (fun _ _ _ hp => hp) (fun _ R s0 sf hq => ?_)
  dsimp only [libcMallocImplFineRawSpec, libcMallocImplFineSpec, withCL] at hq ⊢
  by_cases hReq : req ≤ MallocngMaxAllocSize
  · simp only [hReq, ↓reduceIte] at hq ⊢
    suffices hUpd :
        ((⌜MallocngProcPreserved s0 sf ∧
            MallocngMappedDelta 16 (fineStepReserve (.alloc req) b) s0.mem sf.mem⌝ ∗
          stackFrame s0 704 ∗
          ∃∗ p : BitVec 64, ∃∗ bs : List (BitVec 8), ∃∗ st0 : MallocngSt,
          ∃∗ alignMap0 : BitVec 64 → Option Nat, ∃∗ st' : MallocngSt,
          ∃∗ g' : GroupDesc, ∃∗ idx : Nat, ∃∗ bCoarse : MallocngBudget,
            ⌜sf.readReg64 .x0 = p ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
             MallocngBlockWf p req ∧ bs.length = req ∧
             MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
             MallocngWF maddrs.base brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st' ∧
             MallocngCountIvsWF bCoarse (dynamicRootRegions st') st' ∧
             MallocImplFineRawRel maddrs.base brkStart b ivs0 alignMap0 st0 st' g' idx req p ∧
             (g'.isMmapped = true → bs = List.replicate req 0#8)⌝ ∗
            MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
            MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st' ∗
            MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ MallocngBlockToken (fineBaseGam γ) p req) ∗
         ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝) ⊢
        |==> (((⌜MallocngProcPreserved s0 sf ∧
                  MallocngMappedDelta 16 (fineStepReserve (.alloc req) b) s0.mem sf.mem⌝ ∗
                stackFrame s0 704 ∗
                ∃∗ p : BitVec 64, ∃∗ bs : List (BitVec 8), ∃∗ st' : MallocngSt,
                ∃∗ alignMap' : BitVec 64 → Option Nat, ∃∗ live' : Nat, ∃∗ peak' : Nat,
                  ⌜sf.readReg64 .x0 = p ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
                   MallocngBlockWf p req ∧ bs.length = req ∧
                   MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
                   ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
                     g'.slots[idx]'hIdx = .liveUser p req (max req MallocngMinBlockCost) ∧
                     p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
                     (g'.isMmapped = true → bs = List.replicate req 0#8)⌝ ∗
                  MallocngRoTablesA maddrs ∗
                  FineCoreStInflightA 0 γ maddrs brkStart sf.brk (FineBudget.stepAlloc req b)
                    (dynamicRootRegions st') alignMap' live' peak' st' ∗
                  MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ FineBlock γ p req 16) ∗
               ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝)) by
      exact (satisfies_bupd _ sf.mem).mp
        (Satisfies.mono (Entails.trans (sepConj_mono_left hUpd) (bupd_frame_r _ _)) hq)
    refine Entails.trans (sepConj_mono_left ?_) (bupd_frame_r _ _)
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right ?_))
      (Entails.trans (sepConj_mono_right bupd_frame_left_loc) bupd_frame_left_loc)
    apply Entails.sepExists_elim; intro p
    apply Entails.sepExists_elim; intro bs
    apply Entails.sepExists_elim; intro st0
    apply Entails.sepExists_elim; intro alignMap0
    apply Entails.sepExists_elim; intro st'
    apply Entails.sepExists_elim; intro g'
    apply Entails.sepExists_elim; intro idx
    apply Entails.sepExists_elim; intro bCoarse
    apply Entails.pure_left
    rintro ⟨hx0, htp, hbrkS, hBlkWf, hbsLen, hNoOrph, hwf', _hCntIvs, hRawRel, hZeroMm⟩
    obtain ⟨hAnone, hInv'⟩ := commit_mallocImplFineRawRel_alloc hwf' hRawRel
    let alignMap' : BitVec 64 → Option Nat := fun k => if k = p then some 16 else alignMap0 k
    have hAllocGhost := ghostMap_alloc (fineAlignGam γ) alignMap0 p 16 hAnone
    have hFrameGhost :
        MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
          MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st' ∗
          MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ MallocngBlockToken (fineBaseGam γ) p req ⊢
        |==> (MallocngRoTablesA maddrs ∗
              FineCoreStInflightA 0 γ maddrs brkStart sf.brk (FineBudget.stepAlloc req b)
                (dynamicRootRegions st') alignMap' bCoarse.liveCost bCoarse.peakCost st' ∗
              MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ FineBlock γ p req 16) := by
      have hPermIn :
          MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
            MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st' ∗
            MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ MallocngBlockToken (fineBaseGam γ) p req =
          ghostMapAuth (fineAlignGam γ) alignMap0 ∗
            (MallocngRoTablesA maddrs ∗
             MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st' ∗
             MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ MallocngBlockToken (fineBaseGam γ) p req) := by
        ac_rfl
      rw [hPermIn]
      refine Entails.trans (Entails.trans (sepConj_mono_left hAllocGhost) (bupd_frame_r _ _)) (bupd_mono ?_)
      unfold FineCoreStInflightA FineBlock MallocngCoreStA
      rw [pure_sepConj_of_true hInv', pure_sepConj_of_true (Nat.le_refl 16)]
      generalize ghostMapAuth (fineAlignGam γ) alignMap' = pGa,
        ghostMapElem (fineAlignGam γ) p 16 = pGe,
        MallocngRoTablesA maddrs = pRo,
        MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st' = pCr,
        MallocngRuntime maddrs tp = pRt,
        (p ↦ₛ bs) = pBs,
        MallocngBlockToken (fineBaseGam γ) p req = pTok
      exact Entails.of_eq (by ac_rfl)
    refine Entails.trans hFrameGhost (bupd_mono ?_)
    refine Entails.trans ?_ (Entails.sepExists_intro p)
    refine Entails.trans ?_ (Entails.sepExists_intro bs)
    refine Entails.trans ?_ (Entails.sepExists_intro st')
    refine Entails.trans ?_ (Entails.sepExists_intro alignMap')
    refine Entails.trans ?_ (Entails.sepExists_intro bCoarse.liveCost)
    refine Entails.trans ?_ (Entails.sepExists_intro bCoarse.peakCost)
    obtain ⟨hIdx, hSlot⟩ := hRawRel.2.2.2.2.2.1
    exact Entails.pure_right
      ⟨hx0, htp, hbrkS, hBlkWf, hbsLen, hNoOrph,
       g', hRawRel.2.2.2.2.1, idx, hIdx, hSlot, hRawRel.2.2.2.2.2.2.1, hZeroMm⟩
      (Entails.refl _)
  · simp only [hReq, ↓reduceIte] at hq ⊢
    exact hq

/-! ## Placed `default_malloc` / `malloc` -/

private theorem b04_tail_to_b09_fine [MallocngMultiPlacement] {spec : Spec Unit}
    (h9 : subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9) (withCL mmpl spec))
    (hPrePC : ∀ s0 pc', spec.pre () (s0.setPC pc') = spec.pre () s0)
    (hPostPC : ∀ s0 pc' sf, spec.post () (s0.setPC pc') sf = spec.post () s0 sf)
    (hOomPC : ∀ s0 pc' sf, spec.onOom () (s0.setPC pc') sf = spec.onOom () s0 sf)
    (hNoPanic : ∀ s0 sf, spec.onPanic () s0 sf = ⌜False⌝)
    (hNoExit : ∀ code s0 sf, spec.onExit () code s0 sf = ⌜False⌝) :
    subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4) (withCL mmpl spec) := by
  apply subroutine_ok_of_sepWP_init
  intro u R s0 hpc hrun hpre hspAl0
  cases u
  have hpre_cl : s0.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ ∗ (spec.pre () s0 ∗ R) := by
    refine Satisfies.mono ?_ hpre
    dsimp only [withCL]
    rw [sepConj_comm (spec.pre () s0), sepConj_assoc]
    exact Entails.refl _
  rw [satisfies_pure_sepConj] at hpre_cl
  have hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem := hpre_cl.1
  refine ⟨(withCL mmpl spec).pre () s0, hpre, ?_⟩
  rw [mallocngBlockProg_eq_b04]
  have hpc0 : s0.pc = mbase 4 + 0#64 := by rw [hpc, BitVec.add_zero]
  generalize hb_eq : mbase 4 = b4 at hpc0 ⊢
  have hb4 : BlkBase 4 b4 := hb_eq.symm
  have _ := hb4
  wp_step
  subst hb_eq
  have hTarget9 : mbase 4 + (mbase 9 - mbase 4) = mbase 9 := by bv_arith
  rw [hTarget9]
  refine sepWP_of_other_mallocng_block (j := 9) (svc := msvc) (by decide) hcl0
    (fun pc => externAt?_placedProgram_rebase_none _ _ _ _ pc) rfl ?_
  refine SepWP.call_subroutine_frame (F := emp) (x := ()) (ret_pc := s0.readReg64 .lr) h9
    rfl hrun hspAl0 rfl
    (fun R' hm => ?_)
    (fun R' sf _ hp => by
      dsimp only [withCL] at hp
      rw [hNoPanic] at hp
      exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by
      dsimp only [withCL] at he
      rw [hNoExit] at he
      exact not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun R' sf _ ho => ?_)
  · dsimp only [withCL] at hm ⊢
    rw [hPrePC]
    simpa [emp_sepConj] using hm
  · refine SepWP.done hpc_f hrun_f ⟨?_, hsp_f, hcs_f⟩
    intro hm
    dsimp only [withCL] at hm ⊢
    rw [hPostPC] at hm
    simpa [sepConj_emp] using hm
  · dsimp only [withCL] at ho ⊢
    rw [hOomPC] at ho
    simpa [emp_sepConj] using ho

theorem placed_defaultMalloc_fine_ok : DefaultMallocFineStmt := by
  intro _ γ tp brkStart b ivs0 req
  exact b04_tail_to_b09_fine (placed_libcMallocImpl_fine_ok γ tp brkStart b ivs0 req)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)

end LibsignalBinary.Heap.Fine
