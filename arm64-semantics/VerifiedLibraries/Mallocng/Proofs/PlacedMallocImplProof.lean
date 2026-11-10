/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocLargeProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplStage2b
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Placed `__libc_malloc_impl` Proof

Proves `LibcMallocImplPlaced24B2Stmt` (recording size-class bounds for `aligned_alloc`) and the
`InternalPlaced` contracts `LibcMallocImplPlacedTightKStmt`, `LibcMallocImplPlacedTightStmt`, and
`LibcMallocImplPlacedStmt` for block `9` (`__libc_malloc_impl`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

abbrev miOff_save_cs     : BitVec 64 := words_insn_off% mallocImplWords 0xa90153f3#32 0
abbrev miOff_call_errno  : BitVec 64 := reloc_call_off% mallocImplRelocs "___errno_location" 0
abbrev miOff_after_errno : BitVec 64 := words_insn_off% mallocImplWords 0xaa0003e1#32 0

/-- Strengthened `Spec Unit` body for placed `__libc_malloc_impl(req)` (`blk09`) using
    `mallocImplSuccessPost24` when `req <= MallocngMaxAllocSize`. -/
def libcMallocImplPlacedSpec24B2 [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat) : Spec Unit :=
  let ok := decide (req ≤ MallocngMaxAllocSize)
  let bf := mallocngAllocBudget ok req b
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜(s0.readReg64 .x0).toNat = req⌝ ∗
      stackFrame s0 704 ∗
      MallocngEnv mallocngIface γ maddrs tp brkStart b ivs0 s0
    post := fun _ s0 sf =>
      if req ≤ MallocngMaxAllocSize then
        mallocImplSuccessPost24 γ tp brkStart b ivs0 req s0 sf
      else
        ⌜MallocngProcPreserved s0 sf ∧
         MallocngMappedDelta 16 (MallocngTightStepBound 0 b.peakCount) s0.mem sf.mem⌝ ∗
        stackFrame s0 704 ∗
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf
    onOom := fun _ s0 sf => ⌜MallocngTightOomCond msvc (if ok then req else 0) b.peakCount s0 sf⌝
  }

/-- Strengthened placed `__libc_malloc_impl(req)` statement (`blk09`, `704` B stack). -/
def LibcMallocImplPlaced24B2Stmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9)
      (libcMallocImplPlacedSpec24B2 γ tp brkStart b ivs0 req)

private theorem at_bl_target_b09 [MallocngMultiPlacement] {b : BitVec 64}
    (_hb : BlkBase 9 b) (j : Nat) (off : BitVec 64) :
    mbase j = b + off + (mbase j - b - off) := by bv_arith

private theorem ult_ofNat_iff {c req : Nat} (hc : c < 2 ^ 64) (hr : req < 2 ^ 64) :
    ((BitVec.ofNat 64 c).ult (BitVec.ofNat 64 req) = true) ↔ c < req := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hr,
    decide_eq_true_eq]

private theorem stackFrame_704_split_prologue (s0 : State) :
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

private theorem enomem_repack_stackFrame (s0 : State) :
    (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
     (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
     memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
     stackFrameAt (s0.sp - 80#64) 624) ⊢ stackFrame s0 704 := by
  rw [stackFrame_704_split_prologue s0]
  exact sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _) (Entails.refl _))

private theorem memRegion_64_unpack (sp1 : BitVec 64) :
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

private structure AllGprCSPreserved (s0 s : State) : Prop where
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

private theorem allGprCS_of_calleeSaved {s0 s1 s2 : State}
    (h1 : AllGprCSPreserved s0 s1) (h2 : CalleeSavedPreserved s1 s2) :
    AllGprCSPreserved s0 s2 := by
  obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, _, cv⟩ := h2
  exact ⟨c19.trans h1.x19, c20.trans h1.x20, c21.trans h1.x21, c22.trans h1.x22,
    c23.trans h1.x23, c24.trans h1.x24, c25.trans h1.x25, c26.trans h1.x26,
    c27.trans h1.x27, c28.trans h1.x28, cv.trans h1.vregs⟩

set_option maxHeartbeats 400000 in
private theorem mallocImpl_enomem_branch [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget}
    {ivs0 : List (BitVec 64 × Nat)} {s0 s : State}
    {oom : State → SepProp}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hpc : s.pc = b + miOff_call_errno) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hbrk : s.brk = s0.brk) (hperm : s.mem.perm = s0.mem.perm)
    (hProc : MallocngProcPreserved s0 s) (hcs : AllGprCSPreserved s0 s) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (s0.readReg64 (.gpr 30#5)) s
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
       (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
       memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
       stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngHeapImpl γ maddrs tp brkStart s0.brk bud ivs0)
      (fun sf P_f =>
        (P_f ⊢
          ⌜MallocngProcPreserved s0 sf ∧
           MallocngMappedDelta 16 (MallocngTightStepBound 0 bud.peakCount) s0.mem sf.mem⌝ ∗
          stackFrame s0 704 ∗
          ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          MallocngPostEnv mallocngIface γ maddrs tp brkStart bud ivs0 s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      oom := by
  have hUnpack :
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
       (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
       memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
       stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngHeapImpl γ maddrs tp brkStart s0.brk bud ivs0) =
      (∃∗ errnoVal : BitVec 32,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngCoreImpl γ maddrs brkStart s0.brk bud ivs0 ∗
         ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) := by
    rw [MallocngHeapImpl_eq]
    unfold MallocngRuntime
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepExists_congr fun errnoVal => ?_
    generalize ((tp - 0xa4#64) ↦₃₂ errnoVal) = pEr,
      ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
      ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48,
      MallocngCoreImpl γ maddrs brkStart s0.brk bud ivs0 = pCr,
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
    MallocngCoreImpl γ maddrs brkStart s0.brk bud ivs0 ∗
    ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
  change SepWP _ _ _ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ errRest) _ _
  have hSpAl : s.spAligned = true := by
    dsimp [State.spAligned]; rw [hsp]; exact sp_sub_80_aligned hsp_align
  dsimp only [miOff_call_errno] at hpc
  wp_step
  have herr := placed_errnoLocation_perm_ok (P := blkPC_b09.rebase b (fun _ => none))
  rw [at_bl_target_b09 hb 0 miOff_call_errno] at herr
  dsimp only [miOff_call_errno] at herr
  let errnoFrame := ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ errRest
  have hPreErr : (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ errRest) ⊢
      (emp ∗ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem⌝) ∗ errnoFrame := by
    rw [emp_sepConj]
    exact Entails.pure_right hcl (Entails.refl _)
  apply SepWP.weaken_pre hPreErr
  refine SepWP.call_subroutine_frame (F := errnoFrame) (x := ()) (ret_pc := b + miOff_after_errno)
    herr (by subst hb; rfl)
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
  have hcs_bl : AllGprCSPreserved s0 ((s.writeReg64 (.gpr 30#5) (b + 460#64)).setPC
      (b + 456#64 + (mbase 0 - mbase 9 - 456#64))) :=
    ⟨by simpa using hcs.x19, by simpa using hcs.x20, by simpa using hcs.x21,
     by simpa using hcs.x22, by simpa using hcs.x23, by simpa using hcs.x24,
     by simpa using hcs.x25, by simpa using hcs.x26, by simpa using hcs.x27,
     by simpa using hcs.x28, by simpa [calleeSavedVRegs] using hcs.vregs⟩
  have hcs_se : AllGprCSPreserved s0 s_e := allGprCS_of_calleeSaved hcs_bl hcs_e
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
      have hDeltaF : MallocngMappedDelta 16 (MallocngTightStepBound 0 bud.peakCount) s0.mem m_er :=
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
            MallocngCoreImpl γ maddrs brkStart s0.brk bud ivs0 ∗
            ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) =
          ((((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
            stackFrameAt (s0.sp - 80#64) 624) ∗
           (MallocngCoreImpl γ maddrs brkStart s0.brk bud ivs0 ∗
            (((tp - 0xa4#64) ↦₃₂ 12#32) ∗
             ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)))) := by
        generalize ((tp - 0xa4#64) ↦₃₂ 12#32) = pEr,
          ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
          ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48,
          MallocngCoreImpl γ maddrs brkStart s0.brk bud ivs0 = pCr,
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) = p29,
          (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) = p30,
          memRegion ((s0.sp - 80#64) + 16#64) 64 = pMid,
          stackFrameAt (s0.sp - 80#64) 624 = pSf
        ac_rfl
      rw [hRearr]
      refine sepConj_mono (enomem_repack_stackFrame s0) ?_
      refine Entails.pure_right (by simp [arm64_norm]) ?_
      unfold MallocngPostEnv MallocngEnv
      refine Entails.trans ?_ (Entails.sepExists_intro ivs0)
      refine Entails.pure_right hNoOrphF ?_
      refine Entails.pure_right
        ⟨by simp [arm64_norm, hProc_se.2.2.1, htp0],
         by simp [arm64_norm, hProc_se.2.2.2.1, hbrkS0]⟩ ?_
      dsimp only [mallocngIface]
      (try simp only [arm64_norm, hbrk_se])
      rw [MallocngHeapImpl_eq]
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

set_option maxHeartbeats 400000 in
private theorem mallocImpl_save_cs_dispatch [MallocngMultiPlacement]
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt)
    (hMetaInv : MallocngMetaCountInv)
    {b : BitVec 64} (hb : BlkBase 9 b)
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget}
    {ivs0 : List (BitVec 64 × Nat)} {req : Nat}
    {st0 : MallocngSt} {s0 s1 : State}
    (hcl1 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem)
    (hCount0 : MallocngCountIvsWF bud ivs0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s1.brk bud.liveCost bud.peakCost st0)
    (hReqMax : req ≤ MallocngMaxAllocSize)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hPerm1 : s1.mem.perm = s0.mem.perm)
    (hpc1 : s1.pc = b + miOff_save_cs) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hx0_1 : s1.readReg64 (.gpr 0#5) = BitVec.ofNat 64 req)
    (hProc1 : MallocngProcPreserved s0 s1) (hcs1 : AllGprCSPreserved s0 s1) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (s0.readReg64 (.gpr 30#5)) s1
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
       (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
       memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
       stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA 0 γ maddrs brkStart s1.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ mallocImplSuccessPost24 γ tp brkStart bud ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜MallocngTightOomCond msvc req bud.peakCount s0 sf⌝) := by
  have _ := hb
  have hReq2_64 : req < 2 ^ 64 := by
    have := mallocngMaxAllocSize_eq; omega
  have hSpAl1 : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := sp_sub_80_aligned hsp_align
  generalize hsp1_eq : s0.sp - 80#64 = sp1 at hsp1 hSpAl1 ⊢
  rw [memRegion_64_unpack sp1]
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
      MallocngRoTablesA maddrs ∗
      MallocngCoreStInflightA 0 γ maddrs brkStart s1.brk bud.liveCost bud.peakCost st0 ∗
      MallocngRuntime maddrs tp) ?_
  · generalize stackFrameAt sp1 624 = pSf,
      MallocngRoTablesA maddrs = pRo,
      MallocngCoreStInflightA 0 γ maddrs brkStart s1.brk bud.liveCost bud.peakCost st0 = pCr,
      MallocngRuntime maddrs tp = pRt
    have hA24 : (sp1 + 16#64) + 8#64 = sp1 + 24#64 := by bv_lin
    have hA40 : (sp1 + 32#64) + 8#64 = sp1 + 40#64 := by bv_lin
    have hA56 : (sp1 + 48#64) + 8#64 = sp1 + 56#64 := by bv_lin
    (try simp only [arm64_norm])
    (try rw [hA24]); (try rw [hA40]); (try rw [hA56])
    rw [hcs1.x19, hcs1.x20, hcs1.x21, hcs1.x22, hcs1.x23, hcs1.x24, hcs1.x25]
    unfold MallocImplSavedRegs
    simp only [sepConj_assoc]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro _))))))))))
  subst hsp1_eq
  have hb_eq : mbase 9 = b := hb.symm
  subst hb_eq
  wp_if hHiLarge
  ·
    have hGt131 : 131051 < req := by
      (try rw [hx0_1] at hHiLarge)
      rw [ult_ofNat_iff (by decide) hReq2_64] at hHiLarge
      exact hHiLarge
    rw [← mallocngBlockProg_eq_b09]
    exact mallocImpl_large_branch hMeta hMetaInv hcl5 hCount0 hwf0 hGt131 hReqMax
      htp0 hbrkS0 hPerm5 (by dsimp only [miOff_large_entry]; rfl)
      (by simp [arm64_norm, hrun1]) (by simpa [arm64_norm] using hsp1) hsp_align
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [arm64_norm, hProc1.1, hProc1.2.1, hProc1.2.2.1, hProc1.2.2.2.1,
              hProc1.2.2.2.2.1, hProc1.2.2.2.2.2.1, hProc1.2.2.2.2.2.2])
      ⟨by simpa [arm64_norm] using hcs1.x26, by simpa [arm64_norm] using hcs1.x27,
       by simpa [arm64_norm] using hcs1.x28, by simpa [calleeSavedVRegs] using hcs1.vregs⟩
      (by simp only [arm64_norm]; try exact hx0_1)
  ·
    have hLe131 : req ≤ 131051 := by
      have hF : ¬ 131051 < req := fun hLt =>
        hHiLarge (by (try rw [hx0_1]); exact (ult_ofNat_iff (by decide) hReq2_64).mpr hLt)
      omega
    rw [← mallocngBlockProg_eq_b09]
    exact mallocImpl_small_med_branch hSlot hMetaInv hcl5 hCount0 hwf0 hLe131
      htp0 hbrkS0 hPerm5 (by dsimp only [miOff_small_entry]; rfl)
      (by simp [arm64_norm, hrun1]) (by simpa [arm64_norm] using hsp1) hsp_align
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [arm64_norm, hProc1.1, hProc1.2.1, hProc1.2.2.1, hProc1.2.2.2.1,
              hProc1.2.2.2.2.1, hProc1.2.2.2.2.2.1, hProc1.2.2.2.2.2.2])
      ⟨by simpa [arm64_norm] using hcs1.x26, by simpa [arm64_norm] using hcs1.x27,
       by simpa [arm64_norm] using hcs1.x28, by simpa [calleeSavedVRegs] using hcs1.vregs⟩
      (by simp only [arm64_norm]; try exact hx0_1)

set_option maxHeartbeats 400000 in
theorem placed_libcMallocImpl24B2_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt)
    (hMetaInv : MallocngMetaCountInv) : LibcMallocImplPlaced24B2Stmt := by
  intro _ γ tp brkStart bud ivs0 req
  dsimp only [libcMallocImplPlacedSpec24B2]
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre hspAl0
  have hsp_align : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hspAl0
  have hpre1 : s0.mem ⊨
      ⌜s0.mem = m0 ∧ (s0.readReg64 .x0).toNat = req ∧
       s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
      ((stackFrame s0 704 ∗ MallocngHeapImpl γ maddrs tp brkStart s0.brk bud ivs0) ∗ R) := by
    refine Satisfies.mono ?_ hpre
    unfold MallocngEnv
    change (⌜s0.mem = m0⌝ ∗ (⌜(s0.readReg64 .x0).toNat = req⌝ ∗ stackFrame s0 704 ∗
        (⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
         MallocngHeapImpl γ maddrs tp brkStart s0.brk bud ivs0))) ∗ R ⊢ _
    refine Entails.trans (Entails.of_eq (by ac_rfl) :
      _ ⊢ ⌜s0.mem = m0⌝ ∗ ⌜(s0.readReg64 .x0).toNat = req⌝ ∗
          ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
          ((stackFrame s0 704 ∗ MallocngHeapImpl γ maddrs tp brkStart s0.brk bud ivs0) ∗ R)) ?_
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
  refine ⟨stackFrame s0 704 ∗ MallocngHeapImpl γ maddrs tp brkStart s0.brk bud ivs0, hpre_sp, ?_⟩
  rw [stackFrame_704_split_prologue s0]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v29
  apply SepWP.exists_elim; intro v30
  rw [mallocngBlockProg_eq_b09]
  have hpc0 : s0.pc = mbase 9 + 0#64 := by rw [hpc, BitVec.add_zero]
  generalize hb_eq : mbase 9 = b at hpc0 ⊢
  have hb : BlkBase 9 b := hb_eq.symm
  wp_stp64_cl m1 hm1 hcl hcl1
  wp_steps 5
  have hMaxVal : (9223372036854771710#64 : BitVec 64) = BitVec.ofNat 64 MallocngMaxAllocSize := by
    rw [mallocngMaxAllocSize_eq]
  have hMax2_64 : MallocngMaxAllocSize < 2 ^ 64 := by
    rw [mallocngMaxAllocSize_eq]; decide
  wp_if hHiMax
  ·
    have hGtMax : MallocngMaxAllocSize < req := by
      rw [hMaxVal, ult_ofNat_iff hMax2_64 hReq2_64] at hHiMax
      exact hHiMax
    have hNotLe : ¬ req ≤ MallocngMaxAllocSize := by omega
    have hOkFalse : decide (req ≤ MallocngMaxAllocSize) = false := decide_eq_false hNotLe
    conv => arg 6; ext sf; rw [hOkFalse]; dsimp only [Bool.false_eq_true, ↓reduceIte]
    refine SepWP.mono
      (mallocImpl_enomem_branch (oom := fun sf => ⌜MallocngTightOomCond msvc 0 bud.peakCount s0 sf⌝)
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
    simpa [mallocngAllocBudget] using hEnt
  ·
    have hReqMax : req ≤ MallocngMaxAllocSize := by
      have hF : ¬ MallocngMaxAllocSize < req := fun hLt =>
        hHiMax (by rw [hMaxVal]; exact (ult_ofNat_iff hMax2_64 hReq2_64).mpr hLt)
      omega
    have hOkTrue : decide (req ≤ MallocngMaxAllocSize) = true := decide_eq_true hReqMax
    have hHeapUnpack :
        (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngHeapImpl γ maddrs tp brkStart s0.brk bud ivs0) ⊢
        (∃∗ st0 : MallocngSt,
          ⌜MallocngCountIvsWF bud ivs0 st0⌝ ∗
          ⌜MallocngWF maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st0⌝ ∗
          (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
           (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
           memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
           stackFrameAt (s0.sp - 80#64) 624 ∗
           MallocngRoTablesA maddrs ∗
           MallocngCoreStInflightA 0 γ maddrs brkStart s0.brk bud.liveCost bud.peakCost st0 ∗
           MallocngRuntime maddrs tp)) := by
      rw [MallocngHeapImpl_eq, MallocngCoreImpl_eq]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro st0
      refine Entails.trans ?_ (Entails.sepExists_intro st0)
      refine Entails.trans (Entails.of_eq ?_ : _ ⊢
          (⌜MallocngCountIvsWF bud ivs0 st0⌝ ∗
           MallocngCoreStA γ maddrs brkStart s0.brk bud.liveCost bud.peakCost st0 ∗
           (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
            stackFrameAt (s0.sp - 80#64) 624 ∗
            MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp))) ?_
      · generalize ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) = p29,
          (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) = p30,
          memRegion ((s0.sp - 80#64) + 16#64) 64 = pMid,
          stackFrameAt (s0.sp - 80#64) 624 = pSf,
          MallocngRoTablesA maddrs = pRo,
          MallocngRuntime maddrs tp = pRt,
          MallocngCoreStA γ maddrs brkStart s0.brk bud.liveCost bud.peakCost st0 = pCr
        ac_rfl
      apply Entails.pure_left; intro hCnt0
      refine Entails.pure_right hCnt0 ?_
      dsimp only [MallocngCoreStA]
      have hDupWf :
          MallocngCoreStInflightA 0 γ maddrs brkStart s0.brk bud.liveCost bud.peakCost st0 ⊢
            ⌜MallocngWF maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st0⌝ ∗
            MallocngCoreStInflightA 0 γ maddrs brkStart s0.brk bud.liveCost bud.peakCost st0 := by
        dsimp only [MallocngCoreStInflightA]
        apply Entails.pure_left; intro hwf0
        exact Entails.pure_right hwf0 (Entails.pure_right hwf0 (Entails.refl _))
      refine Entails.trans (sepConj_mono_left hDupWf) ?_
      generalize MallocngCoreStInflightA 0 γ maddrs brkStart s0.brk bud.liveCost bud.peakCost st0 = pBody,
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) = p29,
        (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) = p30,
        memRegion ((s0.sp - 80#64) + 16#64) 64 = pMid,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocngRoTablesA maddrs = pRo,
        MallocngRuntime maddrs tp = pRt
      exact Entails.of_eq (by ac_rfl)
    apply SepWP.weaken_pre hHeapUnpack
    apply SepWP.exists_elim; intro st0
    apply SepWP.pure_elim; intro hCount0
    apply SepWP.pure_elim; intro hwf0
    conv => arg 6; ext sf; rw [hOkTrue]; dsimp only [↓reduceIte]
    refine SepWP.mono
      (mallocImpl_save_cs_dispatch hMeta hSlot hMetaInv hb hcl1 hCount0
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
    exact hEnt

theorem placed_libcMallocImpl_tightK_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt)
    (hMetaInv : MallocngMetaCountInv) : LibcMallocImplPlacedTightKStmt := by
  intro _ γ tp brkStart b ivs0 req
  refine subroutine_ok_mono (placed_libcMallocImpl24B2_ok hMeta hSlot hMetaInv γ tp brkStart b ivs0 req)
    (fun _ _ _ hp => hp) (fun _ R s0 sf hq => ?_)
  dsimp only [libcMallocImplPlacedSpec24B2, libcMallocImplPlacedTightKSpec, withCL] at hq ⊢
  refine Satisfies.mono (sepConj_mono_left ?_) hq
  refine sepConj_mono_left ?_
  by_cases hReq : req ≤ MallocngMaxAllocSize
  · simp only [hReq, ↓reduceIte]
    unfold mallocImplSuccessPost24 mallocImplSuccessBody24
    refine sepConj_mono_right (sepConj_mono_right ?_)
    apply Entails.sepExists_elim; intro p
    apply Entails.sepExists_elim; intro bs
    apply Entails.sepExists_elim; intro st'
    refine Entails.trans ?_ (Entails.sepExists_intro p)
    refine Entails.trans ?_ (Entails.sepExists_intro bs)
    refine Entails.trans ?_ (Entails.sepExists_intro st')
    apply Entails.pure_left
    rintro ⟨h1, h2, h3, h4, h5, h6, h7, g', hg', idx, hIdx, hSl, hOff, hMm, _, _, _⟩
    exact Entails.pure_right ⟨h1, h2, h3, h4, h5, h6, h7, g', hg', idx, hIdx, hSl, hOff, hMm⟩
      (Entails.refl _)
  · simp only [hReq, ↓reduceIte]
    exact Entails.refl _

theorem placed_libcMallocImpl_tight_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt)
    (hMetaInv : MallocngMetaCountInv) : LibcMallocImplPlacedTightStmt := by
  intro _ γ tp brkStart b ivs0 req
  refine subroutine_ok_mono (placed_libcMallocImpl_tightK_ok hMeta hSlot hMetaInv γ tp brkStart b ivs0 req)
    (fun _ _ _ hp => hp) (fun _ R s0 sf hq => ?_)
  dsimp only [libcMallocImplPlacedTightKSpec, libcMallocImplPlacedTightSpec, withCL] at hq ⊢
  refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_right ?_)))) hq
  by_cases hReq : req ≤ MallocngMaxAllocSize
  · simp only [hReq, ↓reduceIte]
    refine Entails.sepExists_mono fun p => Entails.sepExists_mono fun bs =>
      Entails.sepExists_mono fun st' => ?_
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right ?_))))
    exact mallocngBlockTokenK_to_token γ p req 0
  · simp only [hReq, ↓reduceIte]
    exact Entails.refl _

theorem placed_libcMallocImpl_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt)
    (hMetaInv : MallocngMetaCountInv) : LibcMallocImplPlacedStmt := by
  intro _ γ tp brkStart b ivs0 req
  refine subroutine_ok_mono (placed_libcMallocImpl_tight_ok hMeta hSlot hMetaInv γ tp brkStart b ivs0 req)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
      dsimp only [libcMallocImplPlacedTightSpec, libcMallocImplPlacedSpec, withCL] at hq ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hq
      apply Entails.pure_left
      rintro ⟨h1, h2⟩
      exact Entails.pure_right ⟨h1, MallocngMappedDelta.tight_to_step h2⟩ (Entails.refl _))
    (hoom := fun _ _ _ _ ho => by
      dsimp only [libcMallocImplPlacedTightSpec, libcMallocImplPlacedSpec, withCL] at ho ⊢
      rw [satisfies_pure_sepConj] at ho ⊢
      exact ⟨ho.1.to_oomCond (Nat.le_refl _), ho.2⟩)

theorem placed_libcMallocImpl24B2_uncond_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt) :
    LibcMallocImplPlaced24B2Stmt :=
  placed_libcMallocImpl24B2_ok hMeta hSlot mallocngMetaCountInv_holds

theorem placed_libcMallocImpl_tightK_uncond_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt) :
    LibcMallocImplPlacedTightKStmt :=
  placed_libcMallocImpl_tightK_ok hMeta hSlot mallocngMetaCountInv_holds

theorem placed_libcMallocImpl_tight_uncond_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt) :
    LibcMallocImplPlacedTightStmt :=
  placed_libcMallocImpl_tight_ok hMeta hSlot mallocngMetaCountInv_holds

theorem placed_libcMallocImpl_uncond_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt) :
    LibcMallocImplPlacedStmt :=
  placed_libcMallocImpl_ok hMeta hSlot mallocngMetaCountInv_holds

end VerifiedLibraries.Mallocng.Proofs

