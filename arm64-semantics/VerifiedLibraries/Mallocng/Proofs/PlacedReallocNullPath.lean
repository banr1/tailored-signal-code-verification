/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocStage3Entry

/-!
# Placed `__libc_realloc` Helpers and Null-Pointer Path

Provides arithmetic, alignment, budget, and 800-byte stack-cell helpers for `placed_libcRealloc_ok`,
and proves the null-pointer path `__libc_realloc(0, newSize)` (`realloc_null_path_ok`) branching to
`__libc_malloc_impl`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Arithmetic, Alignment, Budget, and Stack Helpers -/

theorem align16_and15_eq_zero {p : BitVec 64} (h : 16 ∣ p.toNat) :
    p &&& 15#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hm : p.toNat &&& 15 = p.toNat % 16 := Nat.and_two_pow_sub_one_eq_mod p.toNat 4
  change (p.toNat &&& 15) = 0
  rw [hm]
  exact Nat.mod_eq_zero_of_dvd h

theorem maxAllocBv_toNat :
    (0x7fffffffffffeffe#64 : BitVec 64).toNat = MallocngMaxAllocSize := by
  decide

theorem ult_maxAllocBv_iff (n : BitVec 64) :
    (0x7fffffffffffeffe#64 : BitVec 64).ult n = true ↔ ¬ (n.toNat ≤ MallocngMaxAllocSize) := by
  simp only [BitVec.ult, decide_eq_true_eq, maxAllocBv_toNat]
  omega

theorem not_stage3_hi_bounds {p endPtr : BitVec 64} {newSz : Nat}
    (hLe : p.toNat ≤ endPtr.toNat) (hEnd48 : endPtr.toNat ≤ 2 ^ 48)
    (hNewMax : newSz ≤ MallocngMaxAllocSize)
    (hNotHi : ¬ ((if (BitVec.ofNat 64 (endPtr.toNat - p.toNat)).ule 131051#64 then
        BitVec.ofNat 64 (endPtr.toNat - p.toNat) else 131051#64).ult
        (BitVec.ofNat 64 newSz) = true)) :
    newSz ≤ 131051 ∧ p.toNat + newSz ≤ endPtr.toNat := by
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by decide
  have hMax64 : MallocngMaxAllocSize < 2 ^ 64 := maxAllocSize_lt_pow64
  let cap := endPtr.toNat - p.toNat
  have hCapNat : (BitVec.ofNat 64 cap).toNat = cap := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by dsimp only [cap]; omega)
  have hNewNat : (BitVec.ofNat 64 newSz).toNat = newSz := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hMinNat := ule_ite_toNat_eq_min (BitVec.ofNat 64 cap) 131051#64
  rw [hCapNat, show (131051#64 : BitVec 64).toNat = 131051 from rfl] at hMinNat
  simp only [BitVec.ult, decide_eq_true_eq] at hNotHi
  change ¬ ((if (BitVec.ofNat 64 cap).ule 131051#64 then BitVec.ofNat 64 cap else 131051#64).toNat <
    (BitVec.ofNat 64 newSz).toNat) at hNotHi
  rw [hMinNat, hNewNat] at hNotHi
  dsimp only [cap] at hNotHi
  omega

theorem sizeToClassUnits_lt_48 {u : Nat} (hu : u ≤ 8190) :
    sizeToClassUnits u < 48 := by
  by_cases hu9 : u ≤ 9
  · simp only [sizeToClassUnits, hu9, ↓reduceIte]; omega
  · have hu10 : 10 ≤ u := by omega
    have hLarge := sizeToClassLarge_spec hu10 hu
    unfold sizeToClassLargeOk at hLarge
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hLarge
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hSc2Lt⟩, _⟩, _⟩, _⟩ := hLarge
    simpa [sizeToClassUnits, hu9] using hSc2Lt

theorem realloc_null_budget (ok : Bool) (req : Nat) (bgt : MallocngBudget) :
    mallocngAllocBudget ok req bgt = mallocngReallocBudget ok none req bgt := by
  unfold mallocngAllocBudget mallocngReallocBudget
  cases ok <;> rfl

theorem mallocBlock_to_initBlock_nil (γ : GhostName) (q : BitVec 64)
    (bs : List (BitVec 8)) (req a : Nat)
    (hwf : MallocngBlockWf q req) (hlen : bs.length = req) :
    (MallocngTightInitBlock γ a).pureWf q (req, []) ∧
    ((q ↦ₛ bs) ∗ MallocngBlockTokenK γ q req 0 ⊢
      (MallocngTightInitBlock γ a).interp q (req, [])) := by
  obtain ⟨hne, h16, h48⟩ := hwf
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by decide
  refine ⟨⟨hne, h16, by omega, Nat.zero_le req⟩, ?_⟩
  dsimp only [MallocngTightInitBlock, List.length_nil, Nat.sub_zero]
  rw [pointsToBytes_nil, emp_sepConj, show q + BitVec.ofNat 64 0 = q from BitVec.add_zero q,
      sepConj_comm (q ↦ₛ bs)]
  refine sepConj_mono (mallocngBlockTokenK_to_tight γ q req 0 a (Nat.zero_le _)) ?_
  simpa [hlen] using (IsBlock.pointsToBytes q bs).entails_memRegion

theorem stack80_cells_to_stackFrame800 (s0 : State)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
     ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
     ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
     ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
     ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
    stackFrameAt (s0.sp - 80#64) 720 ⊢ stackFrame s0 800 := by
  rw [stackFrame800_split s0]
  rw [show s0.sp - 80#64 + 8#64 = s0.sp - 72#64 by bv_lin,
      show s0.sp - 80#64 + 16#64 = s0.sp - 64#64 by bv_lin,
      show s0.sp - 80#64 + 24#64 = s0.sp - 56#64 by bv_lin,
      show s0.sp - 80#64 + 32#64 = s0.sp - 48#64 by bv_lin,
      show s0.sp - 80#64 + 40#64 = s0.sp - 40#64 by bv_lin,
      show s0.sp - 80#64 + 48#64 = s0.sp - 32#64 by bv_lin,
      show s0.sp - 80#64 + 56#64 = s0.sp - 24#64 by bv_lin,
      show s0.sp - 80#64 + 64#64 = s0.sp - 16#64 by bv_lin,
      show s0.sp - 80#64 + 72#64 = s0.sp - 8#64 by bv_lin]
  have h10 :
      (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
       ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
       ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
       ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
       ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) =
      ((((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
        ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
        ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5)) ∗
       (((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
        ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9))) := by ac_rfl
  rw [h10, sepConj_assoc]
  refine sepConj_mono (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)))))) ?_
  refine sepConj_mono_left (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _))))

theorem stackFrame800_entails_exists_cells (s0 : State) :
    stackFrame s0 800 ⊢
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
      ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
         ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
         ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
         ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
         ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
        stackFrameAt (s0.sp - 80#64) 720 := by
  have hSplit : stackFrame s0 800 = (stackFrameAt s0.sp 80 ∗ stackFrameAt (s0.sp - 80#64) 720) := by
    unfold stackFrame
    rw [← stackFrameAt_eq_memRegion s0.sp 800, show (800 : Nat) = 80 + 720 from rfl,
        stackFrameAt_split s0.sp 80 720]
  rw [hSplit]
  dsimp only [reduceStackFrameAt]
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun v0 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun v1 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun v2 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun v3 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun v4 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun v5 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun v6 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun v7 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun v8 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun v9 => ?_
  exact Entails.refl _

/-! ## Null-Pointer Path -/

set_option maxHeartbeats 400000 in
theorem realloc_null_path_ok [MallocngMultiPlacement]
    (hImpl : LibcMallocImplPlacedTightKStmt)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart newSize : BitVec 64) (a : Nat)
    (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 : State) (R : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = 0#64) (hx1 : s0.readReg64 .x1 = newSize)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem) :
    let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
    let bf := mallocngReallocBudget ok none newSize.toNat bgt
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) s0
      (stackFrame s0 800 ∗ MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R →
          sf.mem ⊨
            ((⌜MallocngCallAccounting 16
                (MallocngTightStepBound (if ok then mallocngReallocRes a newSize.toNat else 0) bgt.peakCount)
                s0 sf⌝ ∗
              stackFrame s0 800 ∗
              MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
              if ok then
                ∃∗ q : BitVec 64,
                  ⌜sf.readReg64 .x0 = q ∧
                   (MallocngTightInitBlock γ a).pureWf q (newSize.toNat, [])⌝ ∗
                  (MallocngTightInitBlock γ a).interp q (newSize.toNat, [])
              else
                ⌜sf.readReg64 .x0 = 0#64⌝ ∗ emp) ∗
             ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf =>
        ⌜MallocngTightOomCond msvc (if ok then newSize.toNat else 0) bgt.peakCount s0 sf⌝) := by
  intro ok bf; have _ := hb; have _ := hx0; have _ := hx1
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
  have hEnvTail : MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s0 =
      MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 sTail := by
    unfold MallocngEnv
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
  have hMalloc := call_placed_libcMallocImpl_tightK hImpl (P := blkPC_b14.rebase b (fun _ => none))
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
      dsimp only [libcMallocImplPlacedTightKSpec, withCL]
      refine Entails.trans (Q :=
          (stackFrame sTail 704 ∗ MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 sTail) ∗
          stackFrameAt (s0.sp - 704#64) 96 ∗ R')
        (Entails.of_eq (by
          generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 sTail) = PEnv
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
    dsimp only [libcMallocImplPlacedTightKSpec, withCL] at hm
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
    obtain ⟨⟨hProcTSf, hDeltaTSf⟩, hm⟩ := hm
    have hProc0T : MallocngProcPreserved s0 sTail := by
      rw [hsTail]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hProc0Sf : MallocngProcPreserved s0 sf := mallocngProcPreserved_trans hProc0T hProcTSf
    have hDelta0Sf : MallocngMappedDelta 16
        (MallocngTightStepBound (if ok then mallocngReallocRes a newSize.toNat else 0) bgt.peakCount)
        s0.mem sf.mem := by
      obtain ⟨ivs, hlen, hsum, hcov⟩ := hDeltaTSf
      have hsb : MallocngTightStepBound (if ok then newSize.toNat else 0) bgt.peakCount ≤
          MallocngTightStepBound (if ok then mallocngReallocRes a newSize.toNat else 0) bgt.peakCount :=
        MallocngTightStepBound_mono (by
          dsimp only [ok]; split
          · exact le_mallocngReallocRes a _
          · exact Nat.le_refl _)
      refine ⟨ivs, hlen, Nat.le_trans hsum hsb, fun a ha => ?_⟩
      rcases hcov a ha with hmT | hin
      · exact Or.inl (by rwa [← hPermTail])
      · exact Or.inr hin
    have hAcc0Sf : MallocngCallAccounting 16
        (MallocngTightStepBound (if ok then mallocngReallocRes a newSize.toNat else 0) bgt.peakCount)
        s0 sf := ⟨hProc0Sf, hDelta0Sf⟩
    by_cases hLeMax : newSize.toNat ≤ MallocngMaxAllocSize
    · have hOkTrue : ok = true := decide_eq_true hLeMax
      have hBfEq : mallocngAllocBudget true newSize.toNat bgt = bf := by
        dsimp only [bf]; rw [hOkTrue, realloc_null_budget]
      simp only [hLeMax, decide_true, hOkTrue, ↓reduceIte] at hAcc0Sf hm ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
      obtain ⟨q, bs, st', hm⟩ := hm
      rw [← sepConj_assoc (stackFrame sTail 704) ⌜_⌝,
          sepConj_comm (stackFrame sTail 704) ⌜_⌝,
          sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
      obtain ⟨⟨hx0Q, htpSf, hbrksSf, hWfQ, hBsLen, hNoOrphT, hCountSt', _⟩, hm⟩ := hm
      rw [hBfEq] at hCountSt' hm
      have hm' : sf.mem ⊨
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
          (stackFrame sTail 704 ∗ stackFrameAt (s0.sp - 704#64) 96) ∗
          (MallocngRoTablesA maddrs ∗
           MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
           MallocngRuntime maddrs tp) ∗
          ((q ↦ₛ bs) ∗ MallocngBlockTokenK γ q newSize.toNat 0) ∗ R := by
        refine Satisfies.mono (Entails.of_eq ?_) hm
        generalize (MallocngRoTablesA maddrs) = PRo
        generalize (MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st') = PCore
        generalize (MallocngRuntime maddrs tp) = PRt
        ac_rfl
      rw [← hSplit704, satisfies_pure_sepConj] at hm'
      obtain ⟨hclSf, hm'⟩ := hm'
      have hNoOrph0 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem := by
        intro a hmA hor0
        rcases hor0 with hnot0 | hin0
        · exact hNoOrphT a hmA (Or.inl (by rwa [hPermTail]))
        · exact hNoOrphT a hmA (Or.inr hin0)
      have ⟨hPureInit, hEntInit⟩ := mallocBlock_to_initBlock_nil γ q bs newSize.toNat a hWfQ hBsLen
      have hPostEnvEnt :
          MallocngRoTablesA maddrs ∗
          MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
          MallocngRuntime maddrs tp ⊢
            MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf :=
        Entails.trans (pack_mallocImpl_env γ tp brkStart bf st' sf htpSf hbrksSf hCountSt')
          (Entails.sepExists_right (dynamicRootRegions st')
            (Entails.pure_right hNoOrph0 (Entails.refl _)))
      have hBlkEnt :
          ((q ↦ₛ bs) ∗ MallocngBlockTokenK γ q newSize.toNat 0) ⊢
          ∃∗ q' : BitVec 64,
            ⌜sf.readReg64 .x0 = q' ∧
             (MallocngTightInitBlock γ a).pureWf q' (newSize.toNat, [])⌝ ∗
            (MallocngTightInitBlock γ a).interp q' (newSize.toNat, []) :=
        Entails.trans hEntInit
          (Entails.sepExists_right q (Entails.pure_right ⟨hx0Q, hPureInit⟩ (Entails.refl _)))
      rw [← hSplit704,
          sepConj_comm (_ : SepProp) ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝,
          sepConj_assoc ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ _ R,
          sepConj_assoc ⌜MallocngCallAccounting 16 _ s0 sf⌝ _ R,
          sepConj_assoc (stackFrame s0 800) _ R,
          sepConj_assoc (MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf) _ R]
      refine Satisfies.mono ?_ hm'
      refine Entails.pure_right hclSf (Entails.pure_right hAcc0Sf ?_)
      exact sepConj_mono_right (sepConj_mono hPostEnvEnt (sepConj_mono_left hBlkEnt))
    · have hOkFalse : ok = false := decide_eq_false hLeMax
      have hBfEq : mallocngAllocBudget false newSize.toNat bgt = bf := by
        dsimp only [bf]; rw [hOkFalse, realloc_null_budget]
      simp only [hLeMax, decide_false, hOkFalse, Bool.false_eq_true, ↓reduceIte] at hAcc0Sf hm ⊢
      rw [← sepConj_assoc (stackFrame sTail 704) ⌜_⌝,
          sepConj_comm (stackFrame sTail 704) ⌜_⌝,
          sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
      obtain ⟨hx0_0, hm⟩ := hm
      rw [hBfEq] at hm
      have hm' : sf.mem ⊨
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
          (stackFrame sTail 704 ∗ stackFrameAt (s0.sp - 704#64) 96) ∗
          MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 sTail sf ∗ R := by
        refine Satisfies.mono (Entails.of_eq ?_) hm
        generalize (MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 sTail sf) = PPost
        ac_rfl
      rw [← hSplit704, satisfies_pure_sepConj] at hm'
      obtain ⟨hclSf, hm'⟩ := hm'
      have hPostCongr :
          MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 sTail sf ⊢
          MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf := by
        unfold MallocngPostEnv
        refine Entails.sepExists_mono fun ivsf => Entails.pure_left fun hNoT => ?_
        refine Entails.pure_right (fun a hmA hor0 => ?_) (Entails.refl _)
        rcases hor0 with hnot0 | hin0
        · exact hNoT a hmA (Or.inl (by rwa [hPermTail]))
        · exact hNoT a hmA (Or.inr hin0)
      rw [← hSplit704, sepConj_emp,
          sepConj_comm (_ : SepProp) ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝,
          sepConj_assoc ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ _ R,
          sepConj_assoc ⌜MallocngCallAccounting 16 _ s0 sf⌝ _ R,
          sepConj_assoc (stackFrame s0 800) _ R,
          sepConj_assoc (MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf) _ R]
      refine Satisfies.mono ?_ hm'
      refine Entails.pure_right hclSf (Entails.pure_right hAcc0Sf ?_)
      exact sepConj_mono_right
        (sepConj_mono hPostCongr (Entails.pure_right hx0_0 (Entails.refl R)))
  ·
    have hOom' := Satisfies.drop_mid hOom
    dsimp only [libcMallocImplPlacedTightKSpec, withCL] at hOom' ⊢
    rw [satisfies_pure_sepConj] at hOom' ⊢
    obtain ⟨hOomT, hR'⟩ := hOom'
    refine ⟨?_, hR'⟩
    exact rdlRealloc_tightOom_congr
      (Nat.le_refl _)
      (by rw [hsTail]; rfl) (by rw [hsTail]; rfl) (by rw [hsTail]; rfl) hPermTail hOomT

end VerifiedLibraries.Mallocng.Proofs
