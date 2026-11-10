/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.Model
public import ProofLib.MallocngBridge

/-!
# Discharging `MallocngStepOomCond` from a Cost-Model Fit

Caller-facing OOM refutation lemmas (`mallocngStepOomCond_false_of_fits`,
`mallocngStepOomCond_false_of_fitsEvent`, and `mallocngStepOomCond_false_of_cvFitsStep`) for the
model-indexed `mallocng` specifications in `Spec.Cost`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## Generic Discharge -/

/-- 48-bit user VA headroom for `n` pre-call intervals totalling `S` bytes plus one call that maps
    at most `stepB` bytes in at most `16` new intervals and then requests `≤ stepB` more. -/
def VaRoom (S n stepB : Nat) : Prop :=
  MMAP_MIN_ADDR + S + stepB + (n + 16) * (stepB + PAGE_SIZE) + stepB ≤ 2 ^ 48

theorem VaRoom.mono {S₁ S₂ n₁ n₂ b₁ b₂ : Nat} (h : VaRoom S₂ n₂ b₂)
    (hS : S₁ ≤ S₂) (hn : n₁ ≤ n₂) (hb : b₁ ≤ b₂) : VaRoom S₁ n₁ b₁ := by
  unfold VaRoom at *
  have : (n₁ + 16) * (b₁ + PAGE_SIZE) ≤ (n₂ + 16) * (b₂ + PAGE_SIZE) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- If `ivsPre` covers every mapped byte of `s0`, physical-plus-RW bytes are conserved, and both
    physical room (`sum ivsPre + stepB ≤ physPlusRw s0`) and `VaRoom` hold, then a sanitized `svc`
    call reserving `stepB` cannot satisfy `MallocngStepOomCond`. -/
theorem mallocngStepOomCond_false_of_fits {svc : State → State} {stepB : Nat} {s0 sf : State}
    {ivsPre : List (BitVec 64 × Nat)}
    (hSan : MallocngSanitizedSvc svc)
    (hCov : ∀ a : BitVec 64, (s0.mem.perm a).mapped = true → MallocngInIntervals ivsPre a)
    (hPhysEq : physPlusRw sf = physPlusRw s0)
    (hPhys : (ivsPre.map Prod.snd).sum + stepB ≤ physPlusRw s0)
    (hVa : VaRoom (ivsPre.map Prod.snd).sum ivsPre.length stepB)
    (hOom : MallocngStepOomCond svc stepB s0 sf) : False := by
  obtain ⟨_, _, _, dIvs, hdLen, hdSum, hdCov, hSanImp⟩ := hOom
  obtain ⟨sz, hSzPos, hSzAl, hSzB, hNoGapOrPhys⟩ := hSanImp hSan
  have hTotCov : ∀ a : BitVec 64, (sf.mem.perm a).mapped = true →
      ∃ iv ∈ ivsPre ++ dIvs, (a - iv.1).toNat < iv.2 := by
    intro a ha
    rcases hdCov a ha with ha0 | ⟨iv, hiv, hin⟩
    · obtain ⟨iv, hiv, hin⟩ := hCov a ha0
      exact ⟨iv, List.mem_append_left _ hiv, hin⟩
    · exact ⟨iv, List.mem_append_right _ hiv, hin⟩
  have hSum : ((ivsPre ++ dIvs).map Prod.snd).sum =
      (ivsPre.map Prod.snd).sum + (dIvs.map Prod.snd).sum := by
    simp [List.map_append, List.sum_append]
  rcases hNoGapOrPhys with hNoGap | hNoPhys
  · have hLen : (ivsPre ++ dIvs).length ≤ ivsPre.length + 16 := by
      rw [List.length_append]; omega
    have hMul : (ivsPre ++ dIvs).length * (sz + PAGE_SIZE) ≤
        (ivsPre.length + 16) * (stepB + PAGE_SIZE) :=
      Nat.mul_le_mul hLen (by omega)
    have hFit : MMAP_MIN_ADDR + ((ivsPre ++ dIvs).map Prod.snd).sum +
        (ivsPre ++ dIvs).length * (sz + PAGE_SIZE) + sz ≤ 2 ^ 48 := by
      unfold VaRoom at hVa; omega
    exact hNoGap (hasGap_of_mappedIntervals hTotCov hSzPos hSzAl hFit)
  · have hrw := rwBytes_le_intervals_sum hTotCov
    dsimp only [physPlusRw] at hPhysEq hPhys
    omega

/-! ## Model-Level Discharge -/

/-- When mapped bytes of `s0` lie in `staticIvs ++ heapIvs`, `heapIvs` satisfies `M`'s footprint
    and interval bounds at `st`, `staticBytes + physCap ≤ physPlusRw s0`, `FitsEvent M physCap st ev`,
    and `VaRoom` holds for `M.stepReserve ev st`, a call reserving `stepB ≤ M.stepReserve ev st`
    cannot satisfy `MallocngStepOomCond`. -/
theorem mallocngStepOomCond_false_of_fitsEvent {M : AllocCostModel} {st : M.σ} {ev : AllocEvent}
    {svc : State → State} {stepB physCap staticBytes staticCount : Nat} {s0 sf : State}
    {staticIvs heapIvs : List (BitVec 64 × Nat)}
    (hSan : MallocngSanitizedSvc svc)
    (hCov : ∀ a : BitVec 64, (s0.mem.perm a).mapped = true →
      MallocngInIntervals (staticIvs ++ heapIvs) a)
    (hStSum : (staticIvs.map Prod.snd).sum ≤ staticBytes)
    (hStLen : staticIvs.length ≤ staticCount)
    (hHeapSum : (heapIvs.map Prod.snd).sum ≤ M.footprint st)
    (hHeapLen : heapIvs.length ≤ M.maxDynIvs st)
    (hCap : staticBytes + physCap ≤ physPlusRw s0)
    (hFits : FitsEvent M physCap st ev)
    (hVa : VaRoom (staticBytes + M.footprint st) (staticCount + M.maxDynIvs st)
      (M.stepReserve ev st))
    (hStep : stepB ≤ M.stepReserve ev st)
    (hPhysEq : physPlusRw sf = physPlusRw s0)
    (hOom : MallocngStepOomCond svc stepB s0 sf) : False := by
  have hSum : ((staticIvs ++ heapIvs).map Prod.snd).sum =
      (staticIvs.map Prod.snd).sum + (heapIvs.map Prod.snd).sum := by
    simp [List.map_append, List.sum_append]
  have hLen : (staticIvs ++ heapIvs).length = staticIvs.length + heapIvs.length :=
    List.length_append
  unfold FitsEvent at hFits
  refine mallocngStepOomCond_false_of_fits hSan hCov hPhysEq ?_
    (hVa.mono (by omega) (by omega) hStep) hOom
  omega

theorem stepB_le_of_alloc0_le {M : AllocCostModel} {st : M.σ} {ev : AllocEvent} (ok : Bool)
    (h0 : M.stepReserve (.alloc 0) st ≤ M.stepReserve ev st) :
    (if ok then M.stepReserve ev st else M.stepReserve (.alloc 0) st) ≤ M.stepReserve ev st := by
  cases ok
  · exact h0
  · exact Nat.le_refl _

theorem tight_alloc0_le_stepReserve (ev : AllocEvent) (b : MallocngBudget) :
    mallocngTight2CostModel.stepReserve (.alloc 0) b ≤ mallocngTight2CostModel.stepReserve ev b := by
  cases ev <;>
    simp only [mallocngTight2CostModel, mallocngTight2Reserve] <;>
    omega

/-! ## Combined Physical and VA Budget Adapter -/

/-- Combined physical and VA budget limits (`staticCount`, `staticBytes`, `physCap`). -/
structure CvBudgetLimits where
  staticCount : Nat
  staticBytes : Nat
  physCap : Nat
  enforced : Bool := true

/-- Combined per-call physical and 48-bit VA fit condition. -/
def CvFitsStep (lim : CvBudgetLimits) (stepB dynIvs fp : Nat) : Prop :=
  lim.enforced = true ∧
  lim.staticBytes + fp + 2 * stepB ≤ lim.physCap ∧
  MMAP_MIN_ADDR + lim.staticBytes + fp + stepB +
    (lim.staticCount + dynIvs + 16) * (stepB + PAGE_SIZE) + stepB ≤ 2 ^ 48

/-- `CvFitsStep` implies the split physical and `VaRoom` conditions of
    `mallocngStepOomCond_false_of_fitsEvent`. -/
theorem cvFitsStep_room {lim : CvBudgetLimits} {stepB dynIvs fp : Nat}
    (h : CvFitsStep lim stepB dynIvs fp) :
    fp + stepB ≤ lim.physCap - lim.staticBytes ∧
      lim.staticBytes + (lim.physCap - lim.staticBytes) ≤ lim.physCap ∧
      VaRoom (lim.staticBytes + fp) (lim.staticCount + dynIvs) stepB := by
  obtain ⟨_, hRam, hVa⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  unfold VaRoom; omega

/-- `CvFitsStep` at `M`'s bounds together with `lim.physCap ≤ physPlusRw s0` refutes
    `MallocngStepOomCond`. -/
theorem mallocngStepOomCond_false_of_cvFitsStep {M : AllocCostModel} {st : M.σ} {ev : AllocEvent}
    {svc : State → State} {stepB : Nat} {lim : CvBudgetLimits} {s0 sf : State}
    {staticIvs heapIvs : List (BitVec 64 × Nat)}
    (hSan : MallocngSanitizedSvc svc)
    (hCov : ∀ a : BitVec 64, (s0.mem.perm a).mapped = true →
      MallocngInIntervals (staticIvs ++ heapIvs) a)
    (hStSum : (staticIvs.map Prod.snd).sum ≤ lim.staticBytes)
    (hStLen : staticIvs.length ≤ lim.staticCount)
    (hHeapSum : (heapIvs.map Prod.snd).sum ≤ M.footprint st)
    (hHeapLen : heapIvs.length ≤ M.maxDynIvs st)
    (hCap : lim.physCap ≤ physPlusRw s0)
    (hFits : CvFitsStep lim (M.stepReserve ev st) (M.maxDynIvs st) (M.footprint st))
    (hStep : stepB ≤ M.stepReserve ev st)
    (hPhysEq : physPlusRw sf = physPlusRw s0)
    (hOom : MallocngStepOomCond svc stepB s0 sf) : False := by
  obtain ⟨hPh, hSt, hVa⟩ := cvFitsStep_room hFits
  exact mallocngStepOomCond_false_of_fitsEvent (physCap := lim.physCap - lim.staticBytes)
    hSan hCov hStSum hStLen hHeapSum hHeapLen (Nat.le_trans hSt hCap) hPh hVa hStep hPhysEq hOom

end VerifiedLibraries.Mallocng.Proofs.Cost
