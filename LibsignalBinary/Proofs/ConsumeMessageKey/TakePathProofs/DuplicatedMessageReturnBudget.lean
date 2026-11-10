/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.CommonBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.DuplicatedMessageReturn
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Shared Epilogue and `DuplicatedMessage` Return Path (Block 24)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.DuplicatedMessageReturnBudget

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState)
open CryptoVerification (
  LibsignalPlacement blkLib_eq_24 blkPC_24 blkPl_24 lsLogFilterAddr withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSessionRepr (
  RatchetGhost consumeMessageKeyResultAt errDuplicatedMessage ratchetAt
)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost cmkPreLoopHeap_placed cmkSavedRegs cmkStack
)
open CryptoVerification.LibsignalSession.TakePath (
  chainKeyBytes_entails_memRegion cmkStack_recombine memRegion_88_entails_dup_slots
  sepWP_to_reaches_pc
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkEnv cmkPlacedSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem ratchetAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    ratchetAt (A.atState lim st s) = ratchetAt A.repAlloc :=
  rfl

private theorem consumeMessageKeyResultAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    consumeMessageKeyResultAt (A.atState lim st s) = consumeMessageKeyResultAt A.repAlloc :=
  rfl

theorem cmk_epilogue_77c_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1916#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ stackAt s0.sp cmkStack)) := by
  rcases htrace with ⟨htrace, hvregs⟩
  unfold cmkSavedRegs
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, ?_⟩
    · simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]
    · exact cmkStack_recombine s0.sp s0

theorem cmk_epilogue_77c_placed_outcome [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : ConsumeMessageKeyGhost}
    {st_init st : M.σ} {remEnv : List AllocEvent → Prop}
    (hsb : SeamBudget M lim (CmkEnv x) st_init st remEnv)
    (hnil : remEnv [])
    (G' : RatchetGhost) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1916#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnpan : (x.model F).1 ≠ .error .panic)
    (hG' : x.G.AgreeExcept G' (x.touched F))
    (hm : s.mem ⊨
      (stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0) ∗
      (ratchetAt A.repAlloc x.self G' (x.model F).2 ∗
       consumeMessageKeyResultAt A.repAlloc x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool lim st s ∗ R)) :
    reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
      (cmkPlacedSpec F A lim) (x, st_init) R s0 s := by
  obtain ⟨evs_tot, hst_tot, henv_tot⟩ := hsb.finish (evs_exit := []) hnil
  have hst_eq : st = M.stepEvents evs_tot st_init := by
    simpa using hst_tot
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, hpc_sf, hrun_sf, P_f, hm_sf, hvm_sf, hsp_sf, htrace_sf, hcc_sf, hP_f⟩ :=
    sepWP_to_reaches_pc (cmk_epilogue_77c_placed_wp s0 s hpc hrun hsp hsp_align htrace) hm hL
  refine reaches_outcome_steps hsteps
    (reaches_outcome_refl_return hpc_sf hrun_sf ⟨?_, hsp_sf, hcc_sf⟩)
  have hm1 : sf.mem ⊨ stackAt s0.sp cmkStack ∗
      (ratchetAt A.repAlloc x.self G' (x.model F).2 ∗
       consumeMessageKeyResultAt A.repAlloc x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool lim (M.stepEvents evs_tot st_init) sf ∗ R) := by
    have hm0 := Satisfies.mono (sepConj_mono_left hP_f) hm_sf
    rw [← hst_eq, A.pool_transport lim st s sf hvm_sf]
    exact hm0
  dsimp only [cmkPlacedSpec, CryptoVerification.LibsignalSession.cmkPlacedSpec, withLsCodeLoaded]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs_tot, ?_⟩
  rw [ratchetAt_atState, consumeMessageKeyResultAt_atState, RustCliAllocBudget.atState_pool]
  refine Satisfies.mono ?_ hm1
  have h_rearrange :
      (stackAt s0.sp cmkStack ∗
        (ratchetAt A.repAlloc x.self G' (x.model F).2 ∗
         consumeMessageKeyResultAt A.repAlloc x.ret (x.model F).1 ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗
         memRegion x.ckA 36 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         A.pool lim (M.stepEvents evs_tot st_init) sf ∗ R)) =
      (ratchetAt A.repAlloc x.self G' (x.model F).2 ∗
       (consumeMessageKeyResultAt A.repAlloc x.ret (x.model F).1 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        memRegion x.ckA 36 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt s0.sp cmkStack ∗
        A.pool lim (M.stepEvents evs_tot st_init) sf ∗ R)) := by sep_ac_rfl
  rw [h_rearrange]
  have hpost_ent :
      ratchetAt A.repAlloc x.self G' (x.model F).2 ⊢
        ⌜CmkEnv x evs_tot⌝ ∗
          (⌜(x.model F).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
            (∃∗ G'' : RatchetGhost,
              ⌜x.G.AgreeExcept G'' (x.touched F)⌝ ∗
                ratchetAt A.repAlloc x.self G'' (x.model F).2)) :=
    Entails.pure_right henv_tot
      (Entails.pure_right ⟨hnpan, htrace_sf⟩
        (Entails.sepExists_right G' (Entails.pure_right hG' (Entails.refl _))))
  refine Entails.trans (sepConj_mono_left hpost_ent) ?_
  exact Entails.of_eq (by sep_ac_rfl)

theorem cmk_dup_0xb4_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)} {A : RustAlloc}
    (x : ConsumeMessageKeyGhost) (s0 s : State)
    (v0 v16 v20 : BitVec 32) (v8 : BitVec 64)
    (hpc : s.pc = (blkPl_24).base + 180#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx20 : s.readReg64 .x20 = x.counter.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = x.ret)
    (hx28 : s.readReg64 .x28 = x.ck.index.zeroExtend 64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H)
      ((blkPl_24).base + 1916#64) s
      ((x.ret ↦₃₂ v0) ∗
       memRegion (x.ret + 4#64) 4 ∗
       ((x.ret + 8#64) ↦₆₄ v8) ∗
       ((x.ret + 16#64) ↦₃₂ v16) ∗
       ((x.ret + 20#64) ↦₃₂ v20) ∗
       memRegion (x.ret + 24#64) 64 ∗
       (lsLogFilterAddr ↦₆₄ 0#64))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        (P_f ⊢ consumeMessageKeyResultAt A x.ret (.error (.duplicatedMessage x.ck.index x.counter)) ∗
          (lsLogFilterAddr ↦₆₄ 0#64))) := by
  rcases htrace with ⟨htrace, hvregs⟩
  apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
    blkLib_eq_24 (mid := (blkPl_24).base + 1916#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun _m_real _hnsp => ?_
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨_hnsp.toVmPreserved (by simp_all [arm64_norm]),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, ?_⟩
  simp only [consumeMessageKeyResultAt, errDuplicatedMessage]
  exact Entails.of_eq (by sep_ac_rfl)

theorem cmk_dup_0xb4_placed_outcome [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {st_init st : M.σ}
    (x : ConsumeMessageKeyGhost)
    (hsb : SeamBudget M lim (CmkEnv x) st_init st FreeOnlyEvs)
    (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 180#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx20 : s.readReg64 .x20 = x.counter.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = x.ret)
    (hx28 : s.readReg64 .x28 = x.ck.index.zeroExtend 64)
    (hmodel : x.model F = (.error (.duplicatedMessage x.ck.index x.counter), x.st))
    (hm : s.mem ⊨ cmkPreLoopHeap_placed (A.atState lim st s) x s0 ∗ R) :
    reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
      (cmkPlacedSpec F A lim) (x, st_init) R s0 s := by
  unfold cmkPreLoopHeap_placed at hm
  rw [ratchetAt_atState, RustCliAllocBudget.atState_pool] at hm
  have hm_slots : s.mem ⊨
      ((∃∗ v0 : BitVec 32, (x.ret ↦₃₂ v0)) ∗
       memRegion (x.ret + 4#64) 4 ∗
       (∃∗ v8 : BitVec 64, ((x.ret + 8#64) ↦₆₄ v8)) ∗
       (∃∗ v16 : BitVec 32, ((x.ret + 16#64) ↦₃₂ v16)) ∗
       (∃∗ v20 : BitVec 32, ((x.ret + 20#64) ↦₃₂ v20)) ∗
       memRegion (x.ret + 24#64) 64 ∗
       (lsLogFilterAddr ↦₆₄ 0#64)) ∗
      (ratchetAt A.repAlloc x.self x.G x.st ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       memRegion (s0.sp - 480#64) 384 ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool lim st s ∗ R) := by
    have hm1 := Satisfies.mono
      (sepConj_mono_left
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono (chainKeyBytes_entails_memRegion x.ckA x.ck)
              (sepConj_mono_left (memRegion_88_entails_dup_slots x.ret)))))) hm
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_slots
  rcases hm_slots with ⟨v20, v16, v8, v0, hm_slots⟩
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hvm1, hsp1, hsp1_align, htrace1, hP1⟩ :=
    sepWP_to_reaches_pc
      (cmk_dup_0xb4_placed_wp (A := A.repAlloc) x s0 s v0 v16 v20 v8
        hpc hrun hsp hsp_align htrace hx20 hx22 hx28)
      hm_slots hL
  have hm1' : s1.mem ⊨
      (consumeMessageKeyResultAt A.repAlloc x.ret (.error (.duplicatedMessage x.ck.index x.counter)) ∗
       (lsLogFilterAddr ↦₆₄ 0#64)) ∗
      (ratchetAt A.repAlloc x.self x.G x.st ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       memRegion (s0.sp - 480#64) 384 ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool lim st s1 ∗ R) := by
    have hm1a := Satisfies.mono (sepConj_mono_left hP1) hm1
    rw [A.pool_transport lim st s s1 hvm1]
    exact hm1a
  have hm1_ep : s1.mem ⊨
      (stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0) ∗
      (ratchetAt A.repAlloc x.self x.G (x.model F).2 ∗
       consumeMessageKeyResultAt A.repAlloc x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool lim st s1 ∗ R) := by
    rw [hmodel]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1'
  have hnpan : (x.model F).1 ≠ .error .panic := by
    rw [hmodel]; intro h; cases h
  have htouch : x.touched F = none := by
    unfold ConsumeMessageKeyGhost.touched; rw [hmodel]
  have hG' : x.G.AgreeExcept x.G (x.touched F) := by
    rw [htouch]; exact RatchetGhost.AgreeExcept.refl_none x.G
  exact reaches_outcome_steps hsteps1
    (cmk_epilogue_77c_placed_outcome hsb FreeOnlyEvs.nil x.G R s0 s1
      hpc1 hrun1 hsp1 hsp1_align htrace1 hnpan hG' hm1_ep)

end LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.DuplicatedMessageReturnBudget
