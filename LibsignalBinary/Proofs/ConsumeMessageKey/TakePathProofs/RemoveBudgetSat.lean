/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.RemoveBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# `HookSat` Sibling of `RemoveBudget` (`SegS1`, Block `24`, `+1508 .. +1916`)
(`LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.RemoveBudgetSat`)

Weakens the exact hook hypothesis `H cmkMemmoveSym = some hookMemmove` of
`LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.RemoveBudget` to
`HookSat H cmkMemmoveSym (sessionMemmoveBoundedBudgetSpec allocHookStack)` (discharging
`MemmoveArithBound mkPtr bs` from `A.block_valid`), with an unbounded
`sessionMemmoveBudgetSpec allocHookStack` corollary and `.toSat` instantiation from `hookMemmove`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.RemoveBudgetSat

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (MessageKeyGenerator)
open CryptoVerification (
  LibsignalPlacement blkLib_24 blkLib_eq_24 blkPC_24 blkPl_24 lsρ
)
open CryptoVerification.RustHeap (
  allocHookStack arrayAt vecBuf vecBuf_split_at
)
open CryptoVerification.LibsignalSessionRepr (
  MessageKeyGhost consumeMessageKeyResultAt messageKeyAt vecBuf_messageKeyAt_of_remove
)
open CryptoVerification.LibsignalSession (
  cmk_hook_ok_of_mem
)
open CryptoVerification.LibsignalTripleRatchet (
  sessionMemmoveSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemmoveBudgetSpec
)
open CryptoVerification.LibsignalSession.TakePath (
  cmkMemmoveSym elemAddr_add_104 entails_of_eq
  memRegion_136_entails_post_memmove_slots memRegion_384_entails_pre_memmove_slots
  ofNat_mkLen_sub_one remBytes_toNat_eq remove_final_stack_entails_memRegion_384
  sepWP_weaken_left vecBuf_split_entails_remove_ready
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks
)
open LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.RemoveBudget (
  cmk_remove_deallocVecs_placed_wp cmk_remove_post_memmove_placed_wp
  cmk_remove_pre_memmove_placed_wp cmk_remove_write_ok_placed_wp
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (
  MemmoveArithBound hookSat_sessionMemmoveBoundedBudget_of_exact
  hookSat_sessionMemmoveBoundedBudget_of_unbounded
  sessionMemmoveBoundedBudgetSpec sessionMemmoveBoundedBudgetSpec_eq_withVmPreserved
  sessionMemmoveBoundedSpec
)

attribute [local irreducible] Program.fetch Program.externAt?

private theorem blk24_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (blkLib_24).text = true := rfl

private theorem vmPreserved_trans {s₁ s₂ s₃ : State}
    (h12 : VmPreserved s₁ s₂) (h23 : VmPreserved s₂ s₃) : VmPreserved s₁ s₃ :=
  h12.trans h23

private theorem repAlloc_live_noWrap {M : AllocCostModel} (A : RustCliAllocBudget M)
    (p : BitVec 64) (n al : Nat) :
    A.repAlloc.live p n al ⊢ ⌜p.toNat + n < 2 ^ 64⌝ ∗ A.repAlloc.live p n al := by
  simp only [RustCliAllocBudget.repAlloc_live]
  refine Entails.trans (A.block_valid p n al) ?_
  apply Entails.pure_left
  rintro ⟨_, _, hnw, _⟩
  exact Entails.pure_right hnw (Entails.refl _)

private theorem remove_ready_with_noWrap {M : AllocCostModel} (A : RustCliAllocBudget M)
    (mkCap mkPtr : BitVec 64) (gks : List (MessageKeyGhost × MessageKeyGenerator))
    (p : Nat) (hp : p < gks.length) :
    (messageKeyAt A.repAlloc gks[p] (mkPtr + BitVec.ofNat 64 (p * 104)) ∗
      (⌜gks.length ≤ mkCap.toNat ∧ mkCap.toNat * 104 < 2 ^ 63 ∧ mkPtr ≠ 0 ∧ mkCap ≠ 0⌝ ∗
        A.repAlloc.live mkPtr (mkCap.toNat * 104) 8 ∗
        (arrayAt (messageKeyAt A.repAlloc) 104 mkPtr (gks.take p) ∗
         arrayAt (messageKeyAt A.repAlloc) 104 (mkPtr + BitVec.ofNat 64 ((p + 1) * 104))
           (gks.drop (p + 1))) ∗
        memRegion (mkPtr + BitVec.ofNat 64 (gks.length * 104)) ((mkCap.toNat - gks.length) * 104))) ⊢
    ⌜mkPtr.toNat + mkCap.toNat * 104 < 2 ^ 64⌝ ∗
    (messageKeyAt A.repAlloc gks[p] (mkPtr + BitVec.ofNat 64 (p * 104)) ∗
      (⌜gks.length ≤ mkCap.toNat ∧ mkCap.toNat * 104 < 2 ^ 63 ∧ mkPtr ≠ 0 ∧ mkCap ≠ 0⌝ ∗
        A.repAlloc.live mkPtr (mkCap.toNat * 104) 8 ∗
        (arrayAt (messageKeyAt A.repAlloc) 104 mkPtr (gks.take p) ∗
         arrayAt (messageKeyAt A.repAlloc) 104 (mkPtr + BitVec.ofNat 64 ((p + 1) * 104))
           (gks.drop (p + 1))) ∗
        memRegion (mkPtr + BitVec.ofNat 64 (gks.length * 104)) ((mkCap.toNat - gks.length) * 104))) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (repAlloc_live_noWrap A mkPtr (mkCap.toNat * 104) 8)))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

@[irreducible] def MemmoveBoundedPlacedAt [LibsignalPlacement]
    (H : String → Option (State → State)) (addr : BitVec 64) : Prop :=
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) addr
    (sessionMemmoveBoundedBudgetSpec allocHookStack)

theorem memmoveBoundedPlacedAt_of_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hmemmove : HookSat H cmkMemmoveSym (sessionMemmoveBoundedBudgetSpec allocHookStack)) :
    MemmoveBoundedPlacedAt H (lsρ cmkMemmoveSym) := by
  unfold MemmoveBoundedPlacedAt
  exact cmk_hook_ok_of_mem hmemmove

theorem call_memmove_bounded_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    {target_pc : BitVec 64}
    (hmemmove : MemmoveBoundedPlacedAt H (lsρ cmkMemmoveSym))
    (base : BitVec 64) (bs : List (BitVec 8)) (dst src len : Nat)
    (sp_val ret_pc : BitVec 64)
    {s : State} {Frame : SepProp} {post : State → SepProp → Prop}
    (hbound : MemmoveArithBound base bs)
    (hx0 : s.readReg64 .x0 = base + BitVec.ofNat 64 dst)
    (hx1 : s.readReg64 .x1 = base + BitVec.ofNat 64 src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hdst : dst + len ≤ bs.length)
    (hsrc : src + len ≤ bs.length)
    (hpc : s.pc = lsρ cmkMemmoveSym)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_val)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_val → CalleeSavedPreserved s sf → sf.trace = s.trace → VmPreserved s sf →
      SepWP ((blkPC_24).rebase (blkPl_24).base H) target_pc sf
        (((base ↦ₛ listMove bs dst src len) ∗ stackAt sp_val allocHookStack) ∗ Frame) post) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) target_pc s
      (((base ↦ₛ bs) ∗ stackAt sp_val allocHookStack) ∗ Frame) post := by
  unfold MemmoveBoundedPlacedAt at hmemmove
  refine SepWP.call_subroutine_frame hmemmove (x := (base, bs, dst, src, len)) (F := Frame)
    hpc hrun hsp_align hlr ?_ ?_ ?_ ?_
  · intro R hm
    simp only [sessionMemmoveBoundedBudgetSpec, sessionMemmoveBudgetSpec, sessionMemmoveSpec,
      libcMemmoveSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hbound, ⟨hx0, hx1, hx2, hdst, hsrc⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · intro _ _ _ hp
    exact not_satisfies_false_sepConj hp
  · intro _ _ _ _ he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    simp only [sessionMemmoveBoundedBudgetSpec, sessionMemmoveBudgetSpec, sessionMemmoveSpec,
      libcMemmoveSpec, hsp, sepConj_assoc]
    refine SepWP.pure_elim fun hvm => SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    simpa only [sepConj_assoc] using hnext sf h1 h2 (h3.trans hsp) h4 htr hvm

theorem cmk_memmove_placed_wp_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hmemmove_sat : HookSat H cmkMemmoveSym (sessionMemmoveBoundedBudgetSpec allocHookStack))
    (mkPtr : BitVec 64) (bs : List (BitVec 8)) (p mkLen : Nat)
    (v19 v21 v22 v24 v26 v29 : BitVec 64)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1580#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = mkPtr + BitVec.ofNat 64 (p * 104))
    (hx1 : s.readReg64 .x1 = mkPtr + BitVec.ofNat 64 ((p + 1) * 104))
    (hx2 : (s.readReg64 .x2).toNat = (mkLen - 1 - p) * 104)
    (hx19 : s.readReg64 .x19 = v19)
    (hx21 : s.readReg64 .x21 = v21)
    (hx22 : s.readReg64 .x22 = v22)
    (hx24 : s.readReg64 .x24 = v24)
    (hx26 : s.readReg64 .x26 = v26)
    (hx29 : s.readReg64 .x29 = v29)
    (hp : p < mkLen)
    (hbs_len : bs.length = mkLen * 104)
    (hbound : MemmoveArithBound mkPtr bs) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1584#64) s
      ((mkPtr ↦ₛ bs) ∗ stackAt (s0.sp - 480#64) allocHookStack)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x19 = v19 ∧
        s1.readReg64 .x21 = v21 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x26 = v26 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        VmPreserved s s1 ∧
        (P1 ⊢ (mkPtr ↦ₛ listMove bs (p * 104) ((p + 1) * 104) ((mkLen - 1 - p) * 104)) ∗
              stackAt (s0.sp - 480#64) allocHookStack)) := by
  have hmemmove : MemmoveBoundedPlacedAt H (lsρ cmkMemmoveSym) :=
    memmoveBoundedPlacedAt_of_sat hmemmove_sat
  have hdst : p * 104 + (mkLen - 1 - p) * 104 ≤ bs.length := by omega
  have hsrc : (p + 1) * 104 + (mkLen - 1 - p) * 104 ≤ bs.length := by omega
  apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
    blkLib_eq_24 blk24_noSvc0 (mid := lsρ cmkMemmoveSym)
  intro _m_strip
  wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
    (by simp only [wp_norm, arm64_norm, hrun]) fun _m_real _hnsp => ?_
  have hvm_bl : VmPreserved s _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  rw [← sepConj_emp ((mkPtr ↦ₛ bs) ∗ stackAt (s0.sp - 480#64) allocHookStack)]
  refine call_memmove_bounded_placed_wp hmemmove mkPtr bs (p * 104) ((p + 1) * 104)
    ((mkLen - 1 - p) * 104) (s0.sp - 480#64) ((blkPl_24).base + 1584#64) hbound
    (by simp only [wp_norm, arm64_norm, hx0]) (by simp only [wp_norm, arm64_norm, hx1])
    (by simp only [wp_norm, arm64_norm, hx2]) hdst hsrc
    (by simp only [wp_norm, arm64_norm, hpc]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_align)
    (by simp only [wp_norm, arm64_norm, hpc]) ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs htr_sf hvm_sf
  have hsp_align' : sf.spAligned = true := by
    rw [State.spAligned, hsp_sf]
    simpa [State.spAligned, hsp] using hsp_align
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm,
    hx19, hx21, hx22, hx24, hx26, hx29] at hcs
  rcases hcs with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩
  rw [sepConj_emp]
  refine SepWP.done hpc_sf hrun_sf ?_
  have htr_total : sf.trace = s.trace := by simpa only [wp_norm, arm64_norm] using htr_sf
  refine ⟨hsp_sf, hsp_align', hcs19, hcs21, hcs22, hcs24, hcs26, hcs29,
    ⟨htr_total, hcsv⟩, vmPreserved_trans hvm_bl hvm_sf, Entails.refl _⟩

theorem cmk_remove_0x5e4_placed_wp_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A lim H)
    (hmemmove_sat : HookSat H cmkMemmoveSym (sessionMemmoveBoundedBudgetSpec allocHookStack))
    (mkCap mkPtr chAddr ret : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator))
    (p : Nat) (hp : p < gks.length)
    (st : M.σ) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 ((gks.length - 1 - p) * 104))
    (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = chAddr)
    (hx22 : s.readReg64 .x22 = ret)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 gks.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1916#64) s
      (A.pool lim st s ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       memRegion (s0.sp - 480#64) 384 ∗
       memRegion ret 88 ∗
       ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
       vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) mkCap mkPtr gks)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P1 ⊢
            A.pool lim (M.stepEvents evs st) s1 ∗
            stackAt (s0.sp - 480#64) allocHookStack ∗
            memRegion (s0.sp - 480#64) 384 ∗
            consumeMessageKeyResultAt A.repAlloc ret (.ok gks[p].2) ∗
            ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 (gks.length - 1)) ∗
            vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) mkCap mkPtr (gks.eraseIdx p))) := by
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (memRegion_384_entails_pre_memmove_slots s0.sp)
        (sepConj_mono_right (sepConj_mono_right
          (vecBuf_split_at A.repAlloc 104 8 (messageKeyAt A.repAlloc) mkCap mkPtr gks hp)))))) ?_
  wp_pull_exists
  wp_seq_frame
    (cmk_remove_pre_memmove_placed_wp (A := A) gks[p] (mkPtr + BitVec.ofNat 64 (p * 104)) chAddr ret
      (BitVec.ofNat 64 ((gks.length - 1 - p) * 104)) (BitVec.ofNat 64 gks.length)
      _ _ _ _ _ _ _ _ _ _ s0 s
      hpc hrun hsp hsp_align hx2 hx8 hx19 hx22 hx24 hx29)
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, halign1, hx0_1, hx1_1, hx2_1, hx19_1, hx21_1, hx22_1,
    hx23_1, hx24_1, hx25_1, hx26_1, hx29_1, htr1, hvm1, hP1⟩
  refine sepWP_weaken_left hP1 ?_
  rw [← A.pool_of_vmPreserved hvm1]
  have hre1 :
      ((messageKeyAt A.repAlloc gks[p] (mkPtr + BitVec.ofNat 64 (p * 104)) ∗
         ((s0.sp - 424#64) ↦₆₄ 0#64) ∗
         ((s0.sp - 416#64) ↦₆₄ gks[p].1.mac.ptr) ∗
         ((s0.sp - 408#64) ↦₆₄ gks[p].1.iv.ptr) ∗
         ((s0.sp - 400#64) ↦₆₄ gks[p].1.cipher.ptr) ∗
         ((s0.sp - 388#64) ↦₃₂ gks[p].2.counter) ∗
         ((s0.sp - 384#64) ↦₆₄ gks[p].1.mac.cap) ∗
         ((s0.sp - 376#64) ↦₆₄ gks[p].1.iv.cap) ∗
         ((s0.sp - 368#64) ↦₆₄ ret) ∗
         ((s0.sp - 224#64) ↦₆₄ gks[p].1.seed.cap) ∗
         ((s0.sp - 216#64) ↦₆₄ gks[p].1.seed.ptr)) ∗
       (A.pool lim st s1 ∗
        stackAt (s0.sp - 480#64) allocHookStack ∗
        memRegion (s0.sp - 480#64) 56 ∗
        memRegion (s0.sp - 392#64) 4 ∗
        memRegion (s0.sp - 360#64) 136 ∗
        memRegion (s0.sp - 208#64) 112 ∗
        memRegion ret 88 ∗
        ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
        ⌜gks.length ≤ mkCap.toNat ∧ mkCap.toNat * 104 < 2 ^ 63 ∧ mkPtr ≠ 0 ∧ mkCap ≠ 0⌝ ∗
        A.repAlloc.live mkPtr (mkCap.toNat * 104) 8 ∗
        arrayAt (messageKeyAt A.repAlloc) 104 mkPtr (gks.take p) ∗
        arrayAt (messageKeyAt A.repAlloc) 104 (mkPtr + BitVec.ofNat 64 ((p + 1) * 104)) (gks.drop (p + 1)) ∗
        memRegion (mkPtr + BitVec.ofNat 64 (gks.length * 104)) ((mkCap.toNat - gks.length) * 104))) =
      ((messageKeyAt A.repAlloc gks[p] (mkPtr + BitVec.ofNat 64 (p * 104)) ∗
        (⌜gks.length ≤ mkCap.toNat ∧ mkCap.toNat * 104 < 2 ^ 63 ∧ mkPtr ≠ 0 ∧ mkCap ≠ 0⌝ ∗
          A.repAlloc.live mkPtr (mkCap.toNat * 104) 8 ∗
          (arrayAt (messageKeyAt A.repAlloc) 104 mkPtr (gks.take p) ∗
           arrayAt (messageKeyAt A.repAlloc) 104 (mkPtr + BitVec.ofNat 64 ((p + 1) * 104)) (gks.drop (p + 1))) ∗
          memRegion (mkPtr + BitVec.ofNat 64 (gks.length * 104)) ((mkCap.toNat - gks.length) * 104))) ∗
       memRegion (s0.sp - 360#64) 136 ∗
       A.pool lim st s1 ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       memRegion (s0.sp - 480#64) 56 ∗
       ((s0.sp - 424#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 416#64) ↦₆₄ gks[p].1.mac.ptr) ∗
       ((s0.sp - 408#64) ↦₆₄ gks[p].1.iv.ptr) ∗
       ((s0.sp - 400#64) ↦₆₄ gks[p].1.cipher.ptr) ∗
       memRegion (s0.sp - 392#64) 4 ∗
       ((s0.sp - 388#64) ↦₃₂ gks[p].2.counter) ∗
       ((s0.sp - 384#64) ↦₆₄ gks[p].1.mac.cap) ∗
       ((s0.sp - 376#64) ↦₆₄ gks[p].1.iv.cap) ∗
       ((s0.sp - 368#64) ↦₆₄ ret) ∗
       ((s0.sp - 224#64) ↦₆₄ gks[p].1.seed.cap) ∗
       ((s0.sp - 216#64) ↦₆₄ gks[p].1.seed.ptr) ∗
       memRegion (s0.sp - 208#64) 112 ∗
       memRegion ret 88 ∗
       ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length)) := by
    sep_ac_rfl
  rw [hre1]
  refine SepWP.weaken_pre (sepConj_mono_left (remove_ready_with_noWrap A mkCap mkPtr gks p hp)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hmkPtr_nw => ?_
  refine SepWP.weaken_pre
    (sepConj_mono (vecBuf_split_entails_remove_ready A.repAlloc mkCap mkPtr gks hp)
      (sepConj_mono_left (memRegion_136_entails_post_memmove_slots s0.sp))) ?_
  wp_pull_exists
  refine SepWP.pure_elim ?_
  rintro ⟨hbs, hbs_len, hlen_le, hcap_lt, hptr_ne, hseed_ne, hcipher_lt, hseed_le, hseed_lt⟩
  have hbound : MemmoveArithBound mkPtr _ :=
    ⟨by rw [hbs_len]; omega, by rw [hbs_len]; omega⟩
  have hx1_1' : s1.readReg64 .x1 = mkPtr + BitVec.ofNat 64 ((p + 1) * 104) := by
    rw [hx1_1, elemAddr_add_104]
  have hx2_1' : (s1.readReg64 .x2).toNat = (gks.length - 1 - p) * 104 := by
    rw [hx2_1, remBytes_toNat_eq hlen_le hcap_lt]
  wp_seq_frame
    (cmk_memmove_placed_wp_sat hmemmove_sat mkPtr _ p gks.length chAddr
      (BitVec.ofNat 64 gks[p].2.seed.length) (s0.sp - 224#64) (BitVec.ofNat 64 gks.length)
      gks[p].1.cipher.cap (s0.sp - 96#64)
      s0 s1 hpc1 hrun1 hsp1 halign1 hx0_1 hx1_1' hx2_1'
      hx19_1 hx21_1 hx22_1 hx24_1 hx26_1 hx29_1 hp hbs_len hbound)
  rintro s2 P2 hpc2 hrun2 ⟨hsp2, halign2, hx19_2, hx21_2, hx22_2, hx24_2, hx26_2, hx29_2, htr2, hvm2, hP2⟩
  refine sepWP_weaken_left hP2 ?_
  rw [← A.pool_of_vmPreserved hvm2]
  wp_seq_frame
    (cmk_remove_post_memmove_placed_wp gks[p] chAddr gks.length _ _ s0 s2
      hpc2 hrun2 hsp2 halign2 hx19_2 hx21_2 hx22_2 hx24_2 hx26_2 hx29_2
      hcipher_lt hseed_ne hseed_le hseed_lt)
  rintro s3 P3 hpc3 hrun3
    ⟨hsp3, halign3, hx19_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx29_3, htr3, hvm3, hP3⟩
  refine sepWP_weaken_left hP3 ?_
  rw [← A.pool_of_vmPreserved hvm3]
  simp only [RustCliAllocBudget.repAlloc_live]
  wp_seq_frame
    (cmk_remove_deallocVecs_placed_wp hA gks[p] ret _ _ _ _ st s0 s3
      hpc3 hrun3 hsp3 halign3 hx19_3 hx21_3 hx22_3 hx23_3 hx26_3 hx29_3)
  rintro s4 P4 hpc4 hrun4
    ⟨hsp4, halign4, hx19_4, hx22_4, hx23_4, hx25_4, hx26_4, hx27_4, hx29_4, htr4, evs, hfree, hP4⟩
  refine sepWP_weaken_left hP4 ?_
  wp_seq_frame
    (cmk_remove_write_ok_placed_wp (A := A) gks[p] ret s0 s4
      hpc4 hrun4 hsp4 halign4 hx19_4 hx22_4 hx23_4 hx25_4 hx26_4 hx27_4 hx29_4)
  rintro s5 P5 hpc5 hrun5 ⟨hsp5, halign5, hx29_5, htr5, hvm5, hP5⟩
  refine sepWP_weaken_left hP5 ?_
  rw [← A.pool_of_vmPreserved hvm5]
  refine SepWP.done hpc5 hrun5 ?_
  refine ⟨hsp5, halign5, hx29_5, by reg_chain, evs, hfree, ?_⟩
  rw [ofNat_mkLen_sub_one hp]
  have hof_rem := vecBuf_messageKeyAt_of_remove A.repAlloc mkCap mkPtr hbs hp hlen_le hcap_lt hptr_ne
  simp only [RustCliAllocBudget.repAlloc_live] at hof_rem ⊢
  exact entails_of_eq (by sep_ac_rfl)
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (remove_final_stack_entails_memRegion_384 s0.sp
        gks[p].1.seed.cap gks[p].1.seed.ptr gks[p].1.seed.ptr)
        (sepConj_mono_right (sepConj_mono_right hof_rem)))))

theorem cmk_remove_0x5e4_placed_wp_unbounded_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A lim H)
    (hmemmove_sat : HookSat H cmkMemmoveSym (sessionMemmoveBudgetSpec allocHookStack))
    (mkCap mkPtr chAddr ret : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator))
    (p : Nat) (hp : p < gks.length)
    (st : M.σ) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 ((gks.length - 1 - p) * 104))
    (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = chAddr)
    (hx22 : s.readReg64 .x22 = ret)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 gks.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1916#64) s
      (A.pool lim st s ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       memRegion (s0.sp - 480#64) 384 ∗
       memRegion ret 88 ∗
       ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
       vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) mkCap mkPtr gks)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P1 ⊢
            A.pool lim (M.stepEvents evs st) s1 ∗
            stackAt (s0.sp - 480#64) allocHookStack ∗
            memRegion (s0.sp - 480#64) 384 ∗
            consumeMessageKeyResultAt A.repAlloc ret (.ok gks[p].2) ∗
            ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 (gks.length - 1)) ∗
            vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) mkCap mkPtr (gks.eraseIdx p))) :=
  cmk_remove_0x5e4_placed_wp_sat hA
    (hookSat_sessionMemmoveBoundedBudget_of_unbounded allocHookStack hmemmove_sat)
    mkCap mkPtr chAddr ret gks p hp st s0 s hpc hrun hsp hsp_align hx2 hx8 hx19 hx22 hx24 hx29

theorem cmk_remove_0x5e4_placed_wp_of_exact [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A lim H)
    (hmemmove_eq : H cmkMemmoveSym = some hookMemmove)
    (mkCap mkPtr chAddr ret : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator))
    (p : Nat) (hp : p < gks.length)
    (st : M.σ) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 ((gks.length - 1 - p) * 104))
    (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = chAddr)
    (hx22 : s.readReg64 .x22 = ret)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 gks.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1916#64) s
      (A.pool lim st s ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       memRegion (s0.sp - 480#64) 384 ∗
       memRegion ret 88 ∗
       ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
       vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) mkCap mkPtr gks)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P1 ⊢
            A.pool lim (M.stepEvents evs st) s1 ∗
            stackAt (s0.sp - 480#64) allocHookStack ∗
            memRegion (s0.sp - 480#64) 384 ∗
            consumeMessageKeyResultAt A.repAlloc ret (.ok gks[p].2) ∗
            ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 (gks.length - 1)) ∗
            vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) mkCap mkPtr (gks.eraseIdx p))) :=
  cmk_remove_0x5e4_placed_wp_sat hA
    (hookSat_sessionMemmoveBoundedBudget_of_exact allocHookStack hmemmove_eq)
    mkCap mkPtr chAddr ret gks p hp st s0 s hpc hrun hsp hsp_align hx2 hx8 hx19 hx22 hx24 hx29

end LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.RemoveBudgetSat
