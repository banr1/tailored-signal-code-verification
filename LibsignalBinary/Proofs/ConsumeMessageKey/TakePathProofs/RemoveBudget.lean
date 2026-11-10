/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.CommonBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Remove
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `remove(p)` and `Ok(mk)` Return Block (Block 24, `+1508 .. +1916`)

Threads `A.pool lim st s`, `FreeOnlyEvs`, and `VmPreserved` across `memmove` and the three optional
`Vec<u8>` deallocations (`cipher`, `mac`, `iv`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.RemoveBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (MessageKeyGenerator)
open CryptoVerification (
  LibsignalPlacement blkLib_24 blkLib_eq_24 blkPC_24 blkPl_24 lsρ
)
open CryptoVerification.RustHeap (
  allocHookStack arrayAt vecBuf vecBuf_split_at vecU8Buf
)
open CryptoVerification.LibsignalSessionRepr (
  MessageKeyGhost consumeMessageKeyResultAt messageKeyAt vecBuf_messageKeyAt_of_remove
)
open CryptoVerification.LibsignalSession (
  cmkRustDeallocSym cmk_hook_ok_of_mem
)
open CryptoVerification.LibsignalSession.TakePath (
  cipher_cap_add_one_ne_zero cmkMemmoveSym
  deallocVecs_slots_entails_memRegion_56 elemAddr_add_104 entails_of_eq
  hookMemmove_trace_ok memRegion_136_entails_post_memmove_slots
  memRegion_384_entails_pre_memmove_slots memRegion_56_entails_write_ok_slots
  memRegion_80_entails_write_ok_slots memRegion_88_entails_ret_ok_slots
  memmoveTraceSpec messageKeyAt_eq_cells_sep_heap ofNat_mkLen_sub_one
  pointsTo64_eq_unaligned_2_1_4_1 pointsTo64_pair_eq_unaligned_16 remBytes_toNat_eq
  remove_final_stack_entails_memRegion_384 seed_len_b2_eq seed_len_b3456_eq
  seed_len_b7_eq seed_len_lo16_eq seed_len_ofNat_ne_zero seed_ptr_reassemble
  sepWP_weaken_left shiftLeft_40_eq_and_mask24 shift_ret_68 shift_sp_256
  vecBuf_split_entails_remove_ready write_ok_post_entails
)
open CryptoVerification.LibsignalSession.TakePath.RemoveBvArith (
  bv_add_add_lit
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
  VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks
)
open LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.CommonBudget (
  dealloc_placed_ok_at
)

attribute [local irreducible] Program.fetch Program.externAt?

private theorem blk24_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (blkLib_24).text = true := rfl

private theorem seed_len_b2_eq' (len : BitVec 64) :
    BitVec.truncate 8 (BitVec.truncate 32 (((len &&& 16777215#64) <<< 40) >>> 40) >>> 16) =
      len.extractLsb' 16 8 := by
  bv_kernel

private theorem vmPreserved_trans {s₁ s₂ s₃ : State}
    (h12 : VmPreserved s₁ s₂) (h23 : VmPreserved s₂ s₃) : VmPreserved s₁ s₃ :=
  h12.trans h23

private theorem vmPreserved_hookMemmove (s : State) : VmPreserved s (hookMemmove s) := by
  dsimp only [hookMemmove, hookMemcpy, retHook]
  simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

private theorem pool_dealloc_reassoc (pool live mem stk slot : SepProp) :
    (pool ∗ live ∗ mem ∗ stk ∗ slot) = ((pool ∗ live ∗ mem ∗ stk) ∗ slot) := by
  sep_ac_rfl

@[irreducible] def DeallocPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) (addr : BitVec 64) : Prop :=
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) addr (rustCliDeallocBudgetSpec M A lim)

theorem deallocPlacedAt_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A lim H) :
    DeallocPlacedAt A lim H (lsρ cmkRustDeallocSym) := by
  unfold DeallocPlacedAt
  exact dealloc_placed_ok_at hA

theorem call_dealloc_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {target_pc : BitVec 64}
    (hdealloc : DeallocPlacedAt A lim H (lsρ cmkRustDeallocSym))
    (p : BitVec 64) (size align : Nat) (st : M.σ) (sp_val ret_pc : BitVec 64)
    {s : State} {Frame : SepProp} {post : State → SepProp → Prop}
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hpc : s.pc = lsρ cmkRustDeallocSym)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_val)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_val → CalleeSavedPreserved s sf → sf.trace = s.trace →
      SepWP ((blkPC_24).rebase (blkPl_24).base H) target_pc sf
        (A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗
          stackAt sp_val allocHookStack ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      simp (config := { decide := true }) only [wp_norm, arm64_norm]) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) target_pc s
      ((A.pool lim st s ∗ A.live p size align ∗ memRegion p size ∗
          stackAt sp_val allocHookStack) ∗ Frame) post := by
  unfold DeallocPlacedAt at hdealloc
  refine SepWP.call_subroutine_frame hdealloc (x := (p, size, align, st)) (F := Frame)
    hpc hrun hsp_align hlr ?_ ?_ ?_ ?_
  · intro R hm
    simp only [rustCliDeallocBudgetSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlr.symm ▸ hlr_ls⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · intro _ _ _ hp
    exact not_satisfies_false_sepConj hp
  · intro _ _ _ _ he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    simp only [rustCliDeallocBudgetSpec, hsp, sepConj_assoc]
    exact SepWP.pure_elim fun ⟨hacp, _⟩ => hnext sf h1 h2 (h3.trans hsp) h4 hacp.2.1

@[irreducible] def MemmovePlacedAt [LibsignalPlacement]
    (H : String → Option (State → State)) (addr : BitVec 64) : Prop :=
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) addr
    (withVmPreserved (memmoveTraceSpec allocHookStack))

theorem memmovePlacedAt_eq [LibsignalPlacement]
    {H : String → Option (State → State)} (hmemmove : H cmkMemmoveSym = some hookMemmove) :
    MemmovePlacedAt H (lsρ cmkMemmoveSym) := by
  unfold MemmovePlacedAt
  exact cmk_hook_ok_of_mem (hookSat_withVmPreserved
    ⟨hookMemmove, hmemmove, hookMemmove_trace_ok allocHookStack⟩
    fun f hf s => by cases hmemmove.symm.trans hf; exact vmPreserved_hookMemmove s)

theorem call_memmove_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    {target_pc : BitVec 64}
    (hmemmove : MemmovePlacedAt H (lsρ cmkMemmoveSym))
    (base : BitVec 64) (bs : List (BitVec 8)) (dst src len : Nat)
    (sp_val ret_pc : BitVec 64)
    {s : State} {Frame : SepProp} {post : State → SepProp → Prop}
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
  unfold MemmovePlacedAt at hmemmove
  refine SepWP.call_subroutine_frame hmemmove (x := (base, bs, dst, src, len)) (F := Frame)
    hpc hrun hsp_align hlr ?_ ?_ ?_ ?_
  · intro R hm
    simp only [withVmPreserved, memmoveTraceSpec, libcMemmoveSpec, hsp, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hdst, hsrc⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · intro _ _ _ hp
    exact not_satisfies_false_sepConj hp
  · intro _ _ _ _ he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    simp only [withVmPreserved, memmoveTraceSpec, libcMemmoveSpec, hsp, sepConj_assoc]
    refine SepWP.pure_elim fun hvm => SepWP.pure_elim fun htr => SepWP.pure_elim fun _ => ?_
    simpa only [sepConj_assoc] using hnext sf h1 h2 (h3.trans hsp) h4 htr hvm

theorem cmk_remove_pre_memmove_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {H : String → Option (State → State)} {A : RustCliAllocBudget M}
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (elemAddr chAddr ret : BitVec 64)
    (remBytes mkLen : BitVec 64)
    (v424 v416 v408 v400 v384 v376 v368 v224 v216 : BitVec 64)
    (v388 : BitVec 32)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = remBytes)
    (hx8 : s.readReg64 .x8 = elemAddr + 56#64)
    (hx19 : s.readReg64 .x19 = chAddr)
    (hx22 : s.readReg64 .x22 = ret)
    (hx24 : s.readReg64 .x24 = mkLen)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1580#64) s
      (messageKeyAt A.repAlloc gk elemAddr ∗
       ((s0.sp - 424#64) ↦₆₄ v424) ∗
       ((s0.sp - 416#64) ↦₆₄ v416) ∗
       ((s0.sp - 408#64) ↦₆₄ v408) ∗
       ((s0.sp - 400#64) ↦₆₄ v400) ∗
       ((s0.sp - 388#64) ↦₃₂ v388) ∗
       ((s0.sp - 384#64) ↦₆₄ v384) ∗
       ((s0.sp - 376#64) ↦₆₄ v376) ∗
       ((s0.sp - 368#64) ↦₆₄ v368) ∗
       ((s0.sp - 224#64) ↦₆₄ v224) ∗
       ((s0.sp - 216#64) ↦₆₄ v216))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x0 = elemAddr ∧
        s1.readReg64 .x1 = elemAddr + 104#64 ∧
        s1.readReg64 .x2 = remBytes ∧
        s1.readReg64 .x19 = chAddr ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 gk.2.seed.length ∧
        s1.readReg64 .x22 = s0.sp - 224#64 ∧
        s1.readReg64 .x23 = 0#64 ∧
        s1.readReg64 .x24 = mkLen ∧
        s1.readReg64 .x25 = 0#64 ∧
        s1.readReg64 .x26 = gk.1.cipher.cap ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        VmPreserved s s1 ∧
        (P1 ⊢
          messageKeyAt A.repAlloc gk elemAddr ∗
          ((s0.sp - 424#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 416#64) ↦₆₄ gk.1.mac.ptr) ∗
          ((s0.sp - 408#64) ↦₆₄ gk.1.iv.ptr) ∗
          ((s0.sp - 400#64) ↦₆₄ gk.1.cipher.ptr) ∗
          ((s0.sp - 388#64) ↦₃₂ gk.2.counter) ∗
          ((s0.sp - 384#64) ↦₆₄ gk.1.mac.cap) ∗
          ((s0.sp - 376#64) ↦₆₄ gk.1.iv.cap) ∗
          ((s0.sp - 368#64) ↦₆₄ ret) ∗
          ((s0.sp - 224#64) ↦₆₄ gk.1.seed.cap) ∗
          ((s0.sp - 216#64) ↦₆₄ gk.1.seed.ptr))) := by
  apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
    blkLib_eq_24 blk24_noSvc0 (mid := (blkPl_24).base + 1580#64)
  intro _m_strip
  rw [messageKeyAt_eq_cells_sep_heap]
  simp only [sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
    (by simp only [wp_norm, arm64_norm, hrun]) fun _m_real _hnsp => ?_
  have hvm : VmPreserved s _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
    (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp],
    by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm, hx8], by simp only [wp_norm, arm64_norm, hx8],
    by simp only [wp_norm, arm64_norm, hx2], by simp only [wp_norm, arm64_norm, hx19],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hsp],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx24],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm, hx29],
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm]⟩,
    hvm, Entails.refl _⟩

theorem cmk_memmove_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hmemmove_eq : H cmkMemmoveSym = some hookMemmove)
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
    (hbs_len : bs.length = mkLen * 104) :
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
  have hmemmove : MemmovePlacedAt H (lsρ cmkMemmoveSym) := memmovePlacedAt_eq hmemmove_eq
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
  refine call_memmove_placed_wp hmemmove mkPtr bs (p * 104) ((p + 1) * 104)
    ((mkLen - 1 - p) * 104) (s0.sp - 480#64) ((blkPl_24).base + 1584#64)
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

theorem cmk_remove_post_memmove_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (chAddr : BitVec 64) (mkLen : Nat)
    (v320 v312 : BitVec 64)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1584#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = chAddr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 gk.2.seed.length)
    (hx22 : s.readReg64 .x22 = s0.sp - 224#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 mkLen)
    (hx26 : s.readReg64 .x26 = gk.1.cipher.cap)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hcipher_lt : gk.1.cipher.cap.toNat < 2 ^ 63)
    (hseed_ne : gk.2.seed ≠ [])
    (hseed_le : gk.2.seed.length ≤ gk.1.seed.cap.toNat)
    (hseed_lt : gk.1.seed.cap.toNat < 2 ^ 63) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1648#64) s
      (((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 mkLen) ∗
       ((s0.sp - 320#64) ↦₆₄ v320) ∗
       ((s0.sp - 312#64) ↦₆₄ v312) ∗
       ((s0.sp - 224#64) ↦₆₄ gk.1.seed.cap) ∗
       ((s0.sp - 216#64) ↦₆₄ gk.1.seed.ptr))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x19 =
          (gk.1.seed.ptr.extractLsb' 16 8 ++ gk.1.seed.ptr.extractLsb' 8 8 ++
           gk.1.seed.ptr.extractLsb' 0 8 ++ gk.1.seed.cap.extractLsb' 56 8 ++
           gk.1.seed.cap.extractLsb' 48 8 ++ gk.1.seed.cap.extractLsb' 40 8 ++
           gk.1.seed.cap.extractLsb' 32 8 ++ gk.1.seed.cap.extractLsb' 24 8) ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 gk.2.seed.length ∧
        s1.readReg64 .x22 = (gk.1.seed.ptr.extractLsb' 56 8).zeroExtend 64 ∧
        s1.readReg64 .x23 =
          (gk.1.seed.ptr.extractLsb' 48 8 ++ gk.1.seed.ptr.extractLsb' 40 8 ++
           gk.1.seed.ptr.extractLsb' 32 8 ++ gk.1.seed.ptr.extractLsb' 24 8).zeroExtend 64 ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 mkLen ∧
        s1.readReg64 .x26 = gk.1.cipher.cap ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        VmPreserved s s1 ∧
        (P1 ⊢
          ((chAddr + 64#64) ↦₆₄ (BitVec.ofNat 64 mkLen - 1#64)) ∗
          ((s0.sp - 320#64) ↦₆₄ gk.1.seed.cap) ∗
          ((s0.sp - 312#64) ↦₆₄ gk.1.seed.ptr) ∗
          ((s0.sp - 224#64) ↦₆₄ gk.1.seed.cap) ∗
          ((s0.sp - 216#64) ↦₆₄ gk.1.seed.ptr))) := by
  have hcipher_ne : gk.1.cipher.cap + 1#64 ≠ 0#64 := cipher_cap_add_one_ne_zero hcipher_lt
  have hseed_nz : BitVec.ofNat 64 gk.2.seed.length ≠ 0#64 :=
    seed_len_ofNat_ne_zero hseed_ne hseed_le hseed_lt
  apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
    blkLib_eq_24 blk24_noSvc0 (mid := (blkPl_24).base + 1648#64)
  intro _m_strip
  wp_step
  wp_step
  wp_step
  wp_step
  apply SepWP.ite_false (by rfl) (by simp [hcipher_ne])
  wp_step
  wp_step
  wp_step
  wp_step
  apply SepWP.ite_false (by rfl) (by simp [hseed_nz])
  have h312 : (s0.sp - 320#64) + 8#64 = s0.sp - 312#64 := by bv_omega
  have h216 : (s0.sp - 224#64) + 8#64 = s0.sp - 216#64 := by bv_omega
  wp_simp_pre only [arm64_norm]
  conv =>
    arg 4
    rw [← sepConj_assoc ((s0.sp - 320#64) ↦₆₄ gk.1.seed.cap) ((s0.sp - 312#64) ↦₆₄ gk.1.seed.ptr),
        ← h312, pointsTo64_pair_eq_unaligned_16 (s0.sp - 320#64) gk.1.seed.cap gk.1.seed.ptr,
        ← h216, pointsTo64_pair_eq_unaligned_16 (s0.sp - 224#64) gk.1.seed.cap gk.1.seed.ptr]
    simp only [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
    (by simp only [wp_norm, arm64_norm, hrun]) fun _m_real _hnsp => ?_
  have hvm : VmPreserved s _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
    (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp],
    by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx21],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm, hx24], by simp only [wp_norm, arm64_norm, hx26],
    by simp only [wp_norm, arm64_norm, hx29],
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm]⟩, hvm, ?_⟩
  conv =>
    rhs
    rw [← sepConj_assoc ((s0.sp - 320#64) ↦₆₄ gk.1.seed.cap) ((s0.sp - 312#64) ↦₆₄ gk.1.seed.ptr),
        ← h312, pointsTo64_pair_eq_unaligned_16 (s0.sp - 320#64) gk.1.seed.cap gk.1.seed.ptr,
        ← h216, pointsTo64_pair_eq_unaligned_16 (s0.sp - 224#64) gk.1.seed.cap gk.1.seed.ptr]
    simp only [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
  simp only [arm64_norm, truncate_16_zeroExtend_32]
  exact Entails.refl _

theorem cmk_dealloc_cipher_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A lim H)
    (cap ptr : BitVec 64) (st : M.σ) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1648#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx26 : s.readReg64 .x26 = cap) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1668#64) s
      (A.pool lim st s ∗
       (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       ((s0.sp - 400#64) ↦₆₄ ptr))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        CalleeSavedPreserved s s1 ∧
        s1.trace = s.trace ∧
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P1 ⊢ A.pool lim (M.stepEvents evs st) s1 ∗
            stackAt (s0.sp - 480#64) allocHookStack ∗ ((s0.sp - 400#64) ↦₆₄ ptr))) := by
  have hdealloc := deallocPlacedAt_of_hooks hA
  by_cases hcap : cap = 0
  · subst hcap
    simp only [↓reduceIte, emp_sepConj]
    apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
      blkLib_eq_24 blk24_noSvc0 (mid := (blkPl_24).base + 1668#64)
    intro _m_strip
    wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc, hx26])
      (by simp only [wp_norm, arm64_norm, hrun]) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc, hx26])
      (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm, hsp],
      by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_align, ?_,
      by simp only [wp_norm, arm64_norm], [], FreeOnlyEvs.nil, Entails.refl _⟩
    simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm]
  · simp only [hcap, ↓reduceIte]
    apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
      blkLib_eq_24 blk24_noSvc0 (mid := lsρ cmkRustDeallocSym)
    intro _m_strip
    wp_step
    apply SepWP.ite_false (by rfl) (by simp [hx26]; exact hcap)
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
      (by simp only [wp_norm, arm64_norm, hrun]) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    rw [pool_dealloc_reassoc]
    refine call_dealloc_placed_wp hdealloc ptr cap.toNat 1 st
      (s0.sp - 480#64) ((blkPl_24).base + 1668#64) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hx26]
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hpc]
    · simp only [wp_norm, arm64_norm, hrun]
    · simp only [wp_norm, arm64_norm, hsp]
    · simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_align
    · simp only [wp_norm, arm64_norm, hpc]
    · intro sf hpc_sf hrun_sf hsp_sf hcs htr_sf
      have hsp_align' : sf.spAligned = true := by
        rw [State.spAligned, hsp_sf]
        simpa [State.spAligned, hsp] using hsp_align
      refine SepWP.done hpc_sf hrun_sf
        ⟨hsp_sf, hsp_align', ?_, by simp only [wp_norm, arm64_norm, htr_sf],
         rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat, Entails.refl _⟩
      simpa (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm] using hcs

theorem cmk_dealloc_mac_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A lim H)
    (cap ptr : BitVec 64) (st : M.σ) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1688#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = cap) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1704#64) s
      (A.pool lim st s ∗
       (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       ((s0.sp - 416#64) ↦₆₄ ptr))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        CalleeSavedPreserved s s1 ∧
        s1.trace = s.trace ∧
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P1 ⊢ A.pool lim (M.stepEvents evs st) s1 ∗
            stackAt (s0.sp - 480#64) allocHookStack ∗ ((s0.sp - 416#64) ↦₆₄ ptr))) := by
  have hdealloc := deallocPlacedAt_of_hooks hA
  by_cases hcap : cap = 0
  · subst hcap
    simp only [↓reduceIte, emp_sepConj]
    apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
      blkLib_eq_24 blk24_noSvc0 (mid := (blkPl_24).base + 1704#64)
    intro _m_strip
    wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc, hx1])
      (by simp only [wp_norm, arm64_norm, hrun]) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc, hx1])
      (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm, hsp],
      by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_align, ?_,
      by simp only [wp_norm, arm64_norm], [], FreeOnlyEvs.nil, Entails.refl _⟩
    simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm]
  · simp only [hcap, ↓reduceIte]
    apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
      blkLib_eq_24 blk24_noSvc0 (mid := lsρ cmkRustDeallocSym)
    intro _m_strip
    wp_step
    apply SepWP.ite_false (by rfl) (by simp [hx1]; exact hcap)
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
      (by simp only [wp_norm, arm64_norm, hrun]) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    rw [pool_dealloc_reassoc]
    refine call_dealloc_placed_wp hdealloc ptr cap.toNat 1 st
      (s0.sp - 480#64) ((blkPl_24).base + 1704#64) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hx1]
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hpc]
    · simp only [wp_norm, arm64_norm, hrun]
    · simp only [wp_norm, arm64_norm, hsp]
    · simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_align
    · simp only [wp_norm, arm64_norm, hpc]
    · intro sf hpc_sf hrun_sf hsp_sf hcs htr_sf
      have hsp_align' : sf.spAligned = true := by
        rw [State.spAligned, hsp_sf]
        simpa [State.spAligned, hsp] using hsp_align
      refine SepWP.done hpc_sf hrun_sf
        ⟨hsp_sf, hsp_align', ?_, by simp only [wp_norm, arm64_norm, htr_sf],
         rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat, Entails.refl _⟩
      simpa (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm] using hcs

theorem cmk_dealloc_iv_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A lim H)
    (cap ptr v19 v22 v23 v26 v27 v29 : BitVec 64) (counter : BitVec 32)
    (st : M.σ) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1724#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = cap)
    (hx9 : s.readReg64 .x9 = counter.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = v19)
    (hx22 : s.readReg64 .x22 = v22)
    (hx23 : s.readReg64 .x23 = v23)
    (hx25 : s.readReg64 .x25 = counter.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = v26)
    (hx27 : s.readReg64 .x27 = v27)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1768#64) s
      (A.pool lim st s ∗
       (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       ((s0.sp - 408#64) ↦₆₄ ptr))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x19 = v19 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x23 = v23 ∧
        s1.readReg64 .x25 = counter.zeroExtend 64 ∧
        s1.readReg64 .x26 = v26 ∧
        s1.readReg64 .x27 = v27 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P1 ⊢ A.pool lim (M.stepEvents evs st) s1 ∗
            stackAt (s0.sp - 480#64) allocHookStack ∗ ((s0.sp - 408#64) ↦₆₄ ptr))) := by
  have hdealloc := deallocPlacedAt_of_hooks hA
  by_cases hcap : cap = 0
  · subst hcap
    simp only [↓reduceIte, emp_sepConj]
    apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
      blkLib_eq_24 blk24_noSvc0 (mid := (blkPl_24).base + 1768#64)
    intro _m_strip
    wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc, hx1])
      (by simp only [wp_norm, arm64_norm, hrun]) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc, hx1])
      (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm, hsp],
      by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_align,
      by simp only [wp_norm, arm64_norm, hx19], by simp only [wp_norm, arm64_norm, hx22],
      by simp only [wp_norm, arm64_norm, hx23], by simp only [wp_norm, arm64_norm, hx25],
      by simp only [wp_norm, arm64_norm, hx26], by simp only [wp_norm, arm64_norm, hx27],
      by simp only [wp_norm, arm64_norm, hx29],
      ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm]⟩,
      [], FreeOnlyEvs.nil, Entails.refl _⟩
  · simp only [hcap, ↓reduceIte]
    apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
      blkLib_eq_24 blk24_noSvc0 (mid := lsρ cmkRustDeallocSym)
    intro _m_strip
    wp_step
    apply SepWP.ite_false (by rfl) (by simp [hx1]; exact hcap)
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
      (by simp only [wp_norm, arm64_norm, hrun]) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    rw [pool_dealloc_reassoc]
    refine call_dealloc_placed_wp hdealloc ptr cap.toNat 1 st
      (s0.sp - 480#64) ((blkPl_24).base + 1752#64) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hx1]
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hpc]
    · simp only [wp_norm, arm64_norm, hrun]
    · simp only [wp_norm, arm64_norm, hsp]
    · simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_align
    · simp only [wp_norm, arm64_norm, hpc]
    · intro sf hpc_sf hrun_sf hsp_sf hcs htr_sf
      have hsp_align' : sf.spAligned = true := by
        rw [State.spAligned, hsp_sf]
        simpa [State.spAligned, hsp] using hsp_align
      simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm,
        hx9, hx19, hx22, hx23, hx26, hx27, hx29] at hcs
      rcases hcs with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩
      apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
        blkLib_eq_24 blk24_noSvc0 (mid := (blkPl_24).base + 1768#64)
      intro _m_strip
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc_sf])
        (by simp only [wp_norm, arm64_norm, hrun_sf]) fun _m_real _hnsp => ?_
      refine SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
      refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc_sf])
        (by simp only [wp_norm, arm64_norm, hrun_sf]) ?_
      refine ⟨by simp only [wp_norm, arm64_norm, hsp_sf],
        by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_align',
        by simp only [wp_norm, arm64_norm, hcs19], by simp only [wp_norm, arm64_norm, hcs22],
        by simp only [wp_norm, arm64_norm, hcs23], by simp only [wp_norm, arm64_norm, hcs25],
        by simp only [wp_norm, arm64_norm, hcs26], by simp only [wp_norm, arm64_norm, hcs27],
        by simp only [wp_norm, arm64_norm, hcs29],
        ⟨by simp only [wp_norm, arm64_norm, htr_sf], by simp only [wp_norm, arm64_norm, hcsv]⟩,
        rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat, Entails.refl _⟩

theorem cmk_remove_prep_mac_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (v19 v21 v22 v23 v29 macCap v424 : BitVec 64) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1668#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = v19)
    (hx21 : s.readReg64 .x21 = v21)
    (hx22 : s.readReg64 .x22 = v22)
    (hx23 : s.readReg64 .x23 = v23)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1688#64) s
      (((s0.sp - 424#64) ↦₆₄ v424) ∗ ((s0.sp - 384#64) ↦₆₄ macCap))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x1 = macCap ∧
        s1.readReg64 .x21 = v21 ∧
        s1.readReg64 .x26 = v19 >>> 40 ∧
        s1.readReg64 .x27 = v23 ||| (v22 <<< 32) ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        VmPreserved s s1 ∧
        (P1 ⊢ ((s0.sp - 424#64) ↦₆₄ ((v21 &&& 16777215#64) <<< 40)) ∗
              ((s0.sp - 384#64) ↦₆₄ macCap))) := by
  apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
    blkLib_eq_24 blk24_noSvc0 (mid := (blkPl_24).base + 1688#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
    (by simp only [wp_norm, arm64_norm, hrun]) fun _m_real _hnsp => ?_
  have hvm : VmPreserved s _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
    (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp],
    by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx21],
    by simp only [wp_norm, arm64_norm, hx19], by simp only [wp_norm, arm64_norm, hx22, hx23],
    by simp only [wp_norm, arm64_norm, hx29],
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm]⟩, hvm, ?_⟩
  rw [shiftLeft_40_eq_and_mask24 v21]
  exact Entails.refl _

theorem cmk_remove_prep_iv_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (v21 v26 v27 v29 ivCap ret : BitVec 64) (counter : BitVec 32) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1704#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = v21)
    (hx26 : s.readReg64 .x26 = v26)
    (hx27 : s.readReg64 .x27 = v27)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1724#64) s
      (((s0.sp - 388#64) ↦₃₂ counter) ∗
       ((s0.sp - 376#64) ↦₆₄ ivCap) ∗
       ((s0.sp - 368#64) ↦₆₄ ret))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x1 = ivCap ∧
        s1.readReg64 .x9 = counter.zeroExtend 64 ∧
        s1.readReg64 .x19 = 1#64 ∧
        s1.readReg64 .x22 = ret ∧
        s1.readReg64 .x23 = v21 >>> 24 ∧
        s1.readReg64 .x25 = counter.zeroExtend 64 ∧
        s1.readReg64 .x26 = v26 ∧
        s1.readReg64 .x27 = v27 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        VmPreserved s s1 ∧
        (P1 ⊢ ((s0.sp - 388#64) ↦₃₂ counter) ∗
              ((s0.sp - 376#64) ↦₆₄ ivCap) ∗
              ((s0.sp - 368#64) ↦₆₄ ret))) := by
  apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
    blkLib_eq_24 blk24_noSvc0 (mid := (blkPl_24).base + 1724#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
    (by simp only [wp_norm, arm64_norm, hrun]) fun _m_real _hnsp => ?_
  have hvm : VmPreserved s _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
    (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp],
    by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm, hx21], by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm, hx26], by simp only [wp_norm, arm64_norm, hx27],
    by simp only [wp_norm, arm64_norm, hx29],
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm]⟩, hvm, Entails.refl _⟩

theorem cmk_remove_deallocVecs_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A lim H)
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (ret v19 v21 v22 v23 : BitVec 64) (st : M.σ) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1648#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = v19)
    (hx21 : s.readReg64 .x21 = v21)
    (hx22 : s.readReg64 .x22 = v22)
    (hx23 : s.readReg64 .x23 = v23)
    (hx26 : s.readReg64 .x26 = gk.1.cipher.cap)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1768#64) s
      (A.pool lim st s ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       (if gk.1.cipher.cap = 0 then emp
        else A.live gk.1.cipher.ptr gk.1.cipher.cap.toNat 1 ∗
          memRegion gk.1.cipher.ptr gk.1.cipher.cap.toNat) ∗
       (if gk.1.mac.cap = 0 then emp
        else A.live gk.1.mac.ptr gk.1.mac.cap.toNat 1 ∗
          memRegion gk.1.mac.ptr gk.1.mac.cap.toNat) ∗
       (if gk.1.iv.cap = 0 then emp
        else A.live gk.1.iv.ptr gk.1.iv.cap.toNat 1 ∗
          memRegion gk.1.iv.ptr gk.1.iv.cap.toNat) ∗
       ((s0.sp - 424#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 416#64) ↦₆₄ gk.1.mac.ptr) ∗
       ((s0.sp - 408#64) ↦₆₄ gk.1.iv.ptr) ∗
       ((s0.sp - 400#64) ↦₆₄ gk.1.cipher.ptr) ∗
       memRegion (s0.sp - 392#64) 4 ∗
       ((s0.sp - 388#64) ↦₃₂ gk.2.counter) ∗
       ((s0.sp - 384#64) ↦₆₄ gk.1.mac.cap) ∗
       ((s0.sp - 376#64) ↦₆₄ gk.1.iv.cap) ∗
       ((s0.sp - 368#64) ↦₆₄ ret))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x19 = 1#64 ∧
        s1.readReg64 .x22 = ret ∧
        s1.readReg64 .x23 = v21 >>> 24 ∧
        s1.readReg64 .x25 = gk.2.counter.zeroExtend 64 ∧
        s1.readReg64 .x26 = v19 >>> 40 ∧
        s1.readReg64 .x27 = v23 ||| (v22 <<< 32) ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P1 ⊢
            A.pool lim (M.stepEvents evs st) s1 ∗
            stackAt (s0.sp - 480#64) allocHookStack ∗
            ((s0.sp - 424#64) ↦₆₄ ((v21 &&& 16777215#64) <<< 40)) ∗
            memRegion (s0.sp - 416#64) 56)) := by
  wp_seq_frame
    (cmk_dealloc_cipher_placed_wp hA gk.1.cipher.cap gk.1.cipher.ptr st s0 s
      hpc hrun hsp hsp_align hx26)
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, halign1, hcs1, htr1, evs1, hf1, hP1⟩
  refine sepWP_weaken_left hP1 ?_
  set st1 := M.stepEvents evs1 st
  wp_seq_frame
    (cmk_remove_prep_mac_placed_wp v19 v21 v22 v23 (s0.sp - 96#64) gk.1.mac.cap 0#64 s0 s1
      hpc1 hrun1 hsp1 halign1 (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
      (by reg_chain))
  rintro s2 P2 hpc2 hrun2 ⟨hsp2, halign2, hx1_2, h21_2, h26_2, h27_2, h29_2, htr2, hvm2, hP2⟩
  refine sepWP_weaken_left hP2 ?_
  rw [← A.pool_of_vmPreserved hvm2]
  wp_seq_frame
    (cmk_dealloc_mac_placed_wp hA gk.1.mac.cap gk.1.mac.ptr st1 s0 s2
      hpc2 hrun2 hsp2 halign2 hx1_2)
  rintro s3 P3 hpc3 hrun3 ⟨hsp3, halign3, hcs3, htr3, evs3, hf3, hP3⟩
  refine sepWP_weaken_left hP3 ?_
  set st3 := M.stepEvents evs3 st1
  wp_seq_frame
    (cmk_remove_prep_iv_placed_wp v21 (v19 >>> 40) (v23 ||| (v22 <<< 32)) (s0.sp - 96#64)
      gk.1.iv.cap ret gk.2.counter s0 s3 hpc3 hrun3 hsp3 halign3
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain))
  rintro s4 P4 hpc4 hrun4
    ⟨hsp4, halign4, hx1_4, hx9_4, h19_4, h22_4, h23_4, h25_4, h26_4, h27_4, h29_4, htr4, hvm4, hP4⟩
  refine sepWP_weaken_left hP4 ?_
  rw [← A.pool_of_vmPreserved hvm4]
  wp_seq_frame
    (cmk_dealloc_iv_placed_wp hA gk.1.iv.cap gk.1.iv.ptr 1#64 ret
      (v21 >>> 24) (v19 >>> 40) (v23 ||| (v22 <<< 32)) (s0.sp - 96#64) gk.2.counter
      st3 s0 s4 hpc4 hrun4 hsp4 halign4 hx1_4 hx9_4 h19_4 h22_4 h23_4 h25_4 h26_4 h27_4 h29_4)
  rintro s5 P5 hpc5 hrun5
    ⟨hsp5, halign5, h19_5, h22_5, h23_5, h25_5, h26_5, h27_5, h29_5, htr5, evs5, hf5, hP5⟩
  refine sepWP_weaken_left hP5 ?_
  refine SepWP.done hpc5 hrun5 ?_
  have hevs_eq : M.stepEvents evs5 st3 = M.stepEvents (evs1 ++ evs3 ++ evs5) st := by
    simp only [st3, st1, M.stepEvents_append]
  rw [hevs_eq]
  refine ⟨hsp5, halign5, h19_5, h22_5, h23_5, h25_5, h26_5, h27_5, h29_5, by reg_chain,
    evs1 ++ evs3 ++ evs5, FreeOnlyEvs.append (FreeOnlyEvs.append hf1 hf3) hf5, ?_⟩
  exact entails_of_eq (by sep_ac_rfl)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (deallocVecs_slots_entails_memRegion_56 s0.sp gk.1.mac.ptr gk.1.iv.ptr gk.1.cipher.ptr
        gk.1.mac.cap gk.1.iv.cap ret gk.2.counter))))

theorem cmk_remove_write_ok_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {H : String → Option (State → State)} {A : RustCliAllocBudget M}
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (ret : BitVec 64) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1768#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx22 : s.readReg64 .x22 = ret)
    (hx23 : s.readReg64 .x23 = (BitVec.ofNat 64 gk.2.seed.length) >>> 24)
    (hx25 : s.readReg64 .x25 = gk.2.counter.zeroExtend 64)
    (hx26 : s.readReg64 .x26 =
      (gk.1.seed.ptr.extractLsb' 16 8 ++ gk.1.seed.ptr.extractLsb' 8 8 ++
       gk.1.seed.ptr.extractLsb' 0 8 ++ gk.1.seed.cap.extractLsb' 56 8 ++
       gk.1.seed.cap.extractLsb' 48 8 ++ gk.1.seed.cap.extractLsb' 40 8 ++
       gk.1.seed.cap.extractLsb' 32 8 ++ gk.1.seed.cap.extractLsb' 24 8) >>> 40)
    (hx27 : s.readReg64 .x27 =
      ((gk.1.seed.ptr.extractLsb' 48 8 ++ gk.1.seed.ptr.extractLsb' 40 8 ++
        gk.1.seed.ptr.extractLsb' 32 8 ++ gk.1.seed.ptr.extractLsb' 24 8).zeroExtend 64) |||
      (((gk.1.seed.ptr.extractLsb' 56 8).zeroExtend 64) <<< 32))
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1916#64) s
      (memRegion (s0.sp - 480#64) 56 ∗
       ((s0.sp - 424#64) ↦₆₄ (((BitVec.ofNat 64 gk.2.seed.length) &&& 16777215#64) <<< 40)) ∗
       memRegion (s0.sp - 304#64) 80 ∗
       ((s0.sp - 224#64) ↦₆₄ gk.1.seed.cap) ∗
       memRegion ret 88 ∗
       vecU8Buf A.repAlloc gk.1.seed.cap gk.1.seed.ptr gk.2.seed)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        VmPreserved s s1 ∧
        (P1 ⊢
          memRegion (s0.sp - 480#64) 64 ∗
          memRegion (s0.sp - 304#64) 88 ∗
          consumeMessageKeyResultAt A.repAlloc ret (.ok gk.2))) := by
  apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
    blkLib_eq_24 blk24_noSvc0 (mid := (blkPl_24).base + 1916#64)
  intro _m_strip
  refine SepWP.weaken_pre
    (sepConj_mono (memRegion_56_entails_write_ok_slots s0.sp)
      (sepConj_mono_right
        (sepConj_mono (memRegion_80_entails_write_ok_slots s0.sp)
          (sepConj_mono_right
            (sepConj_mono_left (memRegion_88_entails_ret_ok_slots ret)))))) ?_
  wp_pull_exists
  conv =>
    arg 4
    rw [pointsTo64_eq_unaligned_2_1_4_1 (ret + 24#64)]
    simp only [bv_add_add_lit, sepConj_assoc]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step
  wp_simp_pre only [arm64_norm]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (shift_sp_256 s0.sp))))))))))) ?_
  wp_pull_exists
  wp_step; wp_step; wp_step; wp_step
  wp_simp_pre only [arm64_norm]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (shift_ret_68 ret))))))))))))))))))))))))))))))))))))) ?_
  wp_pull_exists
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
    (by simp only [wp_norm, arm64_norm, hrun]) fun _m_real _hnsp => ?_
  have hvm : VmPreserved s _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
    (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp],
    by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm, hx29],
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm]⟩, hvm, ?_⟩
  simp only [arm64_norm, seed_ptr_reassemble, seed_len_lo16_eq, seed_len_b2_eq, seed_len_b2_eq',
    seed_len_b3456_eq, seed_len_b7_eq]
  exact write_ok_post_entails s0.sp ret gk

theorem cmk_remove_0x5e4_placed_wp [LibsignalPlacement] {M : AllocCostModel}
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
  refine SepWP.weaken_pre
    (sepConj_mono (vecBuf_split_entails_remove_ready A.repAlloc mkCap mkPtr gks hp)
      (sepConj_mono_left (memRegion_136_entails_post_memmove_slots s0.sp))) ?_
  wp_pull_exists
  refine SepWP.pure_elim ?_
  rintro ⟨hbs, hbs_len, hlen_le, hcap_lt, hptr_ne, hseed_ne, hcipher_lt, hseed_le, hseed_lt⟩
  have hx1_1' : s1.readReg64 .x1 = mkPtr + BitVec.ofNat 64 ((p + 1) * 104) := by
    rw [hx1_1, elemAddr_add_104]
  have hx2_1' : (s1.readReg64 .x2).toNat = (gks.length - 1 - p) * 104 := by
    rw [hx2_1, remBytes_toNat_eq hlen_le hcap_lt]
  wp_seq_frame
    (cmk_memmove_placed_wp hmemmove_eq mkPtr _ p gks.length chAddr
      (BitVec.ofNat 64 gks[p].2.seed.length) (s0.sp - 224#64) (BitVec.ofNat 64 gks.length)
      gks[p].1.cipher.cap (s0.sp - 96#64)
      s0 s1 hpc1 hrun1 hsp1 halign1 hx0_1 hx1_1' hx2_1'
      hx19_1 hx21_1 hx22_1 hx24_1 hx26_1 hx29_1 hp hbs_len)
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

end LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.RemoveBudget
