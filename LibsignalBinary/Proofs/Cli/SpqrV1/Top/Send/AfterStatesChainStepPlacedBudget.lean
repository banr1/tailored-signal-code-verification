/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ChainEpochPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainStepPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainStep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `spqr::send` Phase 3b Chain Step and `send_key` Error Cleanup

Threads `RustCliAllocBudget`, `VmPreserved`, and `FreeOnlyEvs` through the
`[LibsignalPlacement]` `Chain::send_key` error cleanup (`+3492 -> +4576`) and `Chain::into_pb`
call/relocation (`+3712 -> +4000`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainStepPlacedBudget

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withMemEq libsignalSessionCode lsmpl lsρ
   sepWP_mono_lscl sepWP_seq_lscl withLsCodeLoaded withMemEq)
open CryptoVerification.Cli.SpqrV1.Drop (chunkedStatesLocal1JumpTablePlacedAt)
open CryptoVerification.Cli.SpqrV1.Top.Send (spqrSendPlacedEntry spqrSendPlacedProg)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain ChainPB States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet (spqrSendResultAt)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainGhost chainAt chainEpoch chainEpochAlign chainEpochAt chainEpochSize chainRepr
   vecDequeAt vecDequeHeader vecDequeRingBuf vecDequeSlotsAt)
open CryptoVerification.SpqrV1.Drop
  (arrayAt_chainEpochAt_entails_chainEpoch cap_lsl7_sub_lsl4 chainAt_entails_dealloc
   chainHeaders_entails_memRegion_88 chunkedStatesAt chunkedStatesSize dropStack32
   dropStackPoly64 mul_112_add_ptr not_ule_sub_of_gt ofNat_beq_zero_false_112
   ofNat_sub_sub_eq sub_eq_ofNat_sub ule_sub_of_le ult_of_toNat_lt vecCapPtrDealloc
   vecDequeSlotsAt_nil_entails_memRegion vecDequeSlotsAt_nonwrap_entails
   vecDequeSlotsAt_nonwrap_rejoin vecDequeSlotsAt_wrap_entails vecDequeSlotsAt_wrap_rejoin)
open CryptoVerification.SpqrV1.Top.ChainFrom (chainPBAt_protoRepr_eq_exists)
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
  (chainPBAt_expose_cap chainPBRestAt chainRepr_entails_words11
   words11_entails_chainRepr words11_to_memRegion_88)
open CryptoVerification.SpqrV1.Top.DecodeState (vecU8Heap)
open CryptoVerification.SpqrV1.Top.Send
  (add_emp_arrayAt_nil chainPBRestAt_entails_words9 memRegion_72_split_dwords_words
   memRegion_72_words9 optChainPBRegSlotAt sendKeyErrSlot_entails_memRegion_40
   sendKeyOkSlot_entails_words11 sendResultAt_none_of_dwords_words spqrSendCalleeStack
   stackAt_spqrSendCallee_eq_allocHook stackAt_spqrSendCallee_eq_dropStack32
   stackAt_spqrSendCallee_eq_dropStackPoly64 words10_to_memRegion_80
   words9_entails_chainPBRestAt)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget
  (dropChunkedStatesLocal1PlacedSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainPlacedBudget
  (DeallocOkPlaced)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropChainEpochSliceSpec)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32 LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero

attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.SpqrV1.Top.Send.extractLsb_lo_append64
  CryptoVerification.SpqrV1.Top.Send.extractLsb_hi_append64

private def deallocFreeOnlySpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

omit [LibsignalPlacement] in
private theorem subroutine_ok_withMemEq_of_withLsCodeLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : MultiPlacement} {spec : Spec α} {m : Memory}
    (hcl : LibsignalCodeLoaded pl m)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withMemEq m spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hm, hpre⟩ := extract_withMemEq hp
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hm ▸ hcl, hpre⟩)
    (fun _ _ _ _ hq => hq)

omit [LibsignalPlacement] in
private theorem sepWP_seq_lscl_mid {prog : Program} {mid tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : MultiPlacement} {Mid post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h1 : SepWP prog mid s P Mid)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded pl sm.mem → Mid sm Pm → SepWP prog tgt sm Pm post) :
    SepWP prog tgt s P post :=
  sepWP_seq_lscl hcl (sepWP_mono_lscl hcl h1 fun sm Pm hpc hrun hclm hMid _ =>
    h2 sm Pm hpc hrun hclm hMid)

omit [LibsignalPlacement] in
private theorem sepWP_seq_lscl_lr {prog : Program} {tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : MultiPlacement} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog (s.readReg64 .x30) s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWP prog tgt sm Pm post)) :
    SepWP prog tgt s P post :=
  sepWP_seq_lscl hcl h

private theorem seq_vm_lscl {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP ((blkPC_427).rebase (blkPl_427).base Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → Q sm →
      SepWP ((blkPC_427).rebase (blkPl_427).base Hk) target sm P_mid post) :
    SepWP ((blkPC_427).rebase (blkPl_427).base Hk) target s Pre post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ hcl_m =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hcl_m hvm hQ))

/-- `+4524 -> +4576` (`0x31a08 -> 0x31a3c`, 13 instructions = 52 bytes):
    deallocates the `Chain.links` ring buffer (when `G.linksCap ≠ 0`), deallocates `Chain.next_root`
    (when `G.nextRoot.cap ≠ 0`), and calls `drop_glue::<States> [local#3]` (Block `443`) on `s.sp + 0x190#64`. -/
theorem step_drop_chain_tail_31a08_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkPlaced M A lim ext)
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (s : State) (st : M.σ) (x23 : BitVec 64) (G : ChainGhost) (c : Chain)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 4524#64)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = G.linksPtr)
    (hx21 : s.readReg64 .x21 = G.linksCap)
    (hx23 : s.readReg64 .x23 = x23)
    (hcap_lt : G.linksCap.toNat * 112 < 2 ^ 63)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4576#64) s
      (vecDequeHeader (s.sp + 0x590#64) G.linksCap G.linksPtr G.linksHead
        (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        (if G.linksCap = 0 then emp
         else A.repAlloc.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
           memRegion G.linksPtr (G.linksCap.toNat * 112)) ∗
        ((s.sp + 0x5b0#64) ↦₆₄ G.nextRoot.cap) ∗
        ((s.sp + 0x5b8#64) ↦₆₄ G.nextRoot.ptr) ∗
        memRegion (s.sp + 0x5c0#64) 40 ∗
        vecCapPtrDealloc A.repAlloc G.nextRoot.cap G.nextRoot.ptr ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 0x590#64) 88 ∗
            memRegion (s.sp + 0x190#64) 928 ∗
            chunkedStatesLocal1JumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have h88 :
      vecDequeHeader (s.sp + 1424#64) G.linksCap G.linksPtr G.linksHead
        (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        ((s.sp + 1456#64) ↦₆₄ G.nextRoot.cap) ∗
        ((s.sp + 1464#64) ↦₆₄ G.nextRoot.ptr) ∗
        memRegion (s.sp + 1472#64) 40 ⊢
        memRegion (s.sp + 1424#64) 88 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      chainHeaders_entails_memRegion_88 (s.sp + 1424#64) G.linksCap G.linksPtr G.linksHead
        (BitVec.ofNat 64 (G.epochs.zip c.links).length) G.nextRoot.cap G.nextRoot.ptr
  refine sepWP_seq_lscl_mid hcl
    (mid := spqrSendPlacedEntry + 4548#64)
    (Mid := fun s1 P1 =>
      ∃ evs₁ : List AllocEvent,
        FreeOnlyEvs evs₁ ∧
        AllocCallPreserved s s1 ∧
        s1.status = .Running ∧
        s1.trace = s.trace ∧
        s1.sp = s.sp ∧
        s1.readReg64 .x23 = x23 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        (P1 ⊢ vecDequeHeader (s.sp + 0x590#64) G.linksCap G.linksPtr G.linksHead
          (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
          ((s.sp + 0x5b0#64) ↦₆₄ G.nextRoot.cap) ∗
          ((s.sp + 0x5b8#64) ↦₆₄ G.nextRoot.ptr) ∗
          memRegion (s.sp + 0x5c0#64) 40 ∗
          vecCapPtrDealloc A.repAlloc G.nextRoot.cap G.nextRoot.ptr ∗
          chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
          chunkedStatesLocal1JumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs₁ st) s1 ∗
          stackAt s.sp spqrSendCalleeStack ∗ Frame))
    ?_ ?_
  · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
    by_cases hc : G.linksCap = 0#64
    · have hc_beq : (G.linksCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx21 ⊢
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
        LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
        LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
      exact Entails.refl _
    · have hc_beq : ¬((G.linksCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_lsl7_sub_lsl4 hcap_lt
      simp only [hc, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm]
      wp_conv_pre => rw [stackAt_spqrSendCallee_eq_allocHook s.sp]
      wp_steps
      wp_call hdealloc_fo (G.linksPtr, G.linksCap.toNat * 112, 8, st)
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨rustDeallocEvents (G.linksCap.toNat * 112) 8,
          LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 (G.linksCap.toNat * 112),
          by simp only [wp_norm, arm64_norm, *],
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by simp only [wp_norm, arm64_norm, *],
          Entails.of_eq (by simp only [hsp_sf, stackAt_spqrSendCallee_eq_allocHook]; sep_ac_rfl)⟩
  · intro s1 P1 hpc1 _ hcl1 ⟨evs₁, hevs₁, hacp₁, hrun1, htr1, hsp1, hx23_1, hvregs1, hP1⟩
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    refine SepWP.weaken_pre hP1 ?_
    refine sepWP_seq_lscl_mid hcl1
      (mid := spqrSendPlacedEntry + 4568#64)
      (Mid := fun s2 P2 =>
        ∃ evs₂ : List AllocEvent,
          FreeOnlyEvs evs₂ ∧
          AllocCallPreserved s1 s2 ∧
          s2.status = .Running ∧
          s2.trace = s.trace ∧
          s2.sp = s.sp ∧
          s2.readReg64 .x23 = x23 ∧
          calleeSavedVRegs s2 = calleeSavedVRegs s ∧
          (P2 ⊢ memRegion (s.sp + 0x590#64) 88 ∗
            chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
            chunkedStatesLocal1JumpTablePlacedAt ∗
            A.pool lim (M.stepEvents (evs₁ ++ evs₂) st) s2 ∗
            stackAt s.sp spqrSendCalleeStack ∗ Frame))
      ?_ ?_
    · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
      rw [← hsp1] at h88
      wp_conv_pre => rw [← hsp1]
      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hnr : (G.nextRoot.cap == 0#64) = true <;>
        simp only [hnr, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken h88 (by sep_focus) ?_
        refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by wp_norm_goal,
            by wp_norm_goal, (by wp_norm_goal : _ = s1.trace).trans htr1,
            (by wp_norm_goal : _ = s1.sp).trans hsp1, by wp_norm_goal,
            (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1, ?_⟩
        simp only [List.append_nil,
          LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
          LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64, hsp1]
        exact Entails.refl _
      · wp_conv_pre => rw [stackAt_spqrSendCallee_eq_allocHook s1.sp]
        wp_steps
        wp_call hdealloc_fo (G.nextRoot.ptr, G.nextRoot.cap.toNat, 1, M.stepEvents evs₁ st)
        refine SepWP.focus_weaken h88 (by sep_focus) ?_
        refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨rustDeallocEvents G.nextRoot.cap.toNat 1,
            LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 G.nextRoot.cap.toNat,
            by simp only [wp_norm, arm64_norm, *],
            by wp_norm_goal, (by wp_norm_goal : _ = s1.trace).trans htr1,
            (by wp_norm_goal : _ = s1.sp).trans hsp1, by wp_norm_goal,
            (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s1).trans hvregs1, ?_⟩
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        exact Entails.of_eq (by simp only [hsp_sf, hsp1, stackAt_spqrSendCallee_eq_allocHook]; sep_ac_rfl)
    · intro s2 P2 hpc2 _ hcl2 ⟨evs₂, hevs₂, hacp₂, hrun2, htr2, hsp2, hx23_2, hvregs2, hP2⟩
      have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
      refine SepWP.weaken_pre hP2 ?_
      apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 443)
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      wp_conv_pre => rw [← hsp2, stackAt_spqrSendCallee_eq_dropStackPoly64 s2.sp]
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun hcl_call => ?_
      have hdrop_st := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl_call hdrop_states
      clear hdrop_states hcl_call
      simp only [dropChunkedStatesLocal1PlacedSpec, withMemEq] at hdrop_st
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdrop_st
      wp_call hdrop_st (⟨s2.sp + 400#64, st1⟩, M.stepEvents (evs₁ ++ evs₂) st)
      have hevs₃ : FreeOnlyEvs w := by assumption
      have hacp₃ : AllocCallPreserved s2 sf := by simp only [wp_norm, arm64_norm, *]
      refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨(evs₁ ++ evs₂) ++ w,
          LibsignalBinary.Heap.FreeOnlyEvs.append (LibsignalBinary.Heap.FreeOnlyEvs.append hevs₁ hevs₂) hevs₃,
          (hacp₁.trans hacp₂).trans hacp₃,
          by wp_norm_goal, (by wp_norm_goal : _ = s2.trace).trans htr2,
          (by wp_norm_goal : _ = s2.sp).trans hsp2, by wp_norm_goal,
          (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s2).trans hvregs2, ?_⟩
      dsimp only [chunkedStatesSize]
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact Entails.of_eq (by simp only [hsp_sf, hsp2, stackAt_spqrSendCallee_eq_dropStackPoly64]; sep_ac_rfl)

/-- `+3492 -> +4576` (`0x31600 -> 0x31a3c`):
    `Chain::send_key` error cleanup. Writes `spqrSendResultAt A.repAlloc ret none`, drops `chain1` at
    `s.sp + 0x590#64` (via Block `446` and `__rust_dealloc`), and drops `st1` at `s.sp + 0x190#64`
    (via Block `443`), reaching `+4576`. -/
theorem step_err_31600_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkPlaced M A lim ext)
    (hdrop_slice : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 446) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (s : State) (st : M.σ) (ret x23 w0 : BitVec 64) (d0 d1 : BitVec 32) (w2 w3 : BitVec 64)
    (c : Chain) (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 3492#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4576#64) s
      (memRegion ret 72 ∗
        ((s.sp + 0x1260#64) ↦₆₄ w0) ∗
        ((s.sp + 0x1268#64) ↦₃₂ d0) ∗
        ((s.sp + 0x126c#64) ↦₃₂ d1) ∗
        ((s.sp + 0x1270#64) ↦₆₄ w2) ∗
        ((s.sp + 0x1278#64) ↦₆₄ w3) ∗
        memRegion (s.sp + 0x1280#64) 8 ∗
        chainRepr A.repAlloc (s.sp + 0x590#64) c ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ spqrSendResultAt A.repAlloc ret none ∗
            memRegion (s.sp + 0x1260#64) 40 ∗
            memRegion (s.sp + 0x590#64) 88 ∗
            memRegion (s.sp + 0x190#64) 928 ∗
            chunkedStatesLocal1JumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  dsimp only [chainRepr]
  wp_pull_exists; rename_i G
  refine SepWP.focus_weaken (chainAt_entails_dealloc A.repAlloc (s.sp + 0x590#64) G c) (by sep_focus) ?_
  unfold vecDequeAt vecDequeRingBuf vecDequeHeader
  wp_focus_pure
  rintro ⟨hlen_le, hcap_lt, hptr_ne, hhead⟩
  dsimp only [chainEpochSize, chainEpochAlign] at hcap_lt ⊢
  have h40 := sendKeyErrSlot_entails_memRegion_40 (s.sp + 4704#64) w0 d0 d1 w2 w3
  refine sepWP_seq_lscl_mid hcl
    (mid := spqrSendPlacedEntry + 4524#64)
    (Mid := fun s1 P1 =>
      ∃ evs₁ : List AllocEvent,
        FreeOnlyEvs evs₁ ∧
        AllocCallPreserved s s1 ∧
        s1.status = .Running ∧
        s1.trace = s.trace ∧
        s1.sp = s.sp ∧
        s1.readReg64 .x20 = G.linksPtr ∧
        s1.readReg64 .x21 = G.linksCap ∧
        s1.readReg64 .x23 = x23 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        (P1 ⊢ vecDequeHeader (s.sp + 0x590#64) G.linksCap G.linksPtr G.linksHead
          (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
          (if G.linksCap = 0 then emp
           else A.repAlloc.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
             memRegion G.linksPtr (G.linksCap.toNat * 112)) ∗
          ((s.sp + 0x5b0#64) ↦₆₄ G.nextRoot.cap) ∗
          ((s.sp + 0x5b8#64) ↦₆₄ G.nextRoot.ptr) ∗
          memRegion (s.sp + 0x5c0#64) 40 ∗
          vecCapPtrDealloc A.repAlloc G.nextRoot.cap G.nextRoot.ptr ∗
          chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
          chunkedStatesLocal1JumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs₁ st) s1 ∗
          stackAt s.sp spqrSendCalleeStack ∗
          (spqrSendResultAt A.repAlloc ret none ∗ memRegion (s.sp + 0x1260#64) 40 ∗ Frame)))
    ?_ ?_
  · clear hdrop_states hdealloc
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    wp_conv_pre => rw [memRegion_72_split_dwords_words ret, stackAt_spqrSendCallee_eq_dropStack32 s.sp]
    wp_pull_exists
    refine seq_vm_lscl hcl (mid := (blkPl_427).base + 3528#64)
      (P_mid :=
        ((s.sp + 1424#64) ↦₆₄ G.linksCap) ∗
        ((s.sp + 1432#64) ↦₆₄ G.linksPtr) ∗
        ((s.sp + 1440#64) ↦₆₄ G.linksHead) ∗
        ((s.sp + 1448#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        (if G.linksCap = 0#64 then emp
         else A.repAlloc.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 G.linksCap.toNat G.linksHead.toNat
             G.linksPtr (G.epochs.zip c.links) 0 G.linksCap.toNat) ∗
        ((s.sp + 1456#64) ↦₆₄ G.nextRoot.cap) ∗
        ((s.sp + 1464#64) ↦₆₄ G.nextRoot.ptr) ∗
        memRegion (s.sp + 1472#64) 40 ∗
        vecCapPtrDealloc A.repAlloc G.nextRoot.cap G.nextRoot.ptr ∗
        chunkedStatesAt A.repAlloc (s.sp + 400#64) st1 ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim st s ∗
        memRegion (s.sp - 123008#64) (spqrSendCalleeStack - dropStack32) ∗
        stackAt s.sp dropStack32 ∗
        spqrSendResultAt A.repAlloc ret none ∗
        memRegion (s.sp + 4704#64) 40 ∗ Frame)
      (Q := fun s0 =>
        AllocCallPreserved s s0 ∧
        s0.sp = s.sp ∧
        s0.trace = s.trace ∧
        s0.readReg64 .x21 = G.linksCap ∧
        s0.readReg64 .x9 = BitVec.ofNat 64 (G.epochs.zip c.links).length ∧
        s0.readReg64 .x23 = x23 ∧
        calleeSavedVRegs s0 = calleeSavedVRegs s)
      ?_ ?_
    · by_vm_steps (
        wp_steps
        refine SepWP.focus_weaken (sendResultAt_none_of_dwords_words A.repAlloc ret
          (BitVec.truncate 32 (s.readReg64 (Reg.gpr 24#5))) d1 w2 w3) (by sep_focus) ?_
        refine SepWP.focus_weaken h40 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal, Entails.of_eq (by sep_ac_rfl),
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
    · intro s0 hpc0 hrun0 hcl0 hvm0 ⟨hacp0, hsp0, htr0, hx21_0, hx9_0, hx23_0, hvregs0⟩
      have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by rw [hsp0]; exact hsp_align
      wp_conv_pre => rw [← A.pool_of_vmPreserved hvm0, ← hsp0]
      generalize hxs : G.epochs.zip c.links = xs at hlen_le hx9_0 ⊢
      cases xs with
      | nil =>
        have hnil_ent :
            (if G.linksCap = 0#64 then emp
             else A.repAlloc.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
               vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr [] 0 G.linksCap.toNat) ⊢
            (if G.linksCap = 0#64 then emp
             else A.repAlloc.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
               memRegion G.linksPtr (G.linksCap.toNat * 112)) := by
          by_cases hc : G.linksCap = 0#64
          · simp [hc]; exact Entails.refl _
          · simp only [hc, ↓reduceIte]
            exact sepConj_mono_right (vecDequeSlotsAt_nil_entails_memRegion
              (chainEpochAt A.repAlloc) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr hcap_lt)
        refine SepWP.focus_weaken hnil_ent (by sep_focus) ?_
        simp only [List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat] at hx9_0 ⊢
        apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 446)
        wp_steps
        refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun hcl_c1 => ?_
        apply sepWP_seq_lscl_lr hcl_c1
        refine SepWP.focus_weaken (add_emp_arrayAt_nil A.repAlloc ((s0.sp + 1424#64) ↦₆₄ G.linksCap) G.linksPtr) (by sep_focus) ?_
        have hslice1 := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl_c1 hdrop_slice
        simp only [dropChainEpochSliceSpec, chainEpochSize, chainEpochAlign, withMemEq] at hslice1
        dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hslice1
        wp_call hslice1 (⟨G.linksPtr, []⟩, st)
        clear hslice1 hcl_c1
        let evs_a := w
        have hevs_a : FreeOnlyEvs evs_a := by dsimp only [evs_a]; assumption
        let s_r1 := sf
        have hacp_a : AllocCallPreserved s0 s_r1 := by dsimp only [s_r1]; simp only [wp_norm, arm64_norm, *]
        refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun hcl_r1 => ?_
        apply sepWP_seq_lscl hcl_r1 (mid := lsmpl.base 446)
        clear hcl_r1
        wp_steps
        refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun hcl_c2 => ?_
        refine SepWP.focus_weaken (add_emp_arrayAt_nil A.repAlloc ((s0.sp + 1424#64) ↦₆₄ G.linksCap) G.linksPtr) (by sep_focus) ?_
        have hslice2 := subroutine_ok_withMemEq_of_withLsCodeLoaded (spec := dropChainEpochSliceSpec M A lim) hcl_c2 hdrop_slice
        simp only [dropChainEpochSliceSpec, chainEpochSize, chainEpochAlign, withMemEq] at hslice2
        dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hslice2
        wp_call hslice2 (⟨G.linksPtr, []⟩, M.stepEvents evs_a st)
        clear hslice2 hcl_c2
        let evs_b := w_1
        have hevs_b : FreeOnlyEvs evs_b := by dsimp only [evs_b]; assumption
        have hacp_b : AllocCallPreserved s_r1 sf_1 := by dsimp only [s_r1]; simp only [wp_norm, arm64_norm, *]
        refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨evs_a ++ evs_b, LibsignalBinary.Heap.FreeOnlyEvs.append hevs_a hevs_b,
            hacp0.trans (hacp_a.trans hacp_b),
            by wp_norm_goal,
            (by simp only [wp_norm, arm64_norm, *] : _ = s0.trace).trans htr0,
            (by simp only [wp_norm, arm64_norm, *] : _ = s0.sp).trans hsp0,
            by wp_norm_goal,
            (by simp only [wp_norm, arm64_norm, *] : _ = s0.readReg64 .x21).trans hx21_0,
            (by simp only [wp_norm, arm64_norm, *] : _ = s0.readReg64 .x23).trans hx23_0,
            (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s0).trans hvregs0, ?_⟩
        unfold vecDequeHeader
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append,
          List.length_nil, BitVec.ofNat_eq_ofNat, memRegion_zero, emp_sepConj, sepConj_emp,
          Nat.mul_comm, BitVec.add_assoc, BitVec.reduceAdd,
          hsp_sf, hsp0, stackAt_spqrSendCallee_eq_dropStack32 s.sp]
        exact Entails.of_eq (by sep_ac_rfl)
      | cons x tl =>
        have hlen_pos : 0 < (x :: tl).length := by simp
        have hlen_lt : (x :: tl).length * 112 < 2 ^ 63 := by
          have : (x :: tl).length * 112 ≤ G.linksCap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le
          omega
        have hcap_lt_pow : G.linksCap.toNat < 2 ^ 63 := by omega
        have hne0 := ofNat_beq_zero_false_112 hlen_pos hlen_lt
        have hcap_ne : G.linksCap ≠ 0#64 := by
          intro hc0; rw [hc0] at hlen_le; simp at hlen_le
        simp only [hcap_ne, BitVec.ofNat_eq_ofNat, ↓reduceIte] at hhead hx9_0 ⊢
        have hult : G.linksHead.ult G.linksCap = true := ult_of_toNat_lt hhead
        have haddr1 : G.linksPtr + BitVec.ofNat 64 (G.linksHead.toNat * 112) =
            G.linksPtr + G.linksHead * 112#64 := by
          rw [← mul_112_add_ptr, BitVec.add_comm]
        by_cases hwrap : (x :: tl).length ≤ G.linksCap.toNat - G.linksHead.toNat
        · have hule := ule_sub_of_le hcap_lt_pow hhead hwrap
          obtain ⟨ys, hys_len, hys_ent⟩ := vecDequeSlotsAt_nonwrap_entails
            (chainEpochAt A.repAlloc) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) hcap_lt hhead hwrap
          let eps := ys.map Prod.snd
          have heps_len : eps.length = (x :: tl).length := by simp [eps, hys_len]
          have heps_lt : eps.length * 112 < 2 ^ 63 := by rw [heps_len]; exact hlen_lt
          have hx1_eq : G.linksHead + BitVec.ofNat 64 (x :: tl).length - G.linksHead =
              BitVec.ofNat 64 eps.length := by
            rw [CryptoVerification.SpqrV1.Drop.add_sub_cancel_left_bv, heps_len]
          have hent_ep :
              vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) 0 G.linksCap.toNat ⊢
              arrayAt (chainEpoch A.repAlloc) 112 (G.linksPtr + G.linksHead * 112#64) eps ∗
              memRegion G.linksPtr (G.linksHead.toNat * 112) ∗
              memRegion (G.linksPtr + BitVec.ofNat 64 ((G.linksHead.toNat + (x :: tl).length) * 112))
                ((G.linksCap.toNat - G.linksHead.toNat - (x :: tl).length) * 112) := by
            rw [← haddr1]
            exact Entails.trans hys_ent (sepConj_mono_left (arrayAt_chainEpochAt_entails_chainEpoch A.repAlloc _ ys))
          refine SepWP.focus_weaken hent_ep (by sep_focus) ?_
          apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 446)
          wp_steps
          refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun hcl_c1 => ?_
          apply sepWP_seq_lscl_lr hcl_c1
          have hslice1 := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl_c1 hdrop_slice
          simp only [dropChainEpochSliceSpec, chainEpochSize, chainEpochAlign, withMemEq] at hslice1
          dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hslice1
          wp_call hslice1 (⟨G.linksPtr + G.linksHead * 112#64, eps⟩, st)
          clear hslice1 hcl_c1
          let evs_a := w
          have hevs_a : FreeOnlyEvs evs_a := by dsimp only [evs_a]; assumption
          let s_r1 := sf
          have hacp_a : AllocCallPreserved s0 s_r1 := by dsimp only [s_r1]; simp only [wp_norm, arm64_norm, *]
          refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun hcl_r1 => ?_
          apply sepWP_seq_lscl hcl_r1 (mid := lsmpl.base 446)
          clear hcl_r1
          wp_steps
          refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun hcl_c2 => ?_
          refine SepWP.focus_weaken (add_emp_arrayAt_nil A.repAlloc ((s0.sp + 1424#64) ↦₆₄ G.linksCap) G.linksPtr) (by sep_focus) ?_
          have hslice2 := subroutine_ok_withMemEq_of_withLsCodeLoaded (spec := dropChainEpochSliceSpec M A lim) hcl_c2 hdrop_slice
          simp only [dropChainEpochSliceSpec, chainEpochSize, chainEpochAlign, withMemEq] at hslice2
          dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hslice2
          wp_call hslice2 (⟨G.linksPtr, []⟩, M.stepEvents evs_a st)
          clear hslice2 hcl_c2
          let evs_b := w_1
          have hevs_b : FreeOnlyEvs evs_b := by dsimp only [evs_b]; assumption
          have hacp_b : AllocCallPreserved s_r1 sf_1 := by dsimp only [s_r1]; simp only [wp_norm, arm64_norm, *]
          rw [← haddr1, heps_len]
          refine SepWP.focus_weaken
            (vecDequeSlotsAt_nonwrap_rejoin 112 G.linksCap.toNat G.linksHead.toNat (x :: tl).length
              G.linksPtr hcap_lt hhead hwrap) (by sep_focus) ?_
          refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨evs_a ++ evs_b, LibsignalBinary.Heap.FreeOnlyEvs.append hevs_a hevs_b,
              hacp0.trans (hacp_a.trans hacp_b),
              by wp_norm_goal,
              (by simp only [wp_norm, arm64_norm, *] : _ = s0.trace).trans htr0,
              (by simp only [wp_norm, arm64_norm, *] : _ = s0.sp).trans hsp0,
              by wp_norm_goal,
              (by simp only [wp_norm, arm64_norm, *] : _ = s0.readReg64 .x21).trans hx21_0,
              (by simp only [wp_norm, arm64_norm, *] : _ = s0.readReg64 .x23).trans hx23_0,
              (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s0).trans hvregs0, ?_⟩
          unfold vecDequeHeader
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append,
            memRegion_zero, emp_sepConj, sepConj_emp,
            Nat.mul_comm, BitVec.add_assoc, BitVec.reduceAdd,
            hsp_sf, hsp0, stackAt_spqrSendCallee_eq_dropStack32 s.sp]
          exact Entails.of_eq (by sep_ac_rfl)
        · have hgt : G.linksCap.toNat - G.linksHead.toNat < (x :: tl).length := by omega
          have hnule := not_ule_sub_of_gt hcap_lt_pow hhead hlen_le hgt
          obtain ⟨ys₁, ys₂, hys₁_len, hys₂_len, hys_ent⟩ := vecDequeSlotsAt_wrap_entails
            (chainEpochAt A.repAlloc) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) hcap_lt hhead hlen_le hgt
          let eps₁ := ys₁.map Prod.snd
          let eps₂ := ys₂.map Prod.snd
          have heps₁_len : eps₁.length = G.linksCap.toNat - G.linksHead.toNat := by simp [eps₁, hys₁_len]
          have heps₂_len : eps₂.length = (x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat) := by
            simp [eps₂, hys₂_len]
          have heps₁_lt : eps₁.length * 112 < 2 ^ 63 := by
            rw [heps₁_len]
            have : (G.linksCap.toNat - G.linksHead.toNat) * 112 ≤ G.linksCap.toNat * 112 :=
              Nat.mul_le_mul_right 112 (by omega)
            omega
          have heps₂_lt : eps₂.length * 112 < 2 ^ 63 := by
            rw [heps₂_len]
            have : ((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat)) * 112 ≤ (x :: tl).length * 112 :=
              Nat.mul_le_mul_right 112 (by omega)
            omega
          have hent_ep :
              vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) 0 G.linksCap.toNat ⊢
              arrayAt (chainEpoch A.repAlloc) 112 (G.linksPtr + G.linksHead * 112#64) eps₁ ∗
              arrayAt (chainEpoch A.repAlloc) 112 G.linksPtr eps₂ ∗
              memRegion (G.linksPtr + BitVec.ofNat 64 (((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat)) * 112))
                ((G.linksHead.toNat - ((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat))) * 112) := by
            rw [← haddr1]
            exact Entails.trans hys_ent
              (sepConj_mono (arrayAt_chainEpochAt_entails_chainEpoch A.repAlloc _ ys₁)
                (sepConj_mono_left (arrayAt_chainEpochAt_entails_chainEpoch A.repAlloc _ ys₂)))
          refine SepWP.focus_weaken hent_ep (by sep_focus) ?_
          apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 446)
          wp_steps
          refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun hcl_c1 => ?_
          apply sepWP_seq_lscl_lr hcl_c1
          have hx1_1 : G.linksCap - G.linksHead = BitVec.ofNat 64 eps₁.length := by
            rw [heps₁_len, sub_eq_ofNat_sub (by omega)]
          have hslice1 := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl_c1 hdrop_slice
          simp only [dropChainEpochSliceSpec, chainEpochSize, chainEpochAlign, withMemEq] at hslice1
          dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hslice1
          wp_call hslice1 (⟨G.linksPtr + G.linksHead * 112#64, eps₁⟩, st)
          clear hslice1 hcl_c1
          let evs_a := w
          have hevs_a : FreeOnlyEvs evs_a := by dsimp only [evs_a]; assumption
          let s_r1 := sf
          have hacp_a : AllocCallPreserved s0 s_r1 := by dsimp only [s_r1]; simp only [wp_norm, arm64_norm, *]
          refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun hcl_r1 => ?_
          apply sepWP_seq_lscl hcl_r1 (mid := lsmpl.base 446)
          clear hcl_r1
          wp_steps
          refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun hcl_c2 => ?_
          have hx1_2 : BitVec.ofNat 64 (x :: tl).length - (G.linksCap - G.linksHead) =
              BitVec.ofNat 64 eps₂.length := by
            rw [heps₂_len, ofNat_sub_sub_eq hcap_lt_pow hhead (by omega) hlen_le]
          have hslice2 := subroutine_ok_withMemEq_of_withLsCodeLoaded (spec := dropChainEpochSliceSpec M A lim) hcl_c2 hdrop_slice
          simp only [dropChainEpochSliceSpec, chainEpochSize, chainEpochAlign, withMemEq] at hslice2
          dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hslice2
          wp_call hslice2 (⟨G.linksPtr, eps₂⟩, M.stepEvents evs_a st)
          clear hslice2 hcl_c2
          let evs_b := w_1
          have hevs_b : FreeOnlyEvs evs_b := by dsimp only [evs_b]; assumption
          have hacp_b : AllocCallPreserved s_r1 sf_1 := by dsimp only [s_r1]; simp only [wp_norm, arm64_norm, *]
          rw [← haddr1, heps₁_len, heps₂_len]
          refine SepWP.focus_weaken
            (vecDequeSlotsAt_wrap_rejoin 112 G.linksCap.toNat G.linksHead.toNat (x :: tl).length
              G.linksPtr hcap_lt hhead hlen_le hgt) (by sep_focus) ?_
          refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨evs_a ++ evs_b, LibsignalBinary.Heap.FreeOnlyEvs.append hevs_a hevs_b,
              hacp0.trans (hacp_a.trans hacp_b),
              by wp_norm_goal,
              (by simp only [wp_norm, arm64_norm, *] : _ = s0.trace).trans htr0,
              (by simp only [wp_norm, arm64_norm, *] : _ = s0.sp).trans hsp0,
              by wp_norm_goal,
              (by simp only [wp_norm, arm64_norm, *] : _ = s0.readReg64 .x21).trans hx21_0,
              (by simp only [wp_norm, arm64_norm, *] : _ = s0.readReg64 .x23).trans hx23_0,
              (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s0).trans hvregs0, ?_⟩
          unfold vecDequeHeader
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append,
            Nat.mul_comm, BitVec.add_assoc, BitVec.reduceAdd,
            hsp_sf, hsp0, stackAt_spqrSendCallee_eq_dropStack32 s.sp]
          exact Entails.of_eq (by sep_ac_rfl)
  · intro s1 P1 hpc1 _ hcl1 ⟨evs₁, hevs₁, hacp₁, hrun1, htr1, hsp1, hx20_1, hx21_1, hx23_1, hvregs1, hP1⟩
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    refine SepWP.weaken_pre hP1 ?_
    have hstep := step_drop_chain_tail_31a08_placed hdealloc hdrop_states s1 (M.stepEvents evs₁ st) x23 G c st1
      (spqrSendResultAt A.repAlloc ret none ∗ memRegion (s.sp + 0x1260#64) 40 ∗ Frame)
      hcl1 hpc1 hrun1 hx20_1 hx21_1 hx23_1 hcap_lt hsp1_align
    rw [hsp1] at hstep
    refine SepWP.mono hstep ?_
    intro sf Q _ _ ⟨evs₂, hevs₂, hacp₂, hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩
    refine ⟨evs₁ ++ evs₂, LibsignalBinary.Heap.FreeOnlyEvs.append hevs₁ hevs₂, hacp₁.trans hacp₂,
      hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1, ?_⟩
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
    exact Entails.trans hQ (Entails.of_eq (by sep_ac_rfl))

/-! ## 4. Chain Step (`+3712 .. +4000`) -/

/-- `+3800 -> +4000` (`0x31734 -> 0x317fc`, 12 instructions = 48 bytes):
    After `<spqr::chain::Chain>::into_pb` writes `ProtoRepr.chainPBAt A.repAlloc (s.sp + 0x1060#64) ch`,
    loads `x25 := [s.sp + 0x1060]` and copies the remaining 72 bytes (`+8..+80`) to `[s.sp + 0xd90..0xdd8]`,
    forming `optChainPBRegSlotAt A.repAlloc (s.sp + 0xd90#64) x25 (some ch)` and jumping to `+4000`. -/
theorem step_post_chain_into_pb_31734_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {ext : String → Option (State → State)}
    (s : State) (ch : ChainPB) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 3800#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = s.sp + 0x1060#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4000#64) s
      (CryptoVerification.SpqrV1.ProtoRepr.chainPBAt A.repAlloc (s.sp + 0x1060#64) ch ∗
        memRegion (s.sp + 0xd90#64) 72 ∗ Frame)
      (fun sf Q => VmPreserved s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg32 .x24 = s.readReg32 .x24 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ optChainPBRegSlotAt A.repAlloc (s.sp + 0xd90#64) (sf.readReg64 .x25) (some ch) ∗
          memRegion (s.sp + 0x1060#64) 80 ∗ Frame)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    rw [chainPBAt_protoRepr_eq_exists A.repAlloc (s.sp + 4192#64) ch,
        memRegion_72_words9 (s.sp + 3472#64)]
    wp_pull_exists; rename_i d1 d2 d3 d4 d5 d6 d7 d8 d9 g
    refine SepWP.focus_weaken (chainPBAt_expose_cap A.repAlloc g (s.sp + 4192#64) ch) (by sep_focus) ?_
    wp_focus_pure; intro hcap_ne
    refine SepWP.focus_weaken (chainPBRestAt_entails_words9 A.repAlloc g (s.sp + 4192#64) ch) (by sep_focus) ?_
    wp_pull_exists; rename_i w8 w9
    wp_focus_pure; intro hw
    wp_steps
    have hd88 : (s.sp + 3472#64) - 8#64 = s.sp + 3464#64 := by bv_omega
    have hrest := words9_entails_chainPBRestAt A.repAlloc g (s.sp + 3464#64) ch w8 w9 hw
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrest
    have h80 := words10_to_memRegion_80 (s.sp + 4192#64)
      g.linksCap g.linksPtr (BitVec.ofNat 64 (g.epochs.zip ch.links).length)
      g.nextRoot.cap g.nextRoot.ptr (BitVec.ofNat 64 ch.nextRoot.length)
      ch.currentEpoch ch.sendEpoch w8 w9
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h80
    refine SepWP.focus_weaken hrest (by sep_focus) ?_
    refine SepWP.focus_weaken h80 (by sep_focus) ?_
    refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
    dsimp only [optChainPBRegSlotAt]
    rw [hd88]
    refine Entails.trans (Entails.of_eq (show memRegion (s.sp + 4192#64) 80 ∗
        chainPBRestAt A.repAlloc g (s.sp + 3464#64) ch ∗ Frame =
        chainPBRestAt A.repAlloc g (s.sp + 3464#64) ch ∗
        memRegion (s.sp + 4192#64) 80 ∗ Frame by sep_ac_rfl)) ?_
    refine sepConj_mono_left ?_
    refine Entails.sepExists_right g ?_
    exact Entails.pure_right ⟨by wp_norm_goal, hcap_ne⟩ (Entails.refl _))

/-- `+3712 -> lsmpl.base 365` (`0x316dc -> 0x60514`, 22 instructions = 88 bytes):
    Extracts `(mkCap, mkPtr, msgKey.length)` from `sendKeyOkAt` at `s.sp + 0x1260#64` into
    `[s.sp + 0x28]`, `[s.sp + 0x8]`, and `x22`, copies `chainRepr A.repAlloc (s.sp + 0x590#64) c2` to
    `s.sp + 0x1260#64`, and calls `<spqr::chain::Chain>::into_pb` (`x8 = s.sp + 0x1060#64`, `x0 = s.sp + 0x1260#64`). -/
theorem step_pre_chain_into_pb_316dc_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {ext : String → Option (State → State)}
    (s : State) (idx : BitVec 32) (msgKey : Bytes) (c2 : Chain) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 3712#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (lsmpl.base 365) s
      (((s.sp + 0x1260#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x1268#64) ↦₃₂ idx) ∗
        memRegion (s.sp + 0x126c#64) 4 ∗ vecU8 A.repAlloc (s.sp + 0x1270#64) msgKey ∗
        memRegion (s.sp + 0x1288#64) 48 ∗
        chainRepr A.repAlloc (s.sp + 0x590#64) c2 ∗
        memRegion (s.sp + 0x28#64) 8 ∗
        memRegion (s.sp + 0x8#64) 8 ∗ Frame)
      (fun sf Q => VmPreserved s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x8 = s.sp + 0x1060#64 ∧
        sf.readReg64 .x30 = spqrSendPlacedEntry + 3800#64 ∧
        sf.readReg64 .x22 = BitVec.ofNat 64 msgKey.length ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg32 .x24 = s.readReg32 .x24 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ ∃∗ G : ChainGhost, ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          chainAt A.repAlloc (s.sp + 0x1260#64) G c2 ∗
          ((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗
          vecU8Heap A.repAlloc mkCap mkPtr msgKey ∗
          memRegion (s.sp + 0x590#64) 88 ∗ Frame)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    rw [ProofLib.memRegion_eight (s.sp + 40#64), ProofLib.memRegion_eight (s.sp + 8#64)]
    wp_pull_exists; rename_i old28 old8
    have hok_words := sendKeyOkSlot_entails_words11 A.repAlloc (s.sp + 4704#64) idx msgKey
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hok_words
    refine SepWP.focus_weaken hok_words (by sep_focus) ?_
    wp_pull_exists; rename_i mkCap mkPtr d1 d5 d6 d7 d8 d9 d10
    refine SepWP.focus_weaken (chainRepr_entails_words11 A.repAlloc (s.sp + 1424#64) c2) (by sep_focus) ?_
    wp_pull_exists; rename_i G pad
    wp_focus_pure; intro hcap_ne
    wp_steps
    have hpack := words11_entails_chainRepr A.repAlloc (s.sp + 4704#64) G c2 pad
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack
    have h88 := words11_to_memRegion_88 (s.sp + 1424#64)
      G.linksCap G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip c2.links).length)
      G.nextRoot.cap G.nextRoot.ptr (BitVec.ofNat 64 c2.nextRoot.length)
      c2.currentEpoch c2.sendEpoch (c2.params.maxOooKeys ++ c2.params.maxJump) (pad ++ c2.dir.toI32)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h88
    refine SepWP.focus_weaken hpack (by sep_focus) ?_
    refine SepWP.focus_weaken h88 (by sep_focus) ?_
    refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
    dsimp only [chainRepr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro G'
    refine Entails.sepExists_right G' (Entails.sepExists_right mkCap
      (Entails.sepExists_right mkPtr ?_))
    exact Entails.of_eq (by sep_ac_rfl))

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainStepPlacedBudget
