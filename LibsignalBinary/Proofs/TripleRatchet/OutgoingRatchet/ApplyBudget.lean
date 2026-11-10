/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Apply
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `OutgoingTripleRatchet::apply_to_session_state`

Proves `[LibsignalPlacement]` `RustCliAllocBudget` contracts (`DefsBudget.otrApplyRawSpec` and
`otrApplyPlacedSpec`) for `<OutgoingTripleRatchet>::apply_to_session_state`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.ApplyBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (SenderChain OutgoingTripleRatchet)
open CryptoVerification
  (LibsignalPlacement blkPC_20 blkPl_20 lsρ lsLogFilterAddr
   lsRustNoAllocShimSym lsRustAllocSym lsRustDeallocSym
   ls_hook_ok_of_mem)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SenderChainGhost SessionGhost sessionStateAt otrAt)
open CryptoVerification.LibsignalTripleRatchet
  (OtrApplyGhost noAllocShimSpec smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
  (otrApplyInternalStack afterOtrApply
   keyToBytes32_length pack64 stackAt_otrApply_fold
   vecU8Buf_dealloc memRegion_32_cells otrAt_apply_split otr_fold_memRegion
   vecU8Buf_cap_lt vecU8Buf_dealloc_32 sessionStateAt_eq_apply
   sessionStateAt_sender_some vecU8Buf_of_cells_32 applyRel_afterOtrApply
   smallRootStack_split_otrApply)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.ApplyFrameFacts
  (sepWP_unpack_stackAt_otrApply)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
   FitsEvents FitsEnv SeqEnv FreeOnlyEvs rustAllocEvents rustDeallocEvents
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocNoOomExternSpecWithStack rustCliDeallocBudgetExternSpecWithStack
   subroutine_ok_rustCliAllocNoOom_externWithStack
   subroutine_ok_rustCliDeallocBudget_externWithStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.DefsBudget
  (OtrApplyEnv otrApplyRawSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

private theorem addsPState64_hi_false_aux {cap : BitVec 64}
    (h1 : (32#64).ule cap = true) (h2 : cap.ult 0x8000000000000000#64 = true) :
    ConditionHolds CondCode.HI (addsPState64 (cap - 1#64) 3#64) = false := by
  unfold ConditionHolds addsPState64 AddWithCarry64
  dsimp only
  bv_kernel

private theorem addsPState64_hi_false {cap ptr : BitVec 64}
    (h : 32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) :
    ConditionHolds CondCode.HI (addsPState64 (cap - 1#64) 3#64) = false := by
  apply addsPState64_hi_false_aux
  · rw [BitVec.ule_eq_decide, decide_eq_true_eq]; exact h.1
  · rw [BitVec.ult_eq_decide, decide_eq_true_eq]; exact h.2.1

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Budget-threaded relocatable root-level specification of `OTR::apply_to_session_state`
    (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
def otrApplyPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (OtrApplyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st OtrApplyEnv⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyPlacedSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜OtrApplyEnv evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyPlacedSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

private theorem instantiate_otrApplyRaw_post {M : AllocCostModel}
    {prog : Program} {target_pc : BitVec 64} {s s0 : State} {P R : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (x : OtrApplyGhost) (stB : M.σ) (G' : SessionGhost) (evs : List AllocEvent)
    (hval : OtrApplyEnv evs)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
          (⌜x.G.AfterOutgoingRatchetApply G' ∧ G'.pq = ⟨x.pqCap, x.pqPtr⟩⌝ ∗
            sessionStateAt A.repAlloc x.ss G' (x.ot.applyToSessionState x.st)) ∗
          memRegion x.o 200 ∗ stackAt s0.sp otrApplyInternalStack ∗
          A.pool lim (M.stepEvents evs stB) sf) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (otrApplyRawSpec M A lim).post (x, stB) s0 sf ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  refine SepWP.mono h fun sf P_f _ _ ⟨h1, h2⟩ => ⟨fun hm => ?_, h2⟩
  have hm1 : sf.mem ⊨
      (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyRawSpec
        (A.atState lim (M.stepEvents evs stB) sf)).post x s0 sf ∗ R :=
    Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro G'))))
      (h1 hm)
  have hm2 : sf.mem ⊨
      (⌜OtrApplyEnv evs⌝ ∗
        (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyRawSpec
          (A.atState lim (M.stepEvents evs stB) sf)).post x s0 sf) ∗ R :=
    Satisfies.mono
      (sepConj_mono_left (Entails.pure_right hval (Entails.refl _)))
      hm1
  exact Satisfies.mono
    (sepConj_mono_left (Entails.sepExists_intro evs))
    hm2

set_option maxHeartbeats 800000 in
/-- Relocatable `OTR::apply_to_session_state` meets
    `DefsBudget.otrApplyRawSpec M A lim` from budget hook `subroutine_ok` contracts. -/
theorem otrApplyRaw_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_20).rebase (blkPl_20).base H)
      (lsρ lsRustNoAllocShimSym) (withVmPreserved noAllocShimSpec))
    (halloc : subroutine_ok ((blkPC_20).rebase (blkPl_20).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_20).rebase (blkPl_20).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_20).rebase (blkPl_20).base H) (blkPl_20).base
      (otrApplyRawSpec M A lim) := by
  have halloc' : subroutine_ok ((blkPC_20).rebase (blkPl_20).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc)
  have hdealloc' : subroutine_ok ((blkPC_20).rebase (blkPl_20).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetExternSpecWithStack M A lim allocHookStack) :=
    subroutine_ok_rustCliDeallocBudget_externWithStack (stk := allocHookStack)
      (by decide) (by decide) hdealloc
  dsimp only [withVmPreserved, noAllocShimSpec] at hshim
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  dsimp only [rustCliDeallocBudgetExternSpecWithStack,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk] at hdealloc'
  refine subroutine_ok_mono (spec := {
    pre := fun (x, stB) s =>
      ⌜FitsEnv M lim stB OtrApplyEnv ∧
        s.readReg64 .x0 = x.o ∧ s.readReg64 .x1 = x.ss ∧ x.st.senderChain.isSome⌝ ∗
        otrAt A.repAlloc x.o x.pqCap x.pqPtr x.ot ∗
        sessionStateAt A.repAlloc x.ss x.G x.st ∗
        stackAt s.sp otrApplyInternalStack ∗ A.pool lim stB s
    post := (otrApplyRawSpec M A lim).post }) ?_ ?_ (fun _ _ _ _ h => h)
  swap
  · rintro ⟨x, stB⟩ R s0 hpre
    dsimp only [otrApplyRawSpec,
      CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyRawSpec,
      RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1, hpre.2.1⟩, hpre.2.2⟩
  wp_init gx s0
  rcases gx with ⟨⟨o, pqCap, pqPtr, ot, ss, G, st⟩, stB⟩
  dsimp only at *
  have hEnv : FitsEnv M lim stB OtrApplyEnv := by assumption
  have hsc_isSome : st.senderChain.isSome = true := by assumption
  obtain ⟨sc, hsc⟩ : ∃ sc, st.senderChain = some sc := Option.isSome_iff_exists.mp hsc_isSome
  refine sepWP_unpack_stackAt_otrApply s0.sp (by sep_focus)
    fun s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s3 => ?_
  refine SepWP.fold (otrAt_apply_split A.repAlloc o pqCap pqPtr ot) (by sep_focus) ?_
  refine SepWP.fold (sessionStateAt_sender_some A.repAlloc ss G st sc hsc) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro sg
  refine SepWP.focus_pure (by sep_focus) fun hGs => ?_
  let sg_id : SenderChainGhost := { sg with ck := sg.ck }
  have hG_eq : G = { G with sender := some sg_id, pq := G.pq } := by
    cases G; dsimp only at hGs; subst hGs; rfl
  let sc_id : SenderChain := { sc with chainKey := sc.chainKey }
  have hst_eq : st = { st with senderChain := some sc_id, pqRatchetState := st.pqRatchetState } := by
    cases st; dsimp only at hsc; subst hsc; rfl
  conv =>
    arg 4
    rw [hG_eq, hst_eq,
      sessionStateAt_eq_apply A.repAlloc ss G st sg sc G.pq st.pqRatchetState sg.ck sc.chainKey]
  clear hG_eq hst_eq sg_id sc_id
  refine SepWP.fold (vecU8Buf_cap_lt A.repAlloc sg.srk.cap sg.srk.ptr sg.srk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hsrk_cap => ?_
  refine SepWP.fold (vecU8Buf_dealloc_32 A.repAlloc sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key)
    (keyToBytes32_length _)) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hck_bounds => ?_
  refine SepWP.fold (vecU8Buf_dealloc A.repAlloc G.pq.cap G.pq.ptr st.pqRatchetState) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpq_bounds => ?_
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_shim : sf.trace = s0.trace := by assumption
  have hsp_shim : sf.sp = s0.sp - 128#64 := by simp only [wp_norm, arm64_norm, *]
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  have hfe_alloc : FitsEvents M lim stB [.alloc 32] := by
    simpa [rustAllocEvents] using hEnv (rustAllocEvents 32 1) (Or.inl rfl)
  rcases hfe_alloc with ⟨⟨hwma, henf, hram, hva⟩, -⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos32 : 0 < (32 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum32 : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (32, 1, stB)
  have hck_null : sf_1.readReg64 Reg.x0 ≠ 0#64 := by assumption
  have hck_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hck_null
  have htr_alloc : sf_1.trace = sf.trace := by assumption
  have hsp_alloc : sf_1.sp = s0.sp - 128#64 := by simp only [wp_norm, arm64_norm, *]
  wp_simp_pre only [memRegion_32_cells,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  have hsrk_ne : (sg.srk.cap + 1#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; bv_omega
  have hck_hi : ConditionHolds CondCode.HI (addsPState64 (sg.ck.cap - 1#64) 3#64) = false :=
    addsPState64_hi_false hck_bounds
  have hck_pos : 0 < sg.ck.cap.toNat := by omega
  have hck_sum : sg.ck.cap.toNat + 1 ≤ 2 ^ 63 := by omega
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  simp only [State.setMem_setMem]
  wp_call hdealloc' (sg.ck.ptr, sg.ck.cap.toNat, 1, M.stepEvents (rustAllocEvents 32 1) stB)
  have htr_dealloc1 : sf_2.trace = sf_1.trace := by assumption
  have hsp_dealloc1 : sf_2.sp = s0.sp - 128#64 := by simp only [wp_norm, arm64_norm, *]
  have hcells32 :=
    vecU8Buf_of_cells_32 A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) ot.senderChainKey.key hck_null
  rw [A.repAlloc_live_norm] at hcells32
  have hfree_dealloc1 : FreeOnlyEvs (rustDeallocEvents sg.ck.cap.toNat 1) := by
    intro ev hev
    simp only [rustDeallocEvents, List.mem_singleton] at hev
    subst hev
    exact ⟨1, sg.ck.cap.toNat, rfl⟩
  let sc' : SenderChain := { sc with chainKey := ot.senderChainKey }
  by_cases hpq0 : G.pq.cap = (0 : BitVec 64)
  · have hpq_beq : (G.pq.cap == 0#64) = true := beq_iff_eq.mpr hpq0
    rw [ite_eq_left_iff.mpr (fun h => absurd hpq0 h)]
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    let evs1 := rustAllocEvents 32 1 ++ rustDeallocEvents sg.ck.cap.toNat 1
    have hval1 : OtrApplyEnv evs1 :=
      Or.inr ⟨rustAllocEvents 32 1, rustDeallocEvents sg.ck.cap.toNat 1, rfl, rfl, hfree_dealloc1⟩
    have hstep1 :
        M.stepEvents (rustDeallocEvents sg.ck.cap.toNat 1)
          (M.stepEvents (rustAllocEvents 32 1) stB) =
        M.stepEvents evs1 stB :=
      (M.stepEvents_append (rustAllocEvents 32 1) (rustDeallocEvents sg.ck.cap.toNat 1) stB).symm
    rw [hstep1]
    apply instantiate_otrApplyRaw_post ⟨o, pqCap, pqPtr, ot, ss, G, st⟩ stB
      (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr) evs1 hval1
    dsimp only
    wp_simp_pre only [hsp_alloc, hsp_dealloc1]
    refine SepWP.fold hcells32 (by sep_focus) ?_
    refine SepWP.fold (otr_fold_memRegion o pqCap pqPtr
      (BitVec.ofNat 64 ot.pqrState.length)
      (pack64 ((keyToBytes32 ot.senderChainKey.key).take 8))
      (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 8).take 8))
      (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 16).take 8))
      (pack64 ((keyToBytes32 ot.senderChainKey.key).drop 24))
      ot.senderChainKey.index) (by sep_focus) ?_
    refine SepWP.fold (stackAt_otrApply_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (by sep_focus) ?_
    have hpost_ss :
        sessionStateAt A.repAlloc ss (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
          (ot.applyToSessionState st) =
        sessionStateAt A.repAlloc ss
          { G with sender := some ({ sg with ck := ⟨32#64, sf_1.readReg64 Reg.x0⟩ }), pq := ⟨pqCap, pqPtr⟩ }
          { st with senderChain := some sc', pqRatchetState := ot.pqrState } := by
      simp [afterOtrApply, OutgoingTripleRatchet.applyToSessionState, hsc, sc']
    rw [hpost_ss, sessionStateAt_eq_apply A.repAlloc ss G st sg sc ⟨pqCap, pqPtr⟩ ot.pqrState
      ⟨32#64, sf_1.readReg64 Reg.x0⟩ ot.senderChainKey]
    have hrel := applyRel_afterOtrApply G sg hGs (sf_1.readReg64 Reg.x0) pqCap pqPtr
    have htr_all : sf_2.trace = s0.trace := by rw [htr_dealloc1, htr_alloc, htr_shim]
    wp_done
  · have hpq_beq : (G.pq.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hpq0
    rw [ite_eq_right_iff.mpr (fun h => absurd h hpq0)]
    have hpq_pos : 0 < G.pq.cap.toNat :=
      Nat.pos_of_ne_zero fun h => hpq0 (BitVec.eq_of_toNat_eq h)
    have hpq_sum : G.pq.cap.toNat + 1 ≤ 2 ^ 63 := by
      have := hpq_bounds.2.1
      omega
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc' (G.pq.ptr, G.pq.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents sg.ck.cap.toNat 1)
        (M.stepEvents (rustAllocEvents 32 1) stB))
    have htr_dealloc2 : sf_3.trace = sf_2.trace := by assumption
    have hfree_dealloc2 : FreeOnlyEvs (rustDeallocEvents G.pq.cap.toNat 1) := by
      intro ev hev
      simp only [rustDeallocEvents, List.mem_singleton] at hev
      subst hev
      exact ⟨1, G.pq.cap.toNat, rfl⟩
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    let evs2 :=
      (rustAllocEvents 32 1 ++ rustDeallocEvents sg.ck.cap.toNat 1) ++
        rustDeallocEvents G.pq.cap.toNat 1
    have hval2 : OtrApplyEnv evs2 :=
      Or.inr ⟨rustAllocEvents 32 1,
        rustDeallocEvents sg.ck.cap.toNat 1 ++ rustDeallocEvents G.pq.cap.toNat 1,
        List.append_assoc _ _ _, rfl, fun ev hev => by
          rcases List.mem_append.mp hev with h1 | h2
          · exact hfree_dealloc1 ev h1
          · exact hfree_dealloc2 ev h2⟩
    have hstep2 :
        M.stepEvents (rustDeallocEvents G.pq.cap.toNat 1)
          (M.stepEvents (rustDeallocEvents sg.ck.cap.toNat 1)
            (M.stepEvents (rustAllocEvents 32 1) stB)) =
        M.stepEvents evs2 stB := by
      dsimp only [evs2]
      rw [M.stepEvents_append, M.stepEvents_append]
    rw [hstep2]
    apply instantiate_otrApplyRaw_post ⟨o, pqCap, pqPtr, ot, ss, G, st⟩ stB
      (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr) evs2 hval2
    dsimp only
    wp_simp_pre only [hsp_alloc, hsp_dealloc1]
    refine SepWP.fold hcells32 (by sep_focus) ?_
    refine SepWP.fold (otr_fold_memRegion o pqCap pqPtr
      (BitVec.ofNat 64 ot.pqrState.length)
      (pack64 ((keyToBytes32 ot.senderChainKey.key).take 8))
      (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 8).take 8))
      (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 16).take 8))
      (pack64 ((keyToBytes32 ot.senderChainKey.key).drop 24))
      ot.senderChainKey.index) (by sep_focus) ?_
    refine SepWP.fold (stackAt_otrApply_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (by sep_focus) ?_
    have hpost_ss :
        sessionStateAt A.repAlloc ss (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
          (ot.applyToSessionState st) =
        sessionStateAt A.repAlloc ss
          { G with sender := some ({ sg with ck := ⟨32#64, sf_1.readReg64 Reg.x0⟩ }), pq := ⟨pqCap, pqPtr⟩ }
          { st with senderChain := some sc', pqRatchetState := ot.pqrState } := by
      simp [afterOtrApply, OutgoingTripleRatchet.applyToSessionState, hsc, sc']
    rw [hpost_ss, sessionStateAt_eq_apply A.repAlloc ss G st sg sc ⟨pqCap, pqPtr⟩ ot.pqrState
      ⟨32#64, sf_1.readReg64 Reg.x0⟩ ot.senderChainKey]
    have hrel := applyRel_afterOtrApply G sg hGs (sf_1.readReg64 Reg.x0) pqCap pqPtr
    have htr_all : sf_3.trace = s0.trace := by rw [htr_dealloc2, htr_dealloc1, htr_alloc, htr_shim]
    wp_done

/-- Relocatable `OTR::apply_to_session_state` meets
    `DefsBudget.otrApplyRawSpec M A lim` from `HookSat`. -/
theorem otrApplyRaw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_shim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_20).rebase (blkPl_20).base H) (blkPl_20).base
      (otrApplyRawSpec M A lim) :=
  otrApplyRaw_placed_ok_of_contracts
    (ls_hook_ok_of_mem h_shim) (ls_hook_ok_of_mem h_alloc) (ls_hook_ok_of_mem h_dealloc)

/-- Relocatable `OTR::apply_to_session_state` meets `otrApplyPlacedSpec M A lim`. -/
theorem otrApply_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_shim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_20).rebase (blkPl_20).base H) (blkPl_20).base
      (otrApplyPlacedSpec M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, stB⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre_eq :
      (otrApplyPlacedSpec M A lim).pre (x, stB) s0 ∗ R =
      (otrApplyRawSpec M A lim).pre (x, stB) s0 ∗
        (((lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 65536#64) 61312) ∗ R) := by
    dsimp only [otrApplyPlacedSpec, otrApplyRawSpec,
      CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyRawSpec, stackAt]
    rw [smallRootStack_split_otrApply]
    sep_ac_rfl
  refine (otrApplyRaw_placed_ok h_shim h_alloc h_dealloc).mono_outcome (x, stB)
    (((lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 65536#64) 61312) ∗ R)
    s0 hpc hrun (hpre_eq ▸ hpre) hsp fun sf hout => ?_
  rcases hout with ⟨h1, h2, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨h1, h2, ?_⟩
    dsimp only [otrApplyRawSpec] at hpost
    dsimp only [otrApplyPlacedSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    obtain ⟨evs, hevs⟩ := hpost
    refine ⟨evs, ?_⟩
    have hpost_eq :
        ((⌜OtrApplyEnv evs⌝ ∗
          (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyRawSpec
            (A.atState lim (M.stepEvents evs stB) sf)).post x s0 sf) ∗
          (((lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 65536#64) 61312) ∗ R)) =
        ((⌜OtrApplyEnv evs⌝ ∗
          (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyPlacedSpec
            (A.atState lim (M.stepEvents evs stB) sf)).post x s0 sf) ∗ R) := by
      dsimp only [CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyRawSpec,
        CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyPlacedSpec, stackAt]
      rw [smallRootStack_split_otrApply]
      sep_ac_rfl
    exact hpost_eq ▸ hevs
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

theorem hookSat_noAllocShim_of_rustAllocShimVm {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym rustAllocShimVmSpec) :
    HookSat H sym (withVmPreserved noAllocShimSpec) := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun u R s0 hrun hpre hsp => ?_⟩
  have hpre' : s0.mem ⊨ rustAllocShimVmSpec.pre u s0 ∗ R := by
    simpa [rustAllocShimVmSpec, withVmPreserved, noAllocShimSpec] using hpre
  rcases hok u R s0 hrun hpre' hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hoom, hpost⟩ | ⟨hflt, hpc, hpost⟩ | ⟨htrp, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocShimVmSpec] at hpost
    dsimp only [withVmPreserved, noAllocShimSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1.2, hpost.1.1.2.1, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hoom, hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hflt, hpc, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨htrp, hpost⟩))

theorem otrApply_placed_ok_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_shim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_20).rebase (blkPl_20).base H) (blkPl_20).base
      (otrApplyPlacedSpec M A lim) :=
  otrApply_placed_ok (hookSat_noAllocShim_of_rustAllocShimVm h_shim) h_alloc h_dealloc

end LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.ApplyBudget
