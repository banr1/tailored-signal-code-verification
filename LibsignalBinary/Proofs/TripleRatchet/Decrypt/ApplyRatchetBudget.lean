/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchet
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Segment 9 (`apply_to_session_state`) Proofs

Re-exports the Segment 9 allocator event envelopes and block `130` (`159`) theorems from
`ApplyRatchetBudgetAux`, and proves the block `433` (`549`) theorems
(`applyRatchet_from_6d0_549_placed`, `applyRatchet_549_placed_ok`, and their `_x` `decFn`
variants) over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (
  Crypto SessionState SignalProtocolError TripleRatchet
)
open CryptoVerification (
  LibsignalPlacement lsMemcpySym lsRustDeallocSym lsmpl lsρ
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost decryptDraws okTagVec protocolAddressAt sessionStateAt signalMessageAt
  tapeAfter uuidTryParse vecResultAt
)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded SpqrModel TrGhost TryDecryptGhost extHookStack logOff
  sessionMemcpyRegionSpec trApplyStack trApplyStackX trAt tryDecryptFnSpec
  tryDecryptSpec withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  clearUpkStack clearUpkStackX
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_434 blkLib_eq_434 blkPl_434 logOff_tryDecryptPlacedImg
  tryDecryptCommonHeap tryDecryptPlacedImg tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt (
  Satisfies.mono_focus SepWP.setPC_setMem_ite_false
  SepWPp.elim_exists SepWPp.elim_exists_focus SepWPp.elim_memRegion8_focus
  SepWPp.elim_pure SepWPp.elim_pure_focus SepWPp.elim_vecU8_focus SepWPp.mono_focus
  allocHookStack_to_subStack applyRatchet_local_frame_entails_memRegion
  applyRatchet_ret_split applyRatchet_scr_split clearUpkStackX_to_subStack
  clearUpkStack_to_subStack decRel_of_trApplyRel decResultAt_ok_of_parts
  extHookStack_to_subStack extHookStack_to_trApplyStackX layoutOk_of_cap_ne_zero
  length_trStackBytes newPqr_dealloc_prep' newPqr_zero_prep noPanic_callee
  sepWPp_to_reaches_outcome stackAt_rootStack_of_parts stackAt_sub_split
  trApplyStackX_to_clearUpkStackX trApplyStack_to_clearUpkStack trAt_eq_stack_heap
  trAt_eq_withoutPq trAt_of_stack_heap trAt_of_withoutPq trAt_senderPad_len
  trHeapPart trStackBytes trWithoutPqAt tryDecryptSavedRegs_entails_memRegion
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt.AuthDecryptFacts (
  spAligned_of_sp_eq
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (
  hooksException sepWP_seg_ls_vm
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  clearUpkSpec clearUpkSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustDeallocExternSpecWithStack withStack
)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget (
  TrApplyEnv trApplySpec trApplySpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  S9SeamPlaced S9SeamXPlaced tryDecryptFnRawSpecPlaced tryDecryptFnSpecPlaced
  tryDecryptRawSpecPlaced tryDecryptSpecPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget (
  SepWPp.call_cro_frame_placed SepWPp.call_frame_placed SepWPp.of_sepWP_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux (
  protocolAddressAt_atState sessionStateAt_atState signalMessageAt_atState
  trAt_atState vecResultAt_atState vecU8_atState
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

private theorem sepWP_seg_433 [LibsignalPlacement] {H : String → Option (State → State)}
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_434).rebase (blkPl_434).base (hooksException H)) mid (s.setMem m_strip) Pre
        (fun sm' Pm => ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
          SepWP ((blkPC_434).rebase (blkPl_434).base H) target (sm'.setMem m_real) Pm post oom)) :
    SepWP ((blkPC_434).rebase (blkPl_434).base H) target s Pre post oom :=
  sepWP_seg_ls_vm (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H)) blkLib_eq_434 (by rfl) hseg

local macro "wp_sync_433 " mid:term : tactic =>
  `(tactic| (
    apply sepWP_seg_433 (mid := $mid); intro _m_strip; wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by wp_norm_lhs)) (hnext := ?_)))

/-! ## 1. Re-Exports from `ApplyRatchetBudgetAux` (Envelopes & Block `130` / `159` Proofs) -/

abbrev s9From6d0Env := ApplyRatchetBudgetAux.s9From6d0Env
abbrev s9Env := ApplyRatchetBudgetAux.s9Env
abbrev freeOnlyEvs_rustDeallocEvents := ApplyRatchetBudgetAux.freeOnlyEvs_rustDeallocEvents

abbrev applyRatchet_from_6d0_159_placed := @ApplyRatchetBudgetAux.applyRatchet_from_6d0_159_placed
abbrev applyRatchet_159_placed_ok := @ApplyRatchetBudgetAux.applyRatchet_159_placed_ok
abbrev applyRatchet_from_6d0_159_placed_x := @ApplyRatchetBudgetAux.applyRatchet_from_6d0_159_placed_x
abbrev applyRatchet_159_placed_ok_x := @ApplyRatchetBudgetAux.applyRatchet_159_placed_ok_x

/-! ## 2. Block `433` (`549`) Segment-9 Proofs (`S9SeamPlaced` & `S9SeamXPlaced`) -/

set_option maxHeartbeats 800000 in
theorem applyRatchet_from_6d0_549_placed [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 58)
      (withLsCodeRoLoaded lsmpl (trApplySpec M A lim)))
    (hClearUpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 35)
      (withLsCodeRoLoaded lsmpl (clearUpkSpec M A lim)))
    (hmemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsMemcpySym)
      sessionMemcpyRegionBudgetSpec)
    (x : TryDecryptGhost) (st_init st_cur : M.σ)
    (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (newPqrCap newPqrPtr ptCap ptPtr : BitVec 64)
    (R : SepProp) (s0 s1 : State)
    (hok : (x.model C S uuidTryParse).1 = .ok pt)
    (hst : (x.model C S uuidTryParse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage)
    (hs1 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st_cur s9From6d0Env)
    (hpad : trG.ratchet.senderPad.length = 100)
    (hnew_le : newPqrState.length ≤ newPqrCap.toNat)
    (hnew_lt : newPqrCap.toNat < 2 ^ 63)
    (hnew_nz : newPqrPtr ≠ 0)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_nz : ptPtr ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hpc1 : s1.pc = (blkPl_434).base + 1744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1504#64)
    (hsp_al1 : s1.spAligned = true)
    (htr1 : s1.trace = s0.trace)
    (hcl1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hx9_1 : s1.readReg64 .x9 = s0.sp - 800#64)
    (hx19_1 : s1.readReg64 .x19 = x.ret)
    (hx20_1 : s1.readReg64 .x20 = s0.sp - 1184#64)
    (hx21_1 : s1.readReg64 .x21 = x.ss)
    (hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length)
    (_hx29_1 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0) :
    SepWPp ((blkPC_434).rebase (blkPl_434).base H) (s0.readReg64 .lr) s1
      (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
       trWithoutPqAt A.repAlloc (s0.sp - 1448#64) trG.ratchet tr ∗
       ((s0.sp - 1272#64) ↦₆₄ trG.pq.cap) ∗
       ((s0.sp - 1264#64) ↦₆₄ trG.pq.ptr) ∗
       ((s0.sp - 1256#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       (if newPqrCap = 0 then emp else (A.repAlloc.live newPqrPtr newPqrCap.toNat 1 ∗ (newPqrPtr ↦ₛ newPqrState)) ∗
         memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
       ((s0.sp - 528#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 520#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 512#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (if ptCap = 0 then emp else (A.repAlloc.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt)) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       memRegion x.ret 8 ∗
       memRegion (x.ret + 8#64) 8 ∗
       memRegion (x.ret + 16#64) 8 ∗
       memRegion (x.ret + 24#64) 8 ∗
       memRegion (x.ret + 32#64) 16 ∗
       memRegion (s0.sp - 1504#64) 8 ∗
       ((s0.sp - 1496#64) ↦₆₄ newPqrCap) ∗
       memRegion (s0.sp - 1488#64) 24 ∗
       ((s0.sp - 1464#64) ↦₆₄ newPqrPtr) ∗
       memRegion (s0.sp - 1456#64) 8 ∗
       memRegion (s0.sp - 1184#64) 8 ∗
       memRegion (s0.sp - 1176#64) 8 ∗
       memRegion (s0.sp - 1168#64) 8 ∗
       memRegion (s0.sp - 1160#64) 16 ∗
       memRegion (s0.sp - 1144#64) 8 ∗
       memRegion (s0.sp - 1136#64) 8 ∗
       memRegion (s0.sp - 1128#64) 8 ∗
       memRegion (s0.sp - 1120#64) 16 ∗
       memRegion (s0.sp - 1104#64) 264 ∗
       memRegion (s0.sp - 840#64) 120 ∗
       ((s0.sp - 720#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 712#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 704#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       memRegion (s0.sp - 696#64) 168 ∗
       memRegion (s0.sp - 504#64) 0x198 ∗
       protocolAddressAt A.repAlloc x.rem x.remA ∗
       protocolAddressAt A.repAlloc x.loc x.locA ∗
       signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
       logOff tryDecryptPlacedImg ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool lim st_cur s1)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (tryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv).post (x, st_init) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (tryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv).onPanic (x, st_init) s0 sf ∗ R)) := by
  simp only [wp_norm] at hpc1 hsp1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1184#64) (by sep_focus) fun w1184 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1176#64) (by sep_focus) fun w1176 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1168#64) (by sep_focus) fun w1168 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun w1128 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 8#64) (by sep_focus) fun wret8 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 16#64) (by sep_focus) fun wret16 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 24#64) (by sep_focus) fun wret24 => ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsMemcpySym)
  wp_sync_433 (lsρ lsMemcpySym)
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  refine SepWPp.mono_focus
    (trAt_of_withoutPq A.repAlloc s0.sp trG tr newPqrCap newPqrPtr newPqrState hnew_le hnew_lt hnew_nz)
    (by sep_focus) ?_
  rw [trAt_eq_stack_heap A.repAlloc (s0.sp - 1448#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } hpad]
  refine SepWPp.elim_exists_focus
    (Φ := fun pad : BitVec 32 =>
      ((s0.sp - 1448#64) ↦ₛ trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
        { tr with pqrState := newPqrState } pad) ∗
      trHeapPart A.repAlloc { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState })
    (by sep_focus) fun pad => ?_
  have hbs_len : (trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad).length = 264 :=
    length_trStackBytes _ _ pad hpad
  generalize hbs_def : trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad = bs at hbs_len ⊢
  rw [show memRegion (s0.sp - 1104#64) 264 = memRegion (s0.sp - 1104#64) bs.length by rw [hbs_len]]
  simp only [← sepConj_assoc]
  refine SepWPp.call_frame_placed (spec := sessionMemcpyRegionBudgetSpec)
    (x := (s0.sp - 1104#64, s0.sp - 1448#64, bs))
    (T := memRegion (s0.sp - 1104#64) bs.length ∗ ((s0.sp - 1448#64) ↦ₛ bs))
    (ret_pc := (blkPl_434).base + bv% (1248))
    hcl2 hmemcpy (by rfl) (by exact hrun1)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm, hbs_len]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ hm_pan => by dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx24_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx24_2 hvregs_2
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hvm2
  refine SepWPp.transport_budgetPool hvm2 (hnext := ?_)
  simp only [wp_norm]
  refine SepWPp.elim_pure_focus
    (φ := s2.readReg64 .x0 = s0.sp - 1104#64 ∧ s2.trace = s1.trace)
    (by sep_focus) fun ⟨_, htr2⟩ => ?_
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  rw [← hbs_def]
  refine SepWPp.mono_focus
    (trAt_of_stack_heap A.repAlloc (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } pad hpad)
    (by sep_focus) ?_
  rw [hbs_def]
  rw [stackAt_sub_split (s0.sp - 1504#64) trApplyStack (by decide)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsmpl.base 58)
  wp_sync_433 (lsmpl.base 58)
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  have hfit_tr : FitsEnv M lim st_cur TrApplyEnv := hs1.1.seq_left
  refine SepWPp.call_cro_frame_placed (spec := trApplySpec M A lim)
    (x := (⟨s0.sp - 1104#64, { trG with pq := ⟨newPqrCap, newPqrPtr⟩ },
            { tr with pqrState := newPqrState }, x.ss, x.G.afterTrFrom, st1⟩, st_cur))
    (T := trAt A.repAlloc (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
            { tr with pqrState := newPqrState } ∗
          sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
          stackAt (s0.sp - 1504#64) trApplyStack ∗ A.pool lim st_cur _)
    (ret_pc := (blkPl_434).base + bv% (1260))
    hcl3 hTrApply (by rfl) (by exact hrun2)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [trApplySpec, CryptoVerification.LibsignalTripleRatchet.trApplySpec]
        conv => lhs; rw [eq_true hfit_tr, pure_true, emp_sepConj, trAt_atState, sessionStateAt_atState, A.atState_pool]
        simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [trApplySpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ hm_pan => by dsimp only [trApplySpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx24_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx24_3 hvregs_3
  dsimp only [trApplySpec, CryptoVerification.LibsignalTripleRatchet.trApplySpec]
  simp only [wp_norm, hsp2]
  apply SepWPp.elim_exists; intro evs1
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hevs1
  apply SepWPp.elim_pure; intro htr3
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  apply SepWPp.elim_exists; intro G1
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hG1
  rw [sessionStateAt_atState]
  have hs2 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init (M.stepEvents evs1 st_cur) FreeOnlyEvs :=
    hs1.step (fun _ _ h1 h2 => SeqEnv.append h1 h2) hevs1
  refine SepWPp.mono_focus (trApplyStack_to_clearUpkStack s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl3 (mid := lsmpl.base 35)
  wp_sync_433 (lsmpl.base 35)
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hcl4
  refine SepWPp.call_cro_frame_placed (spec := clearUpkSpec M A lim)
    (x := (⟨x.ss, G1, ({ tr with pqrState := newPqrState }).applyToSessionState st1⟩,
           M.stepEvents evs1 st_cur))
    (T := sessionStateAt A.repAlloc x.ss G1 (({ tr with pqrState := newPqrState }).applyToSessionState st1) ∗
          A.pool lim (M.stepEvents evs1 st_cur) _ ∗ stackAt (s0.sp - 1504#64) clearUpkStack)
    (ret_pc := (blkPl_434).base + bv% (1268))
    hcl4 hClearUpk (by rfl) (by exact hrun3)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
    (by dsimp only [clearUpkSpec]; simp only [wp_norm, hsp3]; rfl)
    (by simp only [wp_norm])
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [clearUpkSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ hm_pan => by dsimp only [clearUpkSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl4
  intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
  simp only [wp_norm, hsp3] at hsp4
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _hx29_4, hvregs_4⟩
  simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx24_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx24_4 hvregs_4
  dsimp only [clearUpkSpec]
  simp only [wp_norm, hsp3, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr4
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  refine SepWPp.elim_exists_focus
    (Φ := fun evs2 : List AllocEvent =>
      ⌜FreeOnlyEvs evs2⌝ ∗ A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st_cur)) s4)
    (by sep_focus) fun evs2 => ?_
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hevs2
  obtain ⟨evs_total, hst_tot, htd_tot⟩ := hs2.finish hevs2
  rw [hst_tot]
  refine SepWPp.mono_focus (clearUpkStack_to_subStack s0.sp) (by sep_focus) ?_
  refine SepWPp.mono_focus
    (applyRatchet_local_frame_entails_memRegion s0.sp newPqrCap newPqrPtr ptCap ptPtr
      (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      ptCap ptPtr (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      bs hbs_len) (by sep_focus) ?_
  refine SepWPp.mono_focus (Entails.refl (tryDecryptSavedRegs s0.sp s0)) (by sep_focus) ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret) (by sep_focus) fun wret => ?_
  unfold tryDecryptSavedRegs
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  wp_sync_433 (s0.readReg64 .lr)
  apply SepWP.done (by rfl) (by exact hrun4)
  refine ⟨fun hmf => ?_, by simp only [wp_norm], ?_⟩
  · dsimp only [tryDecryptSpecPlaced, withLsCodeRoLoaded, tryDecryptRawSpecPlaced]
    refine Satisfies.mono
      (sepConj_mono_left
        (Entails.trans
          (Entails.pure_right htd_tot (Entails.refl _))
          (Entails.sepExists_intro
            (P := fun evs : List AllocEvent =>
              ⌜tdEnv (tryDecryptEnvArgs x) evs⌝ ∗
              (CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptRawSpecPlaced
                C (A.atState lim (M.stepEvents evs st_init) _) ctl uuidTryParse S).post x s0 _)
            evs_total))) ?_
    dsimp only [CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptRawSpecPlaced,
      tryDecryptSpec, Spec.inImage]
    rw [hok]
    rw [← hst] at hmf
    have hdec := decRel_of_trApplyRel hG1
    have hsaved := tryDecryptSavedRegs_entails_memRegion s0.sp s0
    unfold tryDecryptSavedRegs at hsaved
    have hmf1 := Satisfies.mono_focus hsaved (by sep_focus) hmf
    have hmf3 := Satisfies.mono_focus (stackAt_rootStack_of_parts s0.sp) (by sep_focus) hmf1
    rw [show (bv% (2 ^ 64 - 2) : BitVec 64) = okTagVec from rfl] at hmf3
    have hmf4 := Satisfies.mono_focus
      (decResultAt_ok_of_parts A.repAlloc x.ret pt ptCap ptPtr hpt_le hpt_lt hpt_nz) (by sep_focus) hmf3
    have hss : sessionStateAt A.repAlloc x.ss { G1 with pending := none, kyber := none } (x.model C S uuidTryParse).2 ⊢
        ∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
          sessionStateAt A.repAlloc x.ss G' (x.model C S uuidTryParse).2 := by
      refine Entails.trans ?_
        (Entails.sepExists_intro
          (P := fun G' : SessionGhost =>
            ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
            sessionStateAt A.repAlloc x.ss G' (x.model C S uuidTryParse).2)
          { G1 with pending := none, kyber := none })
      exact Entails.pure_right hdec (Entails.refl _)
    have hmf5 := Satisfies.mono_focus hss (by sep_focus) hmf4
    clear hmf hmf1 hmf3 hmf4
    simp only [sessionStateAt_atState, vecResultAt_atState, protocolAddressAt_atState,
      signalMessageAt_atState, A.atState_pool]
    have hno_pan : (Except.ok pt : Except SignalProtocolError (List (BitVec 8))) ≠ .error .panic := nofun
    simp only [wp_norm, sepConj_assoc, satisfies_pure_sepConj] at hmf5 ⊢
    refine ⟨⟨hno_pan, htr40⟩, ?_⟩
    generalize (∃∗ G', ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
      sessionStateAt A.repAlloc x.ss G' (x.model C S uuidTryParse).2) = SS at hmf5 ⊢
    sep_close
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, hvregs_4]

theorem applyRatchet_549_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 58)
      (withLsCodeRoLoaded lsmpl (trApplySpec M A lim)))
    (hClearUpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 35)
      (withLsCodeRoLoaded lsmpl (clearUpkSpec M A lim)))
    (hmemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsMemcpySym)
      sessionMemcpyRegionBudgetSpec)
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim)) :
    S9SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A lim ctl
      uuidTryParse S tdEnv s9Env := by
  intro x st_init st trG tr st1 newPqrState pt R s0 s hok hst hs h9
  rcases h9 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx23, hx24, newPqrCap, newPqrPtr, hnew_le, hnew_lt, hnew_nz, hmem⟩
  have h6d0 := @applyRatchet_from_6d0_549_placed _ M C A lim ctl S tdEnv H
    hTrApply hClearUpk hmemcpy x st_init
  clear hTrApply hClearUpk
  rw [sessionStateAt_atState, trAt_atState, A.atState_live_eq_repAlloc, vecU8_atState] at hmem
  have hpad : trG.ratchet.senderPad.length = 100 := by
    have htr_front := hmem
    rw [← sepConj_assoc, sepConj_comm (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1), sepConj_assoc] at htr_front
    exact trAt_senderPad_len htr_front
  unfold tryDecryptCommonHeap at hmem
  rw [protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState, A.atState_pool,
      trAt_eq_withoutPq A.repAlloc s0.sp trG tr,
      applyRatchet_scr_split s0.sp,
      applyRatchet_ret_split x.ret,
      show s0.sp - 1504#64 + 0x3d0#64 = s0.sp - 528#64 by bv_omega,
      show s0.sp - 1504#64 + 0x8#64 = s0.sp - 1496#64 by bv_omega,
      show s0.sp - 1504#64 + 0x10#64 = s0.sp - 1488#64 by bv_omega,
      show s0.sp - 1504#64 + 0x28#64 = s0.sp - 1464#64 by bv_omega,
      show s0.sp - 1504#64 + 0x30#64 = s0.sp - 1456#64 by bv_omega,
      show s0.sp - 1504#64 + 0x3e8#64 = s0.sp - 504#64 by bv_omega] at hmem
  change s.pc = (blkPl_434).base + 1700#64 at hpc
  simp only [wp_norm] at hx20 hx23 hx29
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_reaches_outcome hmem ?_
  refine SepWPp.elim_pure_focus
    (φ := tr.pqrState.length ≤ trG.pq.cap.toNat ∧ trG.pq.cap.toNat < 2 ^ 63 ∧ trG.pq.ptr ≠ 0)
    (by sep_focus) fun ⟨hpq_le, hpq_lt, _hpq_nz⟩ => ?_
  refine SepWPp.elim_vecU8_focus (A := A.repAlloc) (a := s0.sp - 528#64) (bs := pt)
    (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
  rw [show s0.sp - 528#64 + 8#64 = s0.sp - 520#64 by bv_omega,
      show s0.sp - 528#64 + 16#64 = s0.sp - 512#64 by bv_omega]
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 720#64) (by sep_focus) fun w720 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 712#64) (by sep_focus) fun w712 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 704#64) (by sep_focus) fun w704 => ?_
  by_cases hpq_cap : trG.pq.cap = 0#64
  · have hs1 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s9From6d0Env :=
      hs.weaken (fun _ h2 => SeqEnv.append FreeOnlyEvs.nil h2)
    refine SepWPp.mono_focus (newPqr_zero_prep A.repAlloc trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap) (by sep_focus) ?_
    rw [emp_sepConj]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_434).base + bv% (1744))
    wp_sync_433 ((blkPl_434).base + bv% (1744))
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 st trG tr st1 newPqrState pt newPqrCap newPqrPtr ptCap ptPtr R s0 _
        hok hst hs1 hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun) (by simp only [wp_norm, hsp])
        (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al)
        (by simp only [wp_norm, htr]) hcl1
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19])
        (by simp only [wp_norm, hx20])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx24])
        (by simp only [wp_norm, hx29])
        (by simp only [wp_norm, hvregs]))
  · refine SepWPp.mono_focus (newPqr_dealloc_prep' A.repAlloc trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap hpq_le hpq_lt) (by sep_focus) ?_
    rw [stackAt_sub_split (s0.sp - 1504#64) allocHookStack (by decide)]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_434).base + bv% (1728))
    apply sepWP_seg_433 (mid := (blkPl_434).base + bv% (1728))
    intro _m_strip
    wp_steps
    apply SepWP.setPC_setMem_ite_false (by simp only [beq_iff_eq, hpq_cap, not_false_eq_true])
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by wp_norm_lhs)) (hnext := ?_)
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl0
    apply SepWPp.of_sepWP_placed hcl0 (mid := lsρ lsRustDeallocSym)
    wp_sync_433 (lsρ lsRustDeallocSym)
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    rw [A.repAlloc_live_norm]
    refine SepWPp.call_frame_placed (spec := rustCliDeallocBudgetSpec M A lim)
      (x := (trG.pq.ptr, trG.pq.cap.toNat, 1, st))
      (T := A.pool lim st _ ∗ A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat ∗
            stackAt (s0.sp - 1504#64) allocHookStack)
      (ret_pc := (blkPl_434).base + bv% (1740))
      hcl1 hdealloc (by rfl) (by exact hrun)
      (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
      (by dsimp only [rustCliDeallocBudgetSpec]; simp only [wp_norm, hsp]; rfl)
      (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
        by simpa only [wp_norm] using lsRetAddr624_blockPlacement_base_add 434 (bv% (1740)) (by decide) (by decide)⟩)
      (by sep_focus)
      (fun _ _ _ _ h => by dsimp only [rustCliDeallocBudgetSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
      (fun _ _ hm_pan => by dsimp only [rustCliDeallocBudgetSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
    clear hcl0 hcl1
    intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
    simp only [wp_norm, hsp] at hsp1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, hx19, hx20, hx21, hx24, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx24_1 hx29_1 hvregs_1
    dsimp only [rustCliDeallocBudgetSpec]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; rintro ⟨hacp1, _⟩
    have htr10 : s1.trace = s0.trace := hacp1.2.1.trans (by simp only [wp_norm, htr])
    have hs1 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init
        (M.stepEvents (rustDeallocEvents trG.pq.cap.toNat 1) st) s9From6d0Env :=
      hs.step (fun _ _ h1 h2 => SeqEnv.append h1 h2) (freeOnlyEvs_rustDeallocEvents trG.pq.cap.toNat 1)
    refine SepWPp.mono_focus (allocHookStack_to_subStack s0.sp) (by sep_focus) ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_434).base + bv% (1744))
    wp_sync_433 ((blkPl_434).base + bv% (1744))
    apply SepWP.done (by rfl) (by exact hrun1)
    intro hcl2
    rw [← logOff_tryDecryptPlacedImg]
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 (M.stepEvents (rustDeallocEvents trG.pq.cap.toNat 1) st)
        trG tr st1 newPqrState pt newPqrCap newPqrPtr ptCap ptPtr R s0 _
        hok hst hs1 hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun1) (by simp only [wp_norm, hsp1])
        (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1)
        (by simp only [wp_norm, htr10]) hcl2
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19_1])
        (by simp only [wp_norm, hx20_1])
        (by simp only [wp_norm, hx21_1])
        (by simp only [wp_norm, hx24_1])
        (by simp only [wp_norm, hx29_1])
        (by simp only [wp_norm, hvregs_1]))

set_option maxHeartbeats 800000 in
theorem applyRatchet_from_6d0_549_placed_x [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 58)
      (withLsCodeRoLoaded lsmpl (trApplySpecX M A lim)))
    (hClearUpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 35)
      (withLsCodeRoLoaded lsmpl (clearUpkSpecX M A lim)))
    (hmemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsMemcpySym)
      (withStack sessionMemcpyRegionBudgetSpec extHookStack))
    (x : TryDecryptGhost) (st_init st_cur : M.σ)
    (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (newPqrCap newPqrPtr ptCap ptPtr : BitVec 64)
    (R : SepProp) (s0 s1 : State)
    (hok : (x.modelFn C decFn S uuidTryParse).1 = .ok pt)
    (hst : (x.modelFn C decFn S uuidTryParse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage)
    (hs1 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st_cur s9From6d0Env)
    (hpad : trG.ratchet.senderPad.length = 100)
    (hnew_le : newPqrState.length ≤ newPqrCap.toNat)
    (hnew_lt : newPqrCap.toNat < 2 ^ 63)
    (hnew_nz : newPqrPtr ≠ 0)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_nz : ptPtr ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hpc1 : s1.pc = (blkPl_434).base + 1744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1504#64)
    (hsp_al1 : s1.spAligned = true)
    (htr1 : s1.trace = s0.trace)
    (hcl1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hx9_1 : s1.readReg64 .x9 = s0.sp - 800#64)
    (hx19_1 : s1.readReg64 .x19 = x.ret)
    (hx20_1 : s1.readReg64 .x20 = s0.sp - 1184#64)
    (hx21_1 : s1.readReg64 .x21 = x.ss)
    (hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length)
    (_hx29_1 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0) :
    SepWPp ((blkPC_434).rebase (blkPl_434).base H) (s0.readReg64 .lr) s1
      (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
       trWithoutPqAt A.repAlloc (s0.sp - 1448#64) trG.ratchet tr ∗
       ((s0.sp - 1272#64) ↦₆₄ trG.pq.cap) ∗
       ((s0.sp - 1264#64) ↦₆₄ trG.pq.ptr) ∗
       ((s0.sp - 1256#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       (if newPqrCap = 0 then emp else (A.repAlloc.live newPqrPtr newPqrCap.toNat 1 ∗ (newPqrPtr ↦ₛ newPqrState)) ∗
         memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
       ((s0.sp - 528#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 520#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 512#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (if ptCap = 0 then emp else (A.repAlloc.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt)) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       memRegion x.ret 8 ∗
       memRegion (x.ret + 8#64) 8 ∗
       memRegion (x.ret + 16#64) 8 ∗
       memRegion (x.ret + 24#64) 8 ∗
       memRegion (x.ret + 32#64) 16 ∗
       memRegion (s0.sp - 1504#64) 8 ∗
       ((s0.sp - 1496#64) ↦₆₄ newPqrCap) ∗
       memRegion (s0.sp - 1488#64) 24 ∗
       ((s0.sp - 1464#64) ↦₆₄ newPqrPtr) ∗
       memRegion (s0.sp - 1456#64) 8 ∗
       memRegion (s0.sp - 1184#64) 8 ∗
       memRegion (s0.sp - 1176#64) 8 ∗
       memRegion (s0.sp - 1168#64) 8 ∗
       memRegion (s0.sp - 1160#64) 16 ∗
       memRegion (s0.sp - 1144#64) 8 ∗
       memRegion (s0.sp - 1136#64) 8 ∗
       memRegion (s0.sp - 1128#64) 8 ∗
       memRegion (s0.sp - 1120#64) 16 ∗
       memRegion (s0.sp - 1104#64) 264 ∗
       memRegion (s0.sp - 840#64) 120 ∗
       ((s0.sp - 720#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 712#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 704#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       memRegion (s0.sp - 696#64) 168 ∗
       memRegion (s0.sp - 504#64) 0x198 ∗
       protocolAddressAt A.repAlloc x.rem x.remA ∗
       protocolAddressAt A.repAlloc x.loc x.locA ∗
       signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
       logOff tryDecryptPlacedImg ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool lim st_cur s1)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A lim ctl uuidTryParse S tdEnv).post (x, st_init) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A lim ctl uuidTryParse S tdEnv).onPanic (x, st_init) s0 sf ∗ R)) := by
  simp only [wp_norm] at hpc1 hsp1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1184#64) (by sep_focus) fun w1184 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1176#64) (by sep_focus) fun w1176 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1168#64) (by sep_focus) fun w1168 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun w1128 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 8#64) (by sep_focus) fun wret8 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 16#64) (by sep_focus) fun wret16 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 24#64) (by sep_focus) fun wret24 => ?_
  rw [stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsMemcpySym)
  wp_sync_433 (lsρ lsMemcpySym)
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  refine SepWPp.mono_focus
    (trAt_of_withoutPq A.repAlloc s0.sp trG tr newPqrCap newPqrPtr newPqrState hnew_le hnew_lt hnew_nz)
    (by sep_focus) ?_
  rw [trAt_eq_stack_heap A.repAlloc (s0.sp - 1448#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } hpad]
  refine SepWPp.elim_exists_focus
    (Φ := fun pad : BitVec 32 =>
      ((s0.sp - 1448#64) ↦ₛ trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
        { tr with pqrState := newPqrState } pad) ∗
      trHeapPart A.repAlloc { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState })
    (by sep_focus) fun pad => ?_
  have hbs_len : (trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad).length = 264 :=
    length_trStackBytes _ _ pad hpad
  generalize hbs_def : trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad = bs at hbs_len ⊢
  rw [show memRegion (s0.sp - 1104#64) 264 = memRegion (s0.sp - 1104#64) bs.length by rw [hbs_len]]
  simp only [← sepConj_assoc]
  refine SepWPp.call_frame_placed (spec := withStack sessionMemcpyRegionBudgetSpec extHookStack)
    (x := (s0.sp - 1104#64, s0.sp - 1448#64, bs))
    (T := memRegion (s0.sp - 1104#64) bs.length ∗ ((s0.sp - 1448#64) ↦ₛ bs) ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_434).base + bv% (1248))
    hcl2 hmemcpy (by rfl) (by exact hrun1)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
          sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
        rw [sepConj_assoc, sepConj_assoc]; congr 3; simp only [wp_norm, hsp1])
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm, hbs_len]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ hm_pan => by dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx24_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx24_2 hvregs_2
  dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
    sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hvm2
  refine SepWPp.transport_budgetPool hvm2 (hnext := ?_)
  simp only [wp_norm, hsp1]
  refine SepWPp.elim_pure_focus
    (φ := s2.readReg64 .x0 = s0.sp - 1104#64 ∧ s2.trace = s1.trace)
    (by sep_focus) fun ⟨_, htr2⟩ => ?_
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  rw [← hbs_def]
  refine SepWPp.mono_focus
    (trAt_of_stack_heap A.repAlloc (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } pad hpad)
    (by sep_focus) ?_
  rw [hbs_def]
  refine SepWPp.mono_focus (extHookStack_to_trApplyStackX s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsmpl.base 58)
  wp_sync_433 (lsmpl.base 58)
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  have hfit_tr : FitsEnv M lim st_cur TrApplyEnv := hs1.1.seq_left
  refine SepWPp.call_cro_frame_placed (spec := trApplySpecX M A lim)
    (x := (⟨s0.sp - 1104#64, { trG with pq := ⟨newPqrCap, newPqrPtr⟩ },
            { tr with pqrState := newPqrState }, x.ss, x.G.afterTrFrom, st1⟩, st_cur))
    (T := trAt A.repAlloc (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
            { tr with pqrState := newPqrState } ∗
          sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
          stackAt (s0.sp - 1504#64) trApplyStackX ∗ A.pool lim st_cur _)
    (ret_pc := (blkPl_434).base + bv% (1260))
    hcl3 hTrApply (by rfl) (by exact hrun2)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [trApplySpecX, CryptoVerification.LibsignalTripleRatchet.trApplySpecX]
        conv => lhs; rw [eq_true hfit_tr, pure_true, emp_sepConj, trAt_atState, sessionStateAt_atState, A.atState_pool]
        simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [trApplySpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ hm_pan => by dsimp only [trApplySpecX] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx24_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx24_3 hvregs_3
  dsimp only [trApplySpecX, CryptoVerification.LibsignalTripleRatchet.trApplySpecX]
  simp only [wp_norm, hsp2]
  apply SepWPp.elim_exists; intro evs1
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hevs1
  apply SepWPp.elim_pure; intro htr3
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  apply SepWPp.elim_exists; intro G1
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hG1
  rw [sessionStateAt_atState]
  have hs2 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init (M.stepEvents evs1 st_cur) FreeOnlyEvs :=
    hs1.step (fun _ _ h1 h2 => SeqEnv.append h1 h2) hevs1
  refine SepWPp.mono_focus (trApplyStackX_to_clearUpkStackX s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl3 (mid := lsmpl.base 35)
  wp_sync_433 (lsmpl.base 35)
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hcl4
  refine SepWPp.call_cro_frame_placed (spec := clearUpkSpecX M A lim)
    (x := (⟨x.ss, G1, ({ tr with pqrState := newPqrState }).applyToSessionState st1⟩,
           M.stepEvents evs1 st_cur))
    (T := sessionStateAt A.repAlloc x.ss G1 (({ tr with pqrState := newPqrState }).applyToSessionState st1) ∗
          A.pool lim (M.stepEvents evs1 st_cur) _ ∗ stackAt (s0.sp - 1504#64) clearUpkStackX)
    (ret_pc := (blkPl_434).base + bv% (1268))
    hcl4 hClearUpk (by rfl) (by exact hrun3)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
    (by dsimp only [clearUpkSpecX]; simp only [wp_norm, hsp3]; rfl)
    (by simp only [wp_norm])
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [clearUpkSpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ hm_pan => by dsimp only [clearUpkSpecX] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl4
  intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
  simp only [wp_norm, hsp3] at hsp4
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _hx29_4, hvregs_4⟩
  simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx24_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx24_4 hvregs_4
  dsimp only [clearUpkSpecX]
  simp only [wp_norm, hsp3, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr4
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  refine SepWPp.elim_exists_focus
    (Φ := fun evs2 : List AllocEvent =>
      ⌜FreeOnlyEvs evs2⌝ ∗ A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st_cur)) s4)
    (by sep_focus) fun evs2 => ?_
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hevs2
  obtain ⟨evs_total, hst_tot, htd_tot⟩ := hs2.finish hevs2
  rw [hst_tot]
  refine SepWPp.mono_focus (clearUpkStackX_to_subStack s0.sp) (by sep_focus) ?_
  refine SepWPp.mono_focus
    (applyRatchet_local_frame_entails_memRegion s0.sp newPqrCap newPqrPtr ptCap ptPtr
      (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      ptCap ptPtr (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      bs hbs_len) (by sep_focus) ?_
  refine SepWPp.mono_focus (Entails.refl (tryDecryptSavedRegs s0.sp s0)) (by sep_focus) ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret) (by sep_focus) fun wret => ?_
  unfold tryDecryptSavedRegs
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  wp_sync_433 (s0.readReg64 .lr)
  apply SepWP.done (by rfl) (by exact hrun4)
  refine ⟨fun hmf => ?_, by simp only [wp_norm], ?_⟩
  · dsimp only [tryDecryptFnSpecPlaced, withLsCodeRoLoaded, tryDecryptFnRawSpecPlaced]
    refine Satisfies.mono
      (sepConj_mono_left
        (Entails.trans
          (Entails.pure_right htd_tot (Entails.refl _))
          (Entails.sepExists_intro
            (P := fun evs : List AllocEvent =>
              ⌜tdEnv (tryDecryptEnvArgs x) evs⌝ ∗
              (CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptFnRawSpecPlaced
                C decFn (A.atState lim (M.stepEvents evs st_init) _) ctl uuidTryParse S).post x s0 _)
            evs_total))) ?_
    dsimp only [CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptFnRawSpecPlaced,
      tryDecryptFnSpec, Spec.inImage]
    rw [hok]
    rw [← hst] at hmf
    have hdec := decRel_of_trApplyRel hG1
    have hsaved := tryDecryptSavedRegs_entails_memRegion s0.sp s0
    unfold tryDecryptSavedRegs at hsaved
    have hmf1 := Satisfies.mono_focus hsaved (by sep_focus) hmf
    have hmf3 := Satisfies.mono_focus (stackAt_rootStack_of_parts s0.sp) (by sep_focus) hmf1
    rw [show (bv% (2 ^ 64 - 2) : BitVec 64) = okTagVec from rfl] at hmf3
    have hmf4 := Satisfies.mono_focus
      (decResultAt_ok_of_parts A.repAlloc x.ret pt ptCap ptPtr hpt_le hpt_lt hpt_nz) (by sep_focus) hmf3
    have hss : sessionStateAt A.repAlloc x.ss { G1 with pending := none, kyber := none } (x.modelFn C decFn S uuidTryParse).2 ⊢
        ∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
          sessionStateAt A.repAlloc x.ss G' (x.modelFn C decFn S uuidTryParse).2 := by
      refine Entails.trans ?_
        (Entails.sepExists_intro
          (P := fun G' : SessionGhost =>
            ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
            sessionStateAt A.repAlloc x.ss G' (x.modelFn C decFn S uuidTryParse).2)
          { G1 with pending := none, kyber := none })
      exact Entails.pure_right hdec (Entails.refl _)
    have hmf5 := Satisfies.mono_focus hss (by sep_focus) hmf4
    clear hmf hmf1 hmf3 hmf4
    simp only [sessionStateAt_atState, protocolAddressAt_atState,
      signalMessageAt_atState, A.atState_pool]
    have hno_pan : (Except.ok pt : Except SignalProtocolError (List (BitVec 8))) ≠ .error .panic := nofun
    simp only [wp_norm, sepConj_assoc, satisfies_pure_sepConj] at hmf5 ⊢
    refine ⟨⟨hno_pan, htr40⟩, ?_⟩
    generalize (∃∗ G', ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
      sessionStateAt A.repAlloc x.ss G' (x.modelFn C decFn S uuidTryParse).2) = SS at hmf5 ⊢
    change _ ⊨ SS ∗ vecResultAt A.repAlloc x.ret (.ok pt) ∗ _
    sep_close
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, hvregs_4]

theorem applyRatchet_549_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 58)
      (withLsCodeRoLoaded lsmpl (trApplySpecX M A lim)))
    (hClearUpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 35)
      (withLsCodeRoLoaded lsmpl (clearUpkSpecX M A lim)))
    (hmemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsMemcpySym)
      (withStack sessionMemcpyRegionBudgetSpec extHookStack))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustDeallocSym)
      (rustDeallocExternSpecWithStack M A lim extHookStack)) :
    S9SeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C decFn A lim ctl
      uuidTryParse S tdEnv s9Env := by
  intro x st_init st trG tr st1 newPqrState pt R s0 s hok hst hs h9
  rcases h9 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx23, hx24, newPqrCap, newPqrPtr, hnew_le, hnew_lt, hnew_nz, hmem⟩
  have h6d0 := @applyRatchet_from_6d0_549_placed_x _ M C decFn A lim ctl S tdEnv H
    hTrApply hClearUpk hmemcpy x st_init
  clear hTrApply hClearUpk
  rw [sessionStateAt_atState, trAt_atState, A.atState_live_eq_repAlloc, vecU8_atState] at hmem
  have hpad : trG.ratchet.senderPad.length = 100 := by
    have htr_front := hmem
    rw [← sepConj_assoc, sepConj_comm (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1), sepConj_assoc] at htr_front
    exact trAt_senderPad_len htr_front
  unfold tryDecryptCommonHeap at hmem
  rw [protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState, A.atState_pool,
      trAt_eq_withoutPq A.repAlloc s0.sp trG tr,
      applyRatchet_scr_split s0.sp,
      applyRatchet_ret_split x.ret,
      show s0.sp - 1504#64 + 0x3d0#64 = s0.sp - 528#64 by bv_omega,
      show s0.sp - 1504#64 + 0x8#64 = s0.sp - 1496#64 by bv_omega,
      show s0.sp - 1504#64 + 0x10#64 = s0.sp - 1488#64 by bv_omega,
      show s0.sp - 1504#64 + 0x28#64 = s0.sp - 1464#64 by bv_omega,
      show s0.sp - 1504#64 + 0x30#64 = s0.sp - 1456#64 by bv_omega,
      show s0.sp - 1504#64 + 0x3e8#64 = s0.sp - 504#64 by bv_omega] at hmem
  change s.pc = (blkPl_434).base + 1700#64 at hpc
  simp only [wp_norm] at hx20 hx23 hx29
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_reaches_outcome hmem ?_
  refine SepWPp.elim_pure_focus
    (φ := tr.pqrState.length ≤ trG.pq.cap.toNat ∧ trG.pq.cap.toNat < 2 ^ 63 ∧ trG.pq.ptr ≠ 0)
    (by sep_focus) fun ⟨hpq_le, hpq_lt, _hpq_nz⟩ => ?_
  refine SepWPp.elim_vecU8_focus (A := A.repAlloc) (a := s0.sp - 528#64) (bs := pt)
    (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
  rw [show s0.sp - 528#64 + 8#64 = s0.sp - 520#64 by bv_omega,
      show s0.sp - 528#64 + 16#64 = s0.sp - 512#64 by bv_omega]
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 720#64) (by sep_focus) fun w720 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 712#64) (by sep_focus) fun w712 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 704#64) (by sep_focus) fun w704 => ?_
  by_cases hpq_cap : trG.pq.cap = 0#64
  · have hs1 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s9From6d0Env :=
      hs.weaken (fun _ h2 => SeqEnv.append FreeOnlyEvs.nil h2)
    refine SepWPp.mono_focus (newPqr_zero_prep A.repAlloc trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap) (by sep_focus) ?_
    rw [emp_sepConj]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_434).base + bv% (1744))
    wp_sync_433 ((blkPl_434).base + bv% (1744))
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 st trG tr st1 newPqrState pt newPqrCap newPqrPtr ptCap ptPtr R s0 _
        hok hst hs1 hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun) (by simp only [wp_norm, hsp])
        (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al)
        (by simp only [wp_norm, htr]) hcl1
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19])
        (by simp only [wp_norm, hx20])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx24])
        (by simp only [wp_norm, hx29])
        (by simp only [wp_norm, hvregs]))
  · refine SepWPp.mono_focus (newPqr_dealloc_prep' A.repAlloc trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap hpq_le hpq_lt) (by sep_focus) ?_
    rw [stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide)]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_434).base + bv% (1728))
    apply sepWP_seg_433 (mid := (blkPl_434).base + bv% (1728))
    intro _m_strip
    wp_steps
    apply SepWP.setPC_setMem_ite_false (by simp only [beq_iff_eq, hpq_cap, not_false_eq_true])
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by wp_norm_lhs)) (hnext := ?_)
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl0
    apply SepWPp.of_sepWP_placed hcl0 (mid := lsρ lsRustDeallocSym)
    wp_sync_433 (lsρ lsRustDeallocSym)
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    rw [A.repAlloc_live_norm]
    refine SepWPp.call_frame_placed (spec := rustDeallocExternSpecWithStack M A lim extHookStack)
      (x := (trG.pq.ptr, trG.pq.cap.toNat, 1, st))
      (T := A.pool lim st _ ∗ A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat ∗
            stackAt (s0.sp - 1504#64) extHookStack)
      (ret_pc := (blkPl_434).base + bv% (1740))
      hcl1 hdealloc (by rfl) (by exact hrun)
      (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
      (by dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]; simp only [wp_norm, hsp]; rfl)
      (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                  ⟨layoutOk_of_cap_ne_zero hpq_cap hpq_lt, by decide⟩,
                  by simpa only [wp_norm] using lsRetAddr624_blockPlacement_base_add 434 (bv% (1740)) (by decide) (by decide)⟩)
      (by sep_focus)
      (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
      (fun _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
    clear hcl0 hcl1
    intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
    simp only [wp_norm, hsp] at hsp1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, hx19, hx20, hx21, hx24, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx24_1 hx29_1 hvregs_1
    dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr1
    have htr10 : s1.trace = s0.trace := htr1.trans (by simp only [wp_norm, htr])
    have hs1 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init
        (M.stepEvents (rustDeallocEvents trG.pq.cap.toNat 1) st) s9From6d0Env :=
      hs.step (fun _ _ h1 h2 => SeqEnv.append h1 h2) (freeOnlyEvs_rustDeallocEvents trG.pq.cap.toNat 1)
    refine SepWPp.mono_focus (extHookStack_to_subStack s0.sp) (by sep_focus) ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_434).base + bv% (1744))
    wp_sync_433 ((blkPl_434).base + bv% (1744))
    apply SepWP.done (by rfl) (by exact hrun1)
    intro hcl2
    rw [← logOff_tryDecryptPlacedImg]
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 (M.stepEvents (rustDeallocEvents trG.pq.cap.toNat 1) st)
        trG tr st1 newPqrState pt newPqrCap newPqrPtr ptCap ptPtr R s0 _
        hok hst hs1 hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun1) (by simp only [wp_norm, hsp1])
        (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1)
        (by simp only [wp_norm, htr10]) hcl2
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19_1])
        (by simp only [wp_norm, hx20_1])
        (by simp only [wp_norm, hx21_1])
        (by simp only [wp_norm, hx24_1])
        (by simp only [wp_norm, hx29_1])
        (by simp only [wp_norm, hvregs_1]))

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget
