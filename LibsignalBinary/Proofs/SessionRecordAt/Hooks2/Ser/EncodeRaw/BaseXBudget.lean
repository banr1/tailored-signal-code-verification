/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Callee Step Lemmas for `SessionStructure::encode_raw` (Block `14`)

Proves total-correctness `SepWPpLsCl` sequencing combinators, envelope-parameterized
`encodeChainSpecWithEnvX`, and budget-threaded Block `14` callee step lemmas
(`do_reserve_and_handle`, `encode_varint`, `encode::<Chain>`, and `memcpy`) at `encodeRawSubStackX`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement)
open CryptoGames.LibsignalSession (ReceiverChain)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded withLsCl
  ls_subroutine_ok_of_block
  lsMemcpySym lsρ blkPl_10 blkPl_13
)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack reserveCap DoReserveCall sessionMemcpySpec ls_subroutine_ok_of_callee
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  encodeVarintStackX EncodeVarintGhost
)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  EncodeChainGhost encChainMem protoChainAt
  encodeRawSubStackX encRawSubRestX
  stackAt_sub_to_encodeVarint_erX stackAt_sub_to_doReserve_erX
  stackAt_sub_to_encodeChainX stackAt_sub_to_memcpy_erX
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  satisfies_of_sep_focus entails_of_sep_focus
  vecU8At_expose_slice chainAt_eq_protoChainAt_er reserveCap_bounds_add
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  EncodeChainEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv encodeVarintSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents doReserveSpecX doReserveSpecWithStack finishGrowStackX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget (
  doReserveStackX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  encodeChainStackX SerContractsXPlaced encodeChainSpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  EncodeVarintPlacedOkX DoReservePlacedOkX EncodeChainPlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget (
  sepWPpLsCl_call_lscl_noPanic sepWPpLsCl_call_withLsCl_noPanic
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem encraw_encodeVarint_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX M A lim H) :
    subroutine_ok (lsProg_14 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_14 H) hEV

theorem encraw_doReserve_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX M A lim H) :
    subroutine_ok (lsProg_14 H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_14 H) hDR

theorem encraw_encodeChain_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hEC : EncodeChainPlacedOkX M A lim H) :
    subroutine_ok (lsProg_14 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpecX M A lim)) :=
  ls_subroutine_ok_of_callee (callerProg := lsProg_14 H) hEC

theorem encraw_memcpy_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_14 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)) :=
  hC.memcpy (callerProg := lsProg_14 H)

/-- Total-correctness segment sequencing on `SepWPpLsCl` (`P2 : SepProp`). -/
theorem encraw_seq_wppLsCl {pl : MultiPlacement} {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWPpLsCl pl prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)) (fun _ _ => False))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPpLsCl pl prog ret sm (P2 ∗ F) Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  intro hcl
  have h1' := h1 hcl
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, _, _, hp⟩ | hoom⟩ :=
    h1' (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    have hclm := hcl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ hclm R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact hp.elim
  · exact (not_satisfies_false_sepConj hoom.2).elim

/-- Total-correctness segment sequencing on `SepWPpLsCl` (`P2 : State → SepProp`). -/
theorem encraw_seq_wppLsCl' {pl : MultiPlacement} {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (h1 : SepWPpLsCl pl prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (fun _ _ => False))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPpLsCl pl prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  intro hcl
  have h1' := h1 hcl
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, _, _, hp⟩ | hoom⟩ :=
    h1' (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    have hclm := hcl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ hclm R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact hp.elim
  · exact (not_satisfies_false_sepConj hoom.2).elim

/-- Execute a `bl do_reserve_and_handle` (`lsmpl.base 13`) call inside `encode_raw` (Block `14`),
    threading `A.pool lim st` under `FitsEnv M lim st (DoReserveEnv ...)`. -/
theorem encraw_call_doReserve_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX M A lim H)
    (sp0 v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8)) (add : Nat)
    (st : M.σ)
    (hcap_le : cap.toNat ≤ bs.length + add)
    (hlen_lt : bs.length + add < 2 ^ 62)
    (hfit : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v cap ptr bs add)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = bs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64) (evs : List AllocEvent),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      DoReserveEnv (DoReserveCall.mk v cap ptr bs add) evs →
      bs.length + add ≤ newCap.toNat →
      newCap.toNat < 2 ^ 63 →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc v newCap p' bs ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hcall := encraw_doReserve_placed_ok_x hDR
  obtain ⟨hres_bound, hnew_ge, hnew_lt⟩ := reserveCap_bounds_add hcap_le hlen_lt
  refine sepWPpLsCl_call_lscl_noPanic (x := (DoReserveCall.mk v cap ptr bs add, st))
    (F := encRawSubRestX (sp0 - 80#64) doReserveStackX ∗ F)
    hcall hpc hrun halign hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve_erX (sp0 - 80#64)] at hm
    simp only [doReserveSpecX, doReserveSpecWithStack, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hres_bound, hfit⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    dsimp only [doReserveSpecX, doReserveSpecWithStack]
    rw [hsp, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun p' => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hStackEq : stackAt (sp0 - 80#64) (finishGrowStackX + 64) =
        stackAt (sp0 - 80#64) doReserveStackX := rfl
    refine SepWPpLsCl.weaken_pre ?_
      (hnext sm (BitVec.ofNat 64 (reserveCap cap.toNat bs.length add)) p'
        (doReserveEvents (DoReserveCall.mk v cap ptr bs add))
        hpcm hrunm hspm htrm' hcsm rfl hnew_ge hnew_lt)
    rw [hStackEq, stackAt_sub_to_doReserve_erX (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

/-- Execute a `bl encode_varint` (`lsmpl.base 10`) call inside `encode_raw` (Block `14`),
    threading `A.pool lim st` under `FitsEnv M lim st (EncodeVarintEnv ...)`. -/
theorem encraw_call_encodeVarint_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (sp0 val v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8))
    (st : M.σ)
    (hlen_lt : bs.length + 10 < 2 ^ 62)
    (hfit : FitsEnv M lim st (EncodeVarintEnv ⟨val, v, cap, ptr, bs⟩))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 10)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      EncodeVarintEnv ⟨val, v, cap, ptr, bs⟩ evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc v cap' ptr' (bs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hcall := encraw_encodeVarint_placed_ok_x hEV
  refine sepWPpLsCl_call_lscl_noPanic (x := (⟨val, v, cap, ptr, bs⟩, st))
    (F := encRawSubRestX (sp0 - 80#64) encodeVarintStackX ∗ F)
    hcall hpc hrun halign hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarint_erX (sp0 - 80#64)] at hm
    simp only [encodeVarintSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, Or.inr hlen_lt, hfit⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeVarintSpecX, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun evs => SepWPpLsCl.exists_elim fun cap' =>
      SepWPpLsCl.exists_elim fun ptr' => ?_
    refine SepWPpLsCl.pure_elim fun htrm => ?_
    refine SepWPpLsCl.pure_elim fun _ => ?_
    have hPullEvs :
        (vecU8At A.repAlloc v cap' ptr' (bs ++ encodeVarint val) ∗
          ⌜EncodeVarintEnv ⟨val, v, cap, ptr, bs⟩ evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 80#64) encodeVarintStackX ∗
          encRawSubRestX (sp0 - 80#64) encodeVarintStackX ∗ F) =
        (⌜EncodeVarintEnv ⟨val, v, cap, ptr, bs⟩ evs⌝ ∗
          ((vecU8At A.repAlloc v cap' ptr' (bs ++ encodeVarint val) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)) := by
      rw [stackAt_sub_to_encodeVarint_erX (sp0 - 80#64)]
      sep_ac_rfl
    rw [hPullEvs]
    refine SepWPpLsCl.pure_elim fun hevs => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    exact hnext sm cap' ptr' evs hpcm hrunm hspm htrm' hcsm hevs

/-- Execute a `bl memcpy` (`lsρ lsMemcpySym`) call inside `encode_raw` (Block `14`),
    transporting `A.pool lim st s` to `A.pool lim st sm` via `VmPreserved s sm`. -/
theorem encraw_call_memcpy_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (sp0 v cap ptr srcPtr ret_pc : BitVec 64) (bs payload : List (BitVec 8))
    (st : M.σ)
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hne : payload ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsρ lsMemcpySym)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : (s.readReg64 .x2).toNat = payload.length)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ (srcPtr ↦ₛ payload) ∗ A.pool lim st s ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
            (cap.toNat - bs.length - payload.length) ∗
          (srcPtr ↦ₛ payload) ∗ A.pool lim st sm ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hcall := encraw_memcpy_placed_ok_x hC
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  refine sepWPpLsCl_call_withLsCl_noPanic (x := (ptr + BitVec.ofNat 64 bs.length, srcPtr, payload))
    (F := ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
             (cap.toNat - bs.length - payload.length) ∗
           A.pool lim st s) ∗
          encRawSubRestX (sp0 - 80#64) extHookStack ∗ F)
    hcall hpc hrun halign hlr ?_ ?_
  · intro R' hm
    rw [hP, vecU8At_expose_slice A.repAlloc v cap ptr bs payload.length hle hcap hptr hpos,
        stackAt_sub_to_memcpy_erX (sp0 - 80#64)] at hm
    simp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, hsp, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun hvm => ?_
    refine SepWPpLsCl.pure_elim fun ⟨_, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    rw [← A.pool_of_vmPreserved hvm]
    refine SepWPpLsCl.weaken_pre ?_ (hnext sm hvm hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_memcpy_erX (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

/-- Envelope-parameterized `encode::<Chain>` specification at `encodeChainStackX`
    (`= encodeChainSpecX M A lim` when `chainEnv := EncodeChainEnv`). -/
def encodeChainSpecWithEnvX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (chainEnv : EncodeChainGhost → List AllocEvent → Prop) :
    Spec (EncodeChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = BitVec.ofNat 64 x.tag ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.v ∧
      (x.tag = 6 ∨ x.tag = 7) ∧
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32 ∧
      FitsEnv M lim st (chainEnv x)⌝ ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp encodeChainStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ chainEnv x evs⌝ ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ lenField x.tag (encChainMem x.gc))) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp encodeChainStackX

theorem encodeChainSpecWithEnvX_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    encodeChainSpecWithEnvX M A lim EncodeChainEnv = encodeChainSpecX M A lim := rfl

/-- Execute a `bl encode::<Chain>` (`lsmpl.base 12`) call inside `encode_raw` on `protoChainAt`
    under general envelope `chainEnv`. -/
theorem encraw_call_protoEncodeChain_env_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {chainEnv : EncodeChainGhost → List AllocEvent → Prop}
    {H : LibsignalHooks}
    (hEC : subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpecWithEnvX M A lim chainEnv)))
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (st : M.σ)
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    (hfit : FitsEnv M lim st (chainEnv ⟨tag, a, gc, v, cap, ptr, bs⟩))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 12)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (protoChainAt A.repAlloc gc a ∗ vecU8At A.repAlloc v cap ptr bs ∗
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      chainEnv ⟨tag, a, gc, v, cap, ptr, bs⟩ evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((protoChainAt A.repAlloc gc a ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hcall : subroutine_ok (lsProg_14 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpecWithEnvX M A lim chainEnv)) :=
    ls_subroutine_ok_of_callee (callerProg := lsProg_14 H) hEC
  refine sepWPpLsCl_call_lscl_noPanic (x := (⟨tag, a, gc, v, cap, ptr, bs⟩, st))
    (F := encRawSubRestX (sp0 - 80#64) encodeChainStackX ∗ F)
    hcall hpc hrun halign hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeChainX (sp0 - 80#64)] at hm
    simp only [encodeChainSpecWithEnvX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, htag, hlen_lt, hfit⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeChainSpecWithEnvX, hsp, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun evs => SepWPpLsCl.exists_elim fun cap' =>
      SepWPpLsCl.exists_elim fun ptr' => ?_
    refine SepWPpLsCl.pure_elim fun ⟨htrm, hevs⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpLsCl.weaken_pre ?_ (hnext sm cap' ptr' evs hpcm hrunm hspm htrm' hcsm hevs)
    rw [stackAt_sub_to_encodeChainX (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

/-- Execute a `bl encode::<Chain>` (`lsmpl.base 12`) call inside `encode_raw` on `chainAt`
    under general envelope `chainEnv`. -/
theorem encraw_call_encodeChain_env_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {chainEnv : EncodeChainGhost → List AllocEvent → Prop}
    {H : LibsignalHooks}
    (hEC : subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpecWithEnvX M A lim chainEnv)))
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (st : M.σ)
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    (hfit : FitsEnv M lim st (chainEnv ⟨tag, a, gc, v, cap, ptr, bs⟩))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 12)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (chainAt A.repAlloc gc a ∗ vecU8At A.repAlloc v cap ptr bs ∗
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      chainEnv ⟨tag, a, gc, v, cap, ptr, bs⟩ evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((chainAt A.repAlloc gc a ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hP' : P = (protoChainAt A.repAlloc gc a ∗ vecU8At A.repAlloc v cap ptr bs ∗
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F) := by
    rw [hP, chainAt_eq_protoChainAt_er A.repAlloc gc a]; sep_ac_rfl
  refine encraw_call_protoEncodeChain_env_placed_x hEC tag sp0 a v cap ptr ret_pc gc bs st
    htag hlen_lt hfit hpc hrun hsp halign htr hlr hx0 hx1 hx2 hP' ?_
  intro sm cap' ptr' evs hpcm hrunm hspm htrm hcsm hevs
  have hPostEq :
      ((protoChainAt A.repAlloc gc a ∗
        vecU8At A.repAlloc v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
        (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F)) =
      ((chainAt A.repAlloc gc a ∗
        vecU8At A.repAlloc v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F) := by
    rw [chainAt_eq_protoChainAt_er A.repAlloc gc a]; sep_ac_rfl
  rw [hPostEq]
  exact hnext sm cap' ptr' evs hpcm hrunm hspm htrm hcsm hevs

abbrev encraw_call_protoEncodeChain_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hEC : EncodeChainPlacedOkX M A lim H) :=
  @encraw_call_protoEncodeChain_env_placed_x _ M A lim EncodeChainEnv H
    (by rw [encodeChainSpecWithEnvX_eq]; exact hEC)

abbrev encraw_call_encodeChain_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hEC : EncodeChainPlacedOkX M A lim H) :=
  @encraw_call_encodeChain_env_placed_x _ M A lim EncodeChainEnv H
    (by rw [encodeChainSpecWithEnvX_eq]; exact hEC)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget
