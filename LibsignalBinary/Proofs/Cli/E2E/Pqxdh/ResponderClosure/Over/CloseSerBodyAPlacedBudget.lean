/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyAPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PrologueVersionLocalIdentity
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `SessionRecord::serialize`: Field-2 Proof

Proves the budget-threaded `[LibsignalPlacement]` field-2 encoding steps
`serField2_placed_step_sepWP` and `serField2_placed_step` on Block `52` (`lsProg_52 H`,
`+444 .. +692`) from `DoReservePlacedOkX` and `EncodeVarintPlacedOkX`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyAPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl sepWP_seq_lscl lsρ lsMemcpySym blkPl_10 blkPl_13
)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (
  DoReserveCall finishGrowStackX reserveCap ls_subroutine_ok_cl_of_callee
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  EncodeVarintGhost vecRest vecU8Buf vecU8At_eq_header_sep_buf vecU8Buf_bounds
)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Placed (lsProg_52 blkPl_52 blkLib_eq_52)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  subroutine_ok_withLsCodeLoaded_frame_weaken subroutine_ok_withLsCl_of_withLsCodeLoaded
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  serializeSubStackX stackAt_serializeSub_splitX subroutine_ok_withLsCodeLoaded_of_withLsCl
  sepWP_exists_left_sepX sepWP_pure_left_sepX
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  entails_of_sep_focus satisfies_of_sep_focus encodeVarint_length_le_10
  vecSrcRest vecCopyDone vecU8At_open_src vecU8At_expose_slice
  cmp_hi_false_of_le cmp_hi_true_of_gt cmp_ls_true_of_le ofNat64_len_beq_zero_false
  reserveCap_bounds_add
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  sf2_sp_aligned SerField2Saved sf2_lt_of_ofNat sf2_cap_beq_len_false sf2_cap_eq_ofNat_len
  sf2_lenField_two sf2_off8 sf2_off16 sf2_vec432_eq sf2_vec432_open_one sf2_vec432_close_one
  sf2_vec432_slice_eq
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents doReserveSpecWithStack doReserveSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv encodeVarintEvents encodeVarintEvents_of_spare
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil encRawSegEnv_append
  fitsEnv_encRawSeg_left fitsEnv_encRawSeg_right
  fitsEnv_doReserve_of_encRawSeg fitsEnv_encodeVarint_of_encRawSeg
  doReserveEnv_sub_boundedRustEvs encodeVarintEnv_sub_boundedRustEvs
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget (doReserveStackX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  SepWPpLsCl DoReservePlacedOkX EncodeVarintPlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget (
  encodeVarintSubSpecX memcpySubSpecX encodeVarint_placed_sub_clX memcpy_placed_sub_clX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlacedBudget (
  SerField2Env serField2Env_of_spare serField2Env_of_not_spare
  SerField2PlacedStepStmt SerField2PlacedStepSepWPStmt
)

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
  vecRest vecU8Buf vecSrcRest vecCopyDone
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "wp_seg_sync52 " hseg:ident mid:term : tactic =>
  `(tactic| (
    apply ($hseg:ident (mid := $mid))
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; assumption)
      fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [arm64_norm]))
      (hnext := ?_)
    clear _hnsp
    try clear _m_strip))

/-! ## `SepWP` framing and `EncRawSegEnv` inclusion lemmas -/

set_option allowUnsafeReducibility true in
attribute [local semireducible] SepWP in
private theorem sepWP_extract_vecU8At_bounds {A : RustAlloc} {v cap ptr : BitVec 64}
    {bs : List (BitVec 8)} {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hP : P = vecU8At A v cap ptr bs ∗ F := by sep_frame)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0#64 → SepWP prog ret s P Q) :
    SepWP prog ret s P Q := by
  intro R hm
  have hm' :
      s.mem ⊨ vecU8Buf A cap ptr bs ∗
        (vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ F ∗ R) := by
    rw [hP, vecU8At_eq_header_sep_buf] at hm
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  obtain ⟨h1, h2, h3⟩ := vecU8Buf_bounds hm'
  exact h h1 h2 h3 R hm

private theorem sepWP_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWP prog ret s P' Q) :
    SepWP prog ret s P Q :=
  SepWP.fold hent (F := emp) (sepConj_emp P).symm (by rwa [sepConj_emp])

private theorem sepWP_call_withLsCl {α : Type} {pl : Obj.MultiPlacement} {prog : Program}
    {entry target_pc ret_pc : BitVec 64} {spec : Spec α} {x : α}
    {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hnext : ∀ sf : State, LibsignalCodeLoaded pl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) Q) :
    SepWP prog target_pc s P Q := by
  refine SepWP.call_subroutine_frame hcall (x := x) (F := F) hpc hrun hsp hlr
    (fun R hm => ?_)
    (fun R' sf _ hp => by
      dsimp only [withLsCl] at hp
      rw [hpan_false sf] at hp
      exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by
      dsimp only [withLsCl] at he
      rw [hexit_false code sf] at he
      exact not_satisfies_false_sepConj he)
    (fun sf hpcs hrns hsps hcss => ?_)
    (fun R' sf _ ho => by
      dsimp only [withLsCl] at ho
      rw [hoom_false sf] at ho
      exact False.elim (not_satisfies_false_sepConj ho))
  · dsimp only [withLsCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre R hm⟩
  · dsimp only [withLsCl]
    exact sepWP_pure_left_sepX fun hcl_sf => hnext sf hcl_sf hpcs hrns hsps hcss

private theorem encRawSegEnv_of_doReserveEnv {x : DoReserveCall} {bsLen addedLen : Nat}
    {evs : List AllocEvent}
    (ha_pos : 1 ≤ addedLen)
    (hcap : x.cap.toNat ≤ bsLen + addedLen)
    (hlen : x.bs.length + x.additional ≤ bsLen + addedLen)
    (hout : bsLen + addedLen < 2 ^ 61)
    (hevs : DoReserveEnv x evs) :
    EncRawSegEnv bsLen addedLen evs :=
  (doReserveEnv_sub_boundedRustEvs hcap hlen hout hevs).mono (by omega) (Nat.le_refl _)

private theorem encRawSegEnv_of_encodeVarintEnv {x : EncodeVarintGhost} {bsLen addedLen : Nat}
    {evs : List AllocEvent}
    (ha : (encodeVarint x.val).length ≤ addedLen)
    (hlen : x.bs.length + (encodeVarint x.val).length ≤ bsLen + addedLen)
    (hout : bsLen + addedLen < 2 ^ 61)
    (hevs : EncodeVarintEnv x evs) :
    EncRawSegEnv bsLen addedLen evs :=
  (encodeVarintEnv_sub_boundedRustEvs hlen hout hevs).mono (by omega) (Nat.le_refl _)

private theorem encodeVarint_length_ge_one (v : BitVec 64) :
    1 ≤ (encodeVarint v).length := by
  unfold encodeVarint CryptoVerification.LibsignalProtoCodec.encodeVarintAux
  split <;> simp

private theorem lenField_two_length_ge_two (enc : List (BitVec 8)) :
    2 ≤ (lenField 2 enc).length := by
  have hpos := encodeVarint_length_ge_one (BitVec.ofNat 64 enc.length)
  rw [sf2_lenField_two]
  simp only [List.length_append, List.length_singleton]
  omega

/-! ## Lifted `doReserveSubSpecX` and callee steps -/

/-- `doReserveSpecX M A lim` lifted from `doReserveStackX` to `serializeSubStackX`. -/
def doReserveSubSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      newCap + 1 ≤ 2 ^ 63 ∧ FitsEnv M lim st (DoReserveEnv x)⌝ ∗
    vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp serializeSubStackX
  post := fun (x, st) s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64, vecU8At A.repAlloc x.v (BitVec.ofNat 64 newCap) p' x.bs) ∗
    A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗ stackAt s0.sp serializeSubStackX

theorem doReserve_placed_sub_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hDR : DoReservePlacedOkX M A lim H) :
    subroutine_ok callerProg (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSubSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - doReserveStackX))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (ls_subroutine_ok_cl_of_callee (callerProg := callerProg) hDR))
    (fun ⟨x, st⟩ s0 => ?_)
    (fun ⟨x, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [doReserveSubSpecX, doReserveSpecX, doReserveSpecWithStack,
      doReserveStackX, finishGrowStackX,
      stackAt_serializeSub_splitX s0.sp doReserveStackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [doReserveSubSpecX, doReserveSpecX, doReserveSpecWithStack,
      doReserveStackX, finishGrowStackX,
      stackAt_serializeSub_splitX s0.sp doReserveStackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem doReserve_placed_sub_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hDR : DoReservePlacedOkX M A lim H) :
    subroutine_ok callerProg (blkPl_13).base
      (withLsCl lsmpl (doReserveSubSpecX M A lim)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (doReserve_placed_sub_okX hDR)

private theorem sf2_sepWP_call_doReserve [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX M A lim H)
    (sp0 v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8)) (add : Nat) (st : M.σ)
    (hcap_le : cap.toNat ≤ bs.length + add)
    (hlen_lt : bs.length + add < 2 ^ 62)
    (hfit : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v cap ptr bs add)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 800#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = bs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      bs.length + add ≤ newCap.toNat →
      newCap.toNat < 2 ^ 63 →
      SepWP (lsProg_52 H) ret sm
        ((vecU8At A.repAlloc v newCap p' bs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap ptr bs add)) st) sm ∗
          stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q) :
    SepWP (lsProg_52 H) ret s P Q := by
  have hcall : subroutine_ok (lsProg_52 H) (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSubSpecX M A lim)) :=
    doReserve_placed_sub_clX (callerProg := lsProg_52 H) hDR
  obtain ⟨hres_bound, hnew_ge, hnew_lt⟩ := reserveCap_bounds_add hcap_le hlen_lt
  refine sepWP_call_withLsCl (x := (DoReserveCall.mk v cap ptr bs add, st)) (F := F)
    hcall hcl hpc hrun halign hlr (fun R' hm => ?_)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    fun sm hclm hpcm hrunm hspm hcsm => ?_
  · rw [hP] at hm
    simp only [doReserveSubSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hres_bound, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · rw [hsp] at hspm
    dsimp only [doReserveSubSpecX]
    rw [hsp]
    conv => arg 4; arg 1; simp only [sepExists_sepConj_left, sepConj_assoc]
    refine sepWP_pure_left_sepX fun htrm => ?_
    refine sepWP_exists_left_sepX fun p' => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine sepWP_weaken_pre ?_
      (hnext sm (BitVec.ofNat 64 (reserveCap cap.toNat bs.length add)) p'
        hclm hpcm hrunm hspm htrm' hcsm hnew_ge hnew_lt)
    exact Entails.of_eq (by sep_ac_rfl)

private theorem sf2_sepWP_call_encodeVarint [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (sp0 val v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    (hlen_lt : bs.length + 10 < 2 ^ 62)
    (hfit : FitsEnv M lim st (EncodeVarintEnv ⟨val, v, cap, ptr, bs⟩))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 10)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 800#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      EncodeVarintEnv ⟨val, v, cap, ptr, bs⟩ evs →
      cap.toNat ≤ cap'.toNat →
      (bs ++ encodeVarint val).length ≤ cap'.toNat →
      (bs.length + (encodeVarint val).length ≤ cap.toNat → cap' = cap ∧ ptr' = ptr) →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWP (lsProg_52 H) ret sm
        ((vecU8At A.repAlloc v cap' ptr' (bs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q) :
    SepWP (lsProg_52 H) ret s P Q := by
  have hcall : subroutine_ok (lsProg_52 H) (lsmpl.base 10)
      (withLsCl lsmpl (encodeVarintSubSpecX M A lim)) :=
    encodeVarint_placed_sub_clX (callerProg := lsProg_52 H) hEV
  refine sepWP_call_withLsCl (x := (⟨val, v, cap, ptr, bs⟩, st)) (F := F)
    hcall hcl hpc hrun halign hlr (fun R' hm => ?_)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    fun sm hclm hpcm hrunm hspm hcsm => ?_
  · rw [hP] at hm
    simp only [encodeVarintSubSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hlen_lt, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · rw [hsp] at hspm
    dsimp only [encodeVarintSubSpecX]
    rw [hsp]
    conv => arg 4; arg 1; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine sepWP_exists_left_sepX fun evs => ?_
    refine sepWP_exists_left_sepX fun cap' => ?_
    refine sepWP_exists_left_sepX fun ptr' => ?_
    refine sepWP_pure_left_sepX fun htrm => ?_
    refine sepWP_pure_left_sepX fun ⟨hcap_le, hspare_eq⟩ => ?_
    conv => arg 4; arg 1; rw [sepConj_left_comm]
    refine sepWP_pure_left_sepX fun hevs => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine sepWP_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap')
      (ptr := ptr') (bs := bs ++ encodeVarint val)
      (F := A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 800#64) serializeSubStackX ∗ F)
      (hP := by simp only [sepConj_assoc])
      (h := fun hlen_cap' _ _ => ?_)
    refine sepWP_weaken_pre ?_
      (hnext sm cap' ptr' evs hevs hcap_le hlen_cap' hspare_eq hclm hpcm hrunm hspm htrm' hcsm)
    exact Entails.of_eq (by sep_ac_rfl)

private theorem sf2_sepWP_call_memcpy [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (sp0 v v8 v16 cap ptr srcPtr ret_pc : BitVec 64) (bs payload : List (BitVec 8)) (st : M.σ)
    (h8 : v + 8#64 = v8) (h16 : v + 16#64 = v16)
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hne : payload ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 800#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : (s.readReg64 .x2).toNat = payload.length)
    (hP : P = ((v ↦₆₄ cap) ∗ (v8 ↦₆₄ ptr) ∗ (v16 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A.repAlloc cap ptr bs ∗ (srcPtr ↦ₛ payload) ∗ A.pool lim st s ∗
      stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWP (lsProg_52 H) ret sm
        (((v ↦₆₄ cap) ∗ (v8 ↦₆₄ ptr) ∗ (v16 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecCopyDone A.repAlloc cap ptr bs payload ∗ (srcPtr ↦ₛ payload) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q) :
    SepWP (lsProg_52 H) ret s P Q := by
  subst h8 h16
  have hcall : subroutine_ok (lsProg_52 H) (lsρ lsMemcpySym) (withLsCl lsmpl memcpySubSpecX) :=
    memcpy_placed_sub_clX (callerProg := lsProg_52 H) hC
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  have hexp := vecU8At_expose_slice A.repAlloc v cap ptr bs payload.length hle hcap hptr hpos
  rw [vecU8At_eq_header_sep_buf] at hexp
  refine sepWP_call_withLsCl (x := (ptr + BitVec.ofNat 64 bs.length, srcPtr, payload))
    (F := ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
             (cap.toNat - bs.length - payload.length) ∗ A.pool lim st s) ∗ F)
    hcall hcl hpc hrun halign hlr (fun R' hm => ?_)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    fun sm hclm hpcm hrunm hspm hcsm => ?_
  · have hbuf : (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A.repAlloc cap ptr bs =
        vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A.repAlloc cap ptr bs := by
      simp only [vecHeader, sepConj_assoc]
    rw [hP] at hm
    have hm' : s.mem ⊨
        ((vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A.repAlloc cap ptr bs) ∗
          (srcPtr ↦ₛ payload) ∗ A.pool lim st s ∗
          stackAt (sp0 - 800#64) serializeSubStackX ∗ F) ∗ R' := by
      apply satisfies_of_sep_focus hm
      rw [← hbuf]
      sep_frame
    rw [hexp] at hm'
    simp only [memcpySubSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'
  · rw [hsp] at hspm
    dsimp only [memcpySubSpecX]
    rw [hsp]
    conv => arg 4; arg 1; simp only [sepConj_assoc]
    refine sepWP_pure_left_sepX fun ⟨_, htrm, hvm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_transport lim st s sm hvm).symm
    refine sepWP_weaken_pre ?_ (hnext sm hclm hpcm hrunm hspm htrm' hcsm)
    rw [hpool]
    unfold vecCopyDone
    have hpure : (bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧
        payload ≠ []) = True := eq_true ⟨hle, hcap, hptr, hne⟩
    rw [hpure, pure_true, emp_sepConj]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## Intermediate field-2 segments on `lsProg_52 H` -/

set_option maxHeartbeats 400000 in
private theorem sf2_sepWP_copy [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (sp0 q' cap ptr capE ptrE : BitVec 64) (bs1 enc fin : List (BitVec 8)) (st : M.σ)
    (hfin : fin = bs1 ++ enc)
    (henc : enc ≠ [])
    (hleE : enc.length ≤ capE.toNat)
    (hfit : bs1.length + enc.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hlen : bs1.length + enc.length < 2 ^ 61)
    {ret : BitVec 64} {s0 sI s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_52).base + bv% (472))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 800#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 bs1.length)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 enc.length)
    (hx22 : s.readReg64 .x22 = ptrE)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hsv : SerField2Saved sI s)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (blkPl_52).base + bv% (692) →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      SerField2Saved sI sm →
      SepWP (lsProg_52 H) ret sm
        ((vecU8At A.repAlloc (sp0 - 432#64) cap' ptr' fin ∗
          vecU8At A.repAlloc q' capE ptrE enc ∗ A.pool lim st sm ∗
          stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q) :
    SepWP (lsProg_52 H) ret s
      ((vecU8At A.repAlloc (sp0 - 432#64) cap ptr bs1 ∗
        vecU8At A.repAlloc q' capE ptrE enc ∗ A.pool lim st s ∗
        stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
      Q := by
  subst hfin
  have hseg52 := fun {mid target : BitVec 64} {s : State} {Pre : SepProp}
      {post : State → SepProp → Prop} {oom : State → SepProp} =>
    sepWP_seg_ls_vm (prog := lsProg_52 H) (Q := lsProg_52 (hooksException H))
      blkLib_eq_52 (by rfl) (mid := mid) (target := target) (s := s) (Pre := Pre)
      (post := post) (oom := oom)
  change s.pc = (blkPl_52).base + 472#64 at hpc
  have henc_nat : (BitVec.ofNat 64 enc.length).toNat = enc.length := sf2_lt_of_ofNat (by omega)
  rw [sf2_vec432_eq, vecU8At_open_src A.repAlloc q' capE ptrE enc henc hleE]
  simp only [sepConj_assoc]
  apply sepWP_seq_lscl hcl (mid := lsρ lsMemcpySym)
  wp_seg_sync52 hseg52 (lsρ lsMemcpySym)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl1
  refine sf2_sepWP_call_memcpy (s0 := s0) hC sp0 (sp0 - 432#64) (sp0 - 424#64) (sp0 - 416#64)
    cap ptr ptrE ((blkPl_52).base + bv% (492)) bs1 enc st
    (sf2_off8 sp0) (sf2_off16 sp0) hfit hcap hptr henc hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (sf2_sp_aligned halign (by simp only [arm64_norm, *])) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (F := (q' ↦₆₄ capE) ∗ ((q' + 8#64) ↦₆₄ ptrE) ∗
      ((q' + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗ vecSrcRest A.repAlloc capE ptrE enc ∗ F)
    (by sep_ac_rfl) ?_
  intro sm hclm hpcm hrunm hspm htrm hcsm
  have hx20m : sm.readReg64 .x20 = BitVec.ofNat 64 bs1.length := by
    have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
  have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 enc.length := by
    have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
  have hx25m : sm.readReg64 .x25 = 24#64 := by
    have := hcsm.2.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
  have hsvm : SerField2Saved sI sm :=
    (hsv.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])).trans
      (SerField2Saved.of_calleeSavedPreserved hcsm)
  change sm.pc = (blkPl_52).base + 492#64 at hpcm
  apply sepWP_seq_lscl hclm (mid := (blkPl_52).base + bv% (692))
  wp_seg_sync52 hseg52 ((blkPl_52).base + bv% (692))
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl2
  refine sepWP_weaken_pre ?_ (hnext _ cap ptr hcl2
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hsvm.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])))
  rw [sf2_vec432_slice_eq A.repAlloc sp0 cap ptr bs1 enc hfit hcap hptr henc,
    vecU8At_open_src A.repAlloc q' capE ptrE enc henc hleE]
  exact entails_of_sep_focus (by sep_frame)

set_option maxHeartbeats 400000 in
private theorem sf2_sepWP_after_varint [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (sp0 q' cap ptr capE ptrE : BitVec 64) (bs1 enc : List (BitVec 8)) (st : M.σ)
    (hleE : enc.length ≤ capE.toNat)
    (hlen : bs1.length + enc.length < 2 ^ 61)
    (hfit_dr : ¬ bs1.length + enc.length ≤ cap.toNat →
      FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk (sp0 - 432#64) cap ptr bs1 enc.length)))
    {ret : BitVec 64} {s0 sI s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_52).base + bv% (556))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 800#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 enc.length)
    (hx22 : s.readReg64 .x22 = ptrE)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hsv : SerField2Saved sI s)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evsC : List AllocEvent),
      (if bs1.length + enc.length ≤ cap.toNat then evsC = []
       else DoReserveEnv (DoReserveCall.mk (sp0 - 432#64) cap ptr bs1 enc.length) evsC) →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (blkPl_52).base + bv% (692) →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      SerField2Saved sI sm →
      SepWP (lsProg_52 H) ret sm
        ((vecU8At A.repAlloc (sp0 - 432#64) cap' ptr' (bs1 ++ enc) ∗
          vecU8At A.repAlloc q' capE ptrE enc ∗
          A.pool lim (M.stepEvents evsC st) sm ∗
          stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q) :
    SepWP (lsProg_52 H) ret s
      ((vecU8At A.repAlloc (sp0 - 432#64) cap ptr bs1 ∗
        vecU8At A.repAlloc q' capE ptrE enc ∗ A.pool lim st s ∗
        stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
      Q := by
  have hseg52 := fun {mid target : BitVec 64} {s : State} {Pre : SepProp}
      {post : State → SepProp → Prop} {oom : State → SepProp} =>
    sepWP_seg_ls_vm (prog := lsProg_52 H) (Q := lsProg_52 (hooksException H))
      blkLib_eq_52 (by rfl) (mid := mid) (target := target) (s := s) (Pre := Pre)
      (post := post) (oom := oom)
  change s.pc = (blkPl_52).base + 556#64 at hpc
  refine sepWP_extract_vecU8At_bounds (A := A.repAlloc) (v := sp0 - 432#64) (cap := cap)
    (ptr := ptr) (bs := bs1) (h := fun hle1 hcap1 hptr1 => ?_)
  have hbs1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := sf2_lt_of_ofNat (by omega)
  have henc_nat : (BitVec.ofNat 64 enc.length).toNat = enc.length := sf2_lt_of_ofNat (by omega)
  by_cases hfit : bs1.length + enc.length ≤ cap.toNat
  · have hhi := cmp_hi_false_of_le hfit hcap1
    by_cases henc : enc = []
    · subst henc
      simp only [List.length_nil, Nat.add_zero] at hhi hx21
      rw [sf2_vec432_eq]
      simp only [sepConj_assoc]
      apply sepWP_seq_lscl hcl (mid := (blkPl_52).base + bv% (692))
      wp_seg_sync52 hseg52 ((blkPl_52).base + bv% (692))
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl1
      refine sepWP_weaken_pre ?_ (hnext _ cap ptr []
        (by simp only [List.length_nil, Nat.add_zero] at hfit ⊢; simp [hfit]) hcl1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hsv.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])))
      rw [List.append_nil, sf2_vec432_eq]
      exact entails_of_sep_focus (by sep_frame)
    · have hbeq0 : (BitVec.ofNat 64 enc.length == 0#64) = false :=
        ofNat64_len_beq_zero_false henc (by omega)
      rw [sf2_vec432_eq]
      simp only [sepConj_assoc]
      apply sepWP_seq_lscl hcl (mid := (blkPl_52).base + bv% (472))
      wp_seg_sync52 hseg52 ((blkPl_52).base + bv% (472))
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl1
      refine sepWP_weaken_pre ?_ (sf2_sepWP_copy (s0 := s0) (sI := sI) hC sp0 q' cap ptr capE ptrE
        bs1 enc (bs1 ++ enc) st rfl henc hleE hfit hcap1 hptr1 hlen hcl1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hsv.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm]))
        fun sm cap' ptr' => hnext sm cap' ptr' [] (by simp [hfit]))
      rw [sf2_vec432_eq]
      exact entails_of_sep_focus (by sep_frame)
  · have hnfit : cap.toNat < bs1.length + enc.length := by omega
    have henc : enc ≠ [] := by
      intro h; subst h; simp only [List.length_nil, Nat.add_zero] at hnfit; omega
    have hhi := cmp_hi_true_of_gt (add := enc.length) hle1 hnfit hcap1 (by omega)
    rw [sf2_vec432_eq]
    simp only [sepConj_assoc]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 13)
    wp_seg_sync52 hseg52 (lsmpl.base 13)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    refine sepWP_weaken_pre ?_ (sf2_sepWP_call_doReserve (s0 := s0) hDR sp0 (sp0 - 432#64) cap ptr
      ((blkPl_52).base + bv% (640)) bs1 enc.length st (by omega) (by omega) (hfit_dr hfit) hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (sf2_sp_aligned halign (by simp only [arm64_norm, *])) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (F := vecU8At A.repAlloc q' capE ptrE enc ∗ F) rfl ?_)
    · rw [sf2_vec432_eq]
      exact entails_of_sep_focus (by sep_frame)
    · intro s1 newCap p' hcl_s1 hpc1 hrun1 hsp1 htr1 hcs1 hnew_ge hnew_lt
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 enc.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = ptrE := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx25_1 : s1.readReg64 .x25 = 24#64 := by
        have := hcs1.2.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hsv1 : SerField2Saved sI s1 :=
        (hsv.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])).trans
          (SerField2Saved.of_calleeSavedPreserved hcs1)
      have hls := cmp_ls_true_of_le hnew_ge hnew_lt
      refine sepWP_extract_vecU8At_bounds (A := A.repAlloc) (v := sp0 - 432#64) (cap := newCap)
        (ptr := p') (bs := bs1) (h := fun _ _ hp'_ne => ?_)
      change s1.pc = (blkPl_52).base + 640#64 at hpc1
      rw [sf2_vec432_eq]
      simp only [sepConj_assoc]
      apply sepWP_seq_lscl hcl_s1 (mid := (blkPl_52).base + bv% (472))
      wp_seg_sync52 hseg52 ((blkPl_52).base + bv% (472))
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl2
      let evsDR := doReserveEvents (DoReserveCall.mk (sp0 - 432#64) cap ptr bs1 enc.length)
      refine sepWP_weaken_pre ?_ (sf2_sepWP_copy (s0 := s0) (sI := sI) hC sp0 q' newCap p'
        capE ptrE bs1 enc (bs1 ++ enc)
        (M.stepEvents evsDR st) rfl henc hleE hnew_ge hnew_lt hp'_ne hlen hcl2
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hsv1.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm]))
        fun sm cap' ptr' => hnext sm cap' ptr' evsDR (by simp [hfit, DoReserveEnv, evsDR]))
      rw [sf2_vec432_eq]
      exact entails_of_sep_focus (by sep_frame)

set_option maxHeartbeats 400000 in
private theorem sf2_sepWP_tag [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (sp0 q' cap ptr capE ptrE : BitVec 64) (bs enc : List (BitVec 8)) (st : M.σ)
    (hleE : enc.length ≤ capE.toNat)
    (hlt : bs.length < cap.toNat)
    (hlen : bs.length + 11 + enc.length < 2 ^ 61)
    (hfit_ev : FitsEnv M lim st
      (EncodeVarintEnv ⟨BitVec.ofNat 64 enc.length, sp0 - 432#64, cap, ptr, bs ++ [0x12#8]⟩))
    (hfit_after : ∀ (cap1 ptr1 : BitVec 64) (evsB : List AllocEvent),
      EncodeVarintEnv ⟨BitVec.ofNat 64 enc.length, sp0 - 432#64, cap, ptr, bs ++ [0x12#8]⟩ evsB →
      cap.toNat ≤ cap1.toNat →
      (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length)).length ≤ cap1.toNat →
      ((bs ++ [0x12#8]).length + (encodeVarint (BitVec.ofNat 64 enc.length)).length ≤ cap.toNat →
        cap1 = cap ∧ ptr1 = ptr) →
      ¬ (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length)).length + enc.length ≤
          cap1.toNat →
      FitsEnv M lim (M.stepEvents evsB st)
        (DoReserveEnv (DoReserveCall.mk (sp0 - 432#64) cap1 ptr1
          (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length)) enc.length)))
    {ret : BitVec 64} {s0 sI s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_52).base + bv% (528))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 800#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 bs.length)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 enc.length)
    (hx22 : s.readReg64 .x22 = ptrE)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx27 : s.readReg64 .x27 = 18#64)
    (hsv : SerField2Saved sI s)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evsB evsC : List AllocEvent)
        (cap1 ptr1 : BitVec 64),
      EncodeVarintEnv ⟨BitVec.ofNat 64 enc.length, sp0 - 432#64, cap, ptr, bs ++ [0x12#8]⟩ evsB →
      cap.toNat ≤ cap1.toNat →
      (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length)).length ≤ cap1.toNat →
      ((bs ++ [0x12#8]).length + (encodeVarint (BitVec.ofNat 64 enc.length)).length ≤ cap.toNat →
        cap1 = cap ∧ ptr1 = ptr) →
      (if (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length)).length + enc.length ≤
          cap1.toNat then evsC = []
       else DoReserveEnv (DoReserveCall.mk (sp0 - 432#64) cap1 ptr1
          (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length)) enc.length) evsC) →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (blkPl_52).base + bv% (692) →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      SerField2Saved sI sm →
      SepWP (lsProg_52 H) ret sm
        ((vecU8At A.repAlloc (sp0 - 432#64) cap' ptr'
            (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length) ++ enc) ∗
          vecU8At A.repAlloc q' capE ptrE enc ∗
          A.pool lim (M.stepEvents (evsB ++ evsC) st) sm ∗
          stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q) :
    SepWP (lsProg_52 H) ret s
      ((vecU8At A.repAlloc (sp0 - 432#64) cap ptr bs ∗
        vecU8At A.repAlloc q' capE ptrE enc ∗ A.pool lim st s ∗
        stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
      Q := by
  have hseg52 := fun {mid target : BitVec 64} {s : State} {Pre : SepProp}
      {post : State → SepProp → Prop} {oom : State → SepProp} =>
    sepWP_seg_ls_vm (prog := lsProg_52 H) (Q := lsProg_52 (hooksException H))
      blkLib_eq_52 (by rfl) (mid := mid) (target := target) (s := s) (Pre := Pre)
      (post := post) (oom := oom)
  have hbs_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := sf2_lt_of_ofNat (by omega)
  change s.pc = (blkPl_52).base + 528#64 at hpc
  rw [sf2_vec432_open_one A.repAlloc sp0 cap ptr bs hlt]
  conv => arg 4; arg 1; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine sepWP_exists_left_sepX fun old => ?_
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 10)
  wp_seg_sync52 hseg52 (lsmpl.base 10)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl1
  rw [sf2_vec432_close_one A.repAlloc sp0 cap ptr bs 0x12#8 hlt]
  refine sf2_sepWP_call_encodeVarint (s0 := s0) hEV sp0 (BitVec.ofNat 64 enc.length)
    (sp0 - 432#64) cap ptr
    ((blkPl_52).base + bv% (556)) (bs ++ [0x12#8]) st
    (by simp only [List.length_append, List.length_singleton]; omega) hfit_ev hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (sf2_sp_aligned halign (by simp only [arm64_norm, *])) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (F := vecU8At A.repAlloc q' capE ptrE enc ∗ F) (by sep_ac_rfl) ?_
  intro s1 cap1 ptr1 evsB hevsB hcap_le1 hlen_cap1 hspare_eq1 hcl_s1 hpc1 hrun1 hsp1 htr1 hcs1
  have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 enc.length := by
    have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
  have hx22_1 : s1.readReg64 .x22 = ptrE := by
    have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
  have hx25_1 : s1.readReg64 .x25 = 24#64 := by
    have := hcs1.2.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
  have hsv1 : SerField2Saved sI s1 :=
    (hsv.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])).trans
      (SerField2Saved.of_calleeSavedPreserved hcs1)
  have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 enc.length)
  refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (sf2_sepWP_after_varint (s0 := s0) (sI := sI) hC hDR sp0 q' cap1 ptr1 capE ptrE
      (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length)) enc (M.stepEvents evsB st)
      hleE (by simp only [List.length_append, List.length_singleton]; omega)
      (hfit_after cap1 ptr1 evsB hevsB hcap_le1 hlen_cap1 hspare_eq1)
      hcl_s1 hpc1 hrun1 hsp1 halign htr1 hx21_1 hx22_1 hx25_1 hsv1
      fun sm cap' ptr' evsC hevsC hclm hpcm hrunm hspm htrm hsvm => ?_)
  rw [← AllocCostModel.stepEvents_append]
  exact hnext sm cap' ptr' evsB evsC cap1 ptr1 hevsB hcap_le1 hlen_cap1 hspare_eq1 hevsC
    hclm hpcm hrunm hspm htrm hsvm

/-! ## Exported field-2 step theorems -/

set_option maxHeartbeats 400000 in
/-- Budget-threaded `SepWP` field-2 encoding step (`+444 .. +692`) of `<SessionRecord>::serialize`
on `lsProg_52 H`. -/
theorem serField2_placed_step_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H) :
    SerField2PlacedStepSepWPStmt M A lim H := by
  intro sp0 q' cap ptr capE ptrE bs enc st ret s0 s P F Q
    hlen32 hFit hcl hpc hrun hsp halign htr hx22 hx25 hP hnext
  subst hP
  have hseg52 := fun {mid target : BitVec 64} {s : State} {Pre : SepProp}
      {post : State → SepProp → Prop} {oom : State → SepProp} =>
    sepWP_seg_ls_vm (prog := lsProg_52 H) (Q := lsProg_52 (hooksException H))
      blkLib_eq_52 (by rfl) (mid := mid) (target := target) (s := s) (Pre := Pre)
      (post := post) (oom := oom)
  have h10 : (encodeVarint (BitVec.ofNat 64 enc.length)).length ≤ 10 :=
    encodeVarint_length_le_10 (BitVec.ofNat 64 enc.length)
  have hvlen_pos : 1 ≤ (encodeVarint (BitVec.ofNat 64 enc.length)).length :=
    encodeVarint_length_ge_one (BitVec.ofNat 64 enc.length)
  have hlf := sf2_lenField_two enc
  have hlflen :
      (lenField 2 enc).length =
        1 + (encodeVarint (BitVec.ofNat 64 enc.length)).length + enc.length := by
    rw [hlf]; simp only [List.length_append, List.length_singleton]
  have hlen : bs.length + 11 + enc.length < 2 ^ 61 := by omega
  have hnext' : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      SerField2Env cap bs enc evs →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (blkPl_52).base + bv% (692) →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      SerField2Saved s sm →
      SepWP (lsProg_52 H) ret sm
        ((vecU8At A.repAlloc (sp0 - 432#64) cap' ptr'
            (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length) ++ enc) ∗
          vecU8At A.repAlloc q' capE ptrE enc ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q := by
    intro sm cap' ptr' evs hevs hclm h1 h2 h3 h4 h5
    have h := hnext sm cap' ptr' evs hevs hclm h1 h2 h3 h4 h5
    rw [hlf] at h
    simpa only [List.append_assoc] using h
  refine sepWP_extract_vecU8At_bounds (A := A.repAlloc) (v := sp0 - 432#64) (cap := cap)
    (ptr := ptr) (bs := bs) (h := fun hle1 hcap1 hptr1 => ?_)
  refine sepWP_extract_vecU8At_bounds (A := A.repAlloc) (v := q') (cap := capE) (ptr := ptrE)
    (bs := enc) (h := fun hleE _ _ => ?_)
  have hbs_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := sf2_lt_of_ofNat (by omega)
  change s.pc = (blkPl_52).base + 444#64 at hpc
  rw [sf2_vec432_eq, vecU8At_eq_header_sep_buf A.repAlloc q' capE ptrE enc]
  simp only [vecHeader, sepConj_assoc]
  by_cases hspare : bs.length + (lenField 2 enc).length ≤ cap.toNat
  · -- Case 1: spare capacity already suffices (`evs = []`, neither `doReserve` runs)
    have hlt : bs.length < cap.toNat := by omega
    have hbeq := sf2_cap_beq_len_false hlt
    have hv_spare :
        (bs ++ [0x12#8]).length + (encodeVarint (BitVec.ofNat 64 enc.length)).length ≤ cap.toNat := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hfit_ev : FitsEnv M lim st
        (EncodeVarintEnv ⟨BitVec.ofNat 64 enc.length, sp0 - 432#64, cap, ptr, bs ++ [0x12#8]⟩) := by
      intro evsB hevsB
      rw [hevsB, encodeVarintEvents_of_spare hv_spare]
      trivial
    apply sepWP_seq_lscl hcl (mid := (blkPl_52).base + bv% (528))
    wp_seg_sync52 hseg52 ((blkPl_52).base + bv% (528))
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    refine sepWP_weaken_pre ?_ (sf2_sepWP_tag (s0 := s0) (sI := s) (F := F) hC hDR hEV sp0 q'
      cap ptr capE ptrE bs enc st hleE hlt hlen hfit_ev
      (fun cap1 _ _ _ _ _ hsp_eq hnfit => by
        obtain ⟨rfl, _⟩ := hsp_eq hv_spare
        exfalso
        apply hnfit
        simp only [List.length_append, List.length_singleton]
        omega)
      hcl1
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])
      fun sm cap' ptr' evsB evsC cap1 ptr1 hevsB _ _ hsp_eq hevsC hclm hpcm hrunm hspm htrm hsvm => ?_)
    · rw [sf2_vec432_eq, vecU8At_eq_header_sep_buf A.repAlloc q' capE ptrE enc]
      simp only [vecHeader]
      exact entails_of_sep_focus (by sep_frame)
    · rcases hsp_eq hv_spare with ⟨hcap1_eq, _⟩
      rw [hcap1_eq] at hevsC
      have hevsB0 : evsB = [] := hevsB.trans (encodeVarintEvents_of_spare hv_spare)
      have hfit1 :
          (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length)).length + enc.length ≤
            cap.toNat := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [ite_eq_left hfit1] at hevsC
      subst hevsB0 hevsC
      exact hnext' sm cap' ptr' [] ((serField2Env_of_spare hspare).mpr rfl)
        hclm hpcm hrunm hspm htrm hsvm
  · -- Case 2: capacity must grow; `SerField2Env` reduces to `EncRawSegEnv bs.length (lenField 2 enc).length`
    have hFitSeg :
        FitsEnv M lim st
          (EncRawSegEnv bs.length
            (1 + ((encodeVarint (BitVec.ofNat 64 enc.length)).length + enc.length))) := by
      have h0 : FitsEnv M lim st (EncRawSegEnv bs.length (lenField 2 enc).length) :=
        hFit.mono fun _ h => (serField2Env_of_not_spare hspare).mpr h
      rwa [hlflen, Nat.add_assoc] at h0
    have hrun_tag : ∀ (sT : State) (capT ptrT : BitVec 64) (evsA : List AllocEvent),
        EncRawSegEnv bs.length 1 evsA →
        bs.length < capT.toNat →
        LibsignalCodeLoaded lsmpl sT.mem →
        sT.pc = (blkPl_52).base + bv% (528) →
        sT.status = .Running →
        sT.sp = sp0 - 800#64 →
        sT.trace = s0.trace →
        sT.readReg64 .x20 = BitVec.ofNat 64 bs.length →
        sT.readReg64 .x21 = BitVec.ofNat 64 enc.length →
        sT.readReg64 .x22 = ptrE →
        sT.readReg64 .x25 = 24#64 →
        sT.readReg64 .x27 = 18#64 →
        SerField2Saved s sT →
        SepWP (lsProg_52 H) ret sT
          ((vecU8At A.repAlloc (sp0 - 432#64) capT ptrT bs ∗
            vecU8At A.repAlloc q' capE ptrE enc ∗
            A.pool lim (M.stepEvents evsA st) sT ∗
            stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
          Q := by
      intro sT capT ptrT evsA hevsA hltT hclT hpcT hrunT hspT htrT
        hx20T hx21T hx22T hx25T hx27T hsvT
      have hFitAfterA : FitsEnv M lim (M.stepEvents evsA st)
          (EncRawSegEnv (bs.length + 1)
            ((encodeVarint (BitVec.ofNat 64 enc.length)).length + enc.length)) :=
        fitsEnv_encRawSeg_right hFitSeg hevsA
      have hFitB : FitsEnv M lim (M.stepEvents evsA st)
          (EncRawSegEnv (bs.length + 1) (encodeVarint (BitVec.ofNat 64 enc.length)).length) :=
        fitsEnv_encRawSeg_left hFitAfterA
      have hfit_ev : FitsEnv M lim (M.stepEvents evsA st)
          (EncodeVarintEnv ⟨BitVec.ofNat 64 enc.length, sp0 - 432#64, capT, ptrT, bs ++ [0x12#8]⟩) :=
        fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; exact Nat.le_refl _)
          (by dsimp only; simp only [List.length_append, List.length_singleton]; omega)
          (by omega) hFitB
      refine sf2_sepWP_tag (s0 := s0) (sI := s) hC hDR hEV sp0 q' capT ptrT capE ptrE bs enc
        (M.stepEvents evsA st) hleE hltT hlen hfit_ev
        (fun cap1 ptr1 evsB hevsB _ hlen_cap1 _ hnfit => by
          have hevsB_seg : EncRawSegEnv (bs.length + 1)
              (encodeVarint (BitVec.ofNat 64 enc.length)).length evsB :=
            encRawSegEnv_of_encodeVarintEnv (by dsimp only; exact Nat.le_refl _)
              (by dsimp only; simp only [List.length_append, List.length_singleton]; omega)
              (by omega) hevsB
          have hFitC : FitsEnv M lim (M.stepEvents evsB (M.stepEvents evsA st))
              (EncRawSegEnv
                (bs.length + 1 + (encodeVarint (BitVec.ofNat 64 enc.length)).length)
                enc.length) :=
            fitsEnv_encRawSeg_right hFitAfterA hevsB_seg
          have henc_pos : 1 ≤ enc.length := by
            by_cases he : enc = []
            · subst he
              simp only [List.length_nil, Nat.add_zero] at hnfit
              exact absurd hlen_cap1 hnfit
            · exact List.length_pos_of_ne_nil he
          have hcap1_le :
              cap1.toNat ≤
                (bs.length + 1 + (encodeVarint (BitVec.ofNat 64 enc.length)).length) + enc.length := by
            simp only [List.length_append, List.length_singleton] at hnfit
            omega
          exact fitsEnv_doReserve_of_encRawSeg henc_pos (by dsimp only; exact hcap1_le)
            (by dsimp only; simp only [List.length_append, List.length_singleton]; omega)
            (by omega) hFitC)
        hclT hpcT hrunT hspT halign htrT hx20T hx21T hx22T hx25T hx27T hsvT
        fun sm cap' ptr' evsB evsC cap1 ptr1 hevsB _ hlen_cap1 _ hevsC hclm hpcm hrunm hspm htrm hsvm => ?_
      have hevsB_seg : EncRawSegEnv (bs.length + 1)
          (encodeVarint (BitVec.ofNat 64 enc.length)).length evsB :=
        encRawSegEnv_of_encodeVarintEnv (by dsimp only; exact Nat.le_refl _)
          (by dsimp only; simp only [List.length_append, List.length_singleton]; omega)
          (by omega) hevsB
      have hevsC_seg :
          EncRawSegEnv
            (bs.length + 1 + (encodeVarint (BitVec.ofNat 64 enc.length)).length)
            enc.length evsC := by
        by_cases hfitC :
            (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length)).length + enc.length ≤
              cap1.toNat
        · simp only [hfitC, ↓reduceIte] at hevsC
          subst hevsC
          exact encRawSegEnv_nil _ _
        · simp only [hfitC, ↓reduceIte] at hevsC
          have henc_pos : 1 ≤ enc.length := by
            by_cases he : enc = []
            · subst he
              simp only [List.length_nil, Nat.add_zero] at hfitC
              exact absurd hlen_cap1 hfitC
            · exact List.length_pos_of_ne_nil he
          have hcap1_le :
              cap1.toNat ≤
                (bs.length + 1 + (encodeVarint (BitVec.ofNat 64 enc.length)).length) + enc.length := by
            simp only [List.length_append, List.length_singleton] at hfitC
            omega
          exact encRawSegEnv_of_doReserveEnv henc_pos (by dsimp only; exact hcap1_le)
            (by dsimp only; simp only [List.length_append, List.length_singleton]; omega)
            (by omega) hevsC
      have hevsBC_seg :
          EncRawSegEnv (bs.length + 1)
            ((encodeVarint (BitVec.ofNat 64 enc.length)).length + enc.length) (evsB ++ evsC) :=
        encRawSegEnv_append hevsB_seg hevsC_seg
      have hevsAll_seg : EncRawSegEnv bs.length (lenField 2 enc).length (evsA ++ (evsB ++ evsC)) := by
        rw [hlflen, Nat.add_assoc]
        exact encRawSegEnv_append hevsA hevsBC_seg
      rw [← AllocCostModel.stepEvents_append]
      exact hnext' sm cap' ptr' (evsA ++ (evsB ++ evsC))
        ((serField2Env_of_not_spare hspare).mpr hevsAll_seg) hclm hpcm hrunm hspm htrm hsvm
    by_cases hlt : bs.length < cap.toNat
    · have hbeq := sf2_cap_beq_len_false hlt
      apply sepWP_seq_lscl hcl (mid := (blkPl_52).base + bv% (528))
      wp_seg_sync52 hseg52 ((blkPl_52).base + bv% (528))
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl1
      refine sepWP_weaken_pre ?_ (hrun_tag _ cap ptr [] (encRawSegEnv_nil bs.length 1) hlt hcl1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm]))
      rw [sf2_vec432_eq, vecU8At_eq_header_sep_buf A.repAlloc q' capE ptrE enc]
      simp only [vecHeader]
      exact entails_of_sep_focus (by sep_frame)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := sf2_cap_eq_ofNat_len hcap_eq
      have hFitA : FitsEnv M lim st (EncRawSegEnv bs.length 1) :=
        fitsEnv_encRawSeg_left hFitSeg
      have hfit_dr1 : FitsEnv M lim st
          (DoReserveEnv (DoReserveCall.mk (sp0 - 432#64) cap ptr bs 1)) :=
        fitsEnv_doReserve_of_encRawSeg (Nat.le_refl _) (by dsimp only; omega)
          (by dsimp only; omega) (by omega) hFitA
      apply sepWP_seq_lscl hcl (mid := lsmpl.base 13)
      wp_seg_sync52 hseg52 (lsmpl.base 13)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl1
      refine sepWP_weaken_pre ?_ (sf2_sepWP_call_doReserve (s0 := s0) hDR sp0 (sp0 - 432#64) cap ptr
        ((blkPl_52).base + bv% (608)) bs 1 st (by omega) (by omega) hfit_dr1 hcl1
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (sf2_sp_aligned halign (by simp only [arm64_norm, *])) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (F := vecU8At A.repAlloc q' capE ptrE enc ∗ F) rfl ?_)
      · rw [sf2_vec432_eq, vecU8At_eq_header_sep_buf A.repAlloc q' capE ptrE enc]
        simp only [vecHeader]
        exact entails_of_sep_focus (by sep_frame)
      · intro s1 newCap p' hcl_s1 hpc1 hrun1 hsp1 htr1 hcs1 hnew_ge hnew_lt
        have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 enc.length := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx22_1 : s1.readReg64 .x22 = ptrE := by
          have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx25_1 : s1.readReg64 .x25 = 24#64 := by
          have := hcs1.2.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx27_1 : s1.readReg64 .x27 = 18#64 := by
          have := hcs1.2.2.2.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hsv1 : SerField2Saved s s1 := by
          refine SerField2Saved.trans ?_ (SerField2Saved.of_calleeSavedPreserved hcs1)
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm]
        have hnew_gt : bs.length < newCap.toNat := by omega
        have hevsA : EncRawSegEnv bs.length 1
            (doReserveEvents (DoReserveCall.mk (sp0 - 432#64) cap ptr bs 1)) :=
          encRawSegEnv_of_doReserveEnv (Nat.le_refl _) (by dsimp only; omega)
            (by dsimp only; omega) (by omega) rfl
        change s1.pc = (blkPl_52).base + 608#64 at hpc1
        rw [sf2_vec432_eq]
        simp only [sepConj_assoc]
        apply sepWP_seq_lscl hcl_s1 (mid := (blkPl_52).base + bv% (528))
        wp_seg_sync52 hseg52 ((blkPl_52).base + bv% (528))
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hcl2
        refine sepWP_weaken_pre ?_
          (hrun_tag _ newCap p' (doReserveEvents (DoReserveCall.mk (sp0 - 432#64) cap ptr bs 1))
            hevsA hnew_gt hcl2
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hsv1.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])))
        rw [sf2_vec432_eq]
        exact entails_of_sep_focus (by sep_frame)

/-- Budget-threaded `SepWPpLsCl` field-2 encoding step (`+444 .. +692`) of
`<SessionRecord>::serialize` on `lsProg_52 H`. -/
theorem serField2_placed_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H) :
    SerField2PlacedStepStmt M A lim H := by
  intro sp0 q' cap ptr capE ptrE bs enc st ret s0 s P F Q Qp
    hlen32 hFit hpc hrun hsp halign htr hx22 hx25 hP hnext hcl
  exact SepWPpLsCl.of_sepWP (mid := (blkPl_52).base + bv% (692))
    (serField2_placed_step_sepWP hC hDR hEV sp0 q' cap ptr capE ptrE bs enc st
      hlen32 hFit hcl hpc hrun hsp halign htr hx22 hx25 hP
      fun sm cap' ptr' evs hevs _ hpcm hrunm hspm htrm hsvm =>
        SepWP.done hpcm hrunm (hnext sm cap' ptr' evs hevs hpcm hrunm hspm htrm hsvm))
    hcl

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyAPlacedBudget
