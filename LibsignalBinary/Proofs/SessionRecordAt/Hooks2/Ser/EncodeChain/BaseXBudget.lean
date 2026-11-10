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
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseX
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Callee Step Lemmas for `encode::<Chain, Vec<u8>>` (Block `12`)

Proves `VmPreserved`-threading `SepWPpLsCl` combinators, `EncRawSegEnv` refinement lemmas, and
budget-threaded Block `12` callee step helpers (`encode_varint`, `do_reserve_and_handle`, and
`memcpy`) at `encChainSubStackX`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl LibsignalCodeLoaded
  withLsCodeLoaded withLsCl sepWP_mono_lscl
  ls_subroutine_ok_of_block lsMemcpySym lsρ blkPC_10 blkPl_10 blkPC_13 blkPl_13
)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack reserveCap DoReserveCall sessionMemcpySpec
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  encodeVarintStackX EncodeVarintGhost vecU8Buf vecU8At_eq_header_sep_buf reserveCap_bounds
)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Placed (lsProg_12)
open CryptoVerification.E2E.Record.Serialization (
  EncodeChainGhost encChainMem
  encChainSubStackX encChainSubRestX sp_sub_96_aligned
  stackAt_sub_to_encodeVarintX stackAt_sub_to_doReserveX stackAt_sub_to_memcpyX
  vecSliceRest vecU8Buf_eq_open_slice vecU8Buf_append_slice_eq
  reserveCap_slice_bounds trVRegs_of_call
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  EncodeChainEnv
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget (
  sepWPp_call_lscl_noPanic
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv doReserveEnv_sub_boundedRustEvs encodeVarintEnv_sub_boundedRustEvs
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
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  EncodeVarintPlacedOkX DoReservePlacedOkX
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Lift a `by_vm_steps` `SepWP` basic block into `SepWPpLsCl` while threading `VmPreserved s sm`. -/
theorem sepWPpLsCl_of_sepWP_vm {pl : MultiPlacement} {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧ (VmPreserved s sm → SepWPpLsCl pl prog ret sm Pm Q Qp))) :
    SepWPpLsCl pl prog ret s P Q Qp :=
  fun hcl => SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm ⟨hvm, hnext⟩ => hnext hvm hclm)

theorem sepWPpLsCl_transport_budgetPool {pl : MultiPlacement} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {s1 s2 : State}
    (hvm : VmPreserved s1 s2)
    {prog : Program} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hf : P = A.pool lim st s1 ∗ F := by sep_focus)
    (hnext : SepWPpLsCl pl prog ret s2 (A.pool lim st s2 ∗ F) Q Qp) :
    SepWPpLsCl pl prog ret s2 P Q Qp :=
  fun hcl => SepWPp.transport_budgetPool hvm hf (hnext hcl)

/-- Step a total-correctness (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`, `onExit = ⌜False⌝`)
    `withLsCodeLoaded` call inside `SepWPpLsCl` for arbitrary `Qp`. -/
theorem sepWPpLsCl_call_lscl_noPanic {α : Type} {pl : MultiPlacement} {prog : Program}
    {ret entry ret_pc : BitVec 64} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLsCl pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPpLsCl pl prog ret s P Q Qp :=
  fun hcl =>
    sepWPp_call_lscl_noPanic x hcall hpc hrun hsp hcl hlr hpre
      (fun sf hpcm hrunm hspm hclm hcsm => hnext sf hpcm hrunm hspm hcsm hclm)
      hexit hpanic hoom

/-- Step a total-correctness (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`, `onExit = ⌜False⌝`)
    `withLsCl` call inside `SepWPpLsCl` for arbitrary `Qp`. -/
theorem sepWPpLsCl_call_withLsCl_noPanic {α : Type} {pl : MultiPlacement} {prog : Program}
    {ret entry ret_pc : BitVec 64} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLsCl pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPpLsCl pl prog ret s P Q Qp :=
  sepWPpLsCl_call_lscl_noPanic x
    (subroutine_ok_mono hcall (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2))
    hpc hrun hsp hlr hpre hnext hexit hpanic hoom

/-- `EncRawSegEnv x.bs.length (lenField x.tag (encChainMem x.gc)).length` refines `EncodeChainEnv x`. -/
theorem encRawSegEnv_sub_encodeChainEnv (x : EncodeChainGhost) {evs : List AllocEvent}
    (h : EncRawSegEnv x.bs.length (lenField x.tag (encChainMem x.gc)).length evs) :
    EncodeChainEnv x evs :=
  h.mono (by omega) (Nat.le_max_right _ _)

/-- `FitsEnv M lim st (EncodeChainEnv x)` implies `FitsEnv` for the full `EncRawSegEnv` of `x`. -/
theorem fitsEnv_encRawSeg_of_encodeChainEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (x : EncodeChainGhost) (h : FitsEnv M lim st (EncodeChainEnv x)) :
    FitsEnv M lim st (EncRawSegEnv x.bs.length (lenField x.tag (encChainMem x.gc)).length) :=
  h.mono fun _ hevs => encRawSegEnv_sub_encodeChainEnv x hevs

/-- `doReserveEvents x` satisfies `EncRawSegEnv bsLen addedLen` when `1 ≤ addedLen` and both
    `x.cap.toNat` and `x.bs.length + x.additional` lie within `bsLen + addedLen < 2 ^ 61`. -/
theorem encRawSegEnv_doReserve {x : DoReserveCall} {bsLen addedLen : Nat}
    (ha_pos : 1 ≤ addedLen)
    (hcap : x.cap.toNat ≤ bsLen + addedLen)
    (hlen : x.bs.length + x.additional ≤ bsLen + addedLen)
    (hout : bsLen + addedLen < 2 ^ 61) :
    EncRawSegEnv bsLen addedLen (doReserveEvents x) :=
  (doReserveEnv_sub_boundedRustEvs hcap hlen hout rfl).mono (by omega) (Nat.le_refl _)

/-- Any `EncodeVarintEnv x evs` satisfies `EncRawSegEnv bsLen addedLen evs` when
    `(encodeVarint x.val).length ≤ addedLen` and
    `x.bs.length + (encodeVarint x.val).length ≤ bsLen + addedLen < 2 ^ 61`. -/
theorem encRawSegEnv_of_encodeVarintEnv {x : EncodeVarintGhost} {bsLen addedLen : Nat}
    {evs : List AllocEvent}
    (ha : (encodeVarint x.val).length ≤ addedLen)
    (hlen : x.bs.length + (encodeVarint x.val).length ≤ bsLen + addedLen)
    (hout : bsLen + addedLen < 2 ^ 61)
    (hevs : EncodeVarintEnv x evs) :
    EncRawSegEnv bsLen addedLen evs :=
  (encodeVarintEnv_sub_boundedRustEvs hlen hout hevs).mono (by omega) (Nat.le_refl _)

/-- Step a `bl encode_varint` (`lsmpl.base 10`) call inside `encode::<Chain>` (Block `12`) at
    `encChainSubStackX`, threading `A.pool lim st` under `FitsEnv M lim st (EncodeVarintEnv ...)`. -/
theorem step_encChain_encodeVarint_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (val v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (st : M.σ)
    (hlen_lt : curBs.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncodeVarintEnv (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 10)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      EncodeVarintEnv (EncodeVarintGhost.mk val v curCap curPtr curBs) evs →
      curCap.toNat ≤ cap'.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat → cap' = curCap ∧ ptr' = curPtr) →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap' ptr' (curBs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  have hEV' : subroutine_ok (lsProg_12 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hEV
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine sepWPpLsCl_call_lscl_noPanic (x := (EncodeVarintGhost.mk val v curCap curPtr curBs, st))
    (F := encChainSubRestX (sp0 - 96#64) encodeVarintStackX ∗ F)
    hEV' hpc hrun hsp_aligned hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarintX (sp0 - 96#64)] at hm
    simp only [encodeVarintSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, Or.inr (by omega), hfit⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeVarintSpecX, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun evs => SepWPpLsCl.exists_elim fun cap' =>
      SepWPpLsCl.exists_elim fun ptr' => ?_
    refine SepWPpLsCl.pure_elim fun htrm => ?_
    refine SepWPpLsCl.pure_elim fun ⟨hcap_le, hspare⟩ => ?_
    have hPullEvs :
        (vecU8At A.repAlloc v cap' ptr' (curBs ++ encodeVarint val) ∗
          ⌜EncodeVarintEnv (EncodeVarintGhost.mk val v curCap curPtr curBs) evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 96#64) encodeVarintStackX ∗
          encChainSubRestX (sp0 - 96#64) encodeVarintStackX ∗ F) =
        (⌜EncodeVarintEnv (EncodeVarintGhost.mk val v curCap curPtr curBs) evs⌝ ∗
          ((vecU8At A.repAlloc v cap' ptr' (curBs ++ encodeVarint val) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)) := by
      rw [stackAt_sub_to_encodeVarintX (sp0 - 96#64)]
      sep_ac_rfl
    rw [hPullEvs]
    refine SepWPpLsCl.pure_elim fun hevs => ?_
    exact hnext sm cap' ptr' evs hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm
      hevs hcap_le hspare

/-- Step a 1-byte `bl do_reserve_and_handle` (`lsmpl.base 13`) call inside `encode::<Chain>`
    (Block `12`) at `encChainSubStackX`, threading `A.pool lim st` under `DoReserveEnv`. -/
theorem step_encChain_reserve1_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hDR : DoReservePlacedOkX M A lim H)
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (st : M.σ)
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v curCap curPtr curBs 1)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F))
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      curBs.length < newCap.toNat →
      newCap = BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1) →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc newCap p' curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) st) sm ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  have hDR' : subroutine_ok (lsProg_12 H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hDR
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_gt, _⟩ := reserveCap_bounds (len := curBs.length) (by omega)
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 1 := by
    rw [hx2]; rfl
  refine sepWPpLsCl_call_lscl_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs 1, st))
    (F := encChainSubRestX (sp0 - 96#64) Proofs.libsignal.Hooks2.doReserveStackX ∗ F)
    hDR' hpc hrun hsp_aligned hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserveX (sp0 - 96#64)] at hm
    simp only [doReserveSpecX, doReserveSpecWithStack,
      vecU8At_eq_header_sep_buf, vecHeader, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, ?_, hfit⟩, ?_⟩
    · rw [hcap_eq]; exact hres_bound
    · convert hm using 1; sep_ac_rfl
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [doReserveSpecX, doReserveSpecWithStack,
      vecU8At_eq_header_sep_buf, vecHeader, hsp, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun htrm => ?_
    have hStackEq : stackAt (sp0 - 96#64) (finishGrowStackX + 64) =
        stackAt (sp0 - 96#64) Proofs.libsignal.Hooks2.doReserveStackX := rfl
    have hGoalEq :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)) p' curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) st) sm ∗
          stackAt (sp0 - 96#64) (finishGrowStackX + 64) ∗
          encChainSubRestX (sp0 - 96#64) Proofs.libsignal.Hooks2.doReserveStackX ∗ F) =
        (((v ↦₆₄ BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p' curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) st) sm ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      rw [hStackEq, hcap_eq, stackAt_sub_to_doReserveX (sp0 - 96#64)]
      sep_ac_rfl
    rw [hGoalEq]
    exact hnext sm (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p'
      hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hnew_gt rfl

/-- Step a slice `bl do_reserve_and_handle` (`lsmpl.base 13`) call inside `encode::<Chain>`
    (Block `12`) at `encChainSubStackX`, threading `A.pool lim st` under `DoReserveEnv`. -/
theorem step_encChain_reserveSlice_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hDR : DoReservePlacedOkX M A lim H)
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8)) (add : Nat)
    (st : M.σ)
    (hle : curBs.length ≤ curCap.toNat)
    (hrem : curCap.toNat - curBs.length < add)
    (hlen_lt : curBs.length < 2 ^ 32)
    (hadd_lt : add < 2 ^ 32)
    (hfit : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v curCap curPtr curBs add)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 add)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F))
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      curBs.length + add ≤ newCap.toNat →
      ((newCap - BitVec.ofNat 64 curBs.length).ult (BitVec.ofNat 64 add)) = false →
      newCap = BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add) →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc newCap p' curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs add)) st) sm ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  have hDR' : subroutine_ok (lsProg_12 H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hDR
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_ge, hult_false⟩ := reserveCap_slice_bounds hle hrem hlen_lt hadd_lt
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = add := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPpLsCl_call_lscl_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs add, st))
    (F := encChainSubRestX (sp0 - 96#64) Proofs.libsignal.Hooks2.doReserveStackX ∗ F)
    hDR' hpc hrun hsp_aligned hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserveX (sp0 - 96#64)] at hm
    simp only [doReserveSpecX, doReserveSpecWithStack,
      vecU8At_eq_header_sep_buf, vecHeader, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, hres_bound, hfit⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [doReserveSpecX, doReserveSpecWithStack,
      vecU8At_eq_header_sep_buf, vecHeader, hsp, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun htrm => ?_
    have hStackEq : stackAt (sp0 - 96#64) (finishGrowStackX + 64) =
        stackAt (sp0 - 96#64) Proofs.libsignal.Hooks2.doReserveStackX := rfl
    have hGoalEq :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p' curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs add)) st) sm ∗
          stackAt (sp0 - 96#64) (finishGrowStackX + 64) ∗
          encChainSubRestX (sp0 - 96#64) Proofs.libsignal.Hooks2.doReserveStackX ∗ F) =
        (((v ↦₆₄ BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p' curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs add)) st) sm ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      rw [hStackEq, stackAt_sub_to_doReserveX (sp0 - 96#64)]
      sep_ac_rfl
    rw [hGoalEq]
    exact hnext sm (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p'
      hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hnew_ge hult_false rfl

/-- Step a `bl memcpy` (`lsρ lsMemcpySym`) call inside `encode::<Chain>` (Block `12`) at
    `encChainSubStackX`, transporting `A.pool lim st s` to `A.pool lim st sm` via `VmPreserved`. -/
theorem step_encChain_memcpy_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (curCap curPtr srcPtr sp0 ret_pc : BitVec 64) (curBs sliceBs : List (BitVec 8))
    (st : M.σ)
    (hpos : 0 < sliceBs.length)
    (hle : curBs.length + sliceBs.length ≤ curCap.toNat)
    (hslice_lt : sliceBs.length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsρ lsMemcpySym)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = curPtr + BitVec.ofNat 64 curBs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 sliceBs.length)
    (hP : P = (vecU8Buf A.repAlloc curCap curPtr curBs ∗
      (srcPtr ↦ₛ sliceBs) ∗ A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8Buf A.repAlloc curCap curPtr (curBs ++ sliceBs) ∗
          (srcPtr ↦ₛ sliceBs) ∗ A.pool lim st sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  have hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)) :=
    hC.memcpy (callerProg := lsProg_12 H)
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  have hx2_toNat : (s.readReg64 .x2).toNat = sliceBs.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPpLsCl_call_withLsCl_noPanic (x := (curPtr + BitVec.ofNat 64 curBs.length, srcPtr, sliceBs))
    (F := vecSliceRest A.repAlloc curCap curPtr curBs sliceBs.length ∗
      A.pool lim st s ∗
      encChainSubRestX (sp0 - 96#64) extHookStack ∗ F)
    hmc hpc hrun hsp_aligned hlr ?_ ?_
  · intro R' hm
    rw [hP, vecU8Buf_eq_open_slice A.repAlloc curCap curPtr curBs sliceBs.length hpos hle,
      stackAt_sub_to_memcpyX (sp0 - 96#64)] at hm
    simp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_toNat⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, hsp, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun hvm => ?_
    refine SepWPpLsCl.pure_elim fun ⟨_, htrm⟩ => ?_
    have hGoalEq :
        (((curPtr + BitVec.ofNat 64 curBs.length) ↦ₛ sliceBs) ∗
          (srcPtr ↦ₛ sliceBs) ∗
          stackAt (sp0 - 96#64) extHookStack ∗
          vecSliceRest A.repAlloc curCap curPtr curBs sliceBs.length ∗
          A.pool lim st s ∗
          encChainSubRestX (sp0 - 96#64) extHookStack ∗ F) =
        ((vecU8Buf A.repAlloc curCap curPtr (curBs ++ sliceBs) ∗
          (srcPtr ↦ₛ sliceBs) ∗ A.pool lim st sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      rw [stackAt_sub_to_memcpyX (sp0 - 96#64),
        ← vecU8Buf_append_slice_eq A.repAlloc curCap curPtr curBs sliceBs hpos hle,
        ← A.pool_of_vmPreserved hvm]
      sep_ac_rfl
    rw [hGoalEq]
    exact hnext sm hvm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
