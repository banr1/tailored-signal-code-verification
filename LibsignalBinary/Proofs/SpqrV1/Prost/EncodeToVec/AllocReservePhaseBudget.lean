/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.IfaceDecide
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# `PqRatchetState::encode_to_vec`: Budget-Threaded Callee Specifications and Wrappers

Allocator-budget (`RustCliAllocBudget M`) and `VmPreserved`-strengthened callee specifications
(`shimStackSpecOf`, `rustAllocStackSpecOf`, `encodeVarintExactSpecOf`, `etvMemcpyRegionSpec`,
`encodeChainParamsExactSpecOf`, `epochEncLenStackSpecOf`, `encodeEpochDirectionExactSpecOf`,
`authEncodeExactSpecOf`) and program-polymorphic call wrappers at `s.sp = sp - 144#64`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget RustLayoutOk VmPreserved
   rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.IfaceDecide (rustLayoutOk_iff)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocNoOomSpecWithStack subroutine_ok_rustCliAllocNoOom_withStack)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8At)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.LibsignalSpqrV1
  (AuthenticatorPB ChainEpochPB ChainParamsPB EpochDirectionPB ProtoAuthenticator)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeMessage encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (AuthenticatorPBGhost ChainEpochPBGhost EpochDirectionPBGhost
   authenticatorPBPinnedAt chainEpochPBEncodedLen chainEpochPBPinnedAt epochDirectionPBPinnedAt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (EtvEncodeAuthGhost EtvEncodeChainParamsGhost EtvEncodeEpochDirectionGhost EtvEncodeVarintGhost
   StepInv encodeToVecCalleeStackOf sp_sub_144_aligned withStepInv)

private theorem sepWPp_call_cs_noPanic {α : Type} {prog : Program} {entry ret ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R, s.mem ⊨ P ∗ R → s.mem ⊨ spec.pre x s ∗ (F ∗ R))
    (hexit : ∀ sf code R, sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R) → False)
    (hpanic : ∀ sf R, sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R) → False)
    (hoom : ∀ sf R, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R) → False)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running → sm.sp = s.sp →
      CalleeSavedPreserved s sm → StepInv s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpan_mem⟩ | ⟨code, hex, hex_mem⟩ | ⟨hoom_sm, hoom_mem⟩
  · rw [hlr] at hpcm
    rw [← sepConj_assoc] at hpost
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm
        (StepInv.of_steps hsteps hcsm.2.2.2.2.2.2.2.2.2.2.2) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (hpanic sm (F ∗ R) hpan hpan_mem).elim
  · exact (hexit sm code (F ∗ R) hex hex_mem).elim
  · exact (hoom sm (F ∗ R) hoom_sm hoom_mem).elim

/-! ## 1. Initial Buffer Allocation Callee Contracts (`shimStackSpecOf`, `rustAllocStackSpecOf`) -/

/-- `VmPreserved`-strengthened stack-equipped no-op shim contract at `s.sp = sp - 144#64`. -/
def shimStackSpecOf (resStack : Nat) : Spec Unit where
  pre := fun _ s => stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun _ s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-- Lift `subroutine_ok P entry rustAllocShimVmSpec` to `shimStackSpecOf resStack`. -/
theorem subroutine_ok_shimStackSpecOf_of_rustAllocShimVm {P : Program} {entry : BitVec 64}
    (resStack : Nat) (h : subroutine_ok P entry rustAllocShimVmSpec) :
    subroutine_ok P entry (shimStackSpecOf resStack) := by
  refine subroutine_ok_outcome_intro fun _ R s0 hpc hrun hpre hsp => ?_
  dsimp only [shimStackSpecOf] at hpre
  have hpre_w : s0.mem ⊨
      rustAllocShimVmSpec.pre () s0 ∗ (stackAt s0.sp (encodeToVecCalleeStackOf resStack) ∗ R) := by
    dsimp only [rustAllocShimVmSpec]
    rw [emp_sepConj]
    exact hpre
  refine h.mono_outcome () _ s0 hpc hrun hpre_w hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocShimVmSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hacp, hvm⟩, hm'⟩
    dsimp only [shimStackSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hvm, hacp.2.1⟩, hm'⟩
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

/-- Budget-threaded stack-equipped `__rust_alloc(sz, 1)` total-correctness contract at
`s.sp = sp - 144#64` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under
`FitsEvents M lim st (rustAllocEvents sz 1)`). -/
def rustAllocStackSpecOf [LibsignalPlacement] (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (Nat × M.σ) where
  pre := fun (sz, st) s =>
    ⌜(s.readReg64 .x0).toNat = sz ∧ s.readReg64 .x1 = 1#64 ∧ 0 < sz ∧ sz < 2 ^ 63 ∧
      FitsEvents M lim st (rustAllocEvents sz 1) ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun (sz, st) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) sz 1 ∗ memRegion (sf.readReg64 .x0) sz ∗
      A.pool lim (M.stepEvents (rustAllocEvents sz 1) st) sf ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

private theorem rustLayoutOk_align1_of_lt {sz : Nat} (hpos : 0 < sz) (hlt : sz < 2 ^ 63) :
    RustLayoutOk sz 1 := by
  rw [rustLayoutOk_iff]
  refine ⟨⟨hpos, ⟨by decide, by decide⟩, by omega⟩, by decide⟩

/-- Lift `subroutine_ok P entry (rustCliAllocNoOomSpec M A lim false)` to
`rustAllocStackSpecOf resStack A lim`. -/
theorem subroutine_ok_rustAllocStackSpecOf_of_noOom [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {entry : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {resStack : Nat}
    (hle : allocHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hbound : encodeToVecCalleeStackOf resStack ≤ 2 ^ 64)
    (h : subroutine_ok P entry (rustCliAllocNoOomSpec M A lim false)) :
    subroutine_ok P entry (rustAllocStackSpecOf resStack A lim) := by
  have hw := subroutine_ok_rustCliAllocNoOom_withStack hle hbound h
  refine subroutine_ok_outcome_intro fun ⟨sz, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [rustAllocStackSpecOf] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpos, hlt, hfit, hlr⟩, hm⟩
  have hx1_nat : (s0.readReg64 .x1).toNat = 1 := by rw [hx1]; rfl
  have hpre_w : s0.mem ⊨
      (rustCliAllocNoOomSpecWithStack M A lim false (encodeToVecCalleeStackOf resStack)).pre
        (sz, 1, st) s0 ∗ R := by
    dsimp only [rustCliAllocNoOomSpecWithStack]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_nat, rustLayoutOk_align1_of_lt hpos hlt, hfit, hlr⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  refine hw.mono_outcome (sz, 1, st) R s0 hpc hrun hpre_w hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨c, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustCliAllocNoOomSpecWithStack] at hq
    simp only [Bool.false_eq_true, ↓reduceIte] at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hacp, hnz, _⟩, hm'⟩
    dsimp only [rustAllocStackSpecOf]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hnz, hacp.2.1⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-- Lift `subroutine_ok P entry (rustCliAllocBudgetSpec M A lim false)` directly to
`rustAllocStackSpecOf resStack A lim`. -/
theorem subroutine_ok_rustAllocStackSpecOf_of_budget [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {entry : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {resStack : Nat}
    (hle : allocHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hbound : encodeToVecCalleeStackOf resStack ≤ 2 ^ 64)
    (h : subroutine_ok P entry (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok P entry (rustAllocStackSpecOf resStack A lim) :=
  subroutine_ok_rustAllocStackSpecOf_of_noOom hle hbound (subroutine_ok_allocNoOom_of_budget h)

/-! ## 2. Exact-Capacity Callee Specifications & `{prog : Program}` Call Wrappers -/

/-- Budget-threaded exact-capacity `encode_varint` contract at `s.sp = sp - 144#64`:
requires `bs.length + (Proto.encodeVarint val).length ≤ cap.toNat`, performs 0 allocations
(`st` unchanged), and has `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`. -/
def encodeVarintExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EtvEncodeVarintGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeVarint x.val) ∗ A.pool lim st sf ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

theorem step_etv_encode_varint_call_prog {resStack : Nat} {M : AllocCostModel}
    {prog : Program} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (val v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeVarint val).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v cap ptr (bs ++ encodeVarint val) ∗ A.pool lim st sm ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine sepWPp_call_cs_noPanic (x := (⟨val, v, cap, ptr, bs⟩, st)) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, encodeVarintExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro sf code R' _ hm
    simp only [withStepInv, encodeVarintExactSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sf R' _ hm
    simp only [withStepInv, encodeVarintExactSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sf R' _ hm
    simp only [withStepInv, encodeVarintExactSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, encodeVarintExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

/-- `VmPreserved`-strengthened `memcpy` specification (definitionally equal to
`sessionMemcpyRegionBudgetSpec`). -/
abbrev etvMemcpyRegionSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  sessionMemcpyRegionBudgetSpec

theorem step_etv_memcpy_call_prog {M : AllocCostModel}
    {prog : Program} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hmemcpy : subroutine_ok prog call_pc etvMemcpyRegionSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hinv0 : StepInv s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      VmPreserved s sm →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim st sm) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine sepWPp_call_cs_noPanic (x := (dst, src, bs)) (F := A.pool lim st s ∗ F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro sf code R' _ hm
    dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro sf R' _ hm
    dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro sf R' _ hm
    dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_of_vmPreserved hvm).symm
    rw [hpool]
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hvm hcsm (hinv0.trans hinv_call))

/-- Budget-threaded exact-capacity `encode<ChainParams>` contract at `s.sp = sp - 144#64`. -/
def encodeChainParamsExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EtvEncodeChainParamsGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg32 .x1 = x.p.maxJump ∧
      s.readReg32 .x2 = x.p.maxOooKeys ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag.toNat ∧ x.tag.toNat < 2 ^ 29 ∧
      x.bs.length + (encodeMessage ChainParamsPB.encodeRaw x.tag x.p).length ≤ x.cap.toNat⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr
        (x.bs ++ encodeMessage ChainParamsPB.encodeRaw x.tag x.p) ∗ A.pool lim st sf ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

theorem step_etv_encode_chainParams_call_prog {resStack : Nat} {M : AllocCostModel}
    {prog : Program} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hcp : subroutine_ok prog call_pc
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A lim)))
    (tag : BitVec 32) (p : ChainParamsPB) (v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (htag1 : 1 ≤ tag.toNat) (htag2 : tag.toNat < 2 ^ 29)
    (hfit : bs.length + (encodeMessage ChainParamsPB.encodeRaw tag p).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = tag)
    (hw1 : s.readReg32 .x1 = p.maxJump)
    (hw2 : s.readReg32 .x2 = p.maxOooKeys)
    (hx3 : s.readReg64 .x3 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v cap ptr (bs ++ encodeMessage ChainParamsPB.encodeRaw tag p) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine sepWPp_call_cs_noPanic (x := (⟨tag, p, v, cap, ptr, bs⟩, st)) (F := F)
    hcp hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, encodeChainParamsExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hw1, hw2, hx3, htag1, htag2, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro sf code R' _ hm
    simp only [withStepInv, encodeChainParamsExactSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sf R' _ hm
    simp only [withStepInv, encodeChainParamsExactSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sf R' _ hm
    simp only [withStepInv, encodeChainParamsExactSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, encodeChainParamsExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

/-- `VmPreserved`-strengthened `Epoch::encoded_len` contract at `s.sp = sp - 144#64`
(1-state `A : RustAlloc` representation predicate; callers instantiate `A := B.repAlloc` and
transport `B.pool lim st` via `VmPreserved s sm`). -/
def epochEncLenStackSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec (BitVec 64 × ChainEpochPBGhost × ChainEpochPB) where
  pre := fun ⟨a, g, ep⟩ s =>
    ⌜s.readReg64 .x0 = a ∧ chainEpochPBEncodedLen ep < 2 ^ 64⌝ ∗
      chainEpochPBPinnedAt A g a ep ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun ⟨a, g, ep⟩ s0 sf =>
    ⌜VmPreserved s0 sf ∧
      sf.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen ep) ∧
      sf.trace = s0.trace⌝ ∗
      chainEpochPBPinnedAt A g a ep ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)

theorem step_etv_epoch_encLen_call_prog {resStack : Nat} {M : AllocCostModel}
    {prog : Program} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hep : subroutine_ok prog call_pc
      (withStepInv s0 (epochEncLenStackSpecOf resStack A.repAlloc)))
    (a sp ret_pc : BitVec 64) (g : ChainEpochPBGhost) (ep : ChainEpochPB)
    (hlen : chainEpochPBEncodedLen ep < 2 ^ 64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = a)
    (hinv0 : StepInv s0 s)
    (hP : P = (chainEpochPBPinnedAt A.repAlloc g a ep ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen ep) →
      VmPreserved s sm →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((chainEpochPBPinnedAt A.repAlloc g a ep ∗ A.pool lim st sm ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine sepWPp_call_cs_noPanic (x := (a, g, ep)) (F := A.pool lim st s ∗ F)
    hep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, epochEncLenStackSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hlen⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro sf code R' _ hm
    simp only [withStepInv, epochEncLenStackSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sf R' _ hm
    simp only [withStepInv, epochEncLenStackSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sf R' _ hm
    simp only [withStepInv, epochEncLenStackSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, epochEncLenStackSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hvm, hx0m, htrm⟩ => ?_
    have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_of_vmPreserved hvm).symm
    rw [hpool]
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hvm hcsm (hinv0.trans hinv_call))

/-- Budget-threaded exact-capacity `encode<EpochDirection>` contract at `s.sp = sp - 144#64`. -/
def encodeEpochDirectionExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EtvEncodeEpochDirectionGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧ s.readReg64 .x1 = x.dirA ∧ s.readReg64 .x2 = x.v ∧
      x.bs.length + (encodeMessage EpochDirectionPB.encodeRaw x.tag x.dir).length ≤ x.cap.toNat⌝ ∗
      epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
      vecU8At A.repAlloc x.v x.cap x.ptr
        (x.bs ++ encodeMessage EpochDirectionPB.encodeRaw x.tag x.dir) ∗ A.pool lim st sf ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

theorem step_etv_encode_epochDirection_call_prog {resStack : Nat} {M : AllocCostModel}
    {prog : Program} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hed : subroutine_ok prog call_pc
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A lim)))
    (tag : BitVec 32) (dirA v cap ptr sp ret_pc : BitVec 64)
    (g : EpochDirectionPBGhost) (dir : EpochDirectionPB) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeMessage EpochDirectionPB.encodeRaw tag dir).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = dirA)
    (hx2 : s.readReg64 .x2 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (epochDirectionPBPinnedAt A.repAlloc g dirA dir ∗ vecU8At A.repAlloc v cap ptr bs ∗
      A.pool lim st s ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((epochDirectionPBPinnedAt A.repAlloc g dirA dir ∗
          vecU8At A.repAlloc v cap ptr (bs ++ encodeMessage EpochDirectionPB.encodeRaw tag dir) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine sepWPp_call_cs_noPanic (x := (⟨tag, dirA, g, dir, v, cap, ptr, bs⟩, st)) (F := F)
    hed hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, encodeEpochDirectionExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hx1, hx2, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro sf code R' _ hm
    simp only [withStepInv, encodeEpochDirectionExactSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sf R' _ hm
    simp only [withStepInv, encodeEpochDirectionExactSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sf R' _ hm
    simp only [withStepInv, encodeEpochDirectionExactSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, encodeEpochDirectionExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

/-- Budget-threaded exact-capacity `encode<Authenticator>` contract at `s.sp = sp - 144#64`. -/
def authEncodeExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EtvEncodeAuthGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.authA ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeMessage ProtoAuthenticator.encodeRaw 2#32 x.auth).length ≤ x.cap.toNat⌝ ∗
      authenticatorPBPinnedAt A.repAlloc x.g x.authA x.auth ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorPBPinnedAt A.repAlloc x.g x.authA x.auth ∗
      vecU8At A.repAlloc x.v x.cap x.ptr
        (x.bs ++ encodeMessage ProtoAuthenticator.encodeRaw 2#32 x.auth) ∗ A.pool lim st sf ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

theorem step_etv_encode_auth_call_prog {resStack : Nat} {M : AllocCostModel}
    {prog : Program} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hauth : subroutine_ok prog call_pc
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (authA v cap ptr sp ret_pc : BitVec 64)
    (g : AuthenticatorPBGhost) (auth : AuthenticatorPB) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = authA)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (authenticatorPBPinnedAt A.repAlloc g authA auth ∗ vecU8At A.repAlloc v cap ptr bs ∗
      A.pool lim st s ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((authenticatorPBPinnedAt A.repAlloc g authA auth ∗
          vecU8At A.repAlloc v cap ptr (bs ++ encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine sepWPp_call_cs_noPanic (x := (⟨authA, g, auth, v, cap, ptr, bs⟩, st)) (F := F)
    hauth hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, authEncodeExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro sf code R' _ hm
    simp only [withStepInv, authEncodeExactSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sf R' _ hm
    simp only [withStepInv, authEncodeExactSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sf R' _ hm
    simp only [withStepInv, authEncodeExactSpecOf, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, authEncodeExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
