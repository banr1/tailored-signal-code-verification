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
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PrologueVersionLocalIdentity
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionClone
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneX
import ProofLib.SepLogic.WPp

/-!
# Pre-Reserved Callee Step Lemmas for `SessionStructure::encode_raw` (Block `14`)

Constructs the zero-capacity witness model (`zeroCapModel`, `vmWitnessAlloc`) to derive
`encode_varint_prealloc_placed_ok_x` without re-stepping Block `10`, and proves zero-allocation
(`VmPreserved`-preserving) Block `14` callee step lemmas for `encode_varint`, `memcpy`, and
`encode::<Chain>` when the output buffer has spare capacity.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareBaseXBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ReceiverChain)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded extract_withLsCodeLoaded
  ls_subroutine_ok_of_block
  lsMemcpySym lsρ blkPC_10 blkPl_10
)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack DoReserveCall sessionMemcpySpec doReserveStackX ls_subroutine_ok_of_callee
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  encodeVarintStackX EncodeVarintGhost vecU8Buf vecU8At_eq_header_sep_buf
)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  EncodeChainGhost encChainMem protoChainAt
  encodeRawSubStackX encRawSubRestX
  stackAt_sub_to_encodeVarint_erX stackAt_sub_to_encodeChainX stackAt_sub_to_memcpy_erX
  sepWPp_mono_x
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  satisfies_of_sep_focus entails_of_sep_focus
  vecCopyDone vecU8At_expose_slice chainAt_eq_protoChainAt_er
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (
  PoolPreserved VmPreserved AllocEvent AllocCostModel BudgetLimits zeroBudgetLimits
  RustCliAllocBudget FitsEvent FitsEvents FitsEnv rustAllocEvents rustReallocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv encodeVarintEvents_of_spare
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget (
  doReserveSpecWithPlaced encodeVarintSpecOf
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget (
  encodeVarint_gen_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  encodeChainStackX SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget (
  sepWPpLsCl_call_lscl_noPanic sepWPpLsCl_call_withLsCl_noPanic
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget (
  encraw_memcpy_placed_ok_x
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `VmPreserved` witness model and pre-reserved `encode_varint` (Block `10`) -/

private theorem poolPreserved_symm {s₁ s₂ : State} (h : PoolPreserved s₁ s₂) :
    PoolPreserved s₂ s₁ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

private theorem vmPreserved_symm {s₁ s₂ : State} (h : VmPreserved s₁ s₂) :
    VmPreserved s₂ s₁ :=
  h.symm

/-- Zero-capacity `AllocCostModel` (`stepReserve ev _ := ev.reqBytes + 1`) rejecting every non-empty
    allocation event sequence under `zeroCapLim` (`physCap = 0`, `enforced = true`). -/
def zeroCapModel : AllocCostModel where
  σ := Unit
  init := ()
  step := fun _ _ => ()
  footprint := fun _ => 0
  maxDynIvs := fun _ => 0
  stepReserve := fun ev _ => ev.reqBytes + 1
  liveBytes := fun _ => 0
  footprint_mono := fun _ _ => Nat.le_refl 0
  maxDynIvs_mono := fun _ _ => Nat.le_refl 0
  stepReserve_mono := fun _ _ _ => Nat.le_refl _
  req_le_stepReserve := fun ev _ => Nat.le_succ ev.reqBytes
  liveBytes_free_le := fun _ _ _ => Nat.le_refl 0

def zeroCapLim : BudgetLimits :=
  { staticCount := 0, staticBytes := 0, physCap := 0, enforced := true }

private theorem not_fitsEvent_zeroCapLim (ev : AllocEvent) :
    ¬ FitsEvent zeroCapModel zeroCapLim () ev := by
  rintro ⟨_, _, hram, _⟩
  dsimp only [zeroCapModel, zeroCapLim] at hram
  omega

private theorem not_fitsEnv_doReserve_zeroCapLim (c : DoReserveCall) (st : zeroCapModel.σ) :
    ¬ FitsEnv zeroCapModel zeroCapLim st (DoReserveEnv c) := by
  intro hfit
  cases st
  have hevs : FitsEvents zeroCapModel zeroCapLim () (doReserveEvents c) :=
    hfit (doReserveEvents c) rfl
  unfold doReserveEvents at hevs
  by_cases hc : c.cap = 0#64
  · rw [hc] at hevs
    simp only [↓reduceIte] at hevs
    unfold rustAllocEvents at hevs
    split at hevs <;> exact not_fitsEvent_zeroCapLim _ hevs.1
  · simp only [hc, ↓reduceIte] at hevs
    unfold rustReallocEvents at hevs
    split at hevs <;> exact not_fitsEvent_zeroCapLim _ hevs.1

/-- `RustCliAllocBudget zeroCapModel` whose enforced pool asserts `⌜VmPreserved s0 s⌝` while sharing
    `A.live` and `A.block_valid` (`(vmWitnessAlloc A s0).repAlloc = A.repAlloc` by `rfl`). -/
def vmWitnessAlloc {M : AllocCostModel} (A : RustCliAllocBudget M) (s0 : State) :
    RustCliAllocBudget zeroCapModel where
  pool := fun lim _ s => if lim.enforced then ⌜VmPreserved s0 s⌝ else ⌜PoolPreserved s0 s⌝
  live := A.live
  block_valid := A.block_valid
  pool_transport := by
    intro lim _ s s' h
    cases lim.enforced <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact congrArg SepProp.pure
        (propext ⟨fun h0' => h0'.trans (poolPreserved_symm h.1), fun h0 => h0.trans h.1⟩)
    · exact congrArg SepProp.pure
        (propext ⟨fun h0' => h0'.trans (vmPreserved_symm h), fun h0 => h0.trans h⟩)
  pool_zero_transport := by
    intro _ s s' h
    dsimp only [zeroBudgetLimits]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact congrArg SepProp.pure
      (propext ⟨fun h0' => h0'.trans (poolPreserved_symm h), fun h0 => h0.trans h⟩)

/-- Pre-reserved (`0`-allocation, `VmPreserved`) contract of `encode_varint` (Block `10`) at
    `encodeVarintStackX`. -/
def encodeVarintPreallocSpecX (A : RustAlloc) : Spec EncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat ∧
      (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62)⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ stackAt s.sp encodeVarintStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodeVarint x.val) ∗
      stackAt s0.sp encodeVarintStackX

/-- Block `10` satisfies `encodeVarintPreallocSpecX A.repAlloc` with `0` extern hooks. -/
theorem encode_varint_prealloc_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (H : LibsignalHooks) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintPreallocSpecX A.repAlloc)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre hsp0
  obtain ⟨_, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [encodeVarintPreallocSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hspare, hlen_or⟩, hmem⟩
  let Aw := vmWitnessAlloc A s0
  have hfitAw : FitsEnv zeroCapModel zeroCapLim () (EncodeVarintEnv x) := by
    intro evs hevs
    have heq : evs = [] := hevs.trans (encodeVarintEvents_of_spare hspare)
    subst heq
    trivial
  have hpreAw : s0.mem ⊨ (encodeVarintSpecOf doReserveStackX Aw zeroCapLim).pre (x, ()) s0 ∗ R := by
    simp only [encodeVarintSpecOf, Aw, vmWitnessAlloc, zeroCapLim, ↓reduceIte,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hlen_or, hfitAw⟩, ?_⟩
    rw [eq_true (VmPreserved.refl s0), pure_true, emp_sepConj]
    exact hmem
  have hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced doReserveStackX s0 Aw zeroCapLim) := by
    refine subroutine_ok_outcome_intro fun ⟨c, st⟩ _ _ _ _ hpreDR _ => ?_
    simp only [doReserveSpecWithPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpreDR
    exact (not_fitsEnv_doReserve_zeroCapLim c st hpreDR.1.2.2.2.2.2.2.2).elim
  obtain ⟨P, hP, hwp⟩ := encodeVarint_gen_placed_ok Aw zeroCapLim H (resStack := doReserveStackX)
    (by decide) x () R s0 hdoReserve hpc0 hrun0 hpreAw hsp0
  refine ⟨P, R, hP, sepWPp_mono_x ?_ (fun _ _ hp => hp) hwp⟩
  intro sf P_f ⟨hq, hspf, hcsf⟩
  refine ⟨fun hmf => ?_, hspf, hcsf⟩
  have hpost := hq hmf
  dsimp only [encodeVarintSpecOf, Aw, vmWitnessAlloc, zeroCapLim] at hpost
  simp only [↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hpost
  rcases hpost with ⟨htr, hpost⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
  rcases hpost with ⟨cap', hpost⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
  rcases hpost with ⟨ptr', hpost⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
  rcases hpost with ⟨⟨_, hpres⟩, hpost⟩
  obtain ⟨rfl, rfl⟩ := hpres hspare
  rw [sepConj_left_comm (vecU8At _ _ _ _ _), sepExists_sepConj_left, satisfies_sepExists] at hpost
  rcases hpost with ⟨evs, hpost⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
  rcases hpost with ⟨_, hvm, hcomb⟩
  simp only [encodeVarintPreallocSpecX, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htr, hvm⟩, Satisfies.mono (Entails.of_eq rfl) hcomb⟩

/-! ## Block `14` pre-reserved callee step lemmas -/

/-- Execute a pre-reserved (`0`-allocation, `VmPreserved`) `bl encode_varint` (`lsmpl.base 10`)
    call inside `encode_raw` (Block `14`), preserving `cap` and `ptr` with no `A.pool`. -/
theorem encraw_call_encodeVarint_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {H : LibsignalHooks}
    (sp0 val v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hspare : bs.length + (encodeVarint val).length ≤ cap.toNat)
    (hlen_lt : bs.length + 10 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 10)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc v cap ptr (bs ++ encodeVarint val) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hcall : subroutine_ok (lsProg_14 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintPreallocSpecX A.repAlloc)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_14 H)
      (encode_varint_prealloc_placed_ok_x A H)
  refine sepWPpLsCl_call_lscl_noPanic (x := EncodeVarintGhost.mk val v cap ptr bs)
    (F := encRawSubRestX (sp0 - 80#64) encodeVarintStackX ∗ F)
    hcall hpc hrun halign hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarint_erX (sp0 - 80#64)] at hm
    simp only [encodeVarintPreallocSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hspare, Or.inr hlen_lt⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeVarintPreallocSpecX, hsp, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun ⟨htrm, hvm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpLsCl.weaken_pre ?_ (hnext sm hvm hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_encodeVarint_erX (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

/-- Execute a `bl memcpy` (`lsρ lsMemcpySym`) call inside `encode_raw` (Block `14`) with no `A.pool`,
    yielding `VmPreserved s sm`. -/
theorem encraw_call_memcpy_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (sp0 v cap ptr srcPtr ret_pc : BitVec 64) (bs payload : List (BitVec 8))
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
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ (srcPtr ↦ₛ payload) ∗
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
          (srcPtr ↦ₛ payload) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hcall := encraw_memcpy_placed_ok_x hC
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  refine sepWPpLsCl_call_withLsCl_noPanic (x := (ptr + BitVec.ofNat 64 bs.length, srcPtr, payload))
    (F := ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
             (cap.toNat - bs.length - payload.length)) ∗
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
    refine SepWPpLsCl.weaken_pre ?_ (hnext sm hvm hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_memcpy_erX (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

theorem encraw_call_memcpy_buf_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (sp0 v cap ptr srcPtr ret_pc : BitVec 64) (bs payload : List (BitVec 8))
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
    (hP : P = (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A.repAlloc cap ptr bs ∗ (srcPtr ↦ₛ payload)) ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecCopyDone A.repAlloc cap ptr bs payload ∗ (srcPtr ↦ₛ payload)) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hP' : P = (vecU8At A.repAlloc v cap ptr bs ∗ (srcPtr ↦ₛ payload) ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by
    rw [hP, vecU8At_eq_header_sep_buf]
    simp only [vecHeader, sepConj_assoc]
  refine encraw_call_memcpy_prealloc_placed_x hC sp0 v cap ptr srcPtr ret_pc bs payload
    hle hcap hptr hne hpc hrun hsp halign htr hlr hx0 hx1 hx2 hP' ?_
  intro sm hvm hpcm hrunm hspm htrm hcsm
  refine SepWPpLsCl.weaken_pre ?_ (hnext sm hvm hpcm hrunm hspm htrm hcsm)
  rw [vecCopyDone.eq_def]
  have hpure : (bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧
      ptr ≠ 0#64 ∧ payload ≠ []) = True :=
    eq_true ⟨hle, hcap, hptr, hne⟩
  rw [hpure, pure_true, emp_sepConj]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Pre-reserved `encode::<Chain>` (Block `12`) interface and call wrappers -/

/-- Pre-reserved (`0`-allocation, `VmPreserved`) contract for `encode::<Chain>` (Block `12`) at
`encodeChainStackX`. -/
def encodeChainPreallocSpecX' (A : RustAlloc) : Spec EncodeChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = BitVec.ofNat 64 x.tag ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.v ∧
      (x.tag = 6 ∨ x.tag = 7) ∧
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length ≤ x.cap.toNat ∧
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32⌝ ∗
      protoChainAt A x.gc x.a ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗
      stackAt s.sp encodeChainStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      protoChainAt A x.gc x.a ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ lenField x.tag (encChainMem x.gc)) ∗
      stackAt s0.sp encodeChainStackX

abbrev EncodeChainPreallocPlacedOkX' [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_12 H) (lsmpl.base 12)
    (withLsCodeLoaded lsmpl (encodeChainPreallocSpecX' A))

/-- Execute a pre-reserved `bl encode::<Chain>` (`lsmpl.base 12`) call inside `encode_raw` on
    `protoChainAt`, preserving `cap` and `ptr` with `VmPreserved s sm` and no `A.pool`. -/
theorem encraw_call_protoEncodeChain_prealloc_placed_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (hEC : EncodeChainPreallocPlacedOkX' A H)
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (htag : tag = 6 ∨ tag = 7)
    (hspare : bs.length + (lenField tag (encChainMem gc)).length ≤ cap.toNat)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
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
    (hP : P = (protoChainAt A gc a ∗ vecU8At A v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((protoChainAt A gc a ∗
          vecU8At A v cap ptr (bs ++ lenField tag (encChainMem gc)) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hcall : subroutine_ok (lsProg_14 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainPreallocSpecX' A)) :=
    ls_subroutine_ok_of_callee (callerProg := lsProg_14 H) hEC
  refine sepWPpLsCl_call_lscl_noPanic (x := EncodeChainGhost.mk tag a gc v cap ptr bs)
    (F := encRawSubRestX (sp0 - 80#64) encodeChainStackX ∗ F)
    hcall hpc hrun halign hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeChainX (sp0 - 80#64)] at hm
    simp only [encodeChainPreallocSpecX', hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, htag, hspare, hlen_lt⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeChainPreallocSpecX', hsp, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun ⟨htrm, hvm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpLsCl.weaken_pre ?_ (hnext sm hvm hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_encodeChainX (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

/-- Execute a pre-reserved `bl encode::<Chain>` (`lsmpl.base 12`) call inside `encode_raw` on
    `chainAt`, preserving `cap` and `ptr` with `VmPreserved s sm` and no `A.pool`. -/
theorem encraw_call_encodeChain_prealloc_placed_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (hEC : EncodeChainPreallocPlacedOkX' A H)
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (htag : tag = 6 ∨ tag = 7)
    (hspare : bs.length + (lenField tag (encChainMem gc)).length ≤ cap.toNat)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
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
    (hP : P = (chainAt A gc a ∗ vecU8At A v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((chainAt A gc a ∗
          vecU8At A v cap ptr (bs ++ lenField tag (encChainMem gc)) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hP' : P = (protoChainAt A gc a ∗ vecU8At A v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F) := by
    rw [hP, chainAt_eq_protoChainAt_er A gc a]; sep_ac_rfl
  refine encraw_call_protoEncodeChain_prealloc_placed_x hEC tag sp0 a v cap ptr ret_pc gc bs
    htag hspare hlen_lt hpc hrun hsp halign htr hlr hx0 hx1 hx2 hP' ?_
  intro sm hvm hpcm hrunm hspm htrm hcsm
  have hPostEq :
      ((protoChainAt A gc a ∗
        vecU8At A v cap ptr (bs ++ lenField tag (encChainMem gc)) ∗
        stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
        (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F)) =
      ((chainAt A gc a ∗
        vecU8At A v cap ptr (bs ++ lenField tag (encChainMem gc)) ∗
        stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F) := by
    rw [chainAt_eq_protoChainAt_er A gc a]; sep_ac_rfl
  rw [hPostEq]
  exact hnext sm hvm hpcm hrunm hspm htrm hcsm

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareBaseXBudget
