/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Base Step Lemmas for `prost::encoding::varint::encode_varint`

`VecPushBudgetInv` event algebra, stack-parametric `encodeVarintSpecOf`, and relocatable step
lemmas (prologue, epilogue, and continuation stages 1..3) for `encode_varint` (block 10).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
   rustAllocEvents rustReallocEvents)
open CryptoVerification
  (LibsignalPlacement LibsignalCodeLoaded libsignalSessionCode lsmpl
   ls_subroutine_ok_of_block withLsCodeLoaded blkPC_10 blkPl_10 blkPC_13 blkPl_13)
open CryptoVerification.RustHeap
  (vecU8At vecHeader)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall reserveCap tripleRatchetProgAtExt doReserveName doReserveStack doReserveStackX)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost encodeVarintName vecU8Buf vecU8At_eq_header_sep_buf
   vecU8Buf_eq_open_one vecU8Buf_snoc_eq
   cap_beq_len_false cap_eq_ofNat_len bv_len_add_one sepWPp_extract_vecU8Buf_le
   doReserve_fnAddr_eq sp_sub_48_aligned reserveCap_bounds varintContByte
   StepInv EncVarintCalleeSaved StepInvPlaced EncVarintCalleeSavedPlaced
   VecReserveInv stackAt_encodeVarint_gen_eq)
open scoped CryptoVerification.LibsignalTripleRatchet.Prost
open scoped CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  (zext64_trunc32_orr_mask)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveEvents DoReserveEnv fitsEnv_doReserve_iff doReserveSpec doReserveSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (pushByteStep pushBytesEvents encodeVarintEvents EncodeVarintEnv
   encodeVarintEnv_events encodeVarintSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `pushByteStep`, `pushBytesEvents`, and `VecPushBudgetInv` algebra -/

theorem pushByteStep_of_lt {cap len : Nat} (hlt : len < cap) :
    pushByteStep cap len = (cap, []) := by
  simp [pushByteStep, hlt]

theorem pushByteStep_of_eq (v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hcap_eq : curCap.toNat = curBs.length) :
    pushByteStep curCap.toNat curBs.length =
      (reserveCap curBs.length curBs.length 1,
       doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
  unfold pushByteStep doReserveEvents
  rw [hcap_eq, ite_eq_right_iff.mpr fun hlt => False.elim (Nat.lt_irrefl _ hlt)]
  dsimp only
  congr 1
  by_cases h0 : curCap = 0#64
  · have h0n : curBs.length = 0 := by rw [← hcap_eq, h0]; rfl
    simp [h0, h0n]
  · have h0n : curBs.length ≠ 0 := by
      intro hlen0
      exact h0 (BitVec.eq_of_toNat_eq (hcap_eq.trans hlen0))
    simp [h0, h0n]

/-- Combined capacity/pointer preservation and deterministic `pushBytesEvents` budget-state
invariant across the unrolled byte stages of `encode_varint`. -/
structure VecPushBudgetInv (M : AllocCostModel) (lim : BudgetLimits)
    (x : EncodeVarintGhost) (st0 : M.σ)
    (curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (remLen : Nat) (curSt : M.σ) : Prop where
  res : VecReserveInv x.cap x.ptr curCap curPtr curBs
  events_eq :
    M.stepEvents (encodeVarintEvents x) st0 =
      M.stepEvents (pushBytesEvents remLen curCap.toNat curBs.length) curSt
  fits : FitsEvents M lim curSt (pushBytesEvents remLen curCap.toNat curBs.length)

theorem VecPushBudgetInv.init {M : AllocCostModel} {lim : BudgetLimits}
    (x : EncodeVarintGhost) (st0 : M.σ)
    (hfits : FitsEnv M lim st0 (EncodeVarintEnv x)) :
    VecPushBudgetInv M lim x st0 x.cap x.ptr x.bs (encodeVarint x.val).length st0 where
  res := VecReserveInv.refl x.cap x.ptr x.bs
  events_eq := rfl
  fits := FitsEnv.eq_iff.mp hfits

theorem VecPushBudgetInv.of_rem_eq {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 : M.σ} {curCap curPtr : BitVec 64}
    {curBs : List (BitVec 8)} {n1 n2 : Nat} {curSt : M.σ}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs n1 curSt) (hn : n1 = n2) :
    VecPushBudgetInv M lim x st0 curCap curPtr curBs n2 curSt :=
  hn ▸ hinv

theorem VecPushBudgetInv.fits_reserve {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 : M.σ} {curCap curPtr : BitVec 64}
    {curBs : List (BitVec 8)} {rem : Nat} {curSt : M.σ}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs (rem + 1) curSt)
    (v : BitVec 64) (hcap_eq : curCap.toNat = curBs.length) :
    FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
  have hf := hinv.fits
  simp only [pushBytesEvents, pushByteStep_of_eq v curCap curPtr curBs hcap_eq,
    LibsignalBinary.Heap.fitsEvents_append] at hf
  exact hf.1

theorem VecPushBudgetInv.step {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 : M.σ}
    {curCap curPtr nextCap nextPtr : BitVec 64}
    {curBs : List (BitVec 8)} {byte : BitVec 8} {rem : Nat} {curSt : M.σ}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs (rem + 1) curSt)
    (hge : curCap.toNat ≤ nextCap.toNat)
    (hpres : curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr)
    (hcap_step : nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1) :
    VecPushBudgetInv M lim x st0 nextCap nextPtr (curBs ++ [byte]) rem
      (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) := by
  have hlen : (curBs ++ [byte]).length = curBs.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have hf := hinv.fits
  simp only [pushBytesEvents, LibsignalBinary.Heap.fitsEvents_append] at hf
  refine ⟨hinv.res.step hge hpres, ?_, ?_⟩
  · rw [hinv.events_eq, pushBytesEvents, AllocCostModel.stepEvents_append, hcap_step, hlen]
  · rw [hcap_step, hlen]
    exact hf.2

/-! ## `VmPreserved` and `StepInv` `SepWPp` steppers -/

theorem sepWPp_of_sepWP_cs_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (VmPreserved s sm → StepInv s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s Pre Q Qp := by
  refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.of_sepWP_cs (mid := mid) ?_
  refine SepWP.mono h ?_
  intro sm Pm _ _ ⟨hvm, hnext⟩ hinv
  exact hnext hvm hinv

theorem sepWPp_of_sepWP_cs_placed_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (VmPreserved s sm → StepInvPlaced s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s Pre Q Qp := by
  refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.of_sepWP_cs_placed (mid := mid) ?_
  refine SepWP.mono h ?_
  intro sm Pm _ _ ⟨hvm, hnext⟩ hinv
  exact hnext hvm hinv

theorem sepWPp_of_sepWP_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (VmPreserved s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s Pre Q Qp := by
  refine SepWPp.of_sepWP (mid := mid) ?_
  refine SepWP.mono h ?_
  intro sm Pm _ _ ⟨hvm, hnext⟩
  exact hnext hvm

theorem sepWPp_call_cs_noPanic {α : Type} {prog : Program} {entry ret ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R, s.mem ⊨ P ∗ R → s.mem ⊨ spec.pre x s ∗ (F ∗ R))
    (hexit : ∀ sf code R, sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R) → False)
    (hpanic : ∀ sf R, sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R) → False)
    (hoom : ∀ sf R, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R) → False)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running → sm.sp = s.sp →
      CalleeSavedPreserved s sm → StepInv s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpan_mem⟩ | ⟨code, hex, hex_mem⟩ | ⟨hoom_s, hoom_mem⟩
  · rw [hlr] at hpcm
    rw [← sepConj_assoc] at hpost
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (StepInv.of_steps hsteps) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (hpanic sm (F ∗ R) hpan hpan_mem).elim
  · exact (hexit sm code (F ∗ R) hex hex_mem).elim
  · exact (hoom sm (F ∗ R) hoom_s hoom_mem).elim

theorem sepWPp_call_cs_placed_noPanic {α : Type} {prog : Program} {entry ret ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R, s.mem ⊨ P ∗ R → s.mem ⊨ spec.pre x s ∗ (F ∗ R))
    (hexit : ∀ sf code R, sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R) → False)
    (hpanic : ∀ sf R, sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R) → False)
    (hoom : ∀ sf R, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R) → False)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running → sm.sp = s.sp →
      CalleeSavedPreserved s sm → StepInvPlaced s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpan_mem⟩ | ⟨code, hex, hex_mem⟩ | ⟨hoom_s, hoom_mem⟩
  · rw [hlr] at hpcm
    rw [← sepConj_assoc] at hpost
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (StepInvPlaced.of_steps hsteps) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (hpanic sm (F ∗ R) hpan hpan_mem).elim
  · exact (hexit sm code (F ∗ R) hex hex_mem).elim
  · exact (hoom sm (F ∗ R) hoom_s hoom_mem).elim

/-! ## Stack-parametric `doReserveSpecWith*` and `encodeVarintSpecOf` -/

def doReserveSpecWith (resStack : Nat) (s0 : State) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜EncVarintCalleeSaved s0 s ∧
      s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧
      s.readReg64 .x4 = 1#64 ∧
      reserveCap x.cap.toNat x.bs.length x.additional + 1 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (DoReserveEnv x)⌝ ∗
    vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp resStack
  post := fun (x, st) s0' sf =>
    ⌜sf.trace = s0'.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      vecU8At A.repAlloc x.v (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)) p' x.bs) ∗
    A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗ stackAt s0'.sp resStack

def doReserveSpecWithPlaced (resStack : Nat) (s0 : State) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜EncVarintCalleeSavedPlaced s0 s ∧
      s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧
      s.readReg64 .x4 = 1#64 ∧
      reserveCap x.cap.toNat x.bs.length x.additional + 1 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (DoReserveEnv x)⌝ ∗
    vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp resStack
  post := fun (x, st) s0' sf =>
    ⌜sf.trace = s0'.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      vecU8At A.repAlloc x.v (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)) p' x.bs) ∗
    A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗ stackAt s0'.sp resStack

theorem doReserve_with_of_ok (b : BitVec 64) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (abs : String → Option (State → State)) (s0 : State)
    (h : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserveName) (doReserveSpec M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserveName)
      (doReserveSpecWith doReserveStack s0 A lim) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWith, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine (h.to_outcome x R s hpc hrun ?_ hsp).mono_outcome fun _ hout => hout
  simp only [doReserveSpec, LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre.1.2, hpre.2⟩

theorem doReserve_with_placed_of_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim))) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (lsmpl.base 13)
      (doReserveSpecWithPlaced doReserveStack s0 A lim) := by
  have h14 := ls_subroutine_ok_of_block (callerProg := (blkPC_10).rebase (blkPl_10).base H) h
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWithPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine (h14.to_outcome x R s hpc hrun ?_ hsp).mono_outcome fun _ hout => hout
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcl0.of_keepsFrozen hpre.1.1.2.2.2.2.2.2.2.2.2.2, ?_⟩
  simp only [doReserveSpec, LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre.1.2, hpre.2⟩

theorem doReserve_with_placed_of_ok_x [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim))) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (lsmpl.base 13)
      (doReserveSpecWithPlaced doReserveStackX s0 A lim) := by
  have h14 := ls_subroutine_ok_of_block (callerProg := (blkPC_10).rebase (blkPl_10).base H) h
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWithPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine (h14.to_outcome x R s hpc hrun ?_ hsp).mono_outcome fun _ hout => hout
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcl0.of_keepsFrozen hpre.1.1.2.2.2.2.2.2.2.2.2.2, ?_⟩
  simp only [doReserveSpecX, LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre.1.2, hpre.2⟩

def encodeVarintSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (EncodeVarintGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (EncodeVarintEnv x)⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp (0x30 + resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      (∃∗ evs : List AllocEvent, ⌜EncodeVarintEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (0x30 + resStack)

/-! ## `do_reserve_and_handle` call helpers -/

theorem step_doReserve_call_gen {prog : Program} {resTarget : BitVec 64} {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {s0 s : State}
    (hdoReserve : subroutine_ok prog resTarget (doReserveSpecWith resStack s0 A lim))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 62)
    (hfits : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = resTarget) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 1#64) (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs_s : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      EncVarintCalleeSaved s0 sm →
      curBs.length < newCap.toNat → curCap.toNat ≤ newCap.toNat →
      newCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp prog ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc newCap p' curBs ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  obtain ⟨hres_bound, hnew_gt, hnew_ge⟩ := reserveCap_bounds hlen_lt
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  have hstep_eq := pushByteStep_of_eq v curCap curPtr curBs hcap_eq
  refine sepWPp_call_cs_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs 1, curSt)) (F := F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [doReserveSpecWith, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hcs_s, hx0, hx1_toNat, hx2_toNat, hx3, hx4, ?_, (fitsEnv_doReserve_iff _).mpr hfits⟩, ?_⟩
    · rw [hcap_eq]; exact hres_bound
    · convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [doReserveSpecWith, vecU8At_eq_header_sep_buf, vecHeader, hsp, hcap_eq,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hnew_ge' : curCap.toNat ≤ (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)).toNat := by
      rw [hcap_eq]; exact hnew_ge
    have hnew_toNat :
        (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)).toNat =
          (pushByteStep curCap.toNat curBs.length).1 := by
      rw [hstep_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hstep_evs : (pushByteStep curCap.toNat curBs.length).2 =
        doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1) := by
      rw [hstep_eq]
    rw [← hstep_evs]
    refine SepWPp.weaken_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p'
      hpcm hrunm hspm htrm' hcsm.1 hcsm.2.1
      (hcs_s.trans (EncVarintCalleeSaved.of_calleeSavedPreserved hcsm hinv_call))
      hnew_gt hnew_ge' hnew_toNat)
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_doReserve_call {resStack : Nat} (b : BitVec 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (abs : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserveName) (doReserveSpecWith resStack s0 A lim))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 62)
    (hfits : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]"))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 1#64) (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs_s : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      EncVarintCalleeSaved s0 sm →
      curBs.length < newCap.toNat → curCap.toNat ≤ newCap.toNat →
      newCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc newCap p' curBs ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  rw [doReserve_fnAddr_eq] at hpc
  exact step_doReserve_call_gen A lim hdoReserve v curCap curPtr sp ret_pc curBs curSt
    hcap_eq hlen_lt hfits hpc hrun hsp halign htr hlr hx0 hx1 hx2 hx3 hx4 hcs_s hP hnext

theorem step_doReserve_call_gen_placed {prog : Program} {resTarget : BitVec 64} {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {s0 s : State}
    (hdoReserve : subroutine_ok prog resTarget (doReserveSpecWithPlaced resStack s0 A lim))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 62)
    (hfits : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = resTarget) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 1#64) (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs_s : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      EncVarintCalleeSavedPlaced s0 sm →
      curBs.length < newCap.toNat → curCap.toNat ≤ newCap.toNat →
      newCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp prog ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc newCap p' curBs ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  obtain ⟨hres_bound, hnew_gt, hnew_ge⟩ := reserveCap_bounds hlen_lt
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  have hstep_eq := pushByteStep_of_eq v curCap curPtr curBs hcap_eq
  refine sepWPp_call_cs_placed_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs 1, curSt)) (F := F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [doReserveSpecWithPlaced, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hcs_s, hx0, hx1_toNat, hx2_toNat, hx3, hx4, ?_, (fitsEnv_doReserve_iff _).mpr hfits⟩, ?_⟩
    · rw [hcap_eq]; exact hres_bound
    · convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [doReserveSpecWithPlaced, vecU8At_eq_header_sep_buf, vecHeader, hsp, hcap_eq,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hnew_ge' : curCap.toNat ≤ (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)).toNat := by
      rw [hcap_eq]; exact hnew_ge
    have hnew_toNat :
        (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)).toNat =
          (pushByteStep curCap.toNat curBs.length).1 := by
      rw [hstep_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hstep_evs : (pushByteStep curCap.toNat curBs.length).2 =
        doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1) := by
      rw [hstep_eq]
    rw [← hstep_evs]
    refine SepWPp.weaken_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p'
      hpcm hrunm hspm htrm' hcsm.1 hcsm.2.1
      (hcs_s.trans (EncVarintCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
      hnew_gt hnew_ge' hnew_toNat)
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_doReserve_call_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced resStack s0 A lim))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 62)
    (hfits : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 1#64) (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs_s : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      EncVarintCalleeSavedPlaced s0 sm →
      curBs.length < newCap.toNat → curCap.toNat ≤ newCap.toNat →
      newCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc newCap p' curBs ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) ret s P Q Qp :=
  step_doReserve_call_gen_placed A lim hdoReserve v curCap curPtr sp ret_pc curBs curSt
    hcap_eq hlen_lt hfits hpc hrun hsp halign htr hlr hx0 hx1 hx2 hx3 hx4 hcs_s hP hnext

/-! ## Placed prologue and epilogue lemmas (block 10) -/

theorem final_frame_reassoc (h1 h2 h3 buf pool stk s1 s2 s3 s4 s5 s6 F : SepProp) :
    (h1 ∗ h2 ∗ h3 ∗ buf ∗ pool ∗ stk) ∗ (s1 ∗ s2 ∗ s3 ∗ s4 ∗ s5 ∗ s6 ∗ F) =
      (h1 ∗ h2 ∗ h3 ∗ buf ∗ s1 ∗ s2 ∗ s3 ∗ s4 ∗ s5 ∗ s6 ∗ pool ∗ stk) ∗ F := by
  sep_ac_rfl

theorem stage_frame_reassoc (h1 h2 h3 buf pool stk s1 s2 F : SepProp) :
    (h1 ∗ h2 ∗ h3 ∗ buf ∗ pool ∗ stk) ∗ (s1 ∗ s2 ∗ F) =
      (h1 ∗ h2 ∗ h3 ∗ buf ∗ s1 ∗ s2 ∗ pool ∗ stk) ∗ F := by
  sep_ac_rfl

theorem step_encVarint_prologue_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (val v cap ptr sp v48 v40 v32 v24 v16 v8 : BitVec 64) (bs : List (BitVec 8)) (st0 : M.σ)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_10).base) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗ A.pool lim st0 s) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if val.ult 128#64 then (blkPl_10).base + 512#64 else (blkPl_10).base + 32#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s.trace →
      sm.readReg64 .x0 = val → sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 bs.length → sm.readReg64 .x9 = cap →
      EncVarintCalleeSavedPlaced s sm →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19) ∗
          A.pool lim st0 sm) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) ret s P Q Qp := by
  subst hP
  apply sepWPp_of_sepWP_cs_placed_vm
    (mid := if val.ult 128#64 then (blkPl_10).base + bv% (512) else (blkPl_10).base + bv% (32))
  by_vm_steps
    wp_steps
    refine SepWP.done (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
    rw [← A.pool_of_vmPreserved hvm]
    exact hnext _ (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self])

theorem step_encVarint_final_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced resStack s0 A lim))
    (lastVal v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_10).base + 512#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = lastVal) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sf : State) (cap' ptr' : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → curCap.toNat ≤ cap'.toNat →
      (curBs.length < curCap.toNat → cap' = curCap ∧ ptr' = curPtr) →
      cap'.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      Q sf (((v ↦₆₄ cap') ∗ ((v + 8#64) ↦₆₄ ptr') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
        vecU8Buf A.repAlloc cap' ptr' (curBs ++ [lastVal.setWidth 8]) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sf ∗
        stackAt (sp - 48#64) resStack) ∗ F)) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs, _⟩
    have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
    have hstep_lt := pushByteStep_of_lt hlt
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_vm (mid := s0.readReg64 .lr)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm => ?_⟩
      apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (BitVec.zeroExtend 8 lastVal) hlt,
        ← A.pool_of_vmPreserved hvm]
      have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
        rw [hstep_lt]; rfl
      rw [← hst_eq]
      exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by encodedLen_cc_close) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
        (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve_call_placed A lim H hdoReserve v curCap curPtr sp
        ((blkPl_10).base + bv% (584)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq)
        (F := ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      rcases hcsm with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs, _⟩
      have hx19m' : sm.readReg64 .x19 = lastVal := by simp only [arm64_norm, *]
      have hx20m' : sm.readReg64 .x20 = v := by simp only [arm64_norm, *]
      have hbeq := cap_beq_len_false hnew_gt
      have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      apply sepWPp_of_sepWP_vm (mid := s0.readReg64 .lr)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm2 => ?_⟩
        apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (BitVec.zeroExtend 8 lastVal) hnew_gt,
          ← A.pool_of_vmPreserved hvm2, final_frame_reassoc]
        exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by encodedLen_cc_close) hnew_ge (fun h => absurd h hlt) hcap_step

theorem step_encVarint_exit_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced resStack s0 A lim))
    (x : EncodeVarintGhost) (st0 curSt : M.σ)
    (lastVal curCap curPtr v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_10).base + 512#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 48#64) (halign : s0.sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = lastVal) (hx1 : s.readReg64 .x1 = x.v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 48#64) resStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpecOf resStack A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  refine step_encVarint_final_placed (F := emp) A lim H hdoReserve lastVal x.v curCap curPtr s0.sp v48 v40
    curBs curSt hlen_lt (fun hcap_eq => hinv.fits_reserve x.v hcap_eq)
    hpc hrun hsp halign htr hx0 hx1 hx8 hx9 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro sf cap' ptr' hpcf hrunf hspf htrf hcsf hge hpres hcap_step
  have hinv' := hinv.step (byte := lastVal.setWidth 8) hge hpres hcap_step
  have hres' := hinv'.res
  rw [hbs] at hres'
  have ⟨hcap_le, hcap_pres⟩ := hres'.finish
  have hev_eq : M.stepEvents (encodeVarintEvents x) st0 =
      M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt := by
    simpa [pushBytesEvents] using hinv'.events_eq
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f
  rw [sepConj_emp, hbs, ← hev_eq] at hm_f
  simp only [encodeVarintSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v48, v40, s0.readReg64 .fp, s0.readReg64 .lr,
    s0.readReg64 .x20, s0.readReg64 .x19, encodeVarintEvents x, cap', ptr',
    htrf, ⟨hcap_le, hcap_pres⟩, ?_⟩
  rw [eq_true (encodeVarintEnv_events x), pure_true]
  convert hm_f using 1
  sep_ac_rfl

/-! ## Placed continuation-byte stages 1..3 (block 10) -/

theorem step_encVarint_s1_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced resStack s0 A lim))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_10).base + 32#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 7).ult 128#64 then (blkPl_10).base + 512#64 else (blkPl_10).base + 136#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 7).ult 128#64 then val >>> 7 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte val]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr →
      EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte val]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 7).ult 128#64 = true ∨ (val >>> 7).ult 128#64 = false := by
    cases (val >>> 7).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs (varintContByte val)
    have hstep_lt := pushByteStep_of_lt hlt
    have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte val) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (136))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte val) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve_call_placed A lim H hdoReserve v curCap curPtr sp
        ((blkPl_10).base + bv% (104)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq)
        (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      have hlen1 := bv_len_add_one curBs (varintContByte val)
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step' => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte val) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (136))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step' => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte val) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step

theorem step_encVarint_s2_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced resStack s0 A lim))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_10).base + 136#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 14).ult 128#64 then (blkPl_10).base + 512#64 else (blkPl_10).base + 252#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 14).ult 128#64 then val >>> 14 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr →
      EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 7)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 14).ult 128#64 = true ∨ (val >>> 14).ult 128#64 = false := by
    cases (val >>> 14).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 7))
    have hstep_lt := pushByteStep_of_lt hlt
    have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 7)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (252))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 7)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve_call_placed A lim H hdoReserve v curCap curPtr sp
        ((blkPl_10).base + bv% (216)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq)
        (F := ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
      have hx20m' : sm.readReg64 .x20 =
          BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 val) >>> 7)) |||
            4294967168#64 := by
        simp only [arm64_norm, *]; simp
      have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 7))
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step' => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 7)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v48 val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (252))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step' => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 7)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v48 val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step

theorem step_encVarint_s3_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced resStack s0 A lim))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_10).base + 252#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 21).ult 128#64 then (blkPl_10).base + 512#64 else (blkPl_10).base + 360#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 21).ult 128#64 then val >>> 21 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x12 = val >>> 28 →
      EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 14)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 21).ult 128#64 = true ∨ (val >>> 21).ult 128#64 = false := by
    cases (val >>> 21).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 14))
    have hstep_lt := pushByteStep_of_lt hlt
    have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 14)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (360))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 14)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve_call_placed A lim H hdoReserve v curCap curPtr sp
        ((blkPl_10).base + bv% (328)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq)
        (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      have hx19m' : sm.readReg64 .x19 =
          BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 val) >>> 14)) |||
            4294967168#64 := by
        simp only [arm64_norm, *]; simp
      have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 14))
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step' => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 14)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (360))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step' => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 14)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step

end LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
