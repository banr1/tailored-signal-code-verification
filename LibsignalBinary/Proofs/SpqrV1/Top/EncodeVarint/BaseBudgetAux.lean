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
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BasePlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Prologue, Tail & `grow_one` Helper for `spqr::encode_varint` (`Block 326`)

Defines `SpqrVecPushBudgetInv` and proves the `<RawVec<u8>>::grow_one` call helper
(`lsmpl.base 619`), prologue (`+0..+44`), and shared final-byte writer (`+412..+460`)
for `spqr::encode_varint` (`Block 326`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BaseBudgetAux

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (GrowOneU8Env growOneU8BudgetSpec growOneU8Events growOneU8Events_eq_of_env)
open CryptoVerification
  (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap
  (vecHeader)
open CryptoVerification.LibsignalProtoCodec
  (encodeVarint)
open CryptoVerification.LibsignalSpqrV1
  (GrowOneCall MAX_VARINT_BYTES_LEN encodeVarintLoop newCapU8)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost VecReserveInv bv_len_add_one
   sepWPp_extract_vecU8Buf_le vecU8At_eq_header_sep_buf vecU8Buf
   vecU8Buf_eq_open_one vecU8Buf_snoc_eq)
open scoped CryptoVerification.LibsignalTripleRatchet.Prost
open scoped CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Top.EncodeVarint
  (SpqrEncVarintCalleeSavedPlaced encodeVarintLoop_10_eq newCapU8_bounds
   sp_sub_80_aligned spqr_encode_varint_eq
   stackAt_spqrEncodeVarint_eq vecU8Buf_eq_for_growOne withEncStepInvPlaced)
open CryptoVerification.SpqrV1.Top.Placed
  (blkPC_326 blkPl_326)
open scoped CryptoVerification.SpqrV1.Top.EncodeVarint
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
  (sepWPp_call_cs_placed_noPanic sepWPp_of_sepWP_cs_placed_vm sepWPp_of_sepWP_vm)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget
  (SpqrEncodeVarintEnv growOneU8ByteStep growOneU8BytesEvents
   spqrEncodeVarintEnv_events spqrEncodeVarintEvents spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlacedBudget
  (GrowOneU8StepOkExt)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `growOneU8ByteStep` / `growOneU8BytesEvents` / `SpqrVecPushBudgetInv` Algebra -/

theorem growOneU8ByteStep_of_lt {cap : BitVec 64} {len : Nat} (hlt : len < cap.toNat) :
    growOneU8ByteStep cap len = (cap, []) := by
  simp [growOneU8ByteStep, hlt]

theorem growOneU8ByteStep_of_eq {cap : BitVec 64} {len : Nat} (heq : cap.toNat = len) :
    growOneU8ByteStep cap len = (newCapU8 cap, growOneU8Events cap) := by
  unfold growOneU8ByteStep
  rw [← heq, ite_eq_right_iff.mpr fun hlt => False.elim (Nat.lt_irrefl _ hlt)]

theorem fitsEnv_growOneU8_of_fitsEvents {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} (x : GrowOneCall)
    (hf : FitsEvents M lim st (growOneU8Events x.cap)) :
    FitsEnv M lim st (GrowOneU8Env x) := by
  intro evs henv
  rw [growOneU8Events_eq_of_env henv]
  exact hf

/-- Combined capacity/pointer preservation and deterministic `growOneU8BytesEvents` budget-state
invariant across the unrolled byte stages of `spqr::encode_varint`. -/
structure SpqrVecPushBudgetInv (M : AllocCostModel) (lim : BudgetLimits)
    (x : EncodeVarintGhost) (st0 : M.σ)
    (curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (remLen : Nat) (curSt : M.σ) : Prop where
  res : VecReserveInv x.cap x.ptr curCap curPtr curBs
  events_eq :
    M.stepEvents (spqrEncodeVarintEvents x) st0 =
      M.stepEvents (growOneU8BytesEvents remLen curCap curBs.length) curSt
  fits : FitsEvents M lim curSt (growOneU8BytesEvents remLen curCap curBs.length)

theorem SpqrVecPushBudgetInv.init_loop {M : AllocCostModel} {lim : BudgetLimits}
    (x : EncodeVarintGhost) (st0 : M.σ)
    (hfits : FitsEnv M lim st0 (SpqrEncodeVarintEnv x)) :
    SpqrVecPushBudgetInv M lim x st0 x.cap x.ptr x.bs
      (encodeVarintLoop MAX_VARINT_BYTES_LEN x.val).length st0 where
  res := VecReserveInv.refl x.cap x.ptr x.bs
  events_eq := rfl
  fits := hfits (spqrEncodeVarintEvents x) rfl

theorem SpqrVecPushBudgetInv.init {M : AllocCostModel} {lim : BudgetLimits}
    (x : EncodeVarintGhost) (st0 : M.σ)
    (hfits : FitsEnv M lim st0 (SpqrEncodeVarintEnv x)) :
    SpqrVecPushBudgetInv M lim x st0 x.cap x.ptr x.bs (encodeVarint x.val).length st0 := by
  rw [← encodeVarintLoop_10_eq x.val]
  exact SpqrVecPushBudgetInv.init_loop x st0 hfits

theorem SpqrVecPushBudgetInv.of_rem_eq {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 : M.σ} {curCap curPtr : BitVec 64}
    {curBs : List (BitVec 8)} {n1 n2 : Nat} {curSt : M.σ}
    (hinv : SpqrVecPushBudgetInv M lim x st0 curCap curPtr curBs n1 curSt) (hn : n1 = n2) :
    SpqrVecPushBudgetInv M lim x st0 curCap curPtr curBs n2 curSt :=
  hn ▸ hinv

theorem SpqrVecPushBudgetInv.fits_growOne {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 : M.σ} {curCap curPtr : BitVec 64}
    {curBs : List (BitVec 8)} {rem : Nat} {curSt : M.σ}
    (hinv : SpqrVecPushBudgetInv M lim x st0 curCap curPtr curBs (rem + 1) curSt)
    (hcap_eq : curCap.toNat = curBs.length) :
    FitsEvents M lim curSt (growOneU8Events curCap) := by
  have hf := hinv.fits
  simp only [growOneU8BytesEvents, growOneU8ByteStep_of_eq hcap_eq,
    LibsignalBinary.Heap.fitsEvents_append] at hf
  exact hf.1

theorem SpqrVecPushBudgetInv.step {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 : M.σ}
    {curCap curPtr nextCap nextPtr : BitVec 64}
    {curBs : List (BitVec 8)} {byte : BitVec 8} {rem : Nat} {curSt : M.σ}
    (hinv : SpqrVecPushBudgetInv M lim x st0 curCap curPtr curBs (rem + 1) curSt)
    (hge : curCap.toNat ≤ nextCap.toNat)
    (hpres : curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr)
    (hcap_step : nextCap = (growOneU8ByteStep curCap curBs.length).1) :
    SpqrVecPushBudgetInv M lim x st0 nextCap nextPtr (curBs ++ [byte]) rem
      (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt) := by
  have hlen : (curBs ++ [byte]).length = curBs.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have hf := hinv.fits
  simp only [growOneU8BytesEvents, LibsignalBinary.Heap.fitsEvents_append] at hf
  refine ⟨hinv.res.step hge hpres, ?_, ?_⟩
  · rw [hinv.events_eq, growOneU8BytesEvents, AllocCostModel.stepEvents_append, hcap_step, hlen]
  · rw [hcap_step, hlen]
    exact hf.2

theorem grow_frame_budget_reassoc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (sm : State) (v newCap p' sp : BitVec 64)
    (curBs : List (BitVec 8)) (byte : BitVec 8) (F : SepProp) :
    ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗ vecU8Buf A.repAlloc newCap p' (curBs ++ [byte]) ∗
      A.pool lim st sm ∗ stackAt (sp - 80#64) extHookStack) ∗
      (((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [byte]).length) ∗ F) =
    ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [byte]).length) ∗
      vecU8Buf A.repAlloc newCap p' (curBs ++ [byte]) ∗ A.pool lim st sm ∗
      stackAt (sp - 80#64) extHookStack) ∗ F := by
  sep_ac_rfl

/-! ## 2. `<RawVec<u8>>::grow_one` Call Helper (`lsmpl.base 619`) -/

/-- Execute a `bl <RawVec<u8>>::grow_one` call at `s.pc = lsmpl.base 619`
when `curCap.toNat = curBs.length`. -/
theorem step_growOneU8_placed_call [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (abs : String → Option (State → State))
    {s0 s : State}
    (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 62)
    (hfits : FitsEvents M lim curSt (growOneU8Events curCap))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 619)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hcs_s : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x25 = s.readReg64 .x25 →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curBs.length < newCap.toNat →
      curCap.toNat ≤ newCap.toNat →
      newCap = newCapU8 curCap →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          vecU8Buf A.repAlloc newCap p' curBs ∗
          A.pool lim (M.stepEvents (growOneU8Events curCap) curSt) sm ∗
          stackAt (sp - 80#64) extHookStack) ∗ F)
        Q Qp) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_80_aligned halign
  obtain ⟨hmax_lt, hnew_toNat, hnew_ne, hnew_gt, hnew_ge⟩ := newCapU8_bounds hcap_eq hlen_lt
  have hfits_env : FitsEnv M lim curSt (GrowOneU8Env (GrowOneCall.mk v curCap curPtr curBs)) :=
    fitsEnv_growOneU8_of_fitsEvents (GrowOneCall.mk v curCap curPtr curBs) hfits
  refine sepWPp_call_cs_placed_noPanic (x := (GrowOneCall.mk v curCap curPtr curBs, curSt)) (F := F)
    hgrow hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, vecU8Buf_eq_for_growOne A.repAlloc curCap curPtr curBs hcap_eq] at hm
    have hm' : s.mem ⊨ ⌜curCap.toNat < 2 ^ 63 ∧ curPtr ≠ 0⌝ ∗
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          (if curCap = 0 then emp else A.live curPtr curBs.length 1 ∗ (curPtr ↦ₛ curBs)) ∗
          A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack) ∗ (F ∗ R')) := by
      convert hm using 1; sep_ac_rfl
    rw [satisfies_pure_sepConj] at hm'
    simp only [withEncStepInvPlaced, growOneU8BudgetSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs_s.2.2.2.2, ⟨hx0, hcap_eq.symm, hm'.1.2, hmax_lt, hfits_env⟩, ?_⟩
    convert hm'.2 using 1; sep_ac_rfl
  · intro _ _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withEncStepInvPlaced, growOneU8BudgetSpec, hsp, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun evs => ?_
    refine SepWPp.exists_elim fun p' => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htrm, henv⟩ => ?_
    have hevs : evs = growOneU8Events curCap := growOneU8Events_eq_of_env henv
    subst hevs
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hpost_eq :
        (⌜p' ≠ 0⌝ ∗ (v ↦₆₄ newCapU8 curCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (max (2 * curCap.toNat) 8) 1 ∗ (p' ↦ₛ curBs) ∗
          memRegion (p' + BitVec.ofNat 64 curBs.length) (max (2 * curCap.toNat) 8 - curCap.toNat)) ∗
          A.pool lim (M.stepEvents (growOneU8Events curCap) curSt) sm ∗
          stackAt (sp - 80#64) extHookStack ∗ F =
        (((v ↦₆₄ newCapU8 curCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          vecU8Buf A.repAlloc (newCapU8 curCap) p' curBs ∗
          A.pool lim (M.stepEvents (growOneU8Events curCap) curSt) sm ∗
          stackAt (sp - 80#64) extHookStack) ∗ F) := by
      unfold vecU8Buf
      simp only [hnew_ne, ↓reduceIte, hnew_toNat, hcap_eq]
      have hpure : (curBs.length ≤ max (2 * curBs.length) 8 ∧ max (2 * curBs.length) 8 < 2 ^ 63 ∧ p' ≠ 0) =
          (p' ≠ 0) := by
        apply propext; constructor
        · exact fun h => h.2.2
        · intro hp; exact ⟨by omega, by omega, hp⟩
      rw [hpure]
      sep_ac_rfl
    refine SepWPp.weaken_pre ?_ (hnext sm (newCapU8 curCap) p'
      hpcm hrunm hspm htrm'
      hcsm.1 hcsm.2.1 hcsm.2.2.1 hcsm.2.2.2.1 hcsm.2.2.2.2.1 hcsm.2.2.2.2.2.1 hcsm.2.2.2.2.2.2.1
      (hcs_s.trans (SpqrEncVarintCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
      hnew_gt hnew_ge rfl)
    exact Entails.of_eq (by rw [← hpost_eq]; sep_ac_rfl)

/-! ## 3. Prologue (`+0..+44`) and Shared Tail (`+412..+460`) -/

/-- Prologue (`+0x000..+0x028`, offsets `0..44`): allocates `0x50 = 80` byte stack frame,
saves `fp, lr, x25, x24, x23, x22, x21, x20, x19`, loads `origLen` (`x22`), sets `x19 = v`,
`x20 = val`, and branches on `val.ult 128#64` to `+44` or `+64`, preserving `A.pool lim curSt`. -/
theorem step_spqrEncVarint_placed_prologue [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (curSt : M.σ)
    (abs : String → Option (State → State))
    (val v cap ptr sp v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp - 80#64) ↦₆₄ v80) ∗ ((sp - 72#64) ↦₆₄ v72) ∗
      ((sp - 64#64) ↦₆₄ v64) ∗ ((sp - 56#64) ↦₆₄ v56) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗ A.pool lim curSt s) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if val.ult 128#64 then
        (blkPl_326).base + 44#64
      else
        (blkPl_326).base + 64#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x22 = BitVec.ofNat 64 bs.length →
      SpqrEncVarintCalleeSavedPlaced s sm →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((sp - 80#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 72#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 64#64) ↦₆₄ s.readReg64 .x25) ∗ ((sp - 56#64) ↦₆₄ v56) ∗
          ((sp - 48#64) ↦₆₄ s.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s.readReg64 .x23) ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .x21) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19) ∗
          A.pool lim curSt sm) ∗ F) Q Qp) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) ret s P Q Qp := by
  subst hP
  apply sepWPp_of_sepWP_cs_placed_vm
    (mid := if val.ult 128#64 then (blkPl_326).base + 44#64 else (blkPl_326).base + 64#64)
  by_vm_steps
    wp_steps
    refine SepWP.done (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
    rw [← A.pool_of_vmPreserved hvm]
    exact hnext _ (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])

/-- Shared final-byte writer and epilogue (`+0x19c..+0x1c8`, offsets `412..460`). -/
theorem step_spqrEncVarint_placed_tail [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State}
    (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (x : EncodeVarintGhost) (st0 curSt : M.σ)
    (lastVal curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : SpqrVecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (if curBs.length < curCap.toNat then
      (blkPl_326).base + 420#64
    else
      (blkPl_326).base + 412#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.v)
    (hx20 : (s.readReg64 .x20).setWidth 8 = lastVal.setWidth 8)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by sep_ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · simp only [hlt, ↓reduceIte] at hpc
    rcases hcs with ⟨h26, h27, h28, hvregs, _⟩
    have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
    have hstep_lt := growOneU8ByteStep_of_lt hlt
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_vm (mid := s0.readReg64 .lr)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm => ?_⟩
      apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (lastVal.setWidth 8) hlt,
        ← A.pool_of_vmPreserved hvm]
      have hinv' := hinv.step (byte := lastVal.setWidth 8)
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
      have hres' := hinv'.res
      rw [hbs] at hres'
      have ⟨hcap_le, hcap_pres⟩ := hres'.finish
      have hev_eq : curSt = M.stepEvents (spqrEncodeVarintEvents x) st0 := by
        have heq := hinv'.events_eq
        simp only [growOneU8BytesEvents, hstep_lt, AllocCostModel.stepEvents_nil] at heq
        exact heq.symm
      rw [hev_eq]
      refine ⟨?_, by simp only [arm64_norm, *], by encodedLen_cc_close⟩
      intro hm_f
      rw [hbs] at hm_f
      simp only [spqrEncodeVarintSpecX, spqr_encode_varint_eq, encodeVarintLoop_10_eq,
        vecU8At_eq_header_sep_buf, vecHeader, stackAt_spqrEncodeVarint_eq,
        sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x25, v56,
        s0.readReg64 .x24, s0.readReg64 .x23, s0.readReg64 .x22, s0.readReg64 .x21,
        s0.readReg64 .x20, s0.readReg64 .x19, spqrEncodeVarintEvents x, curCap, curPtr,
        by simp only [arm64_norm, *], ⟨hcap_le, hcap_pres⟩, ?_⟩
      rw [eq_true (spqrEncodeVarintEnv_events x), pure_true]
      simp only [emp_sepConj]
      convert hm_f using 1
      sep_ac_rfl
  · simp only [hlt, ↓reduceIte] at hpc
    have hcap_eq : curCap.toNat = curBs.length := by omega
    have hstep_eq := growOneU8ByteStep_of_eq hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 619)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_growOneU8_placed_call A lim abs hgrow x.v curCap curPtr s0.sp
        ((blkPl_326).base + 420#64) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hinv.fits_growOne hcap_eq)
        (F := ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
           ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m _ _ _ _ hcsm hnew_gt hnew_ge hnew_eq
      rcases hcsm with ⟨h26, h27, h28, hvregs, _⟩
      have hx19m' : sm.readReg64 .x19 = x.v := by simp only [arm64_norm, *]
      have hx20m' : (sm.readReg64 .x20).setWidth 8 = lastVal.setWidth 8 := by
        rw [hx20m]; simp only [arm64_norm, *]
      have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
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
        rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (lastVal.setWidth 8) hnew_gt,
          ← A.pool_of_vmPreserved hvm2]
        have hinv' := hinv.step (nextCap := newCap) (nextPtr := p') (byte := lastVal.setWidth 8)
          hnew_ge (fun h => absurd h hlt) (by rw [hstep_eq, hnew_eq])
        have hres' := hinv'.res
        rw [hbs] at hres'
        have ⟨hcap_le, hcap_pres⟩ := hres'.finish
        have hev_eq : M.stepEvents (growOneU8Events curCap) curSt =
            M.stepEvents (spqrEncodeVarintEvents x) st0 := by
          have heq := hinv'.events_eq
          simp only [growOneU8BytesEvents, hstep_eq, AllocCostModel.stepEvents_nil] at heq
          exact heq.symm
        rw [hev_eq]
        refine ⟨?_, by simp only [arm64_norm, *], by encodedLen_cc_close⟩
        intro hm_f
        rw [hbs] at hm_f
        simp only [spqrEncodeVarintSpecX, spqr_encode_varint_eq, encodeVarintLoop_10_eq,
          vecU8At_eq_header_sep_buf, vecHeader, stackAt_spqrEncodeVarint_eq,
          sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
          sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x25, v56,
          s0.readReg64 .x24, s0.readReg64 .x23, s0.readReg64 .x22, s0.readReg64 .x21,
          s0.readReg64 .x20, s0.readReg64 .x19, spqrEncodeVarintEvents x, newCap, p',
          by simp only [arm64_norm, *], ⟨hcap_le, hcap_pres⟩, ?_⟩
        rw [eq_true (spqrEncodeVarintEnv_events x), pure_true]
        simp only [emp_sepConj]
        convert hm_f using 1
        sep_ac_rfl

end LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BaseBudgetAux
