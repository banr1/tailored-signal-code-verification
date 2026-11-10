/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeated1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeatedCommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2PlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Verification of Deterministic `encode_varint [local#4]` & `encode_repeated [local#3]`

Proves deterministic-capacity `encode_varint [local#4]` (Block `451`) and budget-threaded
`encode_repeated::<Vec<u8>, Vec<u8>> [local#3]` (Block `448`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeated1PlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   VmPreserved allocMemcpyVmSpec fitsEvents_append rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement LibsignalHooks lsmpl lsρ withLsCodeLoaded
   ls_subroutine_ok_of_block)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (setup_x24_eq_59)
open CryptoVerification.Cli.SpqrV1.Varint.Placed
  (blkPC_448 blkPl_448 lsProg_448 blkPC_451 blkPl_451 lsProg_451)
open CryptoVerification.RustHeap (vecU8At vecHeader)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeVarintAux encodeBytesField)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall reserveCap doReserveStack doReserveStackX)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost vecU8Buf vecU8At_eq_header_sep_buf
   varintContByte EncVarintCalleeSavedPlaced stackAt_encodeVarint_gen_eq
   encodeVarintAux_of_ult encodeVarintAux_of_not_ult encodeVarint_exit_bs
   encodeVarint_step_bs shr63_ult_128)
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm (ushr_ushr_7)
open scoped CryptoVerification.LibsignalTripleRatchet.Prost
open scoped CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Varint
  (EncodeRepeatedGhost encodeRepeatedStackOf repeatedBytesElemAt repeatedBytesSliceAt
   repeatedBytesSliceAt_cons repeatedBytesSliceAt_nil
   encodeRepeatedBytes encodeRepeatedBytes_cons encodeRepeatedBytes_nil
   encodeBytesField_some_eq encodeBytesField_some_length encodeKey_lengthDelimited_eq
   encodeVarint_length_bounds stage_len_lt_of_step stage_len_lt_of_exit encodeVarint_exit_bs_s9
   stackAt_encodeRepeated setup_x20_eq setup_x24_eq len_beq_zero_false
   EncRepeatedCalleeSavedPlaced withEncRepeatedCSPlaced subroutine_ok_withEncRepeatedCS_placed)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (pushByteStep pushBytesEvents encodeVarintEvents encodeVarintEnv_events)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
  (VecPushBudgetInv sepWPp_of_sepWP_cs_placed_vm sepWPp_of_sepWP_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (reserveStep pushBytesStep pushBytesStep_snd_eq encodeRepeatedElemStep encodeRepeatedStep)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserve2SpecOf doReserve2SpecWithPlaced doReserve2_with_placed_of_ok)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlacedBudget
  (do_reserve2_placed_ok do_reserve2_placed_ok_x
   step_encVarint2_prologue_placed step_encVarint2_final_placed
   step_encVarint2_s1_placed step_encVarint2_s2_placed step_encVarint2_s3_placed
   step_encVarint2_s9_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2PlacedBudget
  (step_encVarint2_s4_placed step_encVarint2_s5_placed step_encVarint2_s6_placed
   step_encVarint2_s7_placed step_encVarint2_s8_placed)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (encodeRepeatedEvents EncodeRepeatedEnv encodeRepeatedEnv_events
   encodeVarintDetSpecOf encodeVarintDetSpec encodeVarintDetSpecX
   encodeRepeatedSpecOf encodeRepeatedSpec encodeRepeatedSpecX
   encodeRepeated59DetSpecOf)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeatedCommonPlacedBudget
  (EncodeRepeated1.step_iter_placed EncodeRepeated1.step_latch_zero_placed
   EncodeRepeated1.step_latch_succ_59_placed EncodeRepeated1.step_latch_succ_placed)

attribute [local irreducible] Program.externAt? Program.fnAddr
  encodeVarint encodeBytesField encodeRepeatedBytes
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Deterministic-Capacity `encode_varint::<Vec<u8>> [local#4]` (Block `451` → Block `460`) -/

/-- Single-byte `RawVec<u8>::grow_one` / deterministic capacity invariant. -/
def VecCapStepInv2 (x : EncodeVarintGhost) (curCap : BitVec 64)
    (curBs : List (BitVec 8)) (remLen : Nat) : Prop :=
  (pushBytesStep (encodeVarint x.val).length x.cap.toNat x.bs.length).1 =
    (pushBytesStep remLen curCap.toNat curBs.length).1
private theorem VecCapStepInv2.init (x : EncodeVarintGhost) :
    VecCapStepInv2 x x.cap x.bs (encodeVarint x.val).length := rfl
private theorem VecCapStepInv2.of_rem_eq {x : EncodeVarintGhost} {curCap : BitVec 64}
    {curBs : List (BitVec 8)} {n1 n2 : Nat}
    (h : VecCapStepInv2 x curCap curBs n1) (hn : n1 = n2) :
    VecCapStepInv2 x curCap curBs n2 := hn ▸ h
private theorem VecCapStepInv2.step {x : EncodeVarintGhost} {curCap nextCap : BitVec 64}
    {curBs : List (BitVec 8)} {byte : BitVec 8} {rem : Nat}
    (h : VecCapStepInv2 x curCap curBs (rem + 1))
    (hcap_step : nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1) :
    VecCapStepInv2 x nextCap (curBs ++ [byte]) rem := by
  have hlen : (curBs ++ [byte]).length = curBs.length + 1 := by
    rw [List.length_append, List.length_singleton]
  unfold VecCapStepInv2 at h ⊢
  rw [h, pushBytesStep, hcap_step, hlen]

private theorem vecPushBudgetInv2_exit {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 curSt : M.σ} {curCap curPtr : BitVec 64}
    {curBs : List (BitVec 8)} {fuel : Nat} {v : BitVec 64}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs
      (encodeVarintAux (fuel + 1) v).length curSt) (h : v.ult 128#64 = true) :
    VecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt :=
  hinv.of_rem_eq (by rw [encodeVarintAux_of_ult h]; rfl)

private theorem vecCapStepInv2_exit {x : EncodeVarintGhost} {curCap : BitVec 64}
    {curBs : List (BitVec 8)} {fuel : Nat} {v : BitVec 64}
    (hcap : VecCapStepInv2 x curCap curBs (encodeVarintAux (fuel + 1) v).length)
    (h : v.ult 128#64 = true) : VecCapStepInv2 x curCap curBs 1 :=
  hcap.of_rem_eq (by rw [encodeVarintAux_of_ult h]; rfl)

private theorem vecPushBudgetInv2_fits_reserve {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 curSt : M.σ} {curCap curPtr : BitVec 64}
    {curBs : List (BitVec 8)} {fuel : Nat} {v : BitVec 64}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs
      (encodeVarintAux (fuel + 1) v).length curSt)
    (h : v.ult 128#64 = false) (hcap_eq : curCap.toNat = curBs.length) :
    FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk x.v curCap curPtr curBs 1)) :=
  (hinv.of_rem_eq (by rw [encodeVarintAux_of_not_ult h]; rfl)).fits_reserve x.v hcap_eq

private theorem vecPushBudgetInv2_step {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 curSt : M.σ} {curCap curPtr nextCap nextPtr : BitVec 64}
    {curBs : List (BitVec 8)} {byte : BitVec 8} {fuel : Nat} {v nextV : BitVec 64}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs
      (encodeVarintAux (fuel + 1) v).length curSt)
    (h : v.ult 128#64 = false) (hshift : v >>> 7 = nextV)
    (hge : curCap.toNat ≤ nextCap.toNat)
    (hpres : curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr)
    (hcap_step : nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1) :
    VecPushBudgetInv M lim x st0 nextCap nextPtr (curBs ++ [byte])
      (encodeVarintAux fuel nextV).length
      (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) :=
  (hinv.of_rem_eq (by rw [encodeVarintAux_of_not_ult h, hshift]; rfl)).step hge hpres hcap_step

private theorem vecCapStepInv2_step {x : EncodeVarintGhost}
    {curCap nextCap : BitVec 64} {curBs : List (BitVec 8)} {byte : BitVec 8}
    {fuel : Nat} {v nextV : BitVec 64}
    (hcap : VecCapStepInv2 x curCap curBs (encodeVarintAux (fuel + 1) v).length)
    (h : v.ult 128#64 = false) (hshift : v >>> 7 = nextV)
    (hcap_step : nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1) :
    VecCapStepInv2 x nextCap (curBs ++ [byte]) (encodeVarintAux fuel nextV).length :=
  (hcap.of_rem_eq (by rw [encodeVarintAux_of_not_ult h, hshift]; rfl)).step hcap_step

/-- Deterministic-capacity exit lemma proving `(encodeVarintDetSpecOf resStack A lim).post`
for `encode_varint [local#4]` (Block `451` → Block `460`). -/
theorem step_encVarint2_det_exit_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A lim))
    (x : EncodeVarintGhost) (st0 curSt : M.σ)
    (lastVal curCap curPtr v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt)
    (hcap_inv : VecCapStepInv2 x curCap curBs 1)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base + 868#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 48#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = lastVal) (hx1 : s.readReg64 .x1 = x.v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 48#64) resStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (lsProg_451 H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintDetSpecOf resStack A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) Qp := by
  refine step_encVarint2_final_placed (F := emp) A lim H hdoReserve lastVal x.v curCap curPtr s0.sp v48 v40
    curBs curSt hlen_lt (fun hcap_eq => hinv.fits_reserve x.v hcap_eq)
    hpc hrun hsp halign htr hx0 hx1 hx8 hx9 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro sf cap' ptr' hpcf hrunf hspf htrf hcsf hge hpres hcap_step
  have hinv' := hinv.step (byte := lastVal.setWidth 8) hge hpres hcap_step
  have hcap_inv' := hcap_inv.step (byte := lastVal.setWidth 8) hcap_step
  have hcap_det : cap'.toNat = (pushBytesStep (encodeVarint x.val).length x.cap.toNat x.bs.length).1 := by
    simpa [VecCapStepInv2, pushBytesStep] using hcap_inv'.symm
  have hres' := hinv'.res; rw [hbs] at hres'; have ⟨hcap_le, hcap_pres⟩ := hres'.finish
  have hev_eq : M.stepEvents (encodeVarintEvents x) st0 =
      M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt := by
    simpa [pushBytesEvents] using hinv'.events_eq
  refine ⟨?_, hspf, hcsf⟩; intro hm_f
  rw [sepConj_emp, hbs, ← hev_eq] at hm_f
  simp only [encodeVarintDetSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v48, v40, s0.readReg64 .fp, s0.readReg64 .lr,
    s0.readReg64 .x20, s0.readReg64 .x19, encodeVarintEvents x, cap', ptr',
    htrf, ⟨hcap_le, hcap_pres, hcap_det⟩, ?_⟩
  rw [eq_true (encodeVarintEnv_events x), pure_true]; convert hm_f using 1; sep_ac_rfl

/-- Generalized placed correctness theorem for `encode_varint [local#4]` (Block `451` → Block `460`),
proving the deterministic post-capacity specification `encodeVarintDetSpecOf resStack A lim`. -/
theorem encodeVarint2_det_gen_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State))
    {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (x : EncodeVarintGhost) (st0 : M.σ) (R : SepProp) (s0 : State)
    {Qp : State → SepProp → Prop}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A lim))
    (hpc0 : s0.pc = (blkPl_451).base) (hrun0 : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeVarintDetSpecOf resStack A lim).pre (x, st0) s0 ∗ R)
    (hsp0 : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_451 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeVarintDetSpecOf resStack A lim).post (x, st0) s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s') Qp := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp0
  simp only [encodeVarintDetSpecOf, encodeVarintFitSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres s0.sp, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v48, v40, v32, v24, v16, v8, ⟨hx0, hx1, hlen_bound, hfits0⟩, hpre⟩
  refine ⟨((x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
      ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
      A.pool lim st0 s0) ∗ (vecU8Buf A.repAlloc x.cap x.ptr x.bs ∗ stackAt (s0.sp - 48#64) resStack),
    by convert hpre using 1; sep_ac_rfl, ?_⟩
  refine step_encVarint2_prologue_placed A lim H x.val x.v x.cap x.ptr s0.sp
    v48 v40 v32 v24 v16 v8 x.bs st0 hpc0 hrun0 rfl halign hx0 hx1 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hlen_def : (encodeVarint x.val).length = (encodeVarintAux 10 x.val).length := by
    with_unfolding_all rfl
  have hinv0 := (VecPushBudgetInv.init x st0 hfits0).of_rem_eq hlen_def
  have hcap0 := (VecCapStepInv2.init x).of_rem_eq hlen_def
  have hbs0 : x.bs ++ encodeVarintAux 10 x.val = x.bs ++ encodeVarint x.val := by
    with_unfolding_all rfl
  cases hult0 : x.val.ult 128#64
  · simp only [hult0, ↓reduceIte, Bool.false_eq_true] at hpc1
    have hbs1 := encodeVarint_step_bs hbs0 hult0 rfl
    refine step_encVarint2_s1_placed (F := FSave) A lim H hdoReserve x.val x.v x.cap x.ptr s0.sp v48 v40 x.bs st0
      (stage_len_lt_of_step hlen_bound hinv0.res hbs0) (vecPushBudgetInv2_fits_reserve hinv0 hult0)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by dsimp [FSave]; sep_ac_rfl) ?_
    intro s2 cap1 ptr1 v48_1 v40_1 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 hge1 hpres1 hstep1
    have hinv1 := vecPushBudgetInv2_step (byte := varintContByte x.val) hinv0 hult0 rfl hge1 hpres1 hstep1
    have hcap1 := vecCapStepInv2_step (byte := varintContByte x.val) hcap0 hult0 rfl hstep1
    cases hult1 : (x.val >>> 7).ult 128#64
    · simp only [hult1, ↓reduceIte, Bool.false_eq_true] at hpc2 hx0_2
      have hbs2 := encodeVarint_step_bs (nextV := x.val >>> 14) hbs1 hult1 (ushr_ushr_7 x.val 7 14)
      refine step_encVarint2_s2_placed (F := FSave) A lim H hdoReserve x.val x.v cap1 ptr1 s0.sp v48_1 v40_1 _ _
        (stage_len_lt_of_step hlen_bound hinv1.res hbs1) (vecPushBudgetInv2_fits_reserve hinv1 hult1)
        hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 rfl ?_
      intro s3 cap2 ptr2 v48_2 v40_2 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 hge2 hpres2 hstep2
      have hinv2 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 7)) hinv1 hult1 (ushr_ushr_7 x.val 7 14) hge2 hpres2 hstep2
      have hcap2 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 7)) hcap1 hult1 (ushr_ushr_7 x.val 7 14) hstep2
      cases hult2 : (x.val >>> 14).ult 128#64
      · simp only [hult2, ↓reduceIte, Bool.false_eq_true] at hpc3 hx0_3
        have hbs3 := encodeVarint_step_bs (nextV := x.val >>> 21) hbs2 hult2 (ushr_ushr_7 x.val 14 21)
        refine step_encVarint2_s3_placed (F := FSave) A lim H hdoReserve x.val x.v cap2 ptr2 s0.sp v48_2 v40_2 _ _
          (stage_len_lt_of_step hlen_bound hinv2.res hbs2) (vecPushBudgetInv2_fits_reserve hinv2 hult2)
          hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 rfl ?_
        intro s4 cap3 ptr3 v48_3 v40_3 hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 hge3 hpres3 hstep3
        have hinv3 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 14)) hinv2 hult2 (ushr_ushr_7 x.val 14 21) hge3 hpres3 hstep3
        have hcap3 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 14)) hcap2 hult2 (ushr_ushr_7 x.val 14 21) hstep3
        cases hult3 : (x.val >>> 21).ult 128#64
        · simp only [hult3, ↓reduceIte, Bool.false_eq_true] at hpc4 hx0_4
          have hbs4 := encodeVarint_step_bs (nextV := x.val >>> 28) hbs3 hult3 (ushr_ushr_7 x.val 21 28)
          refine step_encVarint2_s4_placed (F := FSave) A lim H hdoReserve x.val x.v cap3 ptr3 s0.sp v48_3 v40_3 _ _
            (stage_len_lt_of_step hlen_bound hinv3.res hbs3) (vecPushBudgetInv2_fits_reserve hinv3 hult3)
            hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 rfl ?_
          intro s5 cap4 ptr4 v48_4 v40_4 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 hge4 hpres4 hstep4
          have hinv4 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 21)) hinv3 hult3 (ushr_ushr_7 x.val 21 28) hge4 hpres4 hstep4
          have hcap4 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 21)) hcap3 hult3 (ushr_ushr_7 x.val 21 28) hstep4
          cases hult4 : (x.val >>> 28).ult 128#64
          · simp only [hult4, ↓reduceIte, Bool.false_eq_true] at hpc5 hx0_5
            have hbs5 := encodeVarint_step_bs (nextV := x.val >>> 35) hbs4 hult4 (ushr_ushr_7 x.val 28 35)
            refine step_encVarint2_s5_placed (F := FSave) A lim H hdoReserve x.val x.v cap4 ptr4 s0.sp v48_4 v40_4 _ _
              (stage_len_lt_of_step hlen_bound hinv4.res hbs4) (vecPushBudgetInv2_fits_reserve hinv4 hult4)
              hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 rfl ?_
            intro s6 cap5 ptr5 v48_5 v40_5 hpc6 hrun6 hsp6 htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx13_6 hcs6 hge5 hpres5 hstep5
            have hinv5 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 28)) hinv4 hult4 (ushr_ushr_7 x.val 28 35) hge5 hpres5 hstep5
            have hcap5 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 28)) hcap4 hult4 (ushr_ushr_7 x.val 28 35) hstep5
            cases hult5 : (x.val >>> 35).ult 128#64
            · simp only [hult5, ↓reduceIte, Bool.false_eq_true] at hpc6 hx0_6
              have hbs6 := encodeVarint_step_bs (nextV := x.val >>> 42) hbs5 hult5 (ushr_ushr_7 x.val 35 42)
              refine step_encVarint2_s6_placed (F := FSave) A lim H hdoReserve x.val x.v cap5 ptr5 s0.sp v48_5 v40_5 _ _
                (stage_len_lt_of_step hlen_bound hinv5.res hbs5) (vecPushBudgetInv2_fits_reserve hinv5 hult5)
                hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx13_6 hcs6 rfl ?_
              intro s7 cap6 ptr6 v48_6 v40_6 hpc7 hrun7 hsp7 htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx12_7 hx13_7 hcs7 hge6 hpres6 hstep6
              have hinv6 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 35)) hinv5 hult5 (ushr_ushr_7 x.val 35 42) hge6 hpres6 hstep6
              have hcap6 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 35)) hcap5 hult5 (ushr_ushr_7 x.val 35 42) hstep6
              cases hult6 : (x.val >>> 42).ult 128#64
              · simp only [hult6, ↓reduceIte, Bool.false_eq_true] at hpc7 hx0_7
                have hbs7 := encodeVarint_step_bs (nextV := x.val >>> 49) hbs6 hult6 (ushr_ushr_7 x.val 42 49)
                refine step_encVarint2_s7_placed (F := FSave) A lim H hdoReserve x.val x.v cap6 ptr6 s0.sp v48_6 v40_6 _ _
                  (stage_len_lt_of_step hlen_bound hinv6.res hbs6) (vecPushBudgetInv2_fits_reserve hinv6 hult6)
                  hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx12_7 hx13_7 hcs7 rfl ?_
                intro s8 cap7 ptr7 v48_7 v40_7 hpc8 hrun8 hsp8 htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 hge7 hpres7 hstep7
                have hinv7 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 42)) hinv6 hult6 (ushr_ushr_7 x.val 42 49) hge7 hpres7 hstep7
                have hcap7 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 42)) hcap6 hult6 (ushr_ushr_7 x.val 42 49) hstep7
                cases hult7 : (x.val >>> 49).ult 128#64
                · simp only [hult7, ↓reduceIte, Bool.false_eq_true] at hpc8 hx0_8
                  have hbs8 := encodeVarint_step_bs (nextV := x.val >>> 56) hbs7 hult7 (ushr_ushr_7 x.val 49 56)
                  refine step_encVarint2_s8_placed (F := FSave) A lim H hdoReserve x.val x.v cap7 ptr7 s0.sp v48_7 v40_7 _ _
                    (stage_len_lt_of_step hlen_bound hinv7.res hbs7) (vecPushBudgetInv2_fits_reserve hinv7 hult7)
                    hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 rfl ?_
                  intro s9 cap8 ptr8 v48_8 v40_8 hpc9 hrun9 hsp9 htr9 hx0_9 hx1_9 hx8_9 hx9_9 hx10_9 hx11_9 hcs9 hge8 hpres8 hstep8
                  have hinv8 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 49)) hinv7 hult7 (ushr_ushr_7 x.val 49 56) hge8 hpres8 hstep8
                  have hcap8 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 49)) hcap7 hult7 (ushr_ushr_7 x.val 49 56) hstep8
                  cases hult8 : (x.val >>> 56).ult 128#64
                  · simp only [hult8, ↓reduceIte, Bool.false_eq_true] at hpc9 hx0_9
                    have hbs9 := encodeVarint_step_bs (nextV := x.val >>> 63) hbs8 hult8 (ushr_ushr_7 x.val 56 63)
                    refine step_encVarint2_s9_placed
                      (F := ((s0.sp - 48#64) ↦₆₄ v48_8) ∗ ((s0.sp - 40#64) ↦₆₄ v40_8) ∗ FSave)
                      A lim H hdoReserve x.val x.v cap8 ptr8 s0.sp _ _ hult8
                      (stage_len_lt_of_step hlen_bound hinv8.res hbs8) (vecPushBudgetInv2_fits_reserve hinv8 hult8)
                      hpc9 hrun9 hsp9 halign htr9 hx1_9 hx8_9 hx9_9 hx10_9 hx11_9 hcs9 (by sep_ac_rfl) ?_
                    intro s10 cap9 ptr9 hpc10 hrun10 hsp10 htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10 hge9 hpres9 hstep9
                    have hinv9 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 56)) hinv8 hult8 (ushr_ushr_7 x.val 56 63) hge9 hpres9 hstep9
                    have hcap9 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 56)) hcap8 hult8 (ushr_ushr_7 x.val 56 63) hstep9
                    exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ 1#64 cap9 ptr9 v48_8 v40_8 _
                      (vecPushBudgetInv2_exit hinv9 (shr63_ult_128 x.val)) (vecCapStepInv2_exit hcap9 (shr63_ult_128 x.val))
                      (encodeVarint_exit_bs_s9 hbs9 hult8) (stage_len_lt_of_exit hlen_bound hinv9.res (encodeVarint_exit_bs_s9 hbs9 hult8))
                      hpc10 hrun10 hsp10 halign htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10 (by dsimp [FSave]; sep_ac_rfl)
                  · simp only [hult8, ↓reduceIte] at hpc9 hx0_9
                    exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 56) cap8 ptr8 v48_8 v40_8 _
                      (vecPushBudgetInv2_exit hinv8 hult8) (vecCapStepInv2_exit hcap8 hult8) (encodeVarint_exit_bs hbs8 hult8)
                      (stage_len_lt_of_exit hlen_bound hinv8.res (encodeVarint_exit_bs hbs8 hult8)) hpc9 hrun9 hsp9 halign htr9 hx0_9 hx1_9 hx8_9 hx9_9 hcs9 rfl
                · simp only [hult7, ↓reduceIte] at hpc8 hx0_8
                  exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 49) cap7 ptr7 v48_7 v40_7 _
                    (vecPushBudgetInv2_exit hinv7 hult7) (vecCapStepInv2_exit hcap7 hult7) (encodeVarint_exit_bs hbs7 hult7)
                    (stage_len_lt_of_exit hlen_bound hinv7.res (encodeVarint_exit_bs hbs7 hult7)) hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hcs8 rfl
              · simp only [hult6, ↓reduceIte] at hpc7 hx0_7
                exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 42) cap6 ptr6 v48_6 v40_6 _
                  (vecPushBudgetInv2_exit hinv6 hult6) (vecCapStepInv2_exit hcap6 hult6) (encodeVarint_exit_bs hbs6 hult6)
                  (stage_len_lt_of_exit hlen_bound hinv6.res (encodeVarint_exit_bs hbs6 hult6)) hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hcs7 rfl
            · simp only [hult5, ↓reduceIte] at hpc6 hx0_6
              exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 35) cap5 ptr5 v48_5 v40_5 _
                (vecPushBudgetInv2_exit hinv5 hult5) (vecCapStepInv2_exit hcap5 hult5) (encodeVarint_exit_bs hbs5 hult5)
                (stage_len_lt_of_exit hlen_bound hinv5.res (encodeVarint_exit_bs hbs5 hult5)) hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hcs6 rfl
          · simp only [hult4, ↓reduceIte] at hpc5 hx0_5
            exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 28) cap4 ptr4 v48_4 v40_4 _
              (vecPushBudgetInv2_exit hinv4 hult4) (vecCapStepInv2_exit hcap4 hult4) (encodeVarint_exit_bs hbs4 hult4)
              (stage_len_lt_of_exit hlen_bound hinv4.res (encodeVarint_exit_bs hbs4 hult4)) hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hcs5 rfl
        · simp only [hult3, ↓reduceIte] at hpc4 hx0_4
          exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 21) cap3 ptr3 v48_3 v40_3 _
            (vecPushBudgetInv2_exit hinv3 hult3) (vecCapStepInv2_exit hcap3 hult3) (encodeVarint_exit_bs hbs3 hult3)
            (stage_len_lt_of_exit hlen_bound hinv3.res (encodeVarint_exit_bs hbs3 hult3)) hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hcs4 rfl
      · simp only [hult2, ↓reduceIte] at hpc3 hx0_3
        exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 14) cap2 ptr2 v48_2 v40_2 _
          (vecPushBudgetInv2_exit hinv2 hult2) (vecCapStepInv2_exit hcap2 hult2) (encodeVarint_exit_bs hbs2 hult2)
          (stage_len_lt_of_exit hlen_bound hinv2.res (encodeVarint_exit_bs hbs2 hult2)) hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hcs3 rfl
    · simp only [hult1, ↓reduceIte] at hpc2 hx0_2
      exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 7) cap1 ptr1 v48_1 v40_1 _
        (vecPushBudgetInv2_exit hinv1 hult1) (vecCapStepInv2_exit hcap1 hult1) (encodeVarint_exit_bs hbs1 hult1)
        (stage_len_lt_of_exit hlen_bound hinv1.res (encodeVarint_exit_bs hbs1 hult1)) hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hcs2 rfl
  · simp only [hult0, ↓reduceIte] at hpc1
    exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 st0 x.val x.cap x.ptr v48 v40 x.bs
      (vecPushBudgetInv2_exit hinv0 hult0) (vecCapStepInv2_exit hcap0 hult0) (encodeVarint_exit_bs hbs0 hult0)
      (stage_len_lt_of_exit hlen_bound hinv0.res (encodeVarint_exit_bs hbs0 hult0))
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by sep_ac_rfl)

theorem encodeVarint2_det_placed_ok_of_doReserve [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State))
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460)
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A lim))) :
    subroutine_ok (lsProg_451 H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc0 hrun0 hpre hsp0
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcode0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := encodeVarint2_det_gen_placed_ok A lim H hres x st0 R s0
    (doReserve2_with_placed_of_ok A lim s0 hcode0 hdoReserve) hpc0 hrun0 hpre hsp0
  exact ⟨P, R, hP, hwp⟩

theorem encode_varint2_det_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_451).rebase (blkPl_451).base H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpec A lim)) :=
  encodeVarint2_det_placed_ok_of_doReserve (resStack := doReserveStack) (by decide) A lim H
    (ls_subroutine_ok_of_block (callerProg := lsProg_451 H)
      (do_reserve2_placed_ok h_panic hshim halloc hrealloc))

theorem encode_varint2_det_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_451).rebase (blkPl_451).base H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecX A lim)) :=
  encodeVarint2_det_placed_ok_of_doReserve (resStack := doReserveStackX) (by decide) A lim H
    (ls_subroutine_ok_of_block (callerProg := lsProg_451 H)
      (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))


/-! ## 2. Placed Budget-Threaded `encode_repeated::<Vec<u8>, Vec<u8>> [local#3]` (Block `448`) -/

private theorem setup_x24_vm_eq_59 {n : Nat} (hlt : n < 2 ^ 59) :
    (BitVec.ofNat 64 n + BitVec.ofNat 64 (2 * n)) <<< 3 = BitVec.ofNat 64 (24 * n) := by
  have h1 : BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [← h1]
  exact setup_x24_eq_59 hlt

namespace EncodeRepeated1

/-- Loop over non-empty `elems` (`96 → 212` of Block `448`, `elems.length < 2 ^ 59`). -/
theorem step_loop_59_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withEncRepeatedCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec)
    (tag : Nat) (v sp : BitVec 64) (elems : List (BitVec 64 × List (BitVec 8)))
    (hne : elems ≠ []) (helem_cnt : elems.length < 2 ^ 59)
    (curBase curCap curPtr : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).2)
    {s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_448).base + 96#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * elems.length))
    (hx25 : s.readReg64 .x25 = curBase + 16#64) (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt curBase elems ∗
      vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_448).base + 212#64 → sm.status = .Running → sm.sp = sp - 80#64 →
      sm.trace = s0.trace → EncRepeatedCalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).1 →
      SepWPp (lsProg_448 H) ret sm
        ((repeatedBytesSliceAt curBase elems ∗
          vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool lim
            (M.stepEvents (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).2 curSt) sm ∗
          stackAt (sp - 80#64) (48 + resStack)) ∗ F) Q Qp) :
    SepWPp (lsProg_448 H) ret s P Q Qp := by
  induction elems generalizing curBase curCap curPtr curBs curSt s P F with
  | nil => exact False.elim (hne rfl)
  | cons head rest ih =>
    rcases head with ⟨elemPtr, elemBs⟩; subst hP
    simp only [List.map_cons, encodeRepeatedStep] at hfits
    obtain ⟨hfits_head, hfits_tail_raw⟩ := (fitsEvents_append M lim _ _ curSt).mp hfits
    simp only [List.map_cons, encodeRepeatedBytes_cons, List.length_append] at hfit
    have hfit_head : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat ∨
        curBs.length + (encodeBytesField tag (some elemBs)).length + 10 < 2 ^ 62 := by
      rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
    refine EncodeRepeated1.step_iter_placed hres A lim H henc hdoReserve hmemcpy
      tag v curCap curPtr curBase elemPtr sp
      (BitVec.ofNat 64 (24 * (rest.length + 1))) curBs elemBs curSt hfit_head hfits_head
      (F := repeatedBytesSliceAt (curBase + 24#64) rest ∗ F)
      hpc hrun hsp halign htr hx19 hx20 hx24 hx25 hcs
      (by rw [repeatedBytesSliceAt_cons]; sep_ac_rfl) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hx25_1 hcs1 hge1 hpres1 hcap1
    set st1 := M.stepEvents (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).2 curSt
    cases rest with
    | nil =>
      simp only [List.length_nil, Nat.zero_add] at hx24_1
      refine EncodeRepeated1.step_latch_zero_placed H sp curBase
        hpc1 hrun1 hsp1 htr1 hx24_1 hx25_1 hcs1 ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hcs2 hvm12
      rw [← A.pool_of_vmPreserved hvm12]
      have hcap_single : cap1.toNat = (encodeRepeatedStep tag curCap.toNat curBs.length [elemBs]).1 := by
        simpa [encodeRepeatedStep] using hcap1
      have hst_single : st1 = M.stepEvents (encodeRepeatedStep tag curCap.toNat curBs.length [elemBs]).2 curSt := by
        simp [st1, encodeRepeatedStep]
      refine SepWPp.weaken_pre ?_
        (hnext s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hcs2 hge1
          (by simpa [encodeRepeatedBytes_cons, encodeRepeatedBytes_nil] using hpres1)
          (by simpa using hcap_single))
      rw [hst_single]
      simp only [repeatedBytesSliceAt_cons, repeatedBytesSliceAt_nil, List.map_cons, List.map_nil,
        encodeRepeatedBytes_cons, encodeRepeatedBytes_nil, List.append_nil]
      exact Entails.of_eq (by sep_ac_rfl)
    | cons nextHead rest' =>
      have hrest_ne : nextHead :: rest' ≠ [] := List.cons_ne_nil _ _
      have hrest_pos : 0 < (nextHead :: rest').length := List.length_pos_of_ne_nil hrest_ne
      have helem_cnt' : (nextHead :: rest').length + 1 < 2 ^ 59 := helem_cnt
      set tail := nextHead :: rest'
      refine EncodeRepeated1.step_latch_succ_59_placed H v (BitVec.ofNat 64 (tag * 8 + 2)) sp curBase
        tail.length hrest_pos helem_cnt'
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hx25_1 hcs1 ?_
      intro s1' hpc1' hrun1' hsp1' htr1' hx19_1' hx20_1' hx24_1' hx25_1' hcs1' hvm1'
      rw [← A.pool_of_vmPreserved hvm1']
      have hfit_rest : (curBs ++ encodeBytesField tag (some elemBs)).length +
          (encodeRepeatedBytes tag (tail.map Prod.snd)).length ≤ cap1.toNat ∨
          (curBs ++ encodeBytesField tag (some elemBs)).length +
            (encodeRepeatedBytes tag (tail.map Prod.snd)).length + 10 < 2 ^ 62 := by
        rw [List.length_append]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
      have hfits_tail : FitsEvents M lim st1
          (encodeRepeatedStep tag cap1.toNat
            (curBs ++ encodeBytesField tag (some elemBs)).length (tail.map Prod.snd)).2 := by
        simpa only [st1, hcap1, List.length_append] using hfits_tail_raw
      refine ih hrest_ne (Nat.lt_of_succ_lt helem_cnt') (curBase + 24#64) cap1 ptr1
        (curBs ++ encodeBytesField tag (some elemBs)) st1 hfit_rest hfits_tail
        (F := repeatedBytesElemAt curBase elemPtr elemBs ∗ F)
        hpc1' hrun1' hsp1' htr1' hx19_1' hx20_1' hx24_1' hx25_1' hcs1' (by sep_ac_rfl) ?_
      intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs2 hge2 hpres2 hcap2
      have hpres_all : curBs.length +
          (encodeRepeatedBytes tag (((elemPtr, elemBs) :: tail).map Prod.snd)).length ≤
          curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr := by
        intro hfit_cap
        simp only [List.map_cons, encodeRepeatedBytes_cons, List.length_append] at hfit_cap
        obtain ⟨hc1, hp1⟩ := hpres1 (by omega)
        obtain ⟨hc2, hp2⟩ := hpres2 (by rw [hc1, List.length_append]; omega)
        exact ⟨hc2.trans hc1, hp2.trans hp1⟩
      have hcap_all : cap2.toNat =
          (encodeRepeatedStep tag curCap.toNat curBs.length (((elemPtr, elemBs) :: tail).map Prod.snd)).1 := by
        simpa only [List.map_cons, encodeRepeatedStep, ← hcap1, ← List.length_append] using hcap2
      have hst_all : M.stepEvents
            (encodeRepeatedStep tag cap1.toNat
              (curBs ++ encodeBytesField tag (some elemBs)).length (tail.map Prod.snd)).2 st1 =
          M.stepEvents
            (encodeRepeatedStep tag curCap.toNat curBs.length
              (((elemPtr, elemBs) :: tail).map Prod.snd)).2 curSt := by
        simp only [List.map_cons, encodeRepeatedStep, st1, hcap1, List.length_append, M.stepEvents_append]
      refine SepWPp.weaken_pre ?_
        (hnext s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs2 (by omega) hpres_all hcap_all)
      rw [hst_all]; clear_value tail
      rw [repeatedBytesSliceAt_cons, List.map_cons, encodeRepeatedBytes_cons, ← List.append_assoc]
      exact Entails.of_eq (by sep_ac_rfl)

/-- Loop over non-empty `elems` (`96 → 212` of Block `448`, `elems.length < 2 ^ 58`). -/
theorem step_loop_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withEncRepeatedCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec)
    (tag : Nat) (v sp : BitVec 64) (elems : List (BitVec 64 × List (BitVec 8)))
    (hne : elems ≠ []) (helem_cnt : elems.length < 2 ^ 58)
    (curBase curCap curPtr : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).2)
    {s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_448).base + 96#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * elems.length))
    (hx25 : s.readReg64 .x25 = curBase + 16#64) (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt curBase elems ∗
      vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_448).base + 212#64 → sm.status = .Running → sm.sp = sp - 80#64 →
      sm.trace = s0.trace → EncRepeatedCalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).1 →
      SepWPp (lsProg_448 H) ret sm
        ((repeatedBytesSliceAt curBase elems ∗
          vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool lim
            (M.stepEvents (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).2 curSt) sm ∗
          stackAt (sp - 80#64) (48 + resStack)) ∗ F) Q Qp) :
    SepWPp (lsProg_448 H) ret s P Q Qp :=
  step_loop_59_placed hres A lim H henc hdoReserve hmemcpy tag v sp elems hne
    (Nat.lt_trans helem_cnt (by decide)) curBase curCap curPtr curBs curSt hfit hfits
    hpc hrun hsp halign htr hx19 hx20 hx24 hx25 hcs hP hnext

theorem encode_repeated_1_59_gen_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 80 < 2 ^ 64) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    {x : EncodeRepeatedGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    {Qp : State → SepProp → Prop}
    (henc : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withEncRepeatedCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec)
    (hpc : s0.pc = (blkPl_448).base) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeRepeated59DetSpecOf resStack A lim).pre (x, st0) s0 ∗ R)
    (halign : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_448 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeRepeated59DetSpecOf resStack A lim).post (x, st0) s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s') Qp := by
  have hloop := step_loop_59_placed hres A lim H henc hdoReserve hmemcpy
  refine ⟨(encodeRepeated59DetSpecOf resStack A lim).pre (x, st0) s0, hpre, ?_⟩
  dsimp only [encodeRepeated59DetSpecOf, encodeRepeatedSpecOf]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, htag1, htag2, helem_cnt, hfit, hEnv⟩ => ?_
  have hfits0 : FitsEvents M lim st0
      (encodeRepeatedStep x.tag x.cap.toNat x.bs.length (x.elems.map Prod.snd)).2 :=
    FitsEnv.eq_iff.mp hEnv
  rcases x with ⟨tag, base, elems, v, cap, ptr, bs⟩
  dsimp only at hx0 hx1 hx2 hx3 htag1 htag2 helem_cnt hfit hfits0 ⊢
  cases elems with
  | nil =>
    apply sepWPp_of_sepWP_vm (mid := s0.readReg64 .lr)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm => ?_⟩
      apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [← A.pool_of_vmPreserved hvm]
      refine ⟨?_, by simp only [arm64_norm, *], by simp only [CalleeSavedPreserved, arm64_norm, *, and_self]⟩
      intro hPR
      have hpure1 : (cap.toNat ≤ cap.toNat ∧
          (bs.length + (encodeRepeatedBytes tag (([] : List (BitVec 64 × List (BitVec 8))).map Prod.snd)).length ≤ cap.toNat →
            cap = cap ∧ ptr = ptr) ∧
          cap.toNat = (encodeRepeatedStep tag cap.toNat bs.length (([] : List (BitVec 64 × List (BitVec 8))).map Prod.snd)).1) = True :=
        eq_true ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl⟩, rfl⟩
      have hpure2 : EncodeRepeatedEnv ⟨tag, base, [], v, cap, ptr, bs⟩ [] = True := eq_true rfl
      simp only [sepExists_sepConj_left, sepExists_sepConj_right,
        satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨[], cap, ptr, by simp only [arm64_norm, *], ?_⟩
      rw [hpure1, hpure2, pure_true]; simp only [emp_sepConj]
      simpa only [List.map_nil, encodeRepeatedBytes_nil, List.append_nil, M.stepEvents_nil, sepConj_assoc] using hPR
  | cons head rest =>
    have hne : head :: rest ≠ [] := List.cons_ne_nil _ _
    have hpos : 0 < (head :: rest).length := List.length_pos_of_ne_nil hne
    have hcbz : (BitVec.ofNat 64 (head :: rest).length == 0#64) = false := len_beq_zero_false hpos (by omega)
    have hx24_setup := setup_x24_vm_eq_59 helem_cnt
    have hx0' : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 32 tag := hx0
    rw [stackAt_encodeRepeated hres s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun v0 => SepWPp.exists_elim fun v1 =>
      SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
      SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 =>
      SepWPp.exists_elim fun v6 => SepWPp.exists_elim fun v7 =>
      SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 => ?_
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_448).base + 96#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_pro hinv_pro => ?_⟩
      rw [← A.pool_of_vmPreserved hvm_pro]
      have hx20_setup := setup_x20_eq htag2
      set savedCells : SepProp :=
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
        with hsaved_def
      clear_value savedCells
      have halign64 : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using halign
      refine hloop tag v s0.sp (head :: rest) hne helem_cnt base cap ptr bs st0 hfit hfits0
        (F := savedCells)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign64
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ((EncRepeatedCalleeSavedPlaced.refl s0).step (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv_pro)
        (by sep_ac_rfl) ?_
      intro sm cap' ptr' hpcm hrunm hspm htrm hcsm hge hpres hcap_det
      rcases hcsm with ⟨hx26m, hx27m, hx28m, hvregsm, _⟩
      rw [hsaved_def]
      apply sepWPp_of_sepWP_vm (mid := s0.readReg64 .lr)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm_ep => ?_⟩
        apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [← A.pool_of_vmPreserved hvm_ep]
        refine ⟨?_, by simp only [arm64_norm, *], by simp only [CalleeSavedPreserved, arm64_norm, *]⟩
        intro hPR
        have hpure1 : (cap.toNat ≤ cap'.toNat ∧
            (bs.length + (encodeRepeatedBytes tag ((head :: rest).map Prod.snd)).length ≤ cap.toNat →
              cap' = cap ∧ ptr' = ptr) ∧
            cap'.toNat = (encodeRepeatedStep tag cap.toNat bs.length ((head :: rest).map Prod.snd)).1) = True :=
          eq_true ⟨hge, hpres, hcap_det⟩
        have hpure2 : EncodeRepeatedEnv ⟨tag, base, head :: rest, v, cap, ptr, bs⟩
            (encodeRepeatedStep tag cap.toNat bs.length ((head :: rest).map Prod.snd)).2 = True :=
          eq_true rfl
        simp only [satisfies_sepExists, satisfies_pure_sepConj]
        refine ⟨s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
          s0.readReg64 (Reg.gpr 25#5), v3, s0.readReg64 (Reg.gpr 24#5),
          s0.readReg64 (Reg.gpr 23#5), s0.readReg64 (Reg.gpr 22#5),
          s0.readReg64 (Reg.gpr 21#5), s0.readReg64 (Reg.gpr 20#5),
          s0.readReg64 (Reg.gpr 19#5),
          (encodeRepeatedStep tag cap.toNat bs.length ((head :: rest).map Prod.snd)).2,
          cap', ptr', by simp only [arm64_norm, *], ?_⟩
        rw [hpure1, hpure2, pure_true]; simp only [emp_sepConj]
        convert hPR using 1; sep_ac_rfl

theorem encode_repeated_1_gen_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 80 < 2 ^ 64) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    {x : EncodeRepeatedGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    {Qp : State → SepProp → Prop}
    (henc : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withEncRepeatedCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec)
    (hpc : s0.pc = (blkPl_448).base) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeRepeatedSpecOf resStack A lim).pre (x, st0) s0 ∗ R)
    (halign : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_448 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeRepeatedSpecOf resStack A lim).post (x, st0) s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s') Qp := by
  have hpre59 : s0.mem ⊨ (encodeRepeated59DetSpecOf resStack A lim).pre (x, st0) s0 ∗ R := by
    dsimp only [encodeRepeatedSpecOf] at hpre
    dsimp only [encodeRepeated59DetSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    obtain ⟨⟨hx0, hx1, hx2, hx3, htag1, htag2, helem_cnt, hfit, hEnv⟩, hm⟩ := hpre
    exact ⟨⟨hx0, hx1, hx2, hx3, htag1, htag2, Nat.lt_trans helem_cnt (by decide), hfit, hEnv⟩, hm⟩
  exact encode_repeated_1_59_gen_placed_ok hres henc hdoReserve hmemcpy hpc hrun hpre59 halign

end EncodeRepeated1

/-! ## 3. Top-Level Placed Contracts for Block `448` (`< 2 ^ 58` and `< 2 ^ 59`) -/

theorem encode_repeated_1_placed_ok_of_callees [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve0 : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_448 H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpecOf resStack A lim)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre halign
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := EncodeRepeated1.encode_repeated_1_gen_placed_ok hres
    (subroutine_ok_withEncRepeatedCS_placed s0 hcl0 henc0)
    (subroutine_ok_withEncRepeatedCS_placed s0 hcl0 hdoReserve0)
    hmemcpy hpc hrun hpre halign
  exact ⟨P, R, hP, hwp⟩

theorem encode_repeated_1_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_448).rebase (blkPl_448).base H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpec A lim)) :=
  encode_repeated_1_placed_ok_of_callees (resStack := doReserveStack) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc)

theorem encode_repeated_1_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_448).rebase (blkPl_448).base H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpecX A lim)) :=
  encode_repeated_1_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc)

theorem encode_repeated_1_placed_ok_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_448).rebase (blkPl_448).base H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpec A lim)) :=
  encode_repeated_1_placed_ok_of_callees (resStack := doReserveStack) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm (spqr_hook_ok_of_mem hmc))

theorem encode_repeated_1_placed_ok_x_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_448).rebase (blkPl_448).base H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpecX A lim)) :=
  encode_repeated_1_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm (spqr_hook_ok_of_mem hmc))

theorem encode_repeated_1_59_placed_ok_of_callees [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve0 : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_448 H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeated59DetSpecOf resStack A lim)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre halign
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := EncodeRepeated1.encode_repeated_1_59_gen_placed_ok hres
    (subroutine_ok_withEncRepeatedCS_placed s0 hcl0 henc0)
    (subroutine_ok_withEncRepeatedCS_placed s0 hcl0 hdoReserve0)
    hmemcpy hpc hrun hpre halign
  exact ⟨P, R, hP, hwp⟩

theorem encode_repeated_1_59_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_448).rebase (blkPl_448).base H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeated59DetSpecOf doReserveStack A lim)) :=
  encode_repeated_1_59_placed_ok_of_callees (resStack := doReserveStack) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc)

theorem encode_repeated_1_59_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_448).rebase (blkPl_448).base H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeated59DetSpecOf doReserveStackX A lim)) :=
  encode_repeated_1_59_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc)

theorem encode_repeated_1_59_placed_ok_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_448).rebase (blkPl_448).base H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeated59DetSpecOf doReserveStack A lim)) :=
  encode_repeated_1_59_placed_ok_of_callees (resStack := doReserveStack) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm (spqr_hook_ok_of_mem hmc))

theorem encode_repeated_1_59_placed_ok_x_of_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_448).rebase (blkPl_448).base H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeated59DetSpecOf doReserveStackX A lim)) :=
  encode_repeated_1_59_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H) (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm (spqr_hook_ok_of_mem hmc))

abbrev encodeRepeated1_placed_ok_of_callees := @encode_repeated_1_placed_ok_of_callees
abbrev encodeRepeated1_placed_ok := @encode_repeated_1_placed_ok
abbrev encodeRepeated1_placed_ok_x := @encode_repeated_1_placed_ok_x
abbrev encodeRepeated1_59_placed_ok_of_callees := @encode_repeated_1_59_placed_ok_of_callees
abbrev encodeRepeated1_59_placed_ok := @encode_repeated_1_59_placed_ok
abbrev encodeRepeated1_59_placed_ok_x := @encode_repeated_1_59_placed_ok_x
abbrev step_latch_succ_1_59_placed := @EncodeRepeated1.step_latch_succ_59_placed
abbrev step_loop_1_59_placed := @EncodeRepeated1.step_loop_59_placed
abbrev encode_repeated_1_59_gen_placed_ok := @EncodeRepeated1.encode_repeated_1_59_gen_placed_ok

end LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeated1PlacedBudget
