/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirection1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2PlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Varint and `VmPreserved` Combinators for `EpochDirection` (Block `457`)

Establishes deterministic-capacity `encode_varint [local#4]` contracts (Block `451` → Block `460`),
`VecU8ReserveChain` / `VecU8EncodeEnv` combinators, and zero-allocation `VmPreserved` anchors for
CLI Block `457`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirection1PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement lsmpl ls_subroutine_ok_of_block withLsCodeLoaded)
open CryptoVerification.Cli.SpqrV1.Varint.Placed (blkPl_451 lsProg_451)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall doReserveStack doReserveStackX reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncVarintCalleeSavedPlaced EncodeVarintGhost StepInvPlaced
   encodeVarintAux_of_not_ult encodeVarintAux_of_ult encodeVarint_exit_bs
   encodeVarint_step_bs shr63_ult_128 stackAt_encodeVarint_gen_eq
   varintContByte vecU8At_eq_header_sep_buf vecU8Buf)
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm (ushr_ushr_7)
open scoped CryptoVerification.LibsignalTripleRatchet.Prost
open scoped CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym)
open CryptoVerification.SpqrV1.Varint
  (encodeVarint_exit_bs_s9 stage_len_lt_of_exit stage_len_lt_of_step)
open CryptoVerification.SpqrV1.ProtoRepr (epochDirectionPBPinnedAt)
open CryptoVerification.SpqrV1.Auth (authEncodeStackOf)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodeEpochDirectionPinnedGhost encodeEpochDirectionMsg)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents RustCliAllocBudget
   VmPreserved fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
   rustCliReallocBudgetSpec rustReallocEvents zeroBudgetLimits)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveEvents fitsEnv_doReserve_iff noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintEnv_events encodeVarintEvents pushByteStep pushBytesEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget (VecPushBudgetInv)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserve2SpecOf doReserve2SpecWithPlaced doReserve2_with_placed_of_ok)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (encodeVarintDetSpecOf vecU8ReserveChain_pushBytesStep vecU8ReserveChain_reserveStep)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (pushBytesStep pushBytesStep_snd_eq reserveStep reserveStep_of_need_doReserveEvents)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (VecU8EncodeEnv VecU8ReserveChain fitsEnv_vecU8EncodeEnv_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
  (EncodeEpochDirectionPinnedEnv encodeEpochDirectionPinnedExactVmSpecOf
   encodeEpochDirectionPinnedSpecOf)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlacedBudget
  (do_reserve2_placed_ok do_reserve2_placed_ok_x step_encVarint2_final_placed
   step_encVarint2_prologue_placed step_encVarint2_s1_placed step_encVarint2_s2_placed
   step_encVarint2_s3_placed step_encVarint2_s9_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2PlacedBudget
  (step_encVarint2_s4_placed step_encVarint2_s5_placed step_encVarint2_s6_placed
   step_encVarint2_s7_placed step_encVarint2_s8_placed)

/-! ## 1. Deterministic-Capacity `encode_varint [local#4]` (Block `451` → Block `460`) -/

private def VecCapStepInv2 (x : EncodeVarintGhost) (curCap : BitVec 64)
    (curBs : List (BitVec 8)) (remLen : Nat) : Prop :=
  (pushBytesStep (encodeVarint x.val).length x.cap.toNat x.bs.length).1 =
    (pushBytesStep remLen curCap.toNat curBs.length).1

private theorem VecCapStepInv2.init (x : EncodeVarintGhost) :
    VecCapStepInv2 x x.cap x.bs (encodeVarint x.val).length :=
  rfl

private theorem VecCapStepInv2.of_rem_eq {x : EncodeVarintGhost} {curCap : BitVec 64}
    {curBs : List (BitVec 8)} {n1 n2 : Nat}
    (h : VecCapStepInv2 x curCap curBs n1) (hn : n1 = n2) :
    VecCapStepInv2 x curCap curBs n2 :=
  hn ▸ h

private theorem VecCapStepInv2.step {x : EncodeVarintGhost} {curCap nextCap : BitVec 64}
    {curBs : List (BitVec 8)} (byte : BitVec 8) {rem : Nat}
    (h : VecCapStepInv2 x curCap curBs (rem + 1))
    (hcap_step : nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1) :
    VecCapStepInv2 x nextCap (curBs ++ [byte]) rem := by
  have hlen : (curBs ++ [byte]).length = curBs.length + 1 := by
    rw [List.length_append, List.length_singleton]
  unfold VecCapStepInv2 at h ⊢
  rw [h, pushBytesStep, hcap_step, hlen]

private theorem rem_len_step {α : Type} {curBs rhs L1 L2 : List α} {b : α}
    (h1 : curBs ++ L1 = rhs) (h2 : (curBs ++ [b]) ++ L2 = rhs) :
    L1.length = L2.length + 1 := by
  have hlen := congrArg List.length (h1.trans h2.symm)
  simp only [List.length_append, List.length_singleton] at hlen
  omega

private theorem rem_len_exit {α : Type} {curBs rhs L : List α} {b : α}
    (h1 : curBs ++ L = rhs) (h2 : curBs ++ [b] = rhs) :
    L.length = 1 := by
  have hlen := congrArg List.length (h1.trans h2.symm)
  simp only [List.length_append, List.length_singleton] at hlen
  omega

private theorem vecPushBudgetInv_exit {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 curSt : M.σ} {curCap curPtr : BitVec 64}
    {curBs : List (BitVec 8)} {fuel : Nat} {v : BitVec 64}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs
      (encodeVarintAux (fuel + 1) v).length curSt)
    (h : v.ult 128#64 = true) :
    VecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt :=
  hinv.of_rem_eq (by rw [encodeVarintAux_of_ult h]; rfl)

private theorem vecPushBudgetInv_fits_reserve {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 curSt : M.σ} {curCap curPtr : BitVec 64}
    {curBs : List (BitVec 8)} {fuel : Nat} {v : BitVec 64}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs
      (encodeVarintAux (fuel + 1) v).length curSt)
    (h : v.ult 128#64 = false)
    (hcap_eq : curCap.toNat = curBs.length) :
    FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk x.v curCap curPtr curBs 1)) := by
  have hinv' : VecPushBudgetInv M lim x st0 curCap curPtr curBs
      ((encodeVarintAux fuel (v >>> 7)).length + 1) curSt :=
    hinv.of_rem_eq (by rw [encodeVarintAux_of_not_ult h]; rfl)
  exact hinv'.fits_reserve x.v hcap_eq

private theorem vecPushBudgetInv_step {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 curSt : M.σ}
    {curCap curPtr nextCap nextPtr : BitVec 64}
    {curBs : List (BitVec 8)} {byte : BitVec 8} {fuel : Nat} {v nextV : BitVec 64}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs
      (encodeVarintAux (fuel + 1) v).length curSt)
    (h : v.ult 128#64 = false) (hshift : v >>> 7 = nextV)
    (hge : curCap.toNat ≤ nextCap.toNat)
    (hpres : curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr)
    (hcap_step : nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1) :
    VecPushBudgetInv M lim x st0 nextCap nextPtr (curBs ++ [byte])
      (encodeVarintAux fuel nextV).length
      (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) := by
  have hinv' : VecPushBudgetInv M lim x st0 curCap curPtr curBs
      ((encodeVarintAux fuel nextV).length + 1) curSt :=
    hinv.of_rem_eq (by rw [encodeVarintAux_of_not_ult h, hshift]; rfl)
  exact hinv'.step hge hpres hcap_step

private theorem step_encVarint2_det_exit_placed [LibsignalPlacement] {resStack : Nat}
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
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  refine step_encVarint2_final_placed (F := emp) A lim H hdoReserve lastVal x.v curCap curPtr s0.sp v48 v40
    curBs curSt hlen_lt (fun hcap_eq => hinv.fits_reserve x.v hcap_eq)
    hpc hrun hsp halign htr hx0 hx1 hx8 hx9 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro sf cap' ptr' hpcf hrunf hspf htrf hcsf hge hpres hcap_step
  have hinv' := hinv.step (byte := lastVal.setWidth 8) hge hpres hcap_step
  have hcap_inv' := hcap_inv.step (byte := lastVal.setWidth 8) hcap_step
  have hcap_det :
      cap'.toNat =
        (pushBytesStep (encodeVarint x.val).length x.cap.toNat x.bs.length).1 := by
    simpa only [VecCapStepInv2, pushBytesStep] using hcap_inv'.symm
  have hres' := hinv'.res; rw [hbs] at hres'; have ⟨hcap_le, hcap_pres⟩ := hres'.finish
  have hev_eq : M.stepEvents (encodeVarintEvents x) st0 =
      M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt := by
    simpa only [pushBytesEvents, M.stepEvents_nil] using hinv'.events_eq
  refine ⟨?_, hspf, hcsf⟩; intro hm_f
  rw [sepConj_emp, hbs, ← hev_eq] at hm_f
  simp only [encodeVarintDetSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v48, v40, s0.readReg64 .fp, s0.readReg64 .lr,
    s0.readReg64 .x20, s0.readReg64 .x19, encodeVarintEvents x, cap', ptr',
    htrf, ⟨hcap_le, hcap_pres, hcap_det⟩, ?_⟩
  rw [eq_true (encodeVarintEnv_events x), pure_true]
  convert hm_f using 1; sep_ac_rfl

/-- Generalized deterministic-capacity placed correctness for `encode_varint [local#4]`
(Block `451` → Block `460`). -/
theorem encodeVarint2_det_gen_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State))
    {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (x : EncodeVarintGhost) (st0 : M.σ) (R : SepProp) (s0 : State)
    {Qp : State → SepProp → Prop}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A lim))
    (hpc0 : s0.pc = (blkPl_451).base) (hrun0 : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeVarintDetSpecOf resStack A lim).pre (x, st0) s0 ∗ R)
    (hsp0 : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_451 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeVarintDetSpecOf resStack A lim).post (x, st0) s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        Qp := by
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp0; exact hsp0
  simp only [encodeVarintDetSpecOf, encodeVarintFitSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres s0.sp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v48, v40, v32, v24, v16, v8, ⟨hx0, hx1, hlen_bound, hfits0⟩, hpre⟩
  refine ⟨((x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ A.pool lim st0 s0) ∗
      (vecU8Buf A.repAlloc x.cap x.ptr x.bs ∗ stackAt (s0.sp - 48#64) resStack),
    ?_, ?_⟩
  · convert hpre using 1; sep_ac_rfl
  refine step_encVarint2_prologue_placed A lim H x.val x.v x.cap x.ptr s0.sp
    v48 v40 v32 v24 v16 v8 x.bs st0 hpc0 hrun0 rfl halign hx0 hx1 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hinv0 : VecPushBudgetInv M lim x st0 x.cap x.ptr x.bs (encodeVarintAux 10 x.val).length st0 :=
    VecPushBudgetInv.init x st0 hfits0
  have hcap0 : VecCapStepInv2 x x.cap x.bs (encodeVarintAux 10 x.val).length :=
    VecCapStepInv2.init x
  have hbs0 : x.bs ++ encodeVarintAux 10 x.val = x.bs ++ encodeVarint x.val := rfl
  cases hult0 : x.val.ult 128#64
  · simp only [hult0, ↓reduceIte, Bool.false_eq_true] at hpc1
    have hbs1 := encodeVarint_step_bs hbs0 hult0 rfl
    refine step_encVarint2_s1_placed (F := FSave) A lim H hdoReserve
      x.val x.v x.cap x.ptr s0.sp v48 v40 x.bs st0
      (stage_len_lt_of_step hlen_bound hinv0.res hbs0)
      (vecPushBudgetInv_fits_reserve hinv0 hult0)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by dsimp only [FSave]; sep_ac_rfl) ?_
    intro s2 cap1 ptr1 v48_1 v40_1 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 hge1 hpres1 hstep1
    have hinv1 := vecPushBudgetInv_step (byte := varintContByte x.val) hinv0 hult0 rfl hge1 hpres1 hstep1
    have hcap1 := (hcap0.of_rem_eq (rem_len_step hbs0 hbs1)).step (varintContByte x.val) hstep1
    cases hult1 : (x.val >>> 7).ult 128#64
    · simp only [hult1, ↓reduceIte, Bool.false_eq_true] at hpc2 hx0_2
      have hbs2 := encodeVarint_step_bs (nextV := x.val >>> 14) hbs1 hult1 (ushr_ushr_7 x.val 7 14)
      refine step_encVarint2_s2_placed (F := FSave) A lim H hdoReserve
        x.val x.v cap1 ptr1 s0.sp v48_1 v40_1 _ _
        (stage_len_lt_of_step hlen_bound hinv1.res hbs1)
        (vecPushBudgetInv_fits_reserve hinv1 hult1)
        hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 rfl ?_
      intro s3 cap2 ptr2 v48_2 v40_2 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 hge2 hpres2 hstep2
      have hinv2 := vecPushBudgetInv_step (byte := varintContByte (x.val >>> 7))
        hinv1 hult1 (ushr_ushr_7 x.val 7 14) hge2 hpres2 hstep2
      have hcap2 := (hcap1.of_rem_eq (rem_len_step hbs1 hbs2)).step (varintContByte (x.val >>> 7)) hstep2
      cases hult2 : (x.val >>> 14).ult 128#64
      · simp only [hult2, ↓reduceIte, Bool.false_eq_true] at hpc3 hx0_3
        have hbs3 := encodeVarint_step_bs (nextV := x.val >>> 21) hbs2 hult2 (ushr_ushr_7 x.val 14 21)
        refine step_encVarint2_s3_placed (F := FSave) A lim H hdoReserve
          x.val x.v cap2 ptr2 s0.sp v48_2 v40_2 _ _
          (stage_len_lt_of_step hlen_bound hinv2.res hbs2)
          (vecPushBudgetInv_fits_reserve hinv2 hult2)
          hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 rfl ?_
        intro s4 cap3 ptr3 v48_3 v40_3 hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 hge3 hpres3 hstep3
        have hinv3 := vecPushBudgetInv_step (byte := varintContByte (x.val >>> 14))
          hinv2 hult2 (ushr_ushr_7 x.val 14 21) hge3 hpres3 hstep3
        have hcap3 := (hcap2.of_rem_eq (rem_len_step hbs2 hbs3)).step (varintContByte (x.val >>> 14)) hstep3
        cases hult3 : (x.val >>> 21).ult 128#64
        · simp only [hult3, ↓reduceIte, Bool.false_eq_true] at hpc4 hx0_4
          have hbs4 := encodeVarint_step_bs (nextV := x.val >>> 28) hbs3 hult3 (ushr_ushr_7 x.val 21 28)
          refine step_encVarint2_s4_placed (F := FSave) A lim H hdoReserve
            x.val x.v cap3 ptr3 s0.sp v48_3 v40_3 _ _
            (stage_len_lt_of_step hlen_bound hinv3.res hbs3)
            (vecPushBudgetInv_fits_reserve hinv3 hult3)
            hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 rfl ?_
          intro s5 cap4 ptr4 v48_4 v40_4 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 hge4 hpres4 hstep4
          have hinv4 := vecPushBudgetInv_step (byte := varintContByte (x.val >>> 21))
            hinv3 hult3 (ushr_ushr_7 x.val 21 28) hge4 hpres4 hstep4
          have hcap4 := (hcap3.of_rem_eq (rem_len_step hbs3 hbs4)).step (varintContByte (x.val >>> 21)) hstep4
          cases hult4 : (x.val >>> 28).ult 128#64
          · simp only [hult4, ↓reduceIte, Bool.false_eq_true] at hpc5 hx0_5
            have hbs5 := encodeVarint_step_bs (nextV := x.val >>> 35) hbs4 hult4 (ushr_ushr_7 x.val 28 35)
            refine step_encVarint2_s5_placed (F := FSave) A lim H hdoReserve
              x.val x.v cap4 ptr4 s0.sp v48_4 v40_4 _ _
              (stage_len_lt_of_step hlen_bound hinv4.res hbs4)
              (vecPushBudgetInv_fits_reserve hinv4 hult4)
              hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 rfl ?_
            intro s6 cap5 ptr5 v48_5 v40_5 hpc6 hrun6 hsp6 htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx13_6 hcs6 hge5 hpres5 hstep5
            have hinv5 := vecPushBudgetInv_step (byte := varintContByte (x.val >>> 28))
              hinv4 hult4 (ushr_ushr_7 x.val 28 35) hge5 hpres5 hstep5
            have hcap5 := (hcap4.of_rem_eq (rem_len_step hbs4 hbs5)).step (varintContByte (x.val >>> 28)) hstep5
            cases hult5 : (x.val >>> 35).ult 128#64
            · simp only [hult5, ↓reduceIte, Bool.false_eq_true] at hpc6 hx0_6
              have hbs6 := encodeVarint_step_bs (nextV := x.val >>> 42) hbs5 hult5 (ushr_ushr_7 x.val 35 42)
              refine step_encVarint2_s6_placed (F := FSave) A lim H hdoReserve
                x.val x.v cap5 ptr5 s0.sp v48_5 v40_5 _ _
                (stage_len_lt_of_step hlen_bound hinv5.res hbs5)
                (vecPushBudgetInv_fits_reserve hinv5 hult5)
                hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx13_6 hcs6 rfl ?_
              intro s7 cap6 ptr6 v48_6 v40_6 hpc7 hrun7 hsp7 htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx12_7 hx13_7 hcs7 hge6 hpres6 hstep6
              have hinv6 := vecPushBudgetInv_step (byte := varintContByte (x.val >>> 35))
                hinv5 hult5 (ushr_ushr_7 x.val 35 42) hge6 hpres6 hstep6
              have hcap6 := (hcap5.of_rem_eq (rem_len_step hbs5 hbs6)).step (varintContByte (x.val >>> 35)) hstep6
              cases hult6 : (x.val >>> 42).ult 128#64
              · simp only [hult6, ↓reduceIte, Bool.false_eq_true] at hpc7 hx0_7
                have hbs7 := encodeVarint_step_bs (nextV := x.val >>> 49) hbs6 hult6 (ushr_ushr_7 x.val 42 49)
                refine step_encVarint2_s7_placed (F := FSave) A lim H hdoReserve
                  x.val x.v cap6 ptr6 s0.sp v48_6 v40_6 _ _
                  (stage_len_lt_of_step hlen_bound hinv6.res hbs6)
                  (vecPushBudgetInv_fits_reserve hinv6 hult6)
                  hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx12_7 hx13_7 hcs7 rfl ?_
                intro s8 cap7 ptr7 v48_7 v40_7 hpc8 hrun8 hsp8 htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 hge7 hpres7 hstep7
                have hinv7 := vecPushBudgetInv_step (byte := varintContByte (x.val >>> 42))
                  hinv6 hult6 (ushr_ushr_7 x.val 42 49) hge7 hpres7 hstep7
                have hcap7 := (hcap6.of_rem_eq (rem_len_step hbs6 hbs7)).step (varintContByte (x.val >>> 42)) hstep7
                cases hult7 : (x.val >>> 49).ult 128#64
                · simp only [hult7, ↓reduceIte, Bool.false_eq_true] at hpc8 hx0_8
                  have hbs8 := encodeVarint_step_bs (nextV := x.val >>> 56) hbs7 hult7 (ushr_ushr_7 x.val 49 56)
                  refine step_encVarint2_s8_placed (F := FSave) A lim H hdoReserve
                    x.val x.v cap7 ptr7 s0.sp v48_7 v40_7 _ _
                    (stage_len_lt_of_step hlen_bound hinv7.res hbs7)
                    (vecPushBudgetInv_fits_reserve hinv7 hult7)
                    hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 rfl ?_
                  intro s9 cap8 ptr8 v48_8 v40_8 hpc9 hrun9 hsp9 htr9 hx0_9 hx1_9 hx8_9 hx9_9 hx10_9 hx11_9 hcs9 hge8 hpres8 hstep8
                  have hinv8 := vecPushBudgetInv_step (byte := varintContByte (x.val >>> 49))
                    hinv7 hult7 (ushr_ushr_7 x.val 49 56) hge8 hpres8 hstep8
                  have hcap8 := (hcap7.of_rem_eq (rem_len_step hbs7 hbs8)).step (varintContByte (x.val >>> 49)) hstep8
                  cases hult8 : (x.val >>> 56).ult 128#64
                  · simp only [hult8, ↓reduceIte, Bool.false_eq_true] at hpc9 hx0_9
                    have hbs9 := encodeVarint_step_bs (nextV := x.val >>> 63) hbs8 hult8 (ushr_ushr_7 x.val 56 63)
                    refine step_encVarint2_s9_placed
                      (F := ((s0.sp - 48#64) ↦₆₄ v48_8) ∗ ((s0.sp - 40#64) ↦₆₄ v40_8) ∗ FSave)
                      A lim H hdoReserve x.val x.v cap8 ptr8 s0.sp _ _ hult8
                      (stage_len_lt_of_step hlen_bound hinv8.res hbs8)
                      (vecPushBudgetInv_fits_reserve hinv8 hult8)
                      hpc9 hrun9 hsp9 halign htr9 hx1_9 hx8_9 hx9_9 hx10_9 hx11_9 hcs9 (by sep_ac_rfl) ?_
                    intro s10 cap9 ptr9 hpc10 hrun10 hsp10 htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10 hge9 hpres9 hstep9
                    have hinv9 := vecPushBudgetInv_step (byte := varintContByte (x.val >>> 56))
                      hinv8 hult8 (ushr_ushr_7 x.val 56 63) hge9 hpres9 hstep9
                    have hcap9 := (hcap8.of_rem_eq (rem_len_step hbs8 hbs9)).step (varintContByte (x.val >>> 56)) hstep9
                    have hexit9 := encodeVarint_exit_bs_s9 hbs9 hult8
                    exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _
                      1#64 cap9 ptr9 v48_8 v40_8 _
                      (vecPushBudgetInv_exit hinv9 (shr63_ult_128 x.val))
                      (hcap9.of_rem_eq (rem_len_exit hbs9 hexit9))
                      hexit9
                      (stage_len_lt_of_exit hlen_bound hinv9.res hexit9)
                      hpc10 hrun10 hsp10 halign htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10
                      (by dsimp only [FSave]; sep_ac_rfl)
                  · simp only [hult8, ↓reduceIte] at hpc9 hx0_9
                    have hexit8 := encodeVarint_exit_bs hbs8 hult8
                    exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _
                      (x.val >>> 56) cap8 ptr8 v48_8 v40_8 _
                      (vecPushBudgetInv_exit hinv8 hult8)
                      (hcap8.of_rem_eq (rem_len_exit hbs8 hexit8))
                      hexit8
                      (stage_len_lt_of_exit hlen_bound hinv8.res hexit8)
                      hpc9 hrun9 hsp9 halign htr9 hx0_9 hx1_9 hx8_9 hx9_9 hcs9 rfl
                · simp only [hult7, ↓reduceIte] at hpc8 hx0_8
                  have hexit7 := encodeVarint_exit_bs hbs7 hult7
                  exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _
                    (x.val >>> 49) cap7 ptr7 v48_7 v40_7 _
                    (vecPushBudgetInv_exit hinv7 hult7)
                    (hcap7.of_rem_eq (rem_len_exit hbs7 hexit7))
                    hexit7
                    (stage_len_lt_of_exit hlen_bound hinv7.res hexit7)
                    hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hcs8 rfl
              · simp only [hult6, ↓reduceIte] at hpc7 hx0_7
                have hexit6 := encodeVarint_exit_bs hbs6 hult6
                exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _
                  (x.val >>> 42) cap6 ptr6 v48_6 v40_6 _
                  (vecPushBudgetInv_exit hinv6 hult6)
                  (hcap6.of_rem_eq (rem_len_exit hbs6 hexit6))
                  hexit6
                  (stage_len_lt_of_exit hlen_bound hinv6.res hexit6)
                  hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hcs7 rfl
            · simp only [hult5, ↓reduceIte] at hpc6 hx0_6
              have hexit5 := encodeVarint_exit_bs hbs5 hult5
              exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _
                (x.val >>> 35) cap5 ptr5 v48_5 v40_5 _
                (vecPushBudgetInv_exit hinv5 hult5)
                (hcap5.of_rem_eq (rem_len_exit hbs5 hexit5))
                hexit5
                (stage_len_lt_of_exit hlen_bound hinv5.res hexit5)
                hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hcs6 rfl
          · simp only [hult4, ↓reduceIte] at hpc5 hx0_5
            have hexit4 := encodeVarint_exit_bs hbs4 hult4
            exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _
              (x.val >>> 28) cap4 ptr4 v48_4 v40_4 _
              (vecPushBudgetInv_exit hinv4 hult4)
              (hcap4.of_rem_eq (rem_len_exit hbs4 hexit4))
              hexit4
              (stage_len_lt_of_exit hlen_bound hinv4.res hexit4)
              hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hcs5 rfl
        · simp only [hult3, ↓reduceIte] at hpc4 hx0_4
          have hexit3 := encodeVarint_exit_bs hbs3 hult3
          exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _
            (x.val >>> 21) cap3 ptr3 v48_3 v40_3 _
            (vecPushBudgetInv_exit hinv3 hult3)
            (hcap3.of_rem_eq (rem_len_exit hbs3 hexit3))
            hexit3
            (stage_len_lt_of_exit hlen_bound hinv3.res hexit3)
            hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hcs4 rfl
      · simp only [hult2, ↓reduceIte] at hpc3 hx0_3
        have hexit2 := encodeVarint_exit_bs hbs2 hult2
        exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _
          (x.val >>> 14) cap2 ptr2 v48_2 v40_2 _
          (vecPushBudgetInv_exit hinv2 hult2)
          (hcap2.of_rem_eq (rem_len_exit hbs2 hexit2))
          hexit2
          (stage_len_lt_of_exit hlen_bound hinv2.res hexit2)
          hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hcs3 rfl
    · simp only [hult1, ↓reduceIte] at hpc2 hx0_2
      have hexit1 := encodeVarint_exit_bs hbs1 hult1
      exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _
        (x.val >>> 7) cap1 ptr1 v48_1 v40_1 _
        (vecPushBudgetInv_exit hinv1 hult1)
        (hcap1.of_rem_eq (rem_len_exit hbs1 hexit1))
        hexit1
        (stage_len_lt_of_exit hlen_bound hinv1.res hexit1)
        hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hcs2 rfl
  · simp only [hult0, ↓reduceIte] at hpc1
    have hexit0 := encodeVarint_exit_bs hbs0 hult0
    exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 st0
      x.val x.cap x.ptr v48 v40 x.bs
      (vecPushBudgetInv_exit hinv0 hult0)
      (hcap0.of_rem_eq (rem_len_exit hbs0 hexit0))
      hexit0
      (stage_len_lt_of_exit hlen_bound hinv0.res hexit0)
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
    subroutine_ok (lsProg_451 H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf doReserveStack A lim)) :=
  encodeVarint2_det_placed_ok_of_doReserve (resStack := doReserveStack) (by decide) A lim H
    (ls_subroutine_ok_of_block (callerProg := lsProg_451 H)
      (do_reserve2_placed_ok h_panic hshim halloc hrealloc))

theorem encode_varint2_det_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_451 H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf doReserveStackX A lim)) :=
  encodeVarint2_det_placed_ok_of_doReserve (resStack := doReserveStackX) (by decide) A lim H
    (ls_subroutine_ok_of_block (callerProg := lsProg_451 H)
      (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))

/-! ## 2. `VmPreserved`, `VecU8ReserveChain`, & Enforced Zero-Allocation Combinators -/

theorem vmPreserved_symm {s s' : State} (h : VmPreserved s s') : VmPreserved s' s :=
  h.symm

theorem sepWPp_of_sepWP_cs_placed_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ProofLib.SepWP prog mid s Pre (fun sm Pm =>
      VmPreserved s sm ∧
        (VmPreserved s sm → StepInvPlaced s sm → SepWPp prog ret sm Pm Q Qp oom))) :
    SepWPp prog ret s Pre Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvmp, hnext⟩ | ⟨_, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext hvmp (StepInvPlaced.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem sepWP_done_tpidr_placed {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0)
    (hpost : Q s P) :
    ProofLib.SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  ProofLib.SepWP.done hpc hrun ⟨htp, hpost⟩

theorem fitsEvents_and_step_of_chain {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {c0 c1 finalLen : Nat} {evs : List AllocEvent}
    (hEnv : FitsEnv M lim st (VecU8EncodeEnv c0 finalLen))
    (hchain : VecU8ReserveChain c0 c1 finalLen evs) :
    FitsEvents M lim st evs ∧
      FitsEnv M lim (M.stepEvents evs st) (VecU8EncodeEnv c1 finalLen) := by
  refine ⟨hEnv evs ⟨c1, hchain⟩, ?_⟩
  rintro evs' ⟨cOut, hchain'⟩
  have htot := hEnv (evs ++ evs') ⟨cOut, hchain.trans (Nat.le_refl _) hchain'⟩
  exact ((fitsEvents_append M lim evs evs' st).mp htot).2

theorem vecU8ReserveChain_encodeVarint {val v curCap curPtr nextCap : BitVec 64}
    {curBs : List (BitVec 8)} {finalLen : Nat}
    (hle : curBs.length + (encodeVarint val).length ≤ finalLen)
    (hdet : nextCap.toNat = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).1) :
    VecU8ReserveChain curCap.toNat nextCap.toNat finalLen
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) := by
  have hc := vecU8ReserveChain_pushBytesStep (encodeVarint val).length curCap.toNat curBs.length
    finalLen hle
  rw [← hdet, pushBytesStep_snd_eq] at hc
  exact hc

theorem fitsEvents_encodeVarint_of_env {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {val v curCap curPtr : BitVec 64} {curBs : List (BitVec 8)} {finalLen : Nat}
    (hEnv : FitsEnv M lim st (VecU8EncodeEnv curCap.toNat finalLen))
    (hle : curBs.length + (encodeVarint val).length ≤ finalLen) :
    FitsEvents M lim st (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) := by
  have hc := vecU8ReserveChain_pushBytesStep (encodeVarint val).length curCap.toNat curBs.length
    finalLen hle
  rw [pushBytesStep_snd_eq] at hc
  exact (fitsEvents_and_step_of_chain hEnv hc).1

theorem vecU8ReserveChain_doReserve (v curCap curPtr : BitVec 64)
    (curBs : List (BitVec 8)) (additional finalLen : Nat)
    (hneed : ¬ (curBs.length + additional ≤ curCap.toNat))
    (hle : curBs.length + additional ≤ finalLen)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63) :
    VecU8ReserveChain curCap.toNat
      (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)).toNat finalLen
      (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) := by
  have hc := vecU8ReserveChain_reserveStep (cap := curCap.toNat) (len := curBs.length)
    (additional := additional) (finalLen := finalLen) hle
  rw [reserveStep_of_need_doReserveEvents v curCap curPtr curBs additional hneed] at hc
  have htoNat : (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)).toNat =
      reserveCap curCap.toNat curBs.length additional := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rwa [htoNat]

def noAllocEnforcedLimits : BudgetLimits :=
  { staticCount := 0, staticBytes := 1, physCap := 0, enforced := true }

theorem not_fitsEvent_noAllocEnforcedLimits (M : AllocCostModel) (st : M.σ) (ev : AllocEvent) :
    ¬ FitsEvent M noAllocEnforcedLimits st ev := by
  rintro ⟨_, _, hram, _⟩
  dsimp only [noAllocEnforcedLimits] at hram
  omega

theorem not_fitsEvents_doReserveEvents_noAllocEnforced (M : AllocCostModel) (st : M.σ)
    (x : DoReserveCall) :
    ¬ FitsEvents M noAllocEnforcedLimits st (doReserveEvents x) := by
  unfold doReserveEvents
  split_ifs
  · unfold rustAllocEvents
    dsimp only
    split_ifs <;> intro h <;> exact not_fitsEvent_noAllocEnforcedLimits M st _ h.1
  · unfold rustReallocEvents
    dsimp only
    split_ifs <;> intro h <;> exact not_fitsEvent_noAllocEnforcedLimits M st _ h.1

def withVmAnchor {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim₀ : BudgetLimits) (s₀ : State) : RustCliAllocBudget M where
  pool := fun lim st s =>
    if lim.enforced then ⌜VmPreserved s₀ s⌝ ∗ A.pool lim₀ st s
    else A.pool zeroBudgetLimits st s
  live := A.live
  block_valid := A.block_valid
  pool_transport := by
    intro lim st s s' hvmp
    split_ifs with henf
    · have hp : (⌜VmPreserved s₀ s'⌝ : SepProp) = ⌜VmPreserved s₀ s⌝ :=
        congrArg SepProp.pure
          (propext ⟨fun h => h.trans (vmPreserved_symm hvmp), fun h => h.trans hvmp⟩)
      rw [hp, A.pool_transport lim₀ st s s' hvmp]
    · exact A.pool_transport zeroBudgetLimits st s s' hvmp
  pool_zero_transport := fun st s s' hpp => A.pool_zero_transport st s s' hpp

@[simp] theorem withVmAnchor_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim₀ : BudgetLimits) (s₀ : State) :
    (withVmAnchor A lim₀ s₀).repAlloc = A.repAlloc :=
  rfl

theorem withVmAnchor_pool_noAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim₀ : BudgetLimits) (s₀ : State) (st : M.σ) (s : State) :
    (withVmAnchor A lim₀ s₀).pool noAllocEnforcedLimits st s =
      (⌜VmPreserved s₀ s⌝ ∗ A.pool lim₀ st s) :=
  rfl

theorem doReserve2_noAllocEnforced_ok [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {fn_pc : BitVec 64} (A : RustCliAllocBudget M) :
    subroutine_ok prog fn_pc
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A noAllocEnforcedLimits)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 _ _ hpre _ => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  have hpre2 := hpre.2
  simp only [doReserve2SpecOf, sepConj_assoc, satisfies_pure_sepConj] at hpre2
  exact absurd ((fitsEnv_doReserve_iff x).mp hpre2.1.2.2.2.2)
    (not_fitsEvents_doReserveEvents_noAllocEnforced M st x)

theorem encodeVarint2_det_noAllocEnforced_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_451 H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A noAllocEnforcedLimits)) :=
  encodeVarint2_det_placed_ok_of_doReserve hres A noAllocEnforcedLimits H
    (doReserve2_noAllocEnforced_ok A)

def encodeEpochDirectionPinnedCoreSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeEpochDirectionPinnedGhost × M.σ) where
  pre := (encodeEpochDirectionPinnedSpecOf resStack A lim).pre
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜EncodeEpochDirectionPinnedEnv x evs ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            evs = [])⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (authEncodeStackOf resStack)

theorem subroutine_ok_encodeEpochDirectionPinned_of_core [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {fn_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hcore_full : subroutine_ok prog fn_pc
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedCoreSpecOf resStack A lim)))
    (hcore_spare : ∀ s0 : State, subroutine_ok prog fn_pc
      (withLsCodeLoaded lsmpl
        (encodeEpochDirectionPinnedCoreSpecOf resStack (withVmAnchor A lim s0)
          noAllocEnforcedLimits))) :
    subroutine_ok prog fn_pc
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hspare : x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat
  · have hpre_anchor : s0.mem ⊨
        (withLsCodeLoaded lsmpl
          (encodeEpochDirectionPinnedCoreSpecOf resStack (withVmAnchor A lim s0)
            noAllocEnforcedLimits)).pre (x, st) s0 ∗ R := by
      dsimp only [withLsCodeLoaded, encodeEpochDirectionPinnedCoreSpecOf,
        encodeEpochDirectionPinnedSpecOf] at hpre ⊢
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨hcl0, hpre⟩
      refine ⟨hcl0, ?_⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨⟨hw0, hx1, hx2, _, _⟩, hmem⟩
      refine ⟨⟨hw0, hx1, hx2, Or.inl hspare,
        fitsEnv_vecU8EncodeEnv_of_spare M noAllocEnforcedLimits st hspare⟩, ?_⟩
      rw [withVmAnchor_repAlloc, withVmAnchor_pool_noAlloc]
      have hmem' : s0.mem ⊨ ⌜VmPreserved s0 s0⌝ ∗
          (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
            (vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
              (A.pool lim st s0 ∗ (stackAt s0.sp (authEncodeStackOf resStack) ∗ R)))) := by
        rw [satisfies_pure_sepConj]
        exact ⟨VmPreserved.refl s0, hmem⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem'
    refine (hcore_spare s0).mono_outcome (x, st) R s0 hpc hrun hpre_anchor hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, encodeEpochDirectionPinnedCoreSpecOf,
        encodeEpochDirectionPinnedSpecOf] at hq ⊢
      simp only [withVmAnchor_repAlloc, withVmAnchor_pool_noAlloc,
        sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨evs, cap', ptr', htr, hmem⟩
      have hmem_reord : sf.mem ⊨
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          ⌜EncodeEpochDirectionPinnedEnv x evs ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              evs = [])⌝ ∗
          ⌜VmPreserved s0 sf⌝ ∗
          (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
            vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (authEncodeStackOf resStack) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hmem_reord
      rcases hmem_reord with ⟨⟨hge, hpres⟩, ⟨hev, hnil⟩, hvmp, hmem_clean⟩
      have hev_nil : evs = [] := hnil hspare
      subst hev_nil
      simp only [AllocCostModel.stepEvents] at hmem_clean
      refine ⟨[], cap', ptr', htr, ?_⟩
      have hout_mem : sf.mem ⊨
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          ⌜EncodeEpochDirectionPinnedEnv x [] ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              ([] : List AllocEvent) = [] ∧ VmPreserved s0 sf)⌝ ∗
          (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
            vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
            A.pool lim st sf ∗
            stackAt s0.sp (authEncodeStackOf resStack) ∗ R) := by
        rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
        exact ⟨⟨hge, hpres⟩, ⟨hev, fun _ => ⟨rfl, hvmp⟩⟩, hmem_clean⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hout_mem
    · exact (not_satisfies_false_sepConj hq).elim
    · exact (not_satisfies_false_sepConj hq).elim
    · exact (not_satisfies_false_sepConj hq).elim
  · refine hcore_full.mono_outcome (x, st) R s0 hpc hrun hpre hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, encodeEpochDirectionPinnedCoreSpecOf,
        encodeEpochDirectionPinnedSpecOf] at hq ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨evs, cap', ptr', htr, hmem⟩
      have hmem_reord : sf.mem ⊨
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          ⌜EncodeEpochDirectionPinnedEnv x evs ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              evs = [])⌝ ∗
          (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
            vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (authEncodeStackOf resStack) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hmem_reord
      rcases hmem_reord with ⟨hcp, ⟨hev, _⟩, hmem_clean⟩
      refine ⟨evs, cap', ptr', htr, ?_⟩
      have hout_mem : sf.mem ⊨
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          ⌜EncodeEpochDirectionPinnedEnv x evs ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              evs = [] ∧ VmPreserved s0 sf)⌝ ∗
          (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
            vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (authEncodeStackOf resStack) ∗ R) := by
        rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
        exact ⟨hcp, ⟨hev, fun h => absurd h hspare⟩, hmem_clean⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hout_mem
    · exact (not_satisfies_false_sepConj hq).elim
    · exact (not_satisfies_false_sepConj hq).elim
    · exact (not_satisfies_false_sepConj hq).elim

theorem subroutine_ok_encodeEpochDirectionPinnedExact_of_budget {resStack : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (st : M.σ)
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (encodeEpochDirectionPinnedSpecOf resStack A lim)) :
    subroutine_ok prog entry
      { pre := fun x s =>
          (encodeEpochDirectionPinnedExactVmSpecOf resStack A.repAlloc).pre x s ∗ A.pool lim st s
        post := fun x s0 sf =>
          (encodeEpochDirectionPinnedExactVmSpecOf resStack A.repAlloc).post x s0 sf ∗
            A.pool lim st sf } := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodeEpochDirectionPinnedExactVmSpecOf] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hx1, hx2, hle⟩, hrest⟩
  have hEnv : FitsEnv M lim st (EncodeEpochDirectionPinnedEnv x) :=
    fitsEnv_vecU8EncodeEnv_of_spare M lim st hle
  have hpreB : s0.mem ⊨ (encodeEpochDirectionPinnedSpecOf resStack A lim).pre (x, st) s0 ∗ R := by
    dsimp only [encodeEpochDirectionPinnedSpecOf]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hw0, hx1, hx2, Or.inl hle, hEnv⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  refine h.mono_outcome (x, st) R s0 hpc hrun hpreB hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encodeEpochDirectionPinnedSpecOf] at hq
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨evs, cap', ptr', htr, hq_mem0⟩
    have hq_reord : sf.mem ⊨
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        ⌜EncodeEpochDirectionPinnedEnv x evs ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp (authEncodeStackOf resStack) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq_mem0
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hq_reord
    rcases hq_reord with ⟨⟨_, hcp⟩, ⟨_, hev⟩, hq_mem⟩
    rcases hcp hle with ⟨rfl, rfl⟩
    rcases hev hle with ⟨rfl, hvm⟩
    simp only [AllocCostModel.stepEvents] at hq_mem
    dsimp only [encodeEpochDirectionPinnedExactVmSpecOf]
    have hgoal : sf.mem ⊨
        ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
        (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
         vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
         stackAt s0.sp (authEncodeStackOf resStack) ∗ A.pool lim st sf ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hvm, htr⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq_mem⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirection1PlacedBudgetAux
