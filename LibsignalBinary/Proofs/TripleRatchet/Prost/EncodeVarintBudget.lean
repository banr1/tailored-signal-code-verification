/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintStagesBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Verification of `prost::encoding::varint::encode_varint`

Assembles the relocatable `[LibsignalPlacement]` verification of `encode_varint::<Vec<u8>>`
(block 10, calling block 13) against `EncDefsBudget.encodeVarintSpec` and `encodeVarintSpecX`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec
   rustCliAllocNoOomSpec rustCliReallocNoOomSpec)
open CryptoVerification
  (LibsignalPlacement lsmpl withLsCodeLoaded extract_withLsCodeLoaded
   lsRustNoAllocShimSym lsRustAllocSym lsRustReallocSym
   blkPC_10 blkPl_10 blkPC_13 blkPl_13)
open CryptoVerification.RustHeap (vecU8At vecHeader)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost vecU8Buf vecU8At_eq_header_sep_buf varintContByte
   contByte9_shr63_eq shr63_ult_128 encodeVarintAux_of_ult encodeVarintAux_of_not_ult
   encodeVarint_exit_bs encodeVarint_step_bs stackAt_encodeVarint_gen_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm (ushr_ushr_7)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveSpec doReserveSpecX noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserveBudget
  (do_reserve_placed_ok do_reserve_placed_ok_x
   do_reserve_placed_ok_noOom do_reserve_placed_ok_x_noOom)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintSpec encodeVarintSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
  (VecPushBudgetInv doReserveSpecWithPlaced doReserve_with_placed_of_ok
   doReserve_with_placed_of_ok_x encodeVarintSpecOf
   step_encVarint_prologue_placed step_encVarint_exit_placed
   step_encVarint_s1_placed step_encVarint_s2_placed step_encVarint_s3_placed)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintStagesBudget
  (step_encVarint_s4_placed step_encVarint_s5_placed step_encVarint_s6_placed
   step_encVarint_s7_placed step_encVarint_s8_placed step_encVarint_s9_placed)

/-! ## Auxiliary `encodeVarintAux` and `VecPushBudgetInv` helpers -/

theorem encodeVarint_exit_bs_s9 {v : BitVec 64} {bs rhs : List (BitVec 8)}
    (hcur : bs ++ encodeVarintAux 1 (v >>> 63) = rhs)
    (h : (v >>> 56).ult 128#64 = false) :
    bs ++ [(1#64 : BitVec 64).setWidth 8] = rhs := by
  have h1 : (1#64 : BitVec 64) = v >>> 63 := contByte9_shr63_eq v h
  rw [h1, ← encodeVarintAux_of_ult (shr63_ult_128 v), hcur]

private theorem vecPushBudgetInv_of_not_ult {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 : M.σ} {curCap curPtr : BitVec 64}
    {curBs : List (BitVec 8)} {fuel : Nat} {v nextV : BitVec 64} {curSt : M.σ}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs (encodeVarintAux (fuel + 1) v).length curSt)
    (h : v.ult 128#64 = false) (hshift : v >>> 7 = nextV) :
    VecPushBudgetInv M lim x st0 curCap curPtr curBs ((encodeVarintAux fuel nextV).length + 1) curSt :=
  hinv.of_rem_eq (by rw [encodeVarintAux_of_not_ult h, hshift, List.length_cons])

private theorem vecPushBudgetInv_of_ult {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 : M.σ} {curCap curPtr : BitVec 64}
    {curBs : List (BitVec 8)} {fuel : Nat} {v : BitVec 64} {curSt : M.σ}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs (encodeVarintAux (fuel + 1) v).length curSt)
    (h : v.ult 128#64 = true) :
    VecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt :=
  hinv.of_rem_eq (by rw [encodeVarintAux_of_ult h]; rfl)

/-! ## Relocatable `encode_varint` proofs (block 10, calling block 13) -/

theorem encodeVarint_gen_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (x : EncodeVarintGhost) (st0 : M.σ) (R : SepProp) (s0 : State)
    (hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced resStack s0 A lim))
    (hpc0 : s0.pc = (blkPl_10).base)
    (hrun0 : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeVarintSpecOf resStack A lim).pre (x, st0) s0 ∗ R)
    (hsp0 : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeVarintSpecOf resStack A lim).post (x, st0) s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧
          CalleeSavedPreserved s0 s')
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (encodeVarintSpecOf resStack A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp0; exact hsp0
  simp only [encodeVarintSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres s0.sp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v48, v40, v32, v24, v16, v8, ⟨hx0, hx1, hlen_bound, hfits⟩, hpre⟩
  refine ⟨((x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ A.pool lim st0 s0) ∗
      (vecU8Buf A.repAlloc x.cap x.ptr x.bs ∗ stackAt (s0.sp - 48#64) resStack),
    ?_, ?_⟩
  · convert hpre using 1; sep_ac_rfl
  refine step_encVarint_prologue_placed A lim H x.val x.v x.cap x.ptr s0.sp
    v48 v40 v32 v24 v16 v8 x.bs st0 hpc0 hrun0 rfl halign hx0 hx1 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hinv0 : VecPushBudgetInv M lim x st0 x.cap x.ptr x.bs (encodeVarintAux 10 x.val).length st0 :=
    VecPushBudgetInv.init x st0 hfits
  have hbs0 : x.bs ++ encodeVarintAux 10 x.val = x.bs ++ encodeVarint x.val := rfl
  cases hult0 : x.val.ult 128#64
  · simp only [hult0, ↓reduceIte, Bool.false_eq_true] at hpc1
    have hbs1 := encodeVarint_step_bs hbs0 hult0 rfl
    have hinv0' := vecPushBudgetInv_of_not_ult hinv0 hult0 rfl
    refine step_encVarint_s1_placed (F := FSave) A lim H hdoReserve
      x.val x.v x.cap x.ptr s0.sp v48 v40 x.bs st0 (by omega)
      (fun hcap_eq => hinv0'.fits_reserve x.v hcap_eq)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by dsimp [FSave]; sep_ac_rfl) ?_
    intro s2 cap1 ptr1 v48_1 v40_1 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 hge1 hpres1 hcap1
    have hinv1 := hinv0'.step (byte := varintContByte x.val) hge1 hpres1 hcap1
    cases hult1 : (x.val >>> 7).ult 128#64
    · simp only [hult1, ↓reduceIte, Bool.false_eq_true] at hpc2 hx0_2
      have hbs2 := encodeVarint_step_bs (nextV := x.val >>> 14) hbs1 hult1 (ushr_ushr_7 x.val 7 14)
      have hinv1' := vecPushBudgetInv_of_not_ult hinv1 hult1 (ushr_ushr_7 x.val 7 14)
      refine step_encVarint_s2_placed (F := FSave) A lim H hdoReserve
        x.val x.v cap1 ptr1 s0.sp v48_1 v40_1 _ _
        (by simp only [List.length_append, List.length_singleton]; omega)
        (fun hcap_eq => hinv1'.fits_reserve x.v hcap_eq)
        hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 rfl ?_
      intro s3 cap2 ptr2 v48_2 v40_2 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 hge2 hpres2 hcap2
      have hinv2 := hinv1'.step (byte := varintContByte (x.val >>> 7)) hge2 hpres2 hcap2
      cases hult2 : (x.val >>> 14).ult 128#64
      · simp only [hult2, ↓reduceIte, Bool.false_eq_true] at hpc3 hx0_3
        have hbs3 := encodeVarint_step_bs (nextV := x.val >>> 21) hbs2 hult2 (ushr_ushr_7 x.val 14 21)
        have hinv2' := vecPushBudgetInv_of_not_ult hinv2 hult2 (ushr_ushr_7 x.val 14 21)
        refine step_encVarint_s3_placed (F := FSave) A lim H hdoReserve
          x.val x.v cap2 ptr2 s0.sp v48_2 v40_2 _ _
          (by simp only [List.length_append, List.length_singleton]; omega)
          (fun hcap_eq => hinv2'.fits_reserve x.v hcap_eq)
          hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 rfl ?_
        intro s4 cap3 ptr3 v48_3 v40_3 hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 hge3 hpres3 hcap3
        have hinv3 := hinv2'.step (byte := varintContByte (x.val >>> 14)) hge3 hpres3 hcap3
        cases hult3 : (x.val >>> 21).ult 128#64
        · simp only [hult3, ↓reduceIte, Bool.false_eq_true] at hpc4 hx0_4
          have hbs4 := encodeVarint_step_bs (nextV := x.val >>> 28) hbs3 hult3 (ushr_ushr_7 x.val 21 28)
          have hinv3' := vecPushBudgetInv_of_not_ult hinv3 hult3 (ushr_ushr_7 x.val 21 28)
          refine step_encVarint_s4_placed (F := FSave) A lim H hdoReserve
            x.val x.v cap3 ptr3 s0.sp v48_3 v40_3 _ _
            (by simp only [List.length_append, List.length_singleton]; omega)
            (fun hcap_eq => hinv3'.fits_reserve x.v hcap_eq)
            hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 rfl ?_
          intro s5 cap4 ptr4 v48_4 v40_4 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 hge4 hpres4 hcap4
          have hinv4 := hinv3'.step (byte := varintContByte (x.val >>> 21)) hge4 hpres4 hcap4
          cases hult4 : (x.val >>> 28).ult 128#64
          · simp only [hult4, ↓reduceIte, Bool.false_eq_true] at hpc5 hx0_5
            have hbs5 := encodeVarint_step_bs (nextV := x.val >>> 35) hbs4 hult4 (ushr_ushr_7 x.val 28 35)
            have hinv4' := vecPushBudgetInv_of_not_ult hinv4 hult4 (ushr_ushr_7 x.val 28 35)
            refine step_encVarint_s5_placed (F := FSave) A lim H hdoReserve
              x.val x.v cap4 ptr4 s0.sp v48_4 v40_4 _ _
              (by simp only [List.length_append, List.length_singleton]; omega)
              (fun hcap_eq => hinv4'.fits_reserve x.v hcap_eq)
              hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 rfl ?_
            intro s6 cap5 ptr5 v48_5 v40_5 hpc6 hrun6 hsp6 htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx12_6 hcs6 hge5 hpres5 hcap5
            have hinv5 := hinv4'.step (byte := varintContByte (x.val >>> 28)) hge5 hpres5 hcap5
            cases hult5 : (x.val >>> 35).ult 128#64
            · simp only [hult5, ↓reduceIte, Bool.false_eq_true] at hpc6 hx0_6
              have hbs6 := encodeVarint_step_bs (nextV := x.val >>> 42) hbs5 hult5 (ushr_ushr_7 x.val 35 42)
              have hinv5' := vecPushBudgetInv_of_not_ult hinv5 hult5 (ushr_ushr_7 x.val 35 42)
              refine step_encVarint_s6_placed (F := FSave) A lim H hdoReserve
                x.val x.v cap5 ptr5 s0.sp v48_5 v40_5 _ _
                (by simp only [List.length_append, List.length_singleton]; omega)
                (fun hcap_eq => hinv5'.fits_reserve x.v hcap_eq)
                hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx12_6 hcs6 rfl ?_
              intro s7 cap6 ptr6 v48_6 v40_6 hpc7 hrun7 hsp7 htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx11_7 hx12_7 hcs7 hge6 hpres6 hcap6
              have hinv6 := hinv5'.step (byte := varintContByte (x.val >>> 35)) hge6 hpres6 hcap6
              cases hult6 : (x.val >>> 42).ult 128#64
              · simp only [hult6, ↓reduceIte, Bool.false_eq_true] at hpc7 hx0_7
                have hbs7 := encodeVarint_step_bs (nextV := x.val >>> 49) hbs6 hult6 (ushr_ushr_7 x.val 42 49)
                have hinv6' := vecPushBudgetInv_of_not_ult hinv6 hult6 (ushr_ushr_7 x.val 42 49)
                refine step_encVarint_s7_placed (F := FSave) A lim H hdoReserve
                  x.val x.v cap6 ptr6 s0.sp v48_6 v40_6 _ _
                  (by simp only [List.length_append, List.length_singleton]; omega)
                  (fun hcap_eq => hinv6'.fits_reserve x.v hcap_eq)
                  hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx11_7 hx12_7 hcs7 rfl ?_
                intro s8 cap7 ptr7 v48_7 v40_7 hpc8 hrun8 hsp8 htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 hge7 hpres7 hcap7
                have hinv7 := hinv6'.step (byte := varintContByte (x.val >>> 42)) hge7 hpres7 hcap7
                cases hult7 : (x.val >>> 49).ult 128#64
                · simp only [hult7, ↓reduceIte, Bool.false_eq_true] at hpc8 hx0_8
                  have hbs8 := encodeVarint_step_bs (nextV := x.val >>> 56) hbs7 hult7 (ushr_ushr_7 x.val 49 56)
                  have hinv7' := vecPushBudgetInv_of_not_ult hinv7 hult7 (ushr_ushr_7 x.val 49 56)
                  refine step_encVarint_s8_placed (F := FSave) A lim H hdoReserve
                    x.val x.v cap7 ptr7 s0.sp v48_7 v40_7 _ _
                    (by simp only [List.length_append, List.length_singleton]; omega)
                    (fun hcap_eq => hinv7'.fits_reserve x.v hcap_eq)
                    hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 rfl ?_
                  intro s9 cap8 ptr8 v48_8 v40_8 hpc9 hrun9 hsp9 htr9 hx0_9 hx1_9 hx8_9 hx9_9 hx10_9 hx12_9 hcs9 hge8 hpres8 hcap8
                  have hinv8 := hinv7'.step (byte := varintContByte (x.val >>> 49)) hge8 hpres8 hcap8
                  cases hult8 : (x.val >>> 56).ult 128#64
                  · simp only [hult8, ↓reduceIte, Bool.false_eq_true] at hpc9 hx0_9
                    have hbs9 := encodeVarint_step_bs (nextV := x.val >>> 63) hbs8 hult8 (ushr_ushr_7 x.val 56 63)
                    have hinv8' := vecPushBudgetInv_of_not_ult hinv8 hult8 (ushr_ushr_7 x.val 56 63)
                    refine step_encVarint_s9_placed
                      (F := ((s0.sp - 48#64) ↦₆₄ v48_8) ∗ ((s0.sp - 40#64) ↦₆₄ v40_8) ∗ FSave)
                      A lim H hdoReserve x.val x.v cap8 ptr8 s0.sp _ _ hult8
                      (by simp only [List.length_append, List.length_singleton]; omega)
                      (fun hcap_eq => hinv8'.fits_reserve x.v hcap_eq)
                      hpc9 hrun9 hsp9 halign htr9 hx1_9 hx8_9 hx9_9 hx10_9 hx12_9 hcs9 (by sep_ac_rfl) ?_
                    intro s10 cap9 ptr9 hpc10 hrun10 hsp10 htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10 hge9 hpres9 hcap9
                    have hinv9 := hinv8'.step (byte := varintContByte (x.val >>> 56)) hge9 hpres9 hcap9
                    exact step_encVarint_exit_placed hres A lim H hdoReserve x st0 _ 1#64 cap9 ptr9 v48_8 v40_8
                      _ (vecPushBudgetInv_of_ult hinv9 (shr63_ult_128 x.val))
                      (encodeVarint_exit_bs_s9 hbs9 hult8)
                      (by simp only [List.length_append, List.length_singleton]; omega)
                      hpc10 hrun10 hsp10 halign htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10
                      (by dsimp [FSave]; sep_ac_rfl)
                  · simp only [hult8, ↓reduceIte] at hpc9 hx0_9
                    exact step_encVarint_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 56) cap8 ptr8 v48_8 v40_8
                      _ (vecPushBudgetInv_of_ult hinv8 hult8) (encodeVarint_exit_bs hbs8 hult8)
                      (by simp only [List.length_append, List.length_singleton]; omega)
                      hpc9 hrun9 hsp9 halign htr9 hx0_9 hx1_9 hx8_9 hx9_9 hcs9 rfl
                · simp only [hult7, ↓reduceIte] at hpc8 hx0_8
                  exact step_encVarint_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 49) cap7 ptr7 v48_7 v40_7
                    _ (vecPushBudgetInv_of_ult hinv7 hult7) (encodeVarint_exit_bs hbs7 hult7)
                    (by simp only [List.length_append, List.length_singleton]; omega)
                    hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hcs8 rfl
              · simp only [hult6, ↓reduceIte] at hpc7 hx0_7
                exact step_encVarint_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 42) cap6 ptr6 v48_6 v40_6
                  _ (vecPushBudgetInv_of_ult hinv6 hult6) (encodeVarint_exit_bs hbs6 hult6)
                  (by simp only [List.length_append, List.length_singleton]; omega)
                  hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hcs7 rfl
            · simp only [hult5, ↓reduceIte] at hpc6 hx0_6
              exact step_encVarint_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 35) cap5 ptr5 v48_5 v40_5
                _ (vecPushBudgetInv_of_ult hinv5 hult5) (encodeVarint_exit_bs hbs5 hult5)
                (by simp only [List.length_append, List.length_singleton]; omega)
                hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hcs6 rfl
          · simp only [hult4, ↓reduceIte] at hpc5 hx0_5
            exact step_encVarint_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 28) cap4 ptr4 v48_4 v40_4
              _ (vecPushBudgetInv_of_ult hinv4 hult4) (encodeVarint_exit_bs hbs4 hult4)
              (by simp only [List.length_append, List.length_singleton]; omega)
              hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hcs5 rfl
        · simp only [hult3, ↓reduceIte] at hpc4 hx0_4
          exact step_encVarint_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 21) cap3 ptr3 v48_3 v40_3
            _ (vecPushBudgetInv_of_ult hinv3 hult3) (encodeVarint_exit_bs hbs3 hult3)
            (by simp only [List.length_append, List.length_singleton]; omega)
            hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hcs4 rfl
      · simp only [hult2, ↓reduceIte] at hpc3 hx0_3
        exact step_encVarint_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 14) cap2 ptr2 v48_2 v40_2
          _ (vecPushBudgetInv_of_ult hinv2 hult2) (encodeVarint_exit_bs hbs2 hult2)
          (by simp only [List.length_append, List.length_singleton]; omega)
          hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hcs3 rfl
    · simp only [hult1, ↓reduceIte] at hpc2 hx0_2
      exact step_encVarint_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 7) cap1 ptr1 v48_1 v40_1
        _ (vecPushBudgetInv_of_ult hinv1 hult1) (encodeVarint_exit_bs hbs1 hult1)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hcs2 rfl
  · simp only [hult0, ↓reduceIte] at hpc1
    exact step_encVarint_exit_placed hres A lim H hdoReserve x st0 st0 x.val x.cap x.ptr v48 v40
      x.bs (vecPushBudgetInv_of_ult hinv0 hult0) (encodeVarint_exit_bs hbs0 hult0) (by omega)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by sep_ac_rfl)

/-- Relocatable `prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]`
(Block `10`, calling Block `13`) meets `withLsCodeLoaded lsmpl (encodeVarintSpec A lim)`. -/
theorem encode_varint_placed_ok_of_doReserve [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hdoReserve : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpec M A lim))) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc0 hrun0 hpre hsp0
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨P, hP, hwp⟩ := encodeVarint_gen_placed_ok A lim H (resStack := doReserveStack)
    (by decide) x st0 R s0 (doReserve_with_placed_of_ok A lim H s0 hcl0 hdoReserve) hpc0 hrun0 hpre hsp0
  exact ⟨P, R, hP, hwp⟩

/-- Relocatable `prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]`
(Block `10`) meets `withLsCodeLoaded lsmpl (encodeVarintSpec A lim)`. -/
theorem encode_varint_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)) :=
  encode_varint_placed_ok_of_doReserve A lim H (do_reserve_placed_ok hshim halloc hrealloc)

/-- Variant of `encode_varint_placed_ok` accepting `NoOom` `HookSat` contracts directly. -/
theorem encode_varint_placed_ok_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)) :=
  encode_varint_placed_ok_of_doReserve A lim H (do_reserve_placed_ok_noOom hshim halloc hrealloc)

/-- Relocatable `prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]`
(Block `10`, calling Block `13`) meets `withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)`. -/
theorem encode_varint_placed_ok_of_doReserve_x [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hdoReserve : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpecX M A lim))) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc0 hrun0 hpre hsp0
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨P, hP, hwp⟩ := encodeVarint_gen_placed_ok A lim H (resStack := doReserveStackX)
    (by decide) x st0 R s0 (doReserve_with_placed_of_ok_x A lim H s0 hcl0 hdoReserve) hpc0 hrun0 hpre hsp0
  exact ⟨P, R, hP, hwp⟩

/-- Relocatable `prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]`
(Block `10`) meets `withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)`. -/
theorem encode_varint_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)) :=
  encode_varint_placed_ok_of_doReserve_x A lim H (do_reserve_placed_ok_x hshim halloc hrealloc)

/-- Variant of `encode_varint_placed_ok_x` accepting `NoOom` `HookSat` contracts directly. -/
theorem encode_varint_placed_ok_x_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)) :=
  encode_varint_placed_ok_of_doReserve_x A lim H (do_reserve_placed_ok_x_noOom hshim halloc hrealloc)

end LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget
