/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint4BasePlaced
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Base
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlaced
import ProofLib.SepLogic.WPp

/-!
# Relocatable Verification of `encode_varint::<Vec<u8>> [local#4]` (Block `451`)

Proves continuation-byte stages 4–8 and top-level `[LibsignalPlacement]` contracts for
`prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]` (Block `451`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Varint

open Arm64 ProofLib CryptoGames.LibsignalSession
  CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
  CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.CodeLayout
  CryptoVerification.Cli.SpqrV1.Alloc.Placed
  CryptoVerification.Cli.SpqrV1.Varint.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Continuation-byte stages 4..8 -/

theorem step_encVarint2_s4_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base + 336#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx12 : s.readReg64 .x12 = val >>> 28) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 28).ult 128#64 then (blkPl_451).base + 868#64 else (blkPl_451).base + 444#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 28).ult 128#64 then val >>> 28 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr →
      sm.readReg64 .x11 = val >>> 35 → sm.readReg64 .x12 = val >>> 28 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_451 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 21)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_451 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 28).ult 128#64 = true ∨ (val >>> 28).ult 128#64 = false := by
    cases (val >>> 28).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 21))
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 868#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 21)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 444#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 21)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 460); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine step_doReserve2_call_gen_placed A hdoReserve v curCap curPtr sp
      ((blkPl_451).base + 408#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 val) >>> 21)) |||
          4294967168#64 := by simp only [arm64_norm, zext64_trunc32_orr_mask, *]
    have hx20m' : sm.readReg64 .x20 = val >>> 28 := by simp only [arm64_norm, *]
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 21))
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 21)]) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 21)]) ∗
          ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 868#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 21)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 444#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 21)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

theorem step_encVarint2_s5_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base + 444#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 28) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 35).ult 128#64 then (blkPl_451).base + 868#64 else (blkPl_451).base + 544#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 35).ult 128#64 then val >>> 35 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr →
      sm.readReg64 .x11 = val >>> 35 → sm.readReg64 .x13 = val >>> 42 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_451 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 28)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_451 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 35).ult 128#64 = true ∨ (val >>> 35).ult 128#64 = false := by
    cases (val >>> 35).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 28))
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 868#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 28)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 544#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 28)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 460); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine step_doReserve2_call_gen_placed A hdoReserve v curCap curPtr sp
      ((blkPl_451).base + 508#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (val >>> 28)) ||| 4294967168#64 := by
      simp only [arm64_norm, zext64_trunc32_orr_mask, *]
    have hx20m' : sm.readReg64 .x20 = val >>> 35 := by simp only [arm64_norm, *]
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 28))
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 28)]) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 28)]) ∗
          ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 868#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 28)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 544#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 28)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

theorem step_encVarint2_s6_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base + 544#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx13 : s.readReg64 .x13 = val >>> 42) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 42).ult 128#64 then (blkPl_451).base + 868#64 else (blkPl_451).base + 648#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 42).ult 128#64 then val >>> 42 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x12 = val >>> 49 →
      sm.readReg64 .x13 = val >>> 42 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_451 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 35)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_451 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 42).ult 128#64 = true ∨ (val >>> 42).ult 128#64 = false := by
    cases (val >>> 42).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 35))
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 868#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 35)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 648#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 35)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 460); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine step_doReserve2_call_gen_placed A hdoReserve v curCap curPtr sp
      ((blkPl_451).base + 612#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (val >>> 35)) ||| 4294967168#64 := by
      simp only [arm64_norm, zext64_trunc32_orr_mask, *]
    have hx20m' : sm.readReg64 .x20 = val >>> 42 := by simp only [arm64_norm, *]
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 35))
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 35)]) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 35)]) ∗
          ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 868#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 35)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 648#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 35)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

theorem step_encVarint2_s7_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base + 648#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx12 : s.readReg64 .x12 = val >>> 49) (hx13 : s.readReg64 .x13 = val >>> 42)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 49).ult 128#64 then (blkPl_451).base + 868#64 else (blkPl_451).base + 684#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 49).ult 128#64 then val >>> 49 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x11 = nextPtr → sm.readReg64 .x12 = val >>> 49 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_451 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 42)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_451 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 49).ult 128#64 = true ∨ (val >>> 49).ult 128#64 = false := by
    cases (val >>> 49).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 42))
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 868#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 42)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 684#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 42)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 460); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine step_doReserve2_call_gen_placed A hdoReserve v curCap curPtr sp
      ((blkPl_451).base + 744#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (val >>> 42)) ||| 4294967168#64 := by
      simp only [arm64_norm, zext64_trunc32_orr_mask, *]
    have hx20m' : sm.readReg64 .x20 = val >>> 49 := by simp only [arm64_norm, *]
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 42))
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 42)]) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 42)]) ∗
          ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 868#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 42)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 684#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 42)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

theorem step_encVarint2_s8_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base + 684#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56) (hx11 : s.readReg64 .x11 = curPtr)
    (hx12 : s.readReg64 .x12 = val >>> 49) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 56).ult 128#64 then (blkPl_451).base + 868#64 else (blkPl_451).base + 840#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 56).ult 128#64 then val >>> 56 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x11 = nextPtr → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_451 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 49)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_451 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 56).ult 128#64 = true ∨ (val >>> 56).ult 128#64 = false := by
    cases (val >>> 56).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 49))
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 868#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 49)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 840#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 49)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 460); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine step_doReserve2_call_gen_placed A hdoReserve v curCap curPtr sp
      ((blkPl_451).base + 808#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (val >>> 49)) ||| 4294967168#64 := by
      simp only [arm64_norm, zext64_trunc32_orr_mask, *]
    have hx20m' : sm.readReg64 .x20 = val >>> 56 := by simp only [arm64_norm, *]
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 49))
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 49)]) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 49)]) ∗
          ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 868#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 49)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base + 840#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 49)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

/-! ## Main Relocatable Per-Block Contracts (Block `451` → Block `460`) -/

theorem encodeVarint2_gen_placed_ok [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (x : EncodeVarintGhost) (R : SepProp) (s0 : State)
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A))
    (hpc0 : s0.pc = (blkPl_451).base) (hrun0 : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeVarintFitSpecOf resStack A).pre x s0 ∗ R) (hsp0 : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_451 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeVarintSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp0; exact hsp0
  simp only [encodeVarintFitSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres s0.sp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v48, v40, v32, v24, v16, v8, ⟨hx0, hx1, hlen_bound⟩, hpre⟩
  refine ⟨((x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗
      (vecU8Buf A x.cap x.ptr x.bs ∗ A.pool ∗ stackAt (s0.sp - 48#64) resStack),
    ?_, ?_⟩
  · convert hpre using 1; ac_rfl
  refine step_encVarint2_prologue_placed H x.val x.v x.cap x.ptr s0.sp
    v48 v40 v32 v24 v16 v8 x.bs hpc0 hrun0 rfl halign hx0 hx1 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hinv0 : VecReserveInv x.cap x.ptr x.cap x.ptr x.bs := VecReserveInv.refl x.cap x.ptr x.bs
  have hbs0 : x.bs ++ encodeVarintAux 10 x.val = x.bs ++ encodeVarint x.val := rfl
  cases hult0 : x.val.ult 128#64
  · simp only [hult0, ↓reduceIte, Bool.false_eq_true] at hpc1
    have hbs1 := encodeVarint_step_bs hbs0 hult0 rfl
    refine step_encVarint2_s1_placed A H (F := FSave) hdoReserve
      x.val x.v x.cap x.ptr s0.sp v48 v40 x.bs (stage_len_lt_of_step hlen_bound hinv0 hbs0)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 cap1 ptr1 v48_1 v40_1 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 hge1 hpres1
    have hinv1 := hinv0.step (byte := varintContByte x.val) hge1 hpres1
    cases hult1 : (x.val >>> 7).ult 128#64
    · simp only [hult1, ↓reduceIte, Bool.false_eq_true] at hpc2 hx0_2
      have hbs2 := encodeVarint_step_bs (nextV := x.val >>> 14) hbs1 hult1 (ushr_ushr_7 x.val 7 14)
      refine step_encVarint2_s2_placed A H (F := FSave) hdoReserve
        x.val x.v cap1 ptr1 s0.sp v48_1 v40_1 _ (stage_len_lt_of_step hlen_bound hinv1 hbs1)
        hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 rfl ?_
      intro s3 cap2 ptr2 v48_2 v40_2 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 hge2 hpres2
      have hinv2 := hinv1.step (byte := varintContByte (x.val >>> 7)) hge2 hpres2
      cases hult2 : (x.val >>> 14).ult 128#64
      · simp only [hult2, ↓reduceIte, Bool.false_eq_true] at hpc3 hx0_3
        have hbs3 := encodeVarint_step_bs (nextV := x.val >>> 21) hbs2 hult2 (ushr_ushr_7 x.val 14 21)
        refine step_encVarint2_s3_placed A H (F := FSave) hdoReserve
          x.val x.v cap2 ptr2 s0.sp v48_2 v40_2 _ (stage_len_lt_of_step hlen_bound hinv2 hbs2)
          hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 rfl ?_
        intro s4 cap3 ptr3 v48_3 v40_3 hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 hge3 hpres3
        have hinv3 := hinv2.step (byte := varintContByte (x.val >>> 14)) hge3 hpres3
        cases hult3 : (x.val >>> 21).ult 128#64
        · simp only [hult3, ↓reduceIte, Bool.false_eq_true] at hpc4 hx0_4
          have hbs4 := encodeVarint_step_bs (nextV := x.val >>> 28) hbs3 hult3 (ushr_ushr_7 x.val 21 28)
          refine step_encVarint2_s4_placed A H (F := FSave) hdoReserve
            x.val x.v cap3 ptr3 s0.sp v48_3 v40_3 _ (stage_len_lt_of_step hlen_bound hinv3 hbs3)
            hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 rfl ?_
          intro s5 cap4 ptr4 v48_4 v40_4 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 hge4 hpres4
          have hinv4 := hinv3.step (byte := varintContByte (x.val >>> 21)) hge4 hpres4
          cases hult4 : (x.val >>> 28).ult 128#64
          · simp only [hult4, ↓reduceIte, Bool.false_eq_true] at hpc5 hx0_5
            have hbs5 := encodeVarint_step_bs (nextV := x.val >>> 35) hbs4 hult4 (ushr_ushr_7 x.val 28 35)
            refine step_encVarint2_s5_placed A H (F := FSave) hdoReserve
              x.val x.v cap4 ptr4 s0.sp v48_4 v40_4 _ (stage_len_lt_of_step hlen_bound hinv4 hbs4)
              hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 rfl ?_
            intro s6 cap5 ptr5 v48_5 v40_5 hpc6 hrun6 hsp6 htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx13_6 hcs6 hge5 hpres5
            have hinv5 := hinv4.step (byte := varintContByte (x.val >>> 28)) hge5 hpres5
            cases hult5 : (x.val >>> 35).ult 128#64
            · simp only [hult5, ↓reduceIte, Bool.false_eq_true] at hpc6 hx0_6
              have hbs6 := encodeVarint_step_bs (nextV := x.val >>> 42) hbs5 hult5 (ushr_ushr_7 x.val 35 42)
              refine step_encVarint2_s6_placed A H (F := FSave) hdoReserve
                x.val x.v cap5 ptr5 s0.sp v48_5 v40_5 _ (stage_len_lt_of_step hlen_bound hinv5 hbs5)
                hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx13_6 hcs6 rfl ?_
              intro s7 cap6 ptr6 v48_6 v40_6 hpc7 hrun7 hsp7 htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx12_7 hx13_7 hcs7 hge6 hpres6
              have hinv6 := hinv5.step (byte := varintContByte (x.val >>> 35)) hge6 hpres6
              cases hult6 : (x.val >>> 42).ult 128#64
              · simp only [hult6, ↓reduceIte, Bool.false_eq_true] at hpc7 hx0_7
                have hbs7 := encodeVarint_step_bs (nextV := x.val >>> 49) hbs6 hult6 (ushr_ushr_7 x.val 42 49)
                refine step_encVarint2_s7_placed A H (F := FSave) hdoReserve
                  x.val x.v cap6 ptr6 s0.sp v48_6 v40_6 _ (stage_len_lt_of_step hlen_bound hinv6 hbs6)
                  hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx12_7 hx13_7 hcs7 rfl ?_
                intro s8 cap7 ptr7 v48_7 v40_7 hpc8 hrun8 hsp8 htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 hge7 hpres7
                have hinv7 := hinv6.step (byte := varintContByte (x.val >>> 42)) hge7 hpres7
                cases hult7 : (x.val >>> 49).ult 128#64
                · simp only [hult7, ↓reduceIte, Bool.false_eq_true] at hpc8 hx0_8
                  have hbs8 := encodeVarint_step_bs (nextV := x.val >>> 56) hbs7 hult7 (ushr_ushr_7 x.val 49 56)
                  refine step_encVarint2_s8_placed A H (F := FSave) hdoReserve
                    x.val x.v cap7 ptr7 s0.sp v48_7 v40_7 _ (stage_len_lt_of_step hlen_bound hinv7 hbs7)
                    hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 rfl ?_
                  intro s9 cap8 ptr8 v48_8 v40_8 hpc9 hrun9 hsp9 htr9 hx0_9 hx1_9 hx8_9 hx9_9 hx10_9 hx11_9 hcs9 hge8 hpres8
                  have hinv8 := hinv7.step (byte := varintContByte (x.val >>> 49)) hge8 hpres8
                  cases hult8 : (x.val >>> 56).ult 128#64
                  · simp only [hult8, ↓reduceIte, Bool.false_eq_true] at hpc9 hx0_9
                    have hbs9 := encodeVarint_step_bs (nextV := x.val >>> 63) hbs8 hult8 (ushr_ushr_7 x.val 56 63)
                    refine step_encVarint2_s9_placed A H (F := ((s0.sp - 48#64) ↦₆₄ v48_8) ∗ ((s0.sp - 40#64) ↦₆₄ v40_8) ∗ FSave)
                      hdoReserve x.val x.v cap8 ptr8 s0.sp _ hult8
                      (stage_len_lt_of_step hlen_bound hinv8 hbs8)
                      hpc9 hrun9 hsp9 halign htr9 hx1_9 hx8_9 hx9_9 hx10_9 hx11_9 hcs9 (by ac_rfl) ?_
                    intro s10 cap9 ptr9 hpc10 hrun10 hsp10 htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10 hge9 hpres9
                    have hinv9 := hinv8.step (byte := varintContByte (x.val >>> 56)) hge9 hpres9
                    exact step_encVarint2_exit_placed hres A H hdoReserve x 1#64 cap9 ptr9 v48_8 v40_8 _ hinv9
                      (encodeVarint_exit_bs_s9 hbs9 hult8)
                      (stage_len_lt_of_exit hlen_bound hinv9 (encodeVarint_exit_bs_s9 hbs9 hult8))
                      hpc10 hrun10 hsp10 halign htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10 (by dsimp [FSave]; ac_rfl)
                  · simp only [hult8, ↓reduceIte] at hpc9 hx0_9
                    exact step_encVarint2_exit_placed hres A H hdoReserve x (x.val >>> 56) cap8 ptr8 v48_8 v40_8 _ hinv8
                      (encodeVarint_exit_bs hbs8 hult8)
                      (stage_len_lt_of_exit hlen_bound hinv8 (encodeVarint_exit_bs hbs8 hult8))
                      hpc9 hrun9 hsp9 halign htr9 hx0_9 hx1_9 hx8_9 hx9_9 hcs9 rfl
                · simp only [hult7, ↓reduceIte] at hpc8 hx0_8
                  exact step_encVarint2_exit_placed hres A H hdoReserve x (x.val >>> 49) cap7 ptr7 v48_7 v40_7 _ hinv7
                    (encodeVarint_exit_bs hbs7 hult7)
                    (stage_len_lt_of_exit hlen_bound hinv7 (encodeVarint_exit_bs hbs7 hult7))
                    hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hcs8 rfl
              · simp only [hult6, ↓reduceIte] at hpc7 hx0_7
                exact step_encVarint2_exit_placed hres A H hdoReserve x (x.val >>> 42) cap6 ptr6 v48_6 v40_6 _ hinv6
                  (encodeVarint_exit_bs hbs6 hult6)
                  (stage_len_lt_of_exit hlen_bound hinv6 (encodeVarint_exit_bs hbs6 hult6))
                  hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hcs7 rfl
            · simp only [hult5, ↓reduceIte] at hpc6 hx0_6
              exact step_encVarint2_exit_placed hres A H hdoReserve x (x.val >>> 35) cap5 ptr5 v48_5 v40_5 _ hinv5
                (encodeVarint_exit_bs hbs5 hult5)
                (stage_len_lt_of_exit hlen_bound hinv5 (encodeVarint_exit_bs hbs5 hult5))
                hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hcs6 rfl
          · simp only [hult4, ↓reduceIte] at hpc5 hx0_5
            exact step_encVarint2_exit_placed hres A H hdoReserve x (x.val >>> 28) cap4 ptr4 v48_4 v40_4 _ hinv4
              (encodeVarint_exit_bs hbs4 hult4)
              (stage_len_lt_of_exit hlen_bound hinv4 (encodeVarint_exit_bs hbs4 hult4))
              hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hcs5 rfl
        · simp only [hult3, ↓reduceIte] at hpc4 hx0_4
          exact step_encVarint2_exit_placed hres A H hdoReserve x (x.val >>> 21) cap3 ptr3 v48_3 v40_3 _ hinv3
            (encodeVarint_exit_bs hbs3 hult3)
            (stage_len_lt_of_exit hlen_bound hinv3 (encodeVarint_exit_bs hbs3 hult3))
            hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hcs4 rfl
      · simp only [hult2, ↓reduceIte] at hpc3 hx0_3
        exact step_encVarint2_exit_placed hres A H hdoReserve x (x.val >>> 14) cap2 ptr2 v48_2 v40_2 _ hinv2
          (encodeVarint_exit_bs hbs2 hult2)
          (stage_len_lt_of_exit hlen_bound hinv2 (encodeVarint_exit_bs hbs2 hult2))
          hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hcs3 rfl
    · simp only [hult1, ↓reduceIte] at hpc2 hx0_2
      exact step_encVarint2_exit_placed hres A H hdoReserve x (x.val >>> 7) cap1 ptr1 v48_1 v40_1 _ hinv1
        (encodeVarint_exit_bs hbs1 hult1)
        (stage_len_lt_of_exit hlen_bound hinv1 (encodeVarint_exit_bs hbs1 hult1))
        hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hcs2 rfl
  · simp only [hult0, ↓reduceIte] at hpc1
    exact step_encVarint2_exit_placed hres A H hdoReserve x x.val x.cap x.ptr v48 v40 x.bs hinv0
      (encodeVarint_exit_bs hbs0 hult0)
      (stage_len_lt_of_exit hlen_bound hinv0 (encodeVarint_exit_bs hbs0 hult0))
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by ac_rfl)

theorem encodeVarint2_fit_placed_ok_of_doReserve [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64) (A : RustAlloc) (H : String → Option (State → State))
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460)
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A))) :
    subroutine_ok (lsProg_451 H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf resStack A)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre hsp0
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcode0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := encodeVarint2_gen_placed_ok A H hres x R s0
    (doReserve2_with_placed_of_ok A s0 hcode0 hdoReserve) hpc0 hrun0 hpre hsp0
  exact ⟨P, R, hP, hwp⟩

theorem encode_varint2_fit_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_451).rebase (blkPl_451).base H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintFitSpec A)) :=
  encodeVarint2_fit_placed_ok_of_doReserve (resStack := doReserveStack) (by decide) A H
    (ls_subroutine_ok_of_block (callerProg := lsProg_451 H) (do_reserve2_placed_ok h_panic hshim halloc hrealloc))

theorem encode_varint2_fit_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_451).rebase (blkPl_451).base H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecX A)) :=
  encodeVarint2_fit_placed_ok_of_doReserve (resStack := doReserveStackX) (by decide) A H
    (ls_subroutine_ok_of_block (callerProg := lsProg_451 H) (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))

private theorem encodeVarint2SpecOf_of_encodeVarintFitSpecOf [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {resStack : Nat} {A : RustAlloc}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf resStack A))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (encodeVarintSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
  refine ⟨hpre.1, ?_⟩
  have hpre2 := hpre.2
  simp only [encodeVarintSpecOf, encodeVarintFitSpecOf, sepConj_assoc, satisfies_pure_sepConj] at hpre2 ⊢
  exact ⟨⟨hpre2.1.1, hpre2.1.2.1,
    hpre2.1.2.2.imp (fun hle => by have := (SpqrV1.Varint.encodeVarint_length_bounds x.val).2; omega) id⟩, hpre2.2⟩

theorem encode_varint2_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_451).rebase (blkPl_451).base H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)) :=
  encodeVarint2SpecOf_of_encodeVarintFitSpecOf
    (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc)

theorem encode_varint2_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_451).rebase (blkPl_451).base H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A)) :=
  encodeVarint2SpecOf_of_encodeVarintFitSpecOf
    (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc)

abbrev encode_varint_2_fit_placed_ok := @encode_varint2_fit_placed_ok
abbrev encode_varint_2_fit_placed_ok_x := @encode_varint2_fit_placed_ok_x
abbrev encode_varint_2_placed_ok := @encode_varint2_placed_ok
abbrev encode_varint_2_placed_ok_x := @encode_varint2_placed_ok_x
abbrev encodeVarint2_fit_placed_ok := @encode_varint2_fit_placed_ok
abbrev encodeVarint2_fit_placed_ok_x := @encode_varint2_fit_placed_ok_x
abbrev encodeVarint2_placed_ok := @encode_varint2_placed_ok
abbrev encodeVarint2_placed_ok_x := @encode_varint2_placed_ok_x

end CryptoVerification.Cli.SpqrV1.Varint
