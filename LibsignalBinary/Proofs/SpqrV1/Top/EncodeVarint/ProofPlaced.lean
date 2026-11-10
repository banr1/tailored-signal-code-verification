/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Base
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BasePlaced
import ProofLib.SepLogic.WPp

/-!
# Relocatable Proof of `spqr::encode_varint` (Block `326`, 164 insns)
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.EncodeVarint

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1
  (encodeVarintLoop MAX_VARINT_BYTES_LEN GrowOneCall newCapU8 growOneU8Spec growOneU8Name SpqrHooks MlKem)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Placed
open CryptoVerification.SpqrV1.Alloc

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Continuation-Byte Stages 3..9 -/

/-- Stage 3 (`+204..+256`): appends `varintContByte (val >>> 14)` and branches on
`(val >>> 21).ult 128#64` to `+256` (`exit3`) or `+276` (Stage 4), setting `x23 = val >>> 28`. -/
theorem step_spqrEncVarint_placed_s3 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (horig : origLen + 2#64 = BitVec.ofNat 64 curBs.length)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 21).ult 128#64 then
        (blkPl_326).base + 256#64
      else
        (blkPl_326).base + 276#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length →
      sm.readReg64 .x22 = origLen →
      sm.readReg64 .x23 = val >>> 28 →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 14)]) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 21).ult 128#64 = true ∨ (val >>> 21).ult 128#64 = false := by
    cases (val >>> 21).ult 128#64 <;> simp
  have hlen1 := origLen_add_step (varintContByte (val >>> 14)) 2#64 3#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 256#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 14)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 276#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 14)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 619)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_growOneU8_placed_call A abs hgrow v curCap curPtr sp
      ((blkPl_326).base + 232#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m _ hx24m _ hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
    have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
    have hx24m' : BitVec.zeroExtend 8 (sm.readReg64 .x24) = varintContByte (val >>> 14) := by
      rw [hx24m]; simp only [arm64_norm, *]
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq := grow_frame_reassoc A v newCap p' sp curBs (varintContByte (val >>> 14)) F
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 256#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 14)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 276#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 14)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

/-- Stage 4 (`+276..+328`): appends `varintContByte (val >>> 21)` and branches on
`(val >>> 28).ult 128#64` to `+328` (`exit_328`) or `+348` (Stage 5), setting `x24 = val >>> 35`. -/
theorem step_spqrEncVarint_placed_s4 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (horig : origLen + 3#64 = BitVec.ofNat 64 curBs.length)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 276#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hx23 : s.readReg64 .x23 = val >>> 28)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 28).ult 128#64 then
        (blkPl_326).base + 328#64
      else
        (blkPl_326).base + 348#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length →
      sm.readReg64 .x22 = origLen →
      sm.readReg64 .x23 = val >>> 28 →
      sm.readReg64 .x24 = val >>> 35 →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 21)]) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 28).ult 128#64 = true ∨ (val >>> 28).ult 128#64 = false := by
    cases (val >>> 28).ult 128#64 <;> simp
  have hlen1 := origLen_add_step (varintContByte (val >>> 21)) 3#64 4#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 328#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 21)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 348#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 21)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 619)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_growOneU8_placed_call A abs hgrow v curCap curPtr sp
      ((blkPl_326).base + 304#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hx23m _ hx25m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
    have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
    have hx23m' : sm.readReg64 .x23 = val >>> 28 := by simp only [arm64_norm, *]
    have hx25m' : BitVec.zeroExtend 8 (sm.readReg64 .x25) = varintContByte (val >>> 21) := by
      rw [hx25m]; simp only [arm64_norm, *]
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq := grow_frame_reassoc A v newCap p' sp curBs (varintContByte (val >>> 21)) F
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 328#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 21)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 348#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 21)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

/-- Stage 5 (`+348..+396`): appends `varintContByte (val >>> 28)` and branches on
`(val >>> 35).ult 128#64` to `+396` (`exit_396`) or `+460` (Stage 6), setting `x23 = val >>> 42`. -/
theorem step_spqrEncVarint_placed_s5 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (horig : origLen + 4#64 = BitVec.ofNat 64 curBs.length)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 348#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hx23 : s.readReg64 .x23 = val >>> 28)
    (hx24 : s.readReg64 .x24 = val >>> 35)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 35).ult 128#64 then
        (blkPl_326).base + 396#64
      else
        (blkPl_326).base + 460#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length →
      sm.readReg64 .x22 = origLen →
      sm.readReg64 .x23 = val >>> 42 →
      sm.readReg64 .x24 = val >>> 35 →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 28)]) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 35).ult 128#64 = true ∨ (val >>> 35).ult 128#64 = false := by
    cases (val >>> 35).ult 128#64 <;> simp
  have hlen1 := origLen_add_step (varintContByte (val >>> 28)) 4#64 5#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 396#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 28)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 460#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 28)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 619)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_growOneU8_placed_call A abs hgrow v curCap curPtr sp
      ((blkPl_326).base + 372#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m _ hx24m hx25m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
    have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
    have hx24m' : sm.readReg64 .x24 = val >>> 35 := by simp only [arm64_norm, *]
    have hx25m' : BitVec.zeroExtend 8 (sm.readReg64 .x25) = varintContByte (val >>> 28) := by
      rw [hx25m]; simp only [arm64_norm, *]
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq := grow_frame_reassoc A v newCap p' sp curBs (varintContByte (val >>> 28)) F
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 396#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 28)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 460#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 28)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

/-- Stage 6 (`+460..+508`): appends `varintContByte (val >>> 35)` and branches on
`(val >>> 42).ult 128#64` to `+328` (`exit_328`) or `+508` (Stage 7), setting `x24 = val >>> 49`. -/
theorem step_spqrEncVarint_placed_s6 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (horig : origLen + 5#64 = BitVec.ofNat 64 curBs.length)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 460#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hx23 : s.readReg64 .x23 = val >>> 42)
    (hx24 : s.readReg64 .x24 = val >>> 35)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 42).ult 128#64 then
        (blkPl_326).base + 328#64
      else
        (blkPl_326).base + 508#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length →
      sm.readReg64 .x22 = origLen →
      sm.readReg64 .x23 = val >>> 42 →
      sm.readReg64 .x24 = val >>> 49 →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 35)]) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 42).ult 128#64 = true ∨ (val >>> 42).ult 128#64 = false := by
    cases (val >>> 42).ult 128#64 <;> simp
  have hlen1 := origLen_add_step (varintContByte (val >>> 35)) 5#64 6#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 328#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 35)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 508#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 35)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 619)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_growOneU8_placed_call A abs hgrow v curCap curPtr sp
      ((blkPl_326).base + 484#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hx23m _ hx25m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
    have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
    have hx23m' : sm.readReg64 .x23 = val >>> 42 := by simp only [arm64_norm, *]
    have hx25m' : BitVec.zeroExtend 8 (sm.readReg64 .x25) = varintContByte (val >>> 35) := by
      rw [hx25m]; simp only [arm64_norm, *]
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq := grow_frame_reassoc A v newCap p' sp curBs (varintContByte (val >>> 35)) F
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 328#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 35)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 508#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 35)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

/-- Stage 7 (`+508..+556`): appends `varintContByte (val >>> 42)` and branches on
`(val >>> 49).ult 128#64` to `+396` (`exit_396`) or `+556` (Stage 8), setting `x23 = val >>> 56`. -/
theorem step_spqrEncVarint_placed_s7 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (horig : origLen + 6#64 = BitVec.ofNat 64 curBs.length)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hx23 : s.readReg64 .x23 = val >>> 42)
    (hx24 : s.readReg64 .x24 = val >>> 49)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 49).ult 128#64 then
        (blkPl_326).base + 396#64
      else
        (blkPl_326).base + 556#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length →
      sm.readReg64 .x22 = origLen →
      sm.readReg64 .x23 = val >>> 56 →
      sm.readReg64 .x24 = val >>> 49 →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 42)]) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 49).ult 128#64 = true ∨ (val >>> 49).ult 128#64 = false := by
    cases (val >>> 49).ult 128#64 <;> simp
  have hlen1 := origLen_add_step (varintContByte (val >>> 42)) 6#64 7#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 396#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 42)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 556#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 42)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 619)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_growOneU8_placed_call A abs hgrow v curCap curPtr sp
      ((blkPl_326).base + 532#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m _ hx24m hx25m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
    have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
    have hx24m' : sm.readReg64 .x24 = val >>> 49 := by simp only [arm64_norm, *]
    have hx25m' : BitVec.zeroExtend 8 (sm.readReg64 .x25) = varintContByte (val >>> 42) := by
      rw [hx25m]; simp only [arm64_norm, *]
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq := grow_frame_reassoc A v newCap p' sp curBs (varintContByte (val >>> 42)) F
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 396#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 42)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 556#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 42)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

/-- Stage 8 (`+556..+600`): appends `varintContByte (val >>> 49)` and branches on
`(val >>> 56).ult 128#64` (via `tbz x20, #63`) to `+328` (`exit_328`) or `+600` (Stage 9). -/
theorem step_spqrEncVarint_placed_s8 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (horig : origLen + 7#64 = BitVec.ofNat 64 curBs.length)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 556#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hx23 : s.readReg64 .x23 = val >>> 56)
    (hx24 : s.readReg64 .x24 = val >>> 49)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 56).ult 128#64 then
        (blkPl_326).base + 328#64
      else
        (blkPl_326).base + 600#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length →
      sm.readReg64 .x22 = origLen →
      sm.readReg64 .x23 = val >>> 56 →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 49)]) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 56).ult 128#64 = true ∨ (val >>> 56).ult 128#64 = false := by
    cases (val >>> 56).ult 128#64 <;> simp
  have hlen1 := origLen_add_step (varintContByte (val >>> 49)) 7#64 8#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 328#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 49)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 600#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 49)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 619)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_growOneU8_placed_call A abs hgrow v curCap curPtr sp
      ((blkPl_326).base + 580#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hx23m hx24m _ hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
    have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
    have hx23m' : sm.readReg64 .x23 = val >>> 56 := by simp only [arm64_norm, *]
    have hx24m' : BitVec.zeroExtend 8 (sm.readReg64 .x24) = varintContByte (val >>> 49) := by
      rw [hx24m]; simp only [arm64_norm, *]
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq := grow_frame_reassoc A v newCap p' sp curBs (varintContByte (val >>> 49)) F
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 328#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 49)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 600#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 49)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

/-- Stage 9 (`+600..+640`): under `(val >>> 56).ult 128#64 = false`,
appends `varintContByte (val >>> 56)` and exits to `+640` (`exit9`) with `x20 = 1#64`. -/
theorem step_spqrEncVarint_placed_s9 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (horig : origLen + 8#64 = BitVec.ofNat 64 curBs.length)
    (hnot_ult : (val >>> 56).ult 128#64 = false)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 600#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hx23 : s.readReg64 .x23 = val >>> 56)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_326).base + 640#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = 1#64 →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 56)]).length →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 56)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 56)]) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hbyte := contByte9_contByte_eq val hnot_ult
  have hlen1 := origLen_add_step (varintContByte (val >>> 56)) 8#64 9#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 640#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 56)) hlt]
    exact hnext _ curCap curPtr
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 619)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_growOneU8_placed_call A abs hgrow v curCap curPtr sp
      ((blkPl_326).base + 620#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m _ hx21m hx22m hx23m _ _ hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
    have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
    have hx23m_val : sm.readReg64 .x23 = val >>> 56 := by simp only [arm64_norm, *]
    have hx23m' : BitVec.zeroExtend 8 (sm.readReg64 .x23) = varintContByte (val >>> 56) := by
      rw [hx23m_val, hbyte]
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq := grow_frame_reassoc A v newCap p' sp curBs (varintContByte (val >>> 56)) F
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 640#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step2
    rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 56)) hnew_gt, hGoalEq]
    exact hnext _ newCap p'
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      hnew_ge (fun h => absurd h hlt)

private theorem encodeVarint_exit_bs_s9 {v : BitVec 64} {bs rhs : List (BitVec 8)}
    (hcur : bs ++ encodeVarintAux 1 (v >>> 63) = rhs)
    (h : (v >>> 56).ult 128#64 = false) :
    bs ++ [(1#64 : BitVec 64).setWidth 8] = rhs := by
  have h1 : (1#64 : BitVec 64) = v >>> 63 := contByte9_shr63_eq v h
  rw [h1, ← encodeVarintAux_of_ult (shr63_ult_128 v), hcur]

private theorem origLen_step1 (bs : List (BitVec 8)) (byte : BitVec 8) :
    BitVec.ofNat 64 bs.length + 1#64 = BitVec.ofNat 64 (bs ++ [byte]).length :=
  bv_len_add_one bs byte

/-! ## Main Theorems -/

/-- `spqr::encode_varint` (Block `326`, 164 instructions) satisfies `spqrEncodeVarintSpecX A`
on `(blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)`. -/
theorem spqrEncodeVarint_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    (hgrow : GrowOneU8PlacedOkExt A abs) :
    SpqrEncodeVarintPlacedOkExt A abs := by
  unfold SpqrEncodeVarintPlacedOkExt
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre hsp0
  have ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have hgrow : GrowOneU8StepOk s0 A abs := growOneU8_stepOk_of_cl hcl0 hgrow
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp0; exact hsp0
  simp only [spqrEncodeVarintSpecX, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_spqrEncodeVarint_eq s0.sp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, ⟨hx0, hx1, hlen_bound⟩, hpre⟩
  refine ⟨((x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗
      ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗
      (vecU8Buf A x.cap x.ptr x.bs ∗ A.pool ∗ stackAt (s0.sp - 80#64) extHookStack),
    R, ?_, ?_⟩
  · convert hpre using 1; ac_rfl
  refine step_spqrEncVarint_placed_prologue abs x.val x.v x.cap x.ptr s0.sp
    v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 x.bs hpc0 hrun0 rfl halign hx0 hx1 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx22_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hinv0 : VecReserveInv x.cap x.ptr x.cap x.ptr x.bs := VecReserveInv.refl x.cap x.ptr x.bs
  have hbs0 : x.bs ++ encodeVarintAux 10 x.val = x.bs ++ encodeVarint x.val := rfl
  cases hult0 : x.val.ult 128#64
  · simp only [hult0, ↓reduceIte, Bool.false_eq_true] at hpc1
    have hbs1 := encodeVarint_step_bs hbs0 hult0 rfl
    refine step_spqrEncVarint_placed_s1 (x := x) (F := FSave) A abs hgrow
      x.val x.v x.cap x.ptr s0.sp x.bs (by omega)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx22_1 hcs1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2 hge1 hpres1
    have hinv1 := hinv0.step (byte := varintContByte x.val) hge1 hpres1
    have horig1 := origLen_step1 x.bs (varintContByte x.val)
    cases hult1 : (x.val >>> 7).ult 128#64
    · simp only [hult1, ↓reduceIte, Bool.false_eq_true] at hpc2
      have hbs2 := encodeVarint_step_bs (nextV := x.val >>> 14) hbs1 hult1 (ushr_ushr_7 x.val 7 14)
      refine step_spqrEncVarint_placed_s2 (x := x) (F := FSave) A abs hgrow
        x.val x.v (BitVec.ofNat 64 x.bs.length) cap1 ptr1 s0.sp _ horig1
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2 rfl ?_
      intro s3 cap2 ptr2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hcs3 hge2 hpres2
      have hinv2 := hinv1.step (byte := varintContByte (x.val >>> 7)) hge2 hpres2
      have horig2 := origLen_add_step (varintContByte (x.val >>> 7)) 1#64 2#64 rfl horig1
      cases hult2 : (x.val >>> 14).ult 128#64
      · simp only [hult2, ↓reduceIte, Bool.false_eq_true] at hpc3
        have hbs3 := encodeVarint_step_bs (nextV := x.val >>> 21) hbs2 hult2 (ushr_ushr_7 x.val 14 21)
        refine step_spqrEncVarint_placed_s3 (x := x) (F := FSave) A abs hgrow
          x.val x.v (BitVec.ofNat 64 x.bs.length) cap2 ptr2 s0.sp _ horig2
          (by simp only [List.length_append, List.length_singleton]; omega)
          hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hx21_3 hx22_3 hcs3 rfl ?_
        intro s4 cap3 ptr3 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hcs4 hge3 hpres3
        have hinv3 := hinv2.step (byte := varintContByte (x.val >>> 14)) hge3 hpres3
        have horig3 := origLen_add_step (varintContByte (x.val >>> 14)) 2#64 3#64 rfl horig2
        cases hult3 : (x.val >>> 21).ult 128#64
        · simp only [hult3, ↓reduceIte, Bool.false_eq_true] at hpc4
          have hbs4 := encodeVarint_step_bs (nextV := x.val >>> 28) hbs3 hult3 (ushr_ushr_7 x.val 21 28)
          refine step_spqrEncVarint_placed_s4 (x := x) (F := FSave) A abs hgrow
            x.val x.v (BitVec.ofNat 64 x.bs.length) cap3 ptr3 s0.sp _ horig3
            (by simp only [List.length_append, List.length_singleton]; omega)
            hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hcs4 rfl ?_
          intro s5 cap4 ptr4 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hcs5 hge4 hpres4
          have hinv4 := hinv3.step (byte := varintContByte (x.val >>> 21)) hge4 hpres4
          have horig4 := origLen_add_step (varintContByte (x.val >>> 21)) 3#64 4#64 rfl horig3
          cases hult4 : (x.val >>> 28).ult 128#64
          · simp only [hult4, ↓reduceIte, Bool.false_eq_true] at hpc5
            have hbs5 := encodeVarint_step_bs (nextV := x.val >>> 35) hbs4 hult4 (ushr_ushr_7 x.val 28 35)
            refine step_spqrEncVarint_placed_s5 (x := x) (F := FSave) A abs hgrow
              x.val x.v (BitVec.ofNat 64 x.bs.length) cap4 ptr4 s0.sp _ horig4
              (by simp only [List.length_append, List.length_singleton]; omega)
              hpc5 hrun5 hsp5 halign htr5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hcs5 rfl ?_
            intro s6 cap5 ptr5 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hcs6 hge5 hpres5
            have hinv5 := hinv4.step (byte := varintContByte (x.val >>> 28)) hge5 hpres5
            have horig5 := origLen_add_step (varintContByte (x.val >>> 28)) 4#64 5#64 rfl horig4
            cases hult5 : (x.val >>> 35).ult 128#64
            · simp only [hult5, ↓reduceIte, Bool.false_eq_true] at hpc6
              have hbs6 := encodeVarint_step_bs (nextV := x.val >>> 42) hbs5 hult5 (ushr_ushr_7 x.val 35 42)
              refine step_spqrEncVarint_placed_s6 (x := x) (F := FSave) A abs hgrow
                x.val x.v (BitVec.ofNat 64 x.bs.length) cap5 ptr5 s0.sp _ horig5
                (by simp only [List.length_append, List.length_singleton]; omega)
                hpc6 hrun6 hsp6 halign htr6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hcs6 rfl ?_
              intro s7 cap6 ptr6 hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hx21_7 hx22_7 hx23_7 hx24_7 hcs7 hge6 hpres6
              have hinv6 := hinv5.step (byte := varintContByte (x.val >>> 35)) hge6 hpres6
              have horig6 := origLen_add_step (varintContByte (x.val >>> 35)) 5#64 6#64 rfl horig5
              cases hult6 : (x.val >>> 42).ult 128#64
              · simp only [hult6, ↓reduceIte, Bool.false_eq_true] at hpc7
                have hbs7 := encodeVarint_step_bs (nextV := x.val >>> 49) hbs6 hult6 (ushr_ushr_7 x.val 42 49)
                refine step_spqrEncVarint_placed_s7 (x := x) (F := FSave) A abs hgrow
                  x.val x.v (BitVec.ofNat 64 x.bs.length) cap6 ptr6 s0.sp _ horig6
                  (by simp only [List.length_append, List.length_singleton]; omega)
                  hpc7 hrun7 hsp7 halign htr7 hx19_7 hx20_7 hx21_7 hx22_7 hx23_7 hx24_7 hcs7 rfl ?_
                intro s8 cap7 ptr7 hpc8 hrun8 hsp8 htr8 hx19_8 hx20_8 hx21_8 hx22_8 hx23_8 hx24_8 hcs8 hge7 hpres7
                have hinv7 := hinv6.step (byte := varintContByte (x.val >>> 42)) hge7 hpres7
                have horig7 := origLen_add_step (varintContByte (x.val >>> 42)) 6#64 7#64 rfl horig6
                cases hult7 : (x.val >>> 49).ult 128#64
                · simp only [hult7, ↓reduceIte, Bool.false_eq_true] at hpc8
                  have hbs8 := encodeVarint_step_bs (nextV := x.val >>> 56) hbs7 hult7 (ushr_ushr_7 x.val 49 56)
                  refine step_spqrEncVarint_placed_s8 (x := x) (F := FSave) A abs hgrow
                    x.val x.v (BitVec.ofNat 64 x.bs.length) cap7 ptr7 s0.sp _ horig7
                    (by simp only [List.length_append, List.length_singleton]; omega)
                    hpc8 hrun8 hsp8 halign htr8 hx19_8 hx20_8 hx21_8 hx22_8 hx23_8 hx24_8 hcs8 rfl ?_
                  intro s9 cap8 ptr8 hpc9 hrun9 hsp9 htr9 hx19_9 hx20_9 hx21_9 hx22_9 hx23_9 hcs9 hge8 hpres8
                  have hinv8 := hinv7.step (byte := varintContByte (x.val >>> 49)) hge8 hpres8
                  have horig8 := origLen_add_step (varintContByte (x.val >>> 49)) 7#64 8#64 rfl horig7
                  cases hult8 : (x.val >>> 56).ult 128#64
                  · simp only [hult8, ↓reduceIte, Bool.false_eq_true] at hpc9
                    have hbs9 := encodeVarint_step_bs (nextV := x.val >>> 63) hbs8 hult8 (ushr_ushr_7 x.val 56 63)
                    refine step_spqrEncVarint_placed_s9 (x := x) (F := FSave) A abs hgrow
                      x.val x.v (BitVec.ofNat 64 x.bs.length) cap8 ptr8 s0.sp _ horig8 hult8
                      (by simp only [List.length_append, List.length_singleton]; omega)
                      hpc9 hrun9 hsp9 halign htr9 hx19_9 hx21_9 hx22_9 hx23_9 hcs9 rfl ?_
                    intro s10 cap9 ptr9 hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hx21_10 hcs10 hge9 hpres9
                    have hinv9 := hinv8.step (byte := varintContByte (x.val >>> 56)) hge9 hpres9
                    exact step_spqrEncVarint_placed_exit9 A abs hgrow x cap9 ptr9 v56 _ hinv9
                      (encodeVarint_exit_bs_s9 hbs9 hult8)
                      (by simp only [List.length_append, List.length_singleton]; omega)
                      hpc10 hrun10 hsp10 halign htr10 hx19_10 hx20_10 hx21_10 hcs10 rfl
                  · simp only [hult8, ↓reduceIte] at hpc9
                    exact step_spqrEncVarint_placed_exit_328 A abs hgrow x (x.val >>> 56) cap8 ptr8 v56 _ hinv8
                      (encodeVarint_exit_bs hbs8 hult8)
                      (by simp only [List.length_append, List.length_singleton]; omega)
                      hpc9 hrun9 hsp9 halign htr9 hx19_9 hx21_9 hx23_9 hcs9 rfl
                · simp only [hult7, ↓reduceIte] at hpc8
                  exact step_spqrEncVarint_placed_exit_396 A abs hgrow x (x.val >>> 49) cap7 ptr7 v56 _ hinv7
                    (encodeVarint_exit_bs hbs7 hult7)
                    (by simp only [List.length_append, List.length_singleton]; omega)
                    hpc8 hrun8 hsp8 halign htr8 hx19_8 hx21_8 hx24_8 hcs8 rfl
              · simp only [hult6, ↓reduceIte] at hpc7
                exact step_spqrEncVarint_placed_exit_328 A abs hgrow x (x.val >>> 42) cap6 ptr6 v56 _ hinv6
                  (encodeVarint_exit_bs hbs6 hult6)
                  (by simp only [List.length_append, List.length_singleton]; omega)
                  hpc7 hrun7 hsp7 halign htr7 hx19_7 hx21_7 hx23_7 hcs7 rfl
            · simp only [hult5, ↓reduceIte] at hpc6
              exact step_spqrEncVarint_placed_exit_396 A abs hgrow x (x.val >>> 35) cap5 ptr5 v56 _ hinv5
                (encodeVarint_exit_bs hbs5 hult5)
                (by simp only [List.length_append, List.length_singleton]; omega)
                hpc6 hrun6 hsp6 halign htr6 hx19_6 hx21_6 hx24_6 hcs6 rfl
          · simp only [hult4, ↓reduceIte] at hpc5
            exact step_spqrEncVarint_placed_exit_328 A abs hgrow x (x.val >>> 28) cap4 ptr4 v56 _ hinv4
              (encodeVarint_exit_bs hbs4 hult4)
              (by simp only [List.length_append, List.length_singleton]; omega)
              hpc5 hrun5 hsp5 halign htr5 hx19_5 hx21_5 hx23_5 hcs5 rfl
        · simp only [hult3, ↓reduceIte] at hpc4
          exact step_spqrEncVarint_placed_exit3 A abs hgrow x cap3 ptr3 v56 _ hinv3
            (encodeVarint_exit_bs hbs3 hult3)
            (by simp only [List.length_append, List.length_singleton]; omega)
            hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hx21_4 hcs4 rfl
      · simp only [hult2, ↓reduceIte] at hpc3
        exact step_spqrEncVarint_placed_exit2 A abs hgrow x cap2 ptr2 v56 _ hinv2
          (encodeVarint_exit_bs hbs2 hult2)
          (by simp only [List.length_append, List.length_singleton]; omega)
          hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hx21_3 hcs3 rfl
    · simp only [hult1, ↓reduceIte] at hpc2
      exact step_spqrEncVarint_placed_exit1 A abs hgrow x cap1 ptr1 v56 _ hinv1
        (encodeVarint_exit_bs hbs1 hult1)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx21_2 hcs2 rfl
  · simp only [hult0, ↓reduceIte] at hpc1
    exact step_spqrEncVarint_placed_exit0 A abs hgrow x x.cap x.ptr v56 x.bs hinv0
      (encodeVarint_exit_bs hbs0 hult0) (by omega)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx22_1 hcs1 (by ac_rfl)

/-- `withLsCodeLoaded`-wrapped `spqr::encode_varint` (Block `326`) correctness theorem. -/
theorem spqrEncodeVarint_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State))
    (hgrow : GrowOneU8PlacedOkExt A ext) :
    SpqrEncodeVarintPlacedOkX A ext := by
  unfold SpqrEncodeVarintPlacedOkX
  rw [← IsLsBlockProg.eq_blockProgram (prog := (blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext))]
  exact spqrEncodeVarint_placed_ok_ext A ext hgrow

theorem spqrEncodeVarint_placed_ok_of_hookSat_x [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A)) :
    SpqrEncodeVarintPlacedOkX A ext :=
  spqrEncodeVarint_placed_ok_x A ext (growOneU8_placed_ok_ext A ext h_panic hshim halloc hrealloc)

end CryptoVerification.SpqrV1.Top.EncodeVarint
