/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Base
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `prost::encoding::varint::encode_varint::<Vec<u8>> [local#4]`

Proves continuation-byte stages 4..8 and top-level fixed-base and `[LibsignalPlacement]`
contracts for `encode_varint::<Vec<u8>> [local#4]` (`0x4d710`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Varint

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Continuation-byte stages 4..9 -/

set_option hygiene false in
local macro "encVarint4_s4_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
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
    · apply ($ofCs (mid := $entry + 512#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 21)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply ($ofCs (mid := $entry + 476#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 21)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply ($ofCs (mid := $callMid)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine $callGen A hdoReserve v curCap curPtr sp
      ($entry + 440#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
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
    · apply ($ofCs (mid := $entry + 512#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 21)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply ($ofCs (mid := $entry + 476#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 21)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)))
/-- Stage 4 (`+0x168..+0x1d8`, offsets `360..476`): appends `varintContByte (val >>> 21)` and either
exits to `+0x200` (`512`) with `x0 = val >>> 28` when `(val >>> 28).ult 128#64`, or continues to
Stage 5 (`+0x1dc` = `476`) with `x10 = nextPtr`, `x11 = val >>> 35`, `x12 = val >>> 28`. -/
theorem step_encVarint4_s4 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve7Name) (doReserveSpecWith resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 360#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx12 : s.readReg64 .x12 = val >>> 28) (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 28).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 512#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 476#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 28).ult 128#64 then val >>> 28 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr →
      sm.readReg64 .x11 = val >>> 35 → sm.readReg64 .x12 = val >>> 28 → EncVarintCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 21)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encodeVarint4_fetches_range b (Rust.withPanics abs) 360 476
  rw [← doReserve7_fnAddr_eq] at hdoReserve
  generalize_entry (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name = entry
  examples_hide_fetches
  encVarint4_s4_body entry (entry + bv% (ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]"
    "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]")) SepWPp.of_sepWP_cs EncVarintCalleeSaved step_doReserve_call_gen

theorem step_encVarint4_s4_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320) (doReserveSpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_292).base + 360#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx12 : s.readReg64 .x12 = val >>> 28) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 28).ult 128#64 then (blkPl_292).base + 512#64 else (blkPl_292).base + 476#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 28).ult 128#64 then val >>> 28 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr →
      sm.readReg64 .x11 = val >>> 35 → sm.readReg64 .x12 = val >>> 28 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_292 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 21)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_292 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint4_s4_body (blkPl_292).base (lsmpl.base 320) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve_call_gen_placed

set_option hygiene false in
local macro "encVarint4_s5_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
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
    · apply ($ofCs (mid := $entry + 512#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 28)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply ($ofCs (mid := $entry + 668#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 28)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply ($ofCs (mid := $callMid)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine $callGen A hdoReserve v curCap curPtr sp
      ($entry + 632#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
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
    · apply ($ofCs (mid := $entry + 512#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 28)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply ($ofCs (mid := $entry + 668#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 28)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)))
/-- Stage 5 (`+0x1dc..+0x1fc` and `+0x258..+0x298`, offsets `476..512` and `600..668`):
appends `varintContByte (val >>> 28)` and either exits to `+0x200` (`512`) with `x0 = val >>> 35`
when `(val >>> 35).ult 128#64`, or continues to Stage 6 (`+0x29c` = `668`) with `x10 = nextPtr`,
`x11 = val >>> 35`, `x12 = val >>> 42`. -/
theorem step_encVarint4_s5 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve7Name) (doReserveSpecWith resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 476#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 28) (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 35).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 512#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 668#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 35).ult 128#64 then val >>> 35 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr →
      sm.readReg64 .x11 = val >>> 35 → sm.readReg64 .x12 = val >>> 42 → EncVarintCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 28)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encodeVarint4_fetches_range b (Rust.withPanics abs) 476 512
  encodeVarint4_fetches_range b (Rust.withPanics abs) 600 668
  rw [← doReserve7_fnAddr_eq] at hdoReserve
  generalize_entry (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name = entry
  examples_hide_fetches
  encVarint4_s5_body entry (entry + bv% (ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]"
    "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]")) SepWPp.of_sepWP_cs EncVarintCalleeSaved step_doReserve_call_gen

theorem step_encVarint4_s5_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320) (doReserveSpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_292).base + 476#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 28) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 35).ult 128#64 then (blkPl_292).base + 512#64 else (blkPl_292).base + 668#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 35).ult 128#64 then val >>> 35 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr →
      sm.readReg64 .x11 = val >>> 35 → sm.readReg64 .x12 = val >>> 42 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_292 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 28)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_292 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint4_s5_body (blkPl_292).base (lsmpl.base 320) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve_call_gen_placed

set_option hygiene false in
local macro "encVarint4_s6_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
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
    · apply ($ofCs (mid := $entry + 512#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 35)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply ($ofCs (mid := $entry + 704#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 35)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply ($ofCs (mid := $callMid)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine $callGen A hdoReserve v curCap curPtr sp
      ($entry + 808#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
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
    · apply ($ofCs (mid := $entry + 512#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 35)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply ($ofCs (mid := $entry + 704#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 35)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)))
/-- Stage 6 (`+0x29c..+0x2bc`, `+0x308..+0x34c`, `+0x190..+0x194`, offsets `668..704`, `776..848`, `400..408`):
appends `varintContByte (val >>> 35)` and either exits to `+0x200` (`512`) with `x0 = val >>> 42`
when `(val >>> 42).ult 128#64`, or continues to Stage 7 (`+0x2c0` = `704`) with `x11 = val >>> 49`,
`x12 = val >>> 42`. -/
theorem step_encVarint4_s6 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve7Name) (doReserveSpecWith resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 668#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 42) (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 42).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 512#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 704#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 42).ult 128#64 then val >>> 42 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x11 = val >>> 49 → sm.readReg64 .x12 = val >>> 42 →
      EncVarintCalleeSaved s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 35)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encodeVarint4_fetches_range b (Rust.withPanics abs) 400 408
  encodeVarint4_fetches_range b (Rust.withPanics abs) 668 704
  encodeVarint4_fetches_range b (Rust.withPanics abs) 776 848
  rw [← doReserve7_fnAddr_eq] at hdoReserve
  generalize_entry (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name = entry
  examples_hide_fetches
  encVarint4_s6_body entry (entry + bv% (ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]"
    "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]")) SepWPp.of_sepWP_cs EncVarintCalleeSaved step_doReserve_call_gen

theorem step_encVarint4_s6_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320) (doReserveSpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_292).base + 668#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 42) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 42).ult 128#64 then (blkPl_292).base + 512#64 else (blkPl_292).base + 704#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 42).ult 128#64 then val >>> 42 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x11 = val >>> 49 → sm.readReg64 .x12 = val >>> 42 →
      EncVarintCalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_292 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 35)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_292 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint4_s6_body (blkPl_292).base (lsmpl.base 320) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve_call_gen_placed

set_option hygiene false in
local macro "encVarint4_s7_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
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
    · apply ($ofCs (mid := $entry + 512#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 42)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply ($ofCs (mid := $entry + 740#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 42)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply ($ofCs (mid := $callMid)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine $callGen A hdoReserve v curCap curPtr sp
      ($entry + 880#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
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
    · apply ($ofCs (mid := $entry + 512#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 42)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply ($ofCs (mid := $entry + 740#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 42)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)))
/-- Stage 7 (`+0x2c0..+0x2e0`, `+0x350..+0x394`, `+0x1fc`, offsets `704..740`, `848..920`, `508..512`):
appends `varintContByte (val >>> 42)` and either exits to `+0x200` (`512`) with `x0 = val >>> 49`
when `(val >>> 49).ult 128#64`, or continues to Stage 8 (`+0x2e4` = `740`) with `x10 = val >>> 56`,
`x11 = val >>> 49`, `x12 = nextPtr`. -/
theorem step_encVarint4_s7 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve7Name) (doReserveSpecWith resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 704#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx11 : s.readReg64 .x11 = val >>> 49) (hx12 : s.readReg64 .x12 = val >>> 42)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 49).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 512#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 740#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 49).ult 128#64 then val >>> 49 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x11 = val >>> 49 → sm.readReg64 .x12 = nextPtr → EncVarintCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 42)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encodeVarint4_fetches_range b (Rust.withPanics abs) 508 512
  encodeVarint4_fetches_range b (Rust.withPanics abs) 704 740
  encodeVarint4_fetches_range b (Rust.withPanics abs) 848 920
  rw [← doReserve7_fnAddr_eq] at hdoReserve
  generalize_entry (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name = entry
  examples_hide_fetches
  encVarint4_s7_body entry (entry + bv% (ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]"
    "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]")) SepWPp.of_sepWP_cs EncVarintCalleeSaved step_doReserve_call_gen

theorem step_encVarint4_s7_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320) (doReserveSpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_292).base + 704#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx11 : s.readReg64 .x11 = val >>> 49) (hx12 : s.readReg64 .x12 = val >>> 42)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 49).ult 128#64 then (blkPl_292).base + 512#64 else (blkPl_292).base + 740#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 49).ult 128#64 then val >>> 49 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x11 = val >>> 49 → sm.readReg64 .x12 = nextPtr → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_292 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 42)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_292 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint4_s7_body (blkPl_292).base (lsmpl.base 320) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve_call_gen_placed

set_option hygiene false in
local macro "encVarint4_s8_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
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
    · apply ($ofCs (mid := $entry + 512#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 49)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply ($ofCs (mid := $entry + 984#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 49)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply ($ofCs (mid := $callMid)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine $callGen A hdoReserve v curCap curPtr sp
      ($entry + 952#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
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
    · apply ($ofCs (mid := $entry + 512#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 49)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply ($ofCs (mid := $entry + 984#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 49)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)))
/-- Stage 8 (`+0x2e4..+0x304`, `+0x398..+0x3d4`, offsets `740..776`, `920..984`):
appends `varintContByte (val >>> 49)` and either exits to `+0x200` (`512`) with `x0 = val >>> 56`
when `(val >>> 56).ult 128#64`, or continues to Stage 9 (`+0x3d8` = `984`) with `x10 = val >>> 56`,
`x12 = nextPtr`. -/
theorem step_encVarint4_s8 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve7Name) (doReserveSpecWith resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 740#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56) (hx11 : s.readReg64 .x11 = val >>> 49)
    (hx12 : s.readReg64 .x12 = curPtr) (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 56).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 512#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name + 984#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 56).ult 128#64 then val >>> 56 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = val >>> 56 → sm.readReg64 .x12 = nextPtr →
      EncVarintCalleeSaved s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 49)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encodeVarint4_fetches_range b (Rust.withPanics abs) 740 776
  encodeVarint4_fetches_range b (Rust.withPanics abs) 920 984
  rw [← doReserve7_fnAddr_eq] at hdoReserve
  generalize_entry (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name = entry
  examples_hide_fetches
  encVarint4_s8_body entry (entry + bv% (ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]"
    "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]")) SepWPp.of_sepWP_cs EncVarintCalleeSaved step_doReserve_call_gen

theorem step_encVarint4_s8_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320) (doReserveSpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_292).base + 740#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56) (hx11 : s.readReg64 .x11 = val >>> 49)
    (hx12 : s.readReg64 .x12 = curPtr) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 56).ult 128#64 then (blkPl_292).base + 512#64 else (blkPl_292).base + 984#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 56).ult 128#64 then val >>> 56 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = val >>> 56 → sm.readReg64 .x12 = nextPtr →
      EncVarintCalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_292 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 49)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_292 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint4_s8_body (blkPl_292).base (lsmpl.base 320) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve_call_gen_placed

/-! ## Main Theorems -/

set_option hygiene false in
local macro "encVarint4_gen_body "
    prol:term:max s1t:term:max s2t:term:max s3t:term:max s4t:term:max s5t:term:max
    s6t:term:max s7t:term:max s8t:term:max s9t:term:max exitt:term:max : tactic =>
  `(tactic| (
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
      (vecU8Buf A x.cap x.ptr x.bs ∗ A.pool ∗ stackAt (s0.sp - 48#64) resStack), ?_, ?_⟩
  · convert hpre using 1; ac_rfl
  refine $prol x.val x.v x.cap x.ptr s0.sp
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
    refine $s1t (F := FSave) hdoReserve
      x.val x.v x.cap x.ptr s0.sp v48 v40 x.bs (stage_len_lt_of_step hlen_bound hinv0 hbs0)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 cap1 ptr1 v48_1 v40_1 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 hge1 hpres1
    have hinv1 := hinv0.step (byte := varintContByte x.val) hge1 hpres1
    cases hult1 : (x.val >>> 7).ult 128#64
    · simp only [hult1, ↓reduceIte, Bool.false_eq_true] at hpc2 hx0_2
      have hbs2 := encodeVarint_step_bs (nextV := x.val >>> 14) hbs1 hult1 (ushr_ushr_7 x.val 7 14)
      refine $s2t (F := FSave) hdoReserve
        x.val x.v cap1 ptr1 s0.sp v48_1 v40_1 _ (stage_len_lt_of_step hlen_bound hinv1 hbs1)
        hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 rfl ?_
      intro s3 cap2 ptr2 v48_2 v40_2 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 hge2 hpres2
      have hinv2 := hinv1.step (byte := varintContByte (x.val >>> 7)) hge2 hpres2
      cases hult2 : (x.val >>> 14).ult 128#64
      · simp only [hult2, ↓reduceIte, Bool.false_eq_true] at hpc3 hx0_3
        have hbs3 := encodeVarint_step_bs (nextV := x.val >>> 21) hbs2 hult2 (ushr_ushr_7 x.val 14 21)
        refine $s3t (F := FSave) hdoReserve
          x.val x.v cap2 ptr2 s0.sp v48_2 v40_2 _ (stage_len_lt_of_step hlen_bound hinv2 hbs2)
          hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 rfl ?_
        intro s4 cap3 ptr3 v48_3 v40_3 hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 hge3 hpres3
        have hinv3 := hinv2.step (byte := varintContByte (x.val >>> 14)) hge3 hpres3
        cases hult3 : (x.val >>> 21).ult 128#64
        · simp only [hult3, ↓reduceIte, Bool.false_eq_true] at hpc4 hx0_4
          have hbs4 := encodeVarint_step_bs (nextV := x.val >>> 28) hbs3 hult3 (ushr_ushr_7 x.val 21 28)
          refine $s4t (F := FSave) hdoReserve
            x.val x.v cap3 ptr3 s0.sp v48_3 v40_3 _ (stage_len_lt_of_step hlen_bound hinv3 hbs3)
            hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 rfl ?_
          intro s5 cap4 ptr4 v48_4 v40_4 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 hge4 hpres4
          have hinv4 := hinv3.step (byte := varintContByte (x.val >>> 21)) hge4 hpres4
          cases hult4 : (x.val >>> 28).ult 128#64
          · simp only [hult4, ↓reduceIte, Bool.false_eq_true] at hpc5 hx0_5
            have hbs5 := encodeVarint_step_bs (nextV := x.val >>> 35) hbs4 hult4 (ushr_ushr_7 x.val 28 35)
            refine $s5t (F := FSave) hdoReserve
              x.val x.v cap4 ptr4 s0.sp v48_4 v40_4 _ (stage_len_lt_of_step hlen_bound hinv4 hbs4)
              hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 rfl ?_
            intro s6 cap5 ptr5 v48_5 v40_5 hpc6 hrun6 hsp6 htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx12_6 hcs6 hge5 hpres5
            have hinv5 := hinv4.step (byte := varintContByte (x.val >>> 28)) hge5 hpres5
            cases hult5 : (x.val >>> 35).ult 128#64
            · simp only [hult5, ↓reduceIte, Bool.false_eq_true] at hpc6 hx0_6
              have hbs6 := encodeVarint_step_bs (nextV := x.val >>> 42) hbs5 hult5 (ushr_ushr_7 x.val 35 42)
              refine $s6t (F := FSave) hdoReserve
                x.val x.v cap5 ptr5 s0.sp v48_5 v40_5 _ (stage_len_lt_of_step hlen_bound hinv5 hbs5)
                hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx12_6 hcs6 rfl ?_
              intro s7 cap6 ptr6 v48_6 v40_6 hpc7 hrun7 hsp7 htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx11_7 hx12_7 hcs7 hge6 hpres6
              have hinv6 := hinv5.step (byte := varintContByte (x.val >>> 35)) hge6 hpres6
              cases hult6 : (x.val >>> 42).ult 128#64
              · simp only [hult6, ↓reduceIte, Bool.false_eq_true] at hpc7 hx0_7
                have hbs7 := encodeVarint_step_bs (nextV := x.val >>> 49) hbs6 hult6 (ushr_ushr_7 x.val 42 49)
                refine $s7t (F := FSave) hdoReserve
                  x.val x.v cap6 ptr6 s0.sp v48_6 v40_6 _ (stage_len_lt_of_step hlen_bound hinv6 hbs6)
                  hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx11_7 hx12_7 hcs7 rfl ?_
                intro s8 cap7 ptr7 v48_7 v40_7 hpc8 hrun8 hsp8 htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 hge7 hpres7
                have hinv7 := hinv6.step (byte := varintContByte (x.val >>> 42)) hge7 hpres7
                cases hult7 : (x.val >>> 49).ult 128#64
                · simp only [hult7, ↓reduceIte, Bool.false_eq_true] at hpc8 hx0_8
                  have hbs8 := encodeVarint_step_bs (nextV := x.val >>> 56) hbs7 hult7 (ushr_ushr_7 x.val 49 56)
                  refine $s8t (F := FSave) hdoReserve
                    x.val x.v cap7 ptr7 s0.sp v48_7 v40_7 _ (stage_len_lt_of_step hlen_bound hinv7 hbs7)
                    hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 rfl ?_
                  intro s9 cap8 ptr8 v48_8 v40_8 hpc9 hrun9 hsp9 htr9 hx0_9 hx1_9 hx8_9 hx9_9 hx10_9 hx12_9 hcs9 hge8 hpres8
                  have hinv8 := hinv7.step (byte := varintContByte (x.val >>> 49)) hge8 hpres8
                  cases hult8 : (x.val >>> 56).ult 128#64
                  · simp only [hult8, ↓reduceIte, Bool.false_eq_true] at hpc9 hx0_9
                    have hbs9 := encodeVarint_step_bs (nextV := x.val >>> 63) hbs8 hult8 (ushr_ushr_7 x.val 56 63)
                    refine $s9t (F := ((s0.sp - 48#64) ↦₆₄ v48_8) ∗ ((s0.sp - 40#64) ↦₆₄ v40_8) ∗ FSave)
                      hdoReserve x.val x.v cap8 ptr8 s0.sp _ hult8
                      (stage_len_lt_of_step hlen_bound hinv8 hbs8)
                      hpc9 hrun9 hsp9 halign htr9 hx1_9 hx8_9 hx9_9 hx10_9 hx12_9 hcs9 (by ac_rfl) ?_
                    intro s10 cap9 ptr9 hpc10 hrun10 hsp10 htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10 hge9 hpres9
                    have hinv9 := hinv8.step (byte := varintContByte (x.val >>> 56)) hge9 hpres9
                    exact $exitt hdoReserve x 1#64 cap9 ptr9 v48_8 v40_8 _ hinv9
                      (encodeVarint_exit_bs_s9 hbs9 hult8)
                      (stage_len_lt_of_exit hlen_bound hinv9 (encodeVarint_exit_bs_s9 hbs9 hult8))
                      hpc10 hrun10 hsp10 halign htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10 (by dsimp [FSave]; ac_rfl)
                  · simp only [hult8, ↓reduceIte] at hpc9 hx0_9
                    exact $exitt hdoReserve x (x.val >>> 56) cap8 ptr8 v48_8 v40_8 _ hinv8
                      (encodeVarint_exit_bs hbs8 hult8)
                      (stage_len_lt_of_exit hlen_bound hinv8 (encodeVarint_exit_bs hbs8 hult8))
                      hpc9 hrun9 hsp9 halign htr9 hx0_9 hx1_9 hx8_9 hx9_9 hcs9 rfl
                · simp only [hult7, ↓reduceIte] at hpc8 hx0_8
                  exact $exitt hdoReserve x (x.val >>> 49) cap7 ptr7 v48_7 v40_7 _ hinv7
                    (encodeVarint_exit_bs hbs7 hult7)
                    (stage_len_lt_of_exit hlen_bound hinv7 (encodeVarint_exit_bs hbs7 hult7))
                    hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hcs8 rfl
              · simp only [hult6, ↓reduceIte] at hpc7 hx0_7
                exact $exitt hdoReserve x (x.val >>> 42) cap6 ptr6 v48_6 v40_6 _ hinv6
                  (encodeVarint_exit_bs hbs6 hult6)
                  (stage_len_lt_of_exit hlen_bound hinv6 (encodeVarint_exit_bs hbs6 hult6))
                  hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hcs7 rfl
            · simp only [hult5, ↓reduceIte] at hpc6 hx0_6
              exact $exitt hdoReserve x (x.val >>> 35) cap5 ptr5 v48_5 v40_5 _ hinv5
                (encodeVarint_exit_bs hbs5 hult5)
                (stage_len_lt_of_exit hlen_bound hinv5 (encodeVarint_exit_bs hbs5 hult5))
                hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hcs6 rfl
          · simp only [hult4, ↓reduceIte] at hpc5 hx0_5
            exact $exitt hdoReserve x (x.val >>> 28) cap4 ptr4 v48_4 v40_4 _ hinv4
              (encodeVarint_exit_bs hbs4 hult4)
              (stage_len_lt_of_exit hlen_bound hinv4 (encodeVarint_exit_bs hbs4 hult4))
              hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hcs5 rfl
        · simp only [hult3, ↓reduceIte] at hpc4 hx0_4
          exact $exitt hdoReserve x (x.val >>> 21) cap3 ptr3 v48_3 v40_3 _ hinv3
            (encodeVarint_exit_bs hbs3 hult3)
            (stage_len_lt_of_exit hlen_bound hinv3 (encodeVarint_exit_bs hbs3 hult3))
            hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hcs4 rfl
      · simp only [hult2, ↓reduceIte] at hpc3 hx0_3
        exact $exitt hdoReserve x (x.val >>> 14) cap2 ptr2 v48_2 v40_2 _ hinv2
          (encodeVarint_exit_bs hbs2 hult2)
          (stage_len_lt_of_exit hlen_bound hinv2 (encodeVarint_exit_bs hbs2 hult2))
          hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hcs3 rfl
    · simp only [hult1, ↓reduceIte] at hpc2 hx0_2
      exact $exitt hdoReserve x (x.val >>> 7) cap1 ptr1 v48_1 v40_1 _ hinv1
        (encodeVarint_exit_bs hbs1 hult1)
        (stage_len_lt_of_exit hlen_bound hinv1 (encodeVarint_exit_bs hbs1 hult1))
        hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hcs2 rfl
  · simp only [hult0, ↓reduceIte] at hpc1
    exact $exitt hdoReserve x x.val x.cap x.ptr v48 v40 x.bs hinv0 (encodeVarint_exit_bs hbs0 hult0)
      (stage_len_lt_of_exit hlen_bound hinv0 (encodeVarint_exit_bs hbs0 hult0))
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by ac_rfl)))

theorem encodeVarint4_gen_ok_ext (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (x : EncodeVarintGhost) (R : SepProp) (s0 : State)
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve7Name) (doReserveSpecWith resStack s0 A))
    (hpc0 : s0.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarint4Name)
    (hrun0 : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeVarintFitSpecOf resStack A).pre x s0 ∗ R)
    (hsp0 : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeVarintSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint4_gen_body
    (step_encVarint4_prologue b abs) (step_encVarint4_s1 b A abs) (step_encVarint4_s2 b A abs)
    (step_encVarint4_s3 b A abs) (step_encVarint4_s4 b A abs) (step_encVarint4_s5 b A abs)
    (step_encVarint4_s6 b A abs) (step_encVarint4_s7 b A abs) (step_encVarint4_s8 b A abs)
    (step_encVarint4_s9 b A abs) (step_encVarint4_exit hres b A abs)

theorem encodeVarint4_fit_ok_ext (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve7Name) (doReserveSpec A)) :
    EncodeVarint4FitOkExt b A abs := by
  unfold EncodeVarint4FitOkExt; apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre hsp0
  obtain ⟨P, hP, hwp⟩ := encodeVarint4_gen_ok_ext b A abs (resStack := doReserveStack)
    (by decide) x R s0 (doReserve7_with_of_ok b A abs s0 hdoReserve) hpc0 hrun0 hpre hsp0
  exact ⟨P, R, hP, hwp⟩

theorem encode_varint4_fit_ok_ext {b : BitVec 64} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocContracts b A abs) :
    EncodeVarint4FitOkExt b A abs :=
  encodeVarint4_fit_ok_ext b A abs (do_reserve_7_ok_ext hA)

theorem encodeVarint4_fit_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hdoReserve : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr doReserve7Name) (doReserveSpec A)) :
    EncodeVarint4FitOk b C A ctl abs :=
  encodeVarint4_fit_ok_ext b A (tripleRatchetExterns C ctl abs) hdoReserve

theorem encode_varint4_fit_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    EncodeVarint4FitOk b C A ctl abs :=
  encodeVarint4_fit_ok b C A ctl abs (do_reserve_7_ok_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA))

theorem encodeVarint4_fit_ok_ext_x (img : Obj.Image) (A : RustAlloc) (abs : String → Option (State → State))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt img.base abs)
      ((tripleRatchetProgAtExt img.base abs).fnAddr doReserve7Name) ((doReserveSpecX A).inImage img)) :
    EncodeVarint4FitOkExtX img A abs := by
  unfold EncodeVarint4FitOkExtX; apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre hsp0
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (encodeVarintFitSpecOf doReserveStackX A).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨himg0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := encodeVarint4_gen_ok_ext img.base A abs (resStack := doReserveStackX)
    (by decide) x R s0 (doReserve7_with_of_ok_x img A abs s0 himg0 hdoReserve) hpc0 hrun0 hpre hsp0
  exact ⟨P, R, hP, hwp⟩

theorem encode_varint4_fit_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocContracts img.base A abs) :
    EncodeVarint4FitOkExtX img A abs :=
  encodeVarint4_fit_ok_ext_x img A abs (do_reserve_7_ok_ext_x hA)

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

theorem encodeVarint4_gen_placed_ok [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (x : EncodeVarintGhost) (R : SepProp) (s0 : State)
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320) (doReserveSpecWithPlaced resStack s0 A))
    (hpc0 : s0.pc = (blkPl_292).base) (hrun0 : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeVarintFitSpecOf resStack A).pre x s0 ∗ R) (hsp0 : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_292 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeVarintSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint4_gen_body
    (step_encVarint4_prologue_placed H) (step_encVarint4_s1_placed A H) (step_encVarint4_s2_placed A H)
    (step_encVarint4_s3_placed A H) (step_encVarint4_s4_placed A H) (step_encVarint4_s5_placed A H)
    (step_encVarint4_s6_placed A H) (step_encVarint4_s7_placed A H) (step_encVarint4_s8_placed A H)
    (step_encVarint4_s9_placed A H) (step_encVarint4_exit_placed hres A H)

theorem encodeVarint4_fit_placed_ok_of_doReserve [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64) (A : RustAlloc) (H : String → Option (State → State))
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320)
      (withLsCodeLoaded lsmpl (doReserveSpecOf resStack A))) :
    subroutine_ok (lsProg_292 H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf resStack A)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre hsp0
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcode0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := encodeVarint4_gen_placed_ok A H hres x R s0
    (doReserve7_with_placed_of_ok A s0 hcode0 hdoReserve) hpc0 hrun0 hpre hsp0
  exact ⟨P, R, hP, hwp⟩

theorem encode_varint4_fit_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_292).rebase (blkPl_292).base H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintFitSpec A)) :=
  encodeVarint4_fit_placed_ok_of_doReserve (resStack := doReserveStack) (by decide) A H
    (ls_subroutine_ok_of_block (callerProg := lsProg_292 H) (do_reserve_7_placed_ok h_panic hshim halloc hrealloc))

theorem encode_varint4_fit_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_292).rebase (blkPl_292).base H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecX A)) :=
  encodeVarint4_fit_placed_ok_of_doReserve (resStack := doReserveStackX) (by decide) A H
    (ls_subroutine_ok_of_block (callerProg := lsProg_292 H) (do_reserve_7_placed_ok_x h_panic hshim halloc hrealloc))

theorem encodeVarintSpecOf_of_encodeVarintFitSpecOf [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {resStack : Nat} {A : RustAlloc}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf resStack A))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (encodeVarintSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
  refine ⟨hpre.1, ?_⟩
  have hpre2 := hpre.2
  simp only [encodeVarintSpecOf, encodeVarintFitSpecOf, sepConj_assoc, satisfies_pure_sepConj] at hpre2 ⊢
  exact ⟨⟨hpre2.1.1, hpre2.1.2.1,
    hpre2.1.2.2.imp (fun hle => by have := (encodeVarint_length_bounds x.val).2; omega) id⟩, hpre2.2⟩

theorem encode_varint4_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_292).rebase (blkPl_292).base H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)) :=
  encodeVarintSpecOf_of_encodeVarintFitSpecOf
    (encode_varint4_fit_placed_ok h_panic hshim halloc hrealloc)

theorem encode_varint4_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_292).rebase (blkPl_292).base H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A)) :=
  encodeVarintSpecOf_of_encodeVarintFitSpecOf
    (encode_varint4_fit_placed_ok_x h_panic hshim halloc hrealloc)

end CryptoVerification.SpqrV1.Varint
