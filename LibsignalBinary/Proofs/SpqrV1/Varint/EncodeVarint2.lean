/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Verification of `prost::encoding::varint::encode_varint::<Vec<u8>> [local#2]`

Proves continuation-byte stages 4..8 and top-level fixed-base and `[LibsignalPlacement]`
contracts for `encode_varint::<Vec<u8>> [local#2]` (`0x36628`).
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
local macro "encVarint2_s4_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
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
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 21)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply ($ofCs (mid := $entry + 444#64)); wp_steps
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
      ($entry + 408#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
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
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 21)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply ($ofCs (mid := $entry + 444#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 21)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)))
/-- Stage 4 (`+0x150..+0x1bc`, offsets `336..444`): appends `varintContByte (val >>> 21)` and either
exits to `+0x364` (`868`) with `x0 = val >>> 28` when `(val >>> 28).ult 128#64`, or continues to
Stage 5 (`+0x1bc` = `444`) with `x10 = nextPtr`, `x11 = val >>> 35`, `x12 = val >>> 28`. -/
theorem step_encVarint2_s4 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve2Name) (doReserve2SpecWith resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 336#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx12 : s.readReg64 .x12 = val >>> 28) (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 28).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 868#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 444#64) →
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
  spqrProgAt_fetches_range b (Rust.withPanics abs)
    libsignalSessionCode_fnOff_0x3670c 222988 336 444
  rw [← doReserve2_fnAddr_eq] at hdoReserve
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name = entry
  examples_hide_fetches
  encVarint2_s4_body entry (entry + 6484#64) SepWPp.of_sepWP_cs EncVarintCalleeSaved step_doReserve2_call_gen

theorem step_encVarint2_s4_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_148 H) (lsmpl.base 157) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_148).base + 336#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx12 : s.readReg64 .x12 = val >>> 28) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 28).ult 128#64 then (blkPl_148).base + 868#64 else (blkPl_148).base + 444#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 28).ult 128#64 then val >>> 28 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr →
      sm.readReg64 .x11 = val >>> 35 → sm.readReg64 .x12 = val >>> 28 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_148 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 21)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_148 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint2_s4_body (blkPl_148).base (lsmpl.base 157) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve2_call_gen_placed

set_option hygiene false in
local macro "encVarint2_s5_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
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
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 28)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply ($ofCs (mid := $entry + 544#64)); wp_steps
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
      ($entry + 508#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
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
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 28)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply ($ofCs (mid := $entry + 544#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 28)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)))
/-- Stage 5 (`+0x1bc..+0x220`, offsets `444..544`): appends `varintContByte (val >>> 28)` and either
exits to `+0x364` (`868`) with `x0 = val >>> 35` when `(val >>> 35).ult 128#64`, or continues to
Stage 6 (`+0x220` = `544`) with `x10 = nextPtr`, `x11 = val >>> 35`, `x13 = val >>> 42`. -/
theorem step_encVarint2_s5 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve2Name) (doReserve2SpecWith resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 444#64)
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
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 868#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 544#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 35).ult 128#64 then val >>> 35 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr →
      sm.readReg64 .x11 = val >>> 35 → sm.readReg64 .x13 = val >>> 42 → EncVarintCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 28)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  spqrProgAt_fetches_range b (Rust.withPanics abs)
    libsignalSessionCode_fnOff_0x3670c 222988 444 544
  rw [← doReserve2_fnAddr_eq] at hdoReserve
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name = entry
  examples_hide_fetches
  encVarint2_s5_body entry (entry + 6484#64) SepWPp.of_sepWP_cs EncVarintCalleeSaved step_doReserve2_call_gen

theorem step_encVarint2_s5_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_148 H) (lsmpl.base 157) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_148).base + 444#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 28) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 35).ult 128#64 then (blkPl_148).base + 868#64 else (blkPl_148).base + 544#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 35).ult 128#64 then val >>> 35 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr →
      sm.readReg64 .x11 = val >>> 35 → sm.readReg64 .x13 = val >>> 42 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_148 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 28)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_148 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint2_s5_body (blkPl_148).base (lsmpl.base 157) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve2_call_gen_placed

set_option hygiene false in
local macro "encVarint2_s6_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
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
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 35)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply ($ofCs (mid := $entry + 648#64)); wp_steps
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
      ($entry + 612#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
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
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 35)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply ($ofCs (mid := $entry + 648#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 35)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)))
/-- Stage 6 (`+0x220..+0x288`, offsets `544..648`): appends `varintContByte (val >>> 35)` and either
exits to `+0x364` (`868`) with `x0 = val >>> 42` when `(val >>> 42).ult 128#64`, or continues to
Stage 7 (`+0x288` = `648`) with `x12 = val >>> 49`, `x13 = val >>> 42`. -/
theorem step_encVarint2_s6 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve2Name) (doReserve2SpecWith resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 544#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx13 : s.readReg64 .x13 = val >>> 42) (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 42).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 868#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 648#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 42).ult 128#64 then val >>> 42 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x12 = val >>> 49 →
      sm.readReg64 .x13 = val >>> 42 → EncVarintCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 35)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  spqrProgAt_fetches_range b (Rust.withPanics abs)
    libsignalSessionCode_fnOff_0x3670c 222988 544 648
  rw [← doReserve2_fnAddr_eq] at hdoReserve
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name = entry
  examples_hide_fetches
  encVarint2_s6_body entry (entry + 6484#64) SepWPp.of_sepWP_cs EncVarintCalleeSaved step_doReserve2_call_gen

theorem step_encVarint2_s6_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_148 H) (lsmpl.base 157) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_148).base + 544#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx13 : s.readReg64 .x13 = val >>> 42) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 42).ult 128#64 then (blkPl_148).base + 868#64 else (blkPl_148).base + 648#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 42).ult 128#64 then val >>> 42 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x12 = val >>> 49 →
      sm.readReg64 .x13 = val >>> 42 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_148 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 35)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_148 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint2_s6_body (blkPl_148).base (lsmpl.base 157) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve2_call_gen_placed

set_option hygiene false in
local macro "encVarint2_s7_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
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
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 42)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply ($ofCs (mid := $entry + 684#64)); wp_steps
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
      ($entry + 744#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
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
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 42)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply ($ofCs (mid := $entry + 684#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 42)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)))
/-- Stage 7 (`+0x288..+0x2ac`, `+0x2d0..+0x310`, `+0x178..+0x180`, offsets `648..684`, `720..784`, `376..384`):
appends `varintContByte (val >>> 42)` and either exits to `+0x364` (`868`) with `x0 = val >>> 49`
when `(val >>> 49).ult 128#64`, or continues to Stage 8 (`+0x2ac` = `684`) with `x10 = val >>> 56`,
`x11 = nextPtr`, `x12 = val >>> 49`. -/
theorem step_encVarint2_s7 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve2Name) (doReserve2SpecWith resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 648#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx12 : s.readReg64 .x12 = val >>> 49) (hx13 : s.readReg64 .x13 = val >>> 42)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 49).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 868#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 684#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 49).ult 128#64 then val >>> 49 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x11 = nextPtr → sm.readReg64 .x12 = val >>> 49 → EncVarintCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 42)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  spqrProgAt_fetches_range b (Rust.withPanics abs)
    libsignalSessionCode_fnOff_0x3670c 222988 376 384
  spqrProgAt_fetches_range b (Rust.withPanics abs)
    libsignalSessionCode_fnOff_0x3670c 222988 648 684
  spqrProgAt_fetches_range b (Rust.withPanics abs)
    libsignalSessionCode_fnOff_0x3670c 222988 720 784
  rw [← doReserve2_fnAddr_eq] at hdoReserve
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name = entry
  examples_hide_fetches
  encVarint2_s7_body entry (entry + 6484#64) SepWPp.of_sepWP_cs EncVarintCalleeSaved step_doReserve2_call_gen

theorem step_encVarint2_s7_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_148 H) (lsmpl.base 157) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_148).base + 648#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx12 : s.readReg64 .x12 = val >>> 49) (hx13 : s.readReg64 .x13 = val >>> 42)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 49).ult 128#64 then (blkPl_148).base + 868#64 else (blkPl_148).base + 684#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 49).ult 128#64 then val >>> 49 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x11 = nextPtr → sm.readReg64 .x12 = val >>> 49 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_148 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 42)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_148 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint2_s7_body (blkPl_148).base (lsmpl.base 157) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve2_call_gen_placed

set_option hygiene false in
local macro "encVarint2_s8_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
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
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 49)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply ($ofCs (mid := $entry + 840#64)); wp_steps
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
      ($entry + 808#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
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
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 49)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply ($ofCs (mid := $entry + 840#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 49)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)))
/-- Stage 8 (`+0x2ac..+0x2d0`, `+0x310..+0x348`, offsets `684..720`, `784..840`):
appends `varintContByte (val >>> 49)` and either exits to `+0x364` (`868`) with `x0 = val >>> 56`
when `(val >>> 56).ult 128#64`, or continues to Stage 9 (`+0x348` = `840`) with `x10 = val >>> 56`,
`x11 = nextPtr`. -/
theorem step_encVarint2_s8 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve2Name) (doReserve2SpecWith resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 684#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56) (hx11 : s.readReg64 .x11 = curPtr)
    (hx12 : s.readReg64 .x12 = val >>> 49) (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 56).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 868#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name + 840#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 56).ult 128#64 then val >>> 56 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x11 = nextPtr → EncVarintCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 49)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  spqrProgAt_fetches_range b (Rust.withPanics abs)
    libsignalSessionCode_fnOff_0x3670c 222988 684 720
  spqrProgAt_fetches_range b (Rust.withPanics abs)
    libsignalSessionCode_fnOff_0x3670c 222988 784 840
  rw [← doReserve2_fnAddr_eq] at hdoReserve
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name = entry
  examples_hide_fetches
  encVarint2_s8_body entry (entry + 6484#64) SepWPp.of_sepWP_cs EncVarintCalleeSaved step_doReserve2_call_gen

theorem step_encVarint2_s8_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_148 H) (lsmpl.base 157) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_148).base + 684#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56) (hx11 : s.readReg64 .x11 = curPtr)
    (hx12 : s.readReg64 .x12 = val >>> 49) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 56).ult 128#64 then (blkPl_148).base + 868#64 else (blkPl_148).base + 840#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 56).ult 128#64 then val >>> 56 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x11 = nextPtr → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_148 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 49)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_148 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint2_s8_body (blkPl_148).base (lsmpl.base 157) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve2_call_gen_placed

/-! ## Main Theorems -/

set_option hygiene false in
local macro "encVarint2_gen_body "
    prol:term:max s1t:term:max s2t:term:max s3t:term:max s4t:term:max s5t:term:max
    s6t:term:max s7t:term:max s8t:term:max s9t:term:max exitt:term:max : tactic => `(tactic| (
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
            intro s6 cap5 ptr5 v48_5 v40_5 hpc6 hrun6 hsp6 htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx13_6 hcs6 hge5 hpres5
            have hinv5 := hinv4.step (byte := varintContByte (x.val >>> 28)) hge5 hpres5
            cases hult5 : (x.val >>> 35).ult 128#64
            · simp only [hult5, ↓reduceIte, Bool.false_eq_true] at hpc6 hx0_6
              have hbs6 := encodeVarint_step_bs (nextV := x.val >>> 42) hbs5 hult5 (ushr_ushr_7 x.val 35 42)
              refine $s6t (F := FSave) hdoReserve
                x.val x.v cap5 ptr5 s0.sp v48_5 v40_5 _ (stage_len_lt_of_step hlen_bound hinv5 hbs5)
                hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx13_6 hcs6 rfl ?_
              intro s7 cap6 ptr6 v48_6 v40_6 hpc7 hrun7 hsp7 htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx12_7 hx13_7 hcs7 hge6 hpres6
              have hinv6 := hinv5.step (byte := varintContByte (x.val >>> 35)) hge6 hpres6
              cases hult6 : (x.val >>> 42).ult 128#64
              · simp only [hult6, ↓reduceIte, Bool.false_eq_true] at hpc7 hx0_7
                have hbs7 := encodeVarint_step_bs (nextV := x.val >>> 49) hbs6 hult6 (ushr_ushr_7 x.val 42 49)
                refine $s7t (F := FSave) hdoReserve
                  x.val x.v cap6 ptr6 s0.sp v48_6 v40_6 _ (stage_len_lt_of_step hlen_bound hinv6 hbs6)
                  hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx12_7 hx13_7 hcs7 rfl ?_
                intro s8 cap7 ptr7 v48_7 v40_7 hpc8 hrun8 hsp8 htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 hge7 hpres7
                have hinv7 := hinv6.step (byte := varintContByte (x.val >>> 42)) hge7 hpres7
                cases hult7 : (x.val >>> 49).ult 128#64
                · simp only [hult7, ↓reduceIte, Bool.false_eq_true] at hpc8 hx0_8
                  have hbs8 := encodeVarint_step_bs (nextV := x.val >>> 56) hbs7 hult7 (ushr_ushr_7 x.val 49 56)
                  refine $s8t (F := FSave) hdoReserve
                    x.val x.v cap7 ptr7 s0.sp v48_7 v40_7 _ (stage_len_lt_of_step hlen_bound hinv7 hbs7)
                    hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 rfl ?_
                  intro s9 cap8 ptr8 v48_8 v40_8 hpc9 hrun9 hsp9 htr9 hx0_9 hx1_9 hx8_9 hx9_9 hx10_9 hx11_9 hcs9 hge8 hpres8
                  have hinv8 := hinv7.step (byte := varintContByte (x.val >>> 49)) hge8 hpres8
                  cases hult8 : (x.val >>> 56).ult 128#64
                  · simp only [hult8, ↓reduceIte, Bool.false_eq_true] at hpc9 hx0_9
                    have hbs9 := encodeVarint_step_bs (nextV := x.val >>> 63) hbs8 hult8 (ushr_ushr_7 x.val 56 63)
                    refine $s9t (F := ((s0.sp - 48#64) ↦₆₄ v48_8) ∗ ((s0.sp - 40#64) ↦₆₄ v40_8) ∗ FSave)
                      hdoReserve x.val x.v cap8 ptr8 s0.sp _ hult8
                      (stage_len_lt_of_step hlen_bound hinv8 hbs8)
                      hpc9 hrun9 hsp9 halign htr9 hx1_9 hx8_9 hx9_9 hx10_9 hx11_9 hcs9 (by ac_rfl) ?_
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

theorem encodeVarint2_gen_ok_ext (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (x : EncodeVarintGhost) (R : SepProp) (s0 : State)
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve2Name) (doReserve2SpecWith resStack s0 A))
    (hpc0 : s0.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarint2Name)
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
  encVarint2_gen_body
    (step_encVarint2_prologue b abs) (step_encVarint2_s1 b A abs) (step_encVarint2_s2 b A abs)
    (step_encVarint2_s3 b A abs) (step_encVarint2_s4 b A abs) (step_encVarint2_s5 b A abs)
    (step_encVarint2_s6 b A abs) (step_encVarint2_s7 b A abs) (step_encVarint2_s8 b A abs)
    (step_encVarint2_s9 b A abs) (step_encVarint2_exit hres b A abs)

theorem encodeVarint2_fit_ok_ext (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserve2Name) (doReserve2Spec A)) :
    EncodeVarint2FitOkExt b A abs := by
  unfold EncodeVarint2FitOkExt; apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre hsp0
  obtain ⟨P, hP, hwp⟩ := encodeVarint2_gen_ok_ext b A abs (resStack := doReserveStack)
    (by decide) x R s0 (doReserve2_with_of_ok b A abs s0 hdoReserve) hpc0 hrun0 hpre hsp0
  exact ⟨P, R, hP, hwp⟩

theorem encode_varint2_fit_ok_ext {b : BitVec 64} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocContracts b A abs) :
    EncodeVarint2FitOkExt b A abs :=
  encodeVarint2_fit_ok_ext b A abs (do_reserve2_ok_ext hA)

theorem encodeVarint2_fit_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hdoReserve : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr doReserve2Name) (doReserve2Spec A)) :
    EncodeVarint2FitOk b C A ctl abs :=
  encodeVarint2_fit_ok_ext b A (tripleRatchetExterns C ctl abs) hdoReserve

theorem encode_varint2_fit_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    EncodeVarint2FitOk b C A ctl abs :=
  encodeVarint2_fit_ok b C A ctl abs (do_reserve2_ok_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA))

theorem encodeVarint2_fit_ok_ext_x (img : Obj.Image) (A : RustAlloc) (abs : String → Option (State → State))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt img.base abs)
      ((tripleRatchetProgAtExt img.base abs).fnAddr doReserve2Name) ((doReserve2SpecX A).inImage img)) :
    EncodeVarint2FitOkExtX img A abs := by
  unfold EncodeVarint2FitOkExtX; apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre hsp0
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (encodeVarintFitSpecOf doReserveStackX A).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨himg0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := encodeVarint2_gen_ok_ext img.base A abs (resStack := doReserveStackX)
    (by decide) x R s0 (doReserve2_with_of_ok_x img A abs s0 himg0 hdoReserve) hpc0 hrun0 hpre hsp0
  exact ⟨P, R, hP, hwp⟩

theorem encode_varint2_fit_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocContracts img.base A abs) :
    EncodeVarint2FitOkExtX img A abs :=
  encodeVarint2_fit_ok_ext_x img A abs (do_reserve2_ok_ext_x hA)

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

theorem encodeVarint2_gen_placed_ok [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (x : EncodeVarintGhost) (R : SepProp) (s0 : State)
    (hdoReserve : subroutine_ok (lsProg_148 H) (lsmpl.base 157) (doReserve2SpecWithPlaced resStack s0 A))
    (hpc0 : s0.pc = (blkPl_148).base) (hrun0 : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeVarintFitSpecOf resStack A).pre x s0 ∗ R) (hsp0 : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_148 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeVarintSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint2_gen_body
    (step_encVarint2_prologue_placed H) (step_encVarint2_s1_placed A H) (step_encVarint2_s2_placed A H)
    (step_encVarint2_s3_placed A H) (step_encVarint2_s4_placed A H) (step_encVarint2_s5_placed A H)
    (step_encVarint2_s6_placed A H) (step_encVarint2_s7_placed A H) (step_encVarint2_s8_placed A H)
    (step_encVarint2_s9_placed A H) (step_encVarint2_exit_placed hres A H)

theorem encodeVarint2_fit_placed_ok_of_doReserve [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64) (A : RustAlloc) (H : String → Option (State → State))
    (hdoReserve : subroutine_ok (lsProg_148 H) (lsmpl.base 157)
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A))) :
    subroutine_ok (lsProg_148 H) (blkPl_148).base
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
    subroutine_ok ((blkPC_148).rebase (blkPl_148).base H) (blkPl_148).base
      (withLsCodeLoaded lsmpl (encodeVarintFitSpec A)) :=
  encodeVarint2_fit_placed_ok_of_doReserve (resStack := doReserveStack) (by decide) A H
    (ls_subroutine_ok_of_block (callerProg := lsProg_148 H) (do_reserve2_placed_ok h_panic hshim halloc hrealloc))

theorem encode_varint2_fit_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_148).rebase (blkPl_148).base H) (blkPl_148).base
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecX A)) :=
  encodeVarint2_fit_placed_ok_of_doReserve (resStack := doReserveStackX) (by decide) A H
    (ls_subroutine_ok_of_block (callerProg := lsProg_148 H) (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))

private theorem encodeVarint2SpecOf_of_encodeVarintFitSpecOf [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
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

theorem encode_varint2_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_148).rebase (blkPl_148).base H) (blkPl_148).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)) :=
  encodeVarint2SpecOf_of_encodeVarintFitSpecOf
    (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc)

theorem encode_varint2_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_148).rebase (blkPl_148).base H) (blkPl_148).base
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A)) :=
  encodeVarint2SpecOf_of_encodeVarintFitSpecOf
    (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc)

end CryptoVerification.SpqrV1.Varint
