/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLen
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
import ProofLib.SepLogic.WPp

/-!
# `VmPreserved`-threaded `<chain::MessageKey as Message>::encoded_len`

Proves `msgKeyLen_placed_ok` (block `118`) against `Serialization.DefsBudget.msgKeyLenSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLenBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (MessageKeyGenerator)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc vecHeader)
open CryptoVerification.LibsignalProtoCodec (encodeKey encodeVarint)
open CryptoVerification.LibsignalSessionRepr (MessageKeyGhost messageKeyAt)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  EncLenCalleeSaved vecU8Buf vecU8At_eq_header_sep_buf stackAt_encodedLen_eq
  hwVarintLen_eq_encodeVarint_length hwVarintLen_bvShift_eq_encodeVarint_length
  encodeVarint_length_bounds ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  bv_add_ofNat_comm ule_zero_64 ult_zero_64
  ule_ofNat_add_of_lt ult_ofNat_add_of_lt
)
open CryptoVerification.E2E.Record (uint32Field bytesField lenField encMessageKey)
open CryptoVerification.E2E.Record.Placed (blkPl_118 lsProg_118)
open CryptoVerification.E2E.Record.Serialization (msgKeyLenStack)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (msgKeyLenSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  hwVarintLen_eq_encodeVarint_length hwVarintLen_bvShift_eq_encodeVarint_length
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64
  ule_zero_64 ult_zero_64

private def msgKeyCells (a : BitVec 64) (mk : MessageKeyGenerator) : SepProp :=
  ((a + 16#64) ↦₆₄ 0#64) ∗
  ((a + 40#64) ↦₆₄ 0#64) ∗
  ((a + 64#64) ↦₆₄ 0#64) ∗
  ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mk.seed.length) ∗
  ((a + 96#64) ↦₃₂ mk.counter)

private def msgKeyRest (A : RustAlloc) (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    SepProp :=
  ⌜gk.2.seed ≠ []⌝ ∗
  (a ↦₆₄ gk.1.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.1.cipher.ptr) ∗ vecU8Buf A gk.1.cipher.cap gk.1.cipher.ptr [] ∗
  ((a + 24#64) ↦₆₄ gk.1.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.1.mac.ptr) ∗ vecU8Buf A gk.1.mac.cap gk.1.mac.ptr [] ∗
  ((a + 48#64) ↦₆₄ gk.1.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.1.iv.ptr) ∗ vecU8Buf A gk.1.iv.cap gk.1.iv.ptr [] ∗
  ((a + 72#64) ↦₆₄ gk.1.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.1.seed.ptr) ∗ vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
  memRegion (a + 100#64) 4

private theorem messageKeyAt_eq_cells_sep_rest (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A gk a = msgKeyCells a gk.2 ∗ msgKeyRest A gk a := by
  simp only [messageKeyAt, msgKeyCells, msgKeyRest, vecU8At_eq_header_sep_buf, vecHeader,
    List.length_nil, sepConj_assoc, arm64_norm]
  sep_ac_rfl

private theorem msgKeyRest_seed_bounds {A : RustAlloc} {gk : MessageKeyGhost × MessageKeyGenerator}
    {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ msgKeyRest A gk a ∗ R) :
    gk.2.seed ≠ [] ∧ gk.2.seed.length < 2 ^ 63 := by
  unfold msgKeyRest at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  refine ⟨hm.1, ?_⟩
  have hbuf : m ⊨ vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      ((a ↦₆₄ gk.1.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.1.cipher.ptr) ∗
        vecU8Buf A gk.1.cipher.cap gk.1.cipher.ptr [] ∗
        ((a + 24#64) ↦₆₄ gk.1.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.1.mac.ptr) ∗
        vecU8Buf A gk.1.mac.cap gk.1.mac.ptr [] ∗
        ((a + 48#64) ↦₆₄ gk.1.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.1.iv.ptr) ∗
        vecU8Buf A gk.1.iv.cap gk.1.iv.ptr [] ∗
        ((a + 72#64) ↦₆₄ gk.1.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
        memRegion (a + 100#64) 4 ∗ R) := by
    convert hm.2 using 1
    sep_ac_rfl
  unfold vecU8Buf at hbuf
  rw [sepConj_assoc, satisfies_pure_sepConj] at hbuf
  have h1 := hbuf.1.1
  have h2 := hbuf.1.2.1
  omega

private theorem seed_len_beq_zero_false {bs : List (BitVec 8)}
    (hne : bs ≠ []) (hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length == 0#64) = false := by
  have hpos : 0 < bs.length := List.length_pos_iff.mpr hne
  rw [beq_eq_false_iff_ne]
  intro heq
  have h := congrArg BitVec.toNat heq
  change bs.length % 2 ^ 64 = 0 at h
  rw [Nat.mod_eq_of_lt (by omega)] at h
  omega

private theorem bv_uint32Field_1_ne_zero {v : BitVec 32} (h : (v == 0#32) = false) :
    BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 v)).length + 1#64 =
      BitVec.ofNat 64 (uint32Field 1 v).length := by
  have hv : v ≠ 0 := by rwa [beq_eq_false_iff_ne] at h
  have hkey : (encodeKey 1 .varint).length = 1 := rfl
  simp only [uint32Field, hv, ↓reduceIte, List.length_append, hkey,
    ← BitVec.ofNat_add, Nat.add_comm]

private theorem uint32Field_1_length_le (v : BitVec 32) :
    (uint32Field 1 v).length ≤ 11 := by
  unfold uint32Field
  split
  · simp
  · have hkey : (encodeKey 1 .varint).length = 1 := rfl
    have hb := (encodeVarint_length_bounds (v.setWidth 64)).2
    simp only [List.length_append, hkey]
    omega

private theorem bv_bytesField_5_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    BitVec.ofNat 64 bs.length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 bs.length)).length + 1#64 =
      BitVec.ofNat 64 (bytesField 5 bs).length := by
  have hkey : (encodeKey 5 .lengthDelimited).length = 1 := rfl
  simp only [bytesField, hne, ↓reduceIte, lenField, List.length_append, hkey, ← BitVec.ofNat_add]
  congr 1
  omega

private theorem bytesField_5_length_lt {bs : List (BitVec 8)} (hne : bs ≠ []) :
    (bytesField 5 bs).length ≤ bs.length + 11 := by
  have hkey : (encodeKey 5 .lengthDelimited).length = 1 := rfl
  have hb := (encodeVarint_length_bounds (BitVec.ofNat 64 bs.length)).2
  simp only [bytesField, hne, ↓reduceIte, lenField, List.length_append, hkey]
  omega

private theorem encMessageKey_length_eq (mk : MessageKeyGenerator) :
    (encMessageKey mk).length =
      (uint32Field 1 mk.counter).length + (bytesField 5 mk.seed).length := by
  simp only [encMessageKey, List.length_append]

private theorem stackAt_msgKeyLen_eq (sp : BitVec 64) :
    stackAt sp msgKeyLenStack = ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) :=
  stackAt_encodedLen_eq sp

@[local simp, local arm64_norm]
private theorem ule_self_64 (x : BitVec 64) : BitVec.ule x x = true := by
  simp [BitVec.ule]

@[local simp, local arm64_norm]
private theorem ult_self_64 (x : BitVec 64) : BitVec.ult x x = false := by
  simp [BitVec.ult]

private theorem sepWPp_of_sepWP_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s Pre Q Qp :=
  SepWPp.of_sepWP (mid := mid) (SepWP.mono h (fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm))

private theorem step_mkLen_f1_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (a sp v16 v8 : BitVec 64) (mk : MessageKeyGenerator)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_118).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (msgKeyCells a mk ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_118).base + 120#64 →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (uint32Field 1 mk.counter).length →
      sm.readReg64 .x9 = 0#64 →
      EncLenCalleeSaved s sm →
      SepWPp (lsProg_118 H) ret sm
        ((msgKeyCells a mk ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (lsProg_118 H) ret s P Q Qp := by
  subst hP
  have hcells : msgKeyCells a mk =
      ((a + 16#64) ↦₆₄ 0#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
      ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mk.seed.length) ∗ ((a + 96#64) ↦₃₂ mk.counter) := rfl
  by_cases hcnt : (mk.counter == 0#32) = true
  · have hcnt0 : mk.counter = 0#32 := by rwa [beq_iff_eq] at hcnt
    rw [hcells]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_118).base + bv% (120))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp_all, fun hvm => ?_⟩
      rw [← hcells]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [uint32Field]) (by simp_all)
        (by simp_all [EncLenCalleeSaved])
  · have hcnt_f : (mk.counter == 0#32) = false := Bool.eq_false_iff.mpr hcnt
    have henc := bv_uint32Field_1_ne_zero hcnt_f
    rw [hcells]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_118).base + bv% (120))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp_all, fun hvm => ?_⟩
      rw [← hcells]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all)
        (by simp_all [EncLenCalleeSaved])

private theorem step_mkLen_f2_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (a sp : BitVec 64) (mk : MessageKeyGenerator) (s1 : Nat)
    (hseed_ne : mk.seed ≠ [])
    (hseed_lt : mk.seed.length < 2 ^ 63)
    (hfit : s1 + (bytesField 5 mk.seed).length < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_118).base + 120#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hx9 : s.readReg64 .x9 = 0#64)
    (hcs : EncLenCalleeSaved s0 s)
    (hP : P = (msgKeyCells a mk ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      VmPreserved s sf →
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (s1 + (bytesField 5 mk.seed).length) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (lsProg_118 H) (s0.readReg64 .lr) s P Q Qp := by
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  have hseed_beq := seed_len_beq_zero_false hseed_ne hseed_lt
  have henc := bv_bytesField_5_ne_nil hseed_ne
  have hcs_ovf := ult_ofNat_add_of_lt hfit
  have hule_ovf := ule_ofNat_add_of_lt hfit
  have hadd := bv_add_ofNat_comm s1 (bytesField 5 mk.seed).length
  subst hP
  have hcells : msgKeyCells a mk =
      ((a + 16#64) ↦₆₄ 0#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
      ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mk.seed.length) ∗ ((a + 96#64) ↦₃₂ mk.counter) := rfl
  rw [hcells]
  apply sepWPp_of_sepWP_vm (mid := s0.readReg64 .lr)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) ⟨by simp_all, fun hvm => ?_⟩
    rw [← hcells]
    apply SepWPp.done (by simp_all) (by simp_all)
    refine hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) ?_
    simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, applyWriteback,
      State.advancePC_eq_setPC, State.setPC_setPC, State.writeReg64_setPC, State.setPState_setPC,
      State.setPState_setPState, State.writeReg64_setPState, State.setMem_setPC, State.setMem_setMem,
      State.writeReg64_setMem, State.setPState_setMem, State.writeReg64_writeReg64_same,
      wp_norm, arm64_norm, *]

/-- Relocatable `MessageKey::encoded_len` (block `118`) satisfies `DefsBudget.msgKeyLenSpec`. -/
theorem msgKeyLen_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_118 H) (blkPl_118).base (msgKeyLenSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, gk⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [msgKeyLenSpec, messageKeyAt_eq_cells_sep_rest, stackAt_msgKeyLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, hx0, hpre⟩
  have hrest_sat : s0.mem ⊨ msgKeyRest A gk a ∗
      (msgKeyCells a gk.2 ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R) := by
    convert hpre using 1
    sep_ac_rfl
  obtain ⟨hseed_ne, hseed_lt⟩ := msgKeyRest_seed_bounds hrest_sat
  let FRest : SepProp := msgKeyRest A gk a ∗ R
  have hmem0 : s0.mem ⊨
      (msgKeyCells a gk.2 ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ FRest := by
    dsimp [FRest]
    convert hpre using 1
    sep_ac_rfl
  refine ⟨(msgKeyCells a gk.2 ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ FRest, emp,
      by rwa [sepConj_emp], ?_⟩
  refine step_mkLen_f1_placed (F := FRest) H a s0.sp v16 v8 gk.2
    hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1
  have h1 := uint32Field_1_length_le gk.2.counter
  have h5 := bytesField_5_length_lt hseed_ne
  refine step_mkLen_f2_placed (F := FRest) H a s0.sp gk.2
    (uint32Field 1 gk.2.counter).length
    hseed_ne hseed_lt (by omega)
    hpc1 hrun1 hsp1 halign hx0_1 hx8_1 hx9_1 hcs1 rfl ?_
  intro sf hvm2 hpcf hrunf hspf htrf hx0_f hcsf
  have htr_all : sf.trace = s0.trace := by rw [htrf, htr1]
  have hvm_all : VmPreserved s0 sf := hvm1.trans hvm2
  rw [← encMessageKey_length_eq] at hx0_f
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f
  rw [sepConj_emp] at hm_f
  simp only [msgKeyLenSpec, messageKeyAt_eq_cells_sep_rest, stackAt_msgKeyLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, htr_all, hvm_all⟩, ?_⟩
  dsimp [FRest] at hm_f
  convert hm_f using 1
  sep_ac_rfl

end LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLenBudget
