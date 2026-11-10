/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSlice
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.InImage.Prost
import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.Slow
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
open CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Stack budget for `decode_varint_slow::<&mut &[u8]>` (`0x47f64`). -/
abbrev decodeVarintSlowStack : Nat := 0x40 + decodeErrorHookStack

/-- Ghost arguments of `decode_varint_slow::<&mut &[u8]>`. -/
structure DecodeVarintSlowGhost where
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Contract of `prost::encoding::varint::decode_varint_slow::<&mut &[u8]>` (`0x47f64`)
in terms of `decodeVarint`. -/
def decodeVarintSlowSpec (A : RustAlloc) : Spec DecodeVarintSlowGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp decodeVarintSlowStack
  post := fun x s0 sf =>
    (match decodeVarint x.bs with
      | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
      | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
      ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp decodeVarintSlowStack ∗
      match decodeVarint x.bs with
      | some (_, rest) =>
        sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem varintSlow_take_min_10 (bs : List (BitVec 8)) :
    varintSlow (bs.take (min 10 bs.length)) = varintSlow bs := by
  simp only [varintSlow, List.take_take]
  by_cases h : 10 ≤ bs.length
  · rw [Nat.min_eq_left h]; rfl
  · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega),
      List.take_length, List.take_of_length_le (by omega)]

theorem readBytes_min_10_of_pointsToBytes {m : Memory} {ptr : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} (h : m ⊨ (ptr ↦ₛ bs) ∗ R) :
    m.readBytes ptr (min 10 bs.length) = bs.take (min 10 bs.length) := by
  have hsplit : bs = bs.take (min 10 bs.length) ++ bs.drop (min 10 bs.length) :=
    (List.take_append_drop (min 10 bs.length) bs).symm
  have h1 : m ⊨ (ptr ↦ₛ (bs.take (min 10 bs.length) ++ bs.drop (min 10 bs.length))) ∗ R := by
    rwa [← hsplit]
  rw [pointsToBytes_append, sepConj_assoc] at h1
  have h2 := (IsBlock.pointsToBytes ptr (bs.take (min 10 bs.length))).read h1
  have hlen : (bs.take (min 10 bs.length)).length = min 10 bs.length := by
    rw [List.length_take]
    omega
  rw [hlen] at h2
  exact h2.2

theorem satisfies_write64_pointsTo64 {m : Memory} {a v₀ : BitVec 64} (v : BitVec 64) {R : SepProp}
    (h : m ⊨ (a ↦₆₄ v₀) ∗ R) :
    m.write64 a v ⊨ (a ↦₆₄ v) ∗ R :=
  (IsBlock.pointsTo64 a v₀).update (IsBlock.pointsTo64 a v) (le_refl 8) h
    (AgreesOutside.write64_zero (AgreesOutside.rfl' m a 8) (by decide))
    (by simp [arm64_norm])

theorem keepsFrozen_write64_pointsTo64 {m : Memory} {a v₀ : BitVec 64} (v : BitVec 64) {R : SepProp}
    (h : m ⊨ (a ↦₆₄ v₀) ∗ R) :
    m.KeepsFrozen (m.write64 a v) :=
  Memory.keepsFrozen_write64 ((IsBlock.pointsTo64 a v₀).canWrite (by decide) h) v

theorem pointsTo64_pair_entails_memRegion16 (a v0 v1 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) ⊢ memRegion a 16 := by
  rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a v0)
    (pointsTo64_entails_memRegion (a + 8#64) v1)

theorem stackAt_decodeVarintSlow_split (sp : BitVec 64) :
    stackAt sp decodeVarintSlowStack =
      (∃∗ v : BitVec 64, (sp - 64#64) ↦₆₄ v) ∗
        memRegion (sp - 56#64) 40 ∗
        memRegion (sp - 16#64) 16 ∗
        stackAt (sp - 64#64) decodeErrorHookStack := by
  simp only [stackAt, decodeVarintSlowStack, decodeErrorHookStack, allocHookStack]
  have h1 := memRegion_split' (b := sp - 8256#64) (b' := sp - 64#64)
    (n := 8192) (k := 64) (N := 8256) rfl (by bv_omega) (by decide)
  have h2 := memRegion_split' (b := sp - 64#64) (b' := sp - 16#64)
    (n := 48) (k := 16) (N := 64) rfl (by bv_omega) (by decide)
  have h3 := memRegion_split' (b := sp - 64#64) (b' := sp - 56#64)
    (n := 8) (k := 40) (N := 48) rfl (by bv_omega) (by decide)
  have hsp : sp - 64#64 - 8192#64 = sp - 8256#64 := by bv_omega
  rw [hsp, h1, h2, h3, memRegion_eight (sp - 64#64)]
  ac_rfl

theorem stackAt_decodeVarintSlow_join (sp : BitVec 64) :
    memRegion (sp - 64#64) 48 ∗
      memRegion (sp - 16#64) 16 ∗
      stackAt (sp - 64#64) decodeErrorHookStack =
      stackAt sp decodeVarintSlowStack := by
  simp only [stackAt, decodeVarintSlowStack, decodeErrorHookStack, allocHookStack]
  have h1 := memRegion_split' (b := sp - 8256#64) (b' := sp - 64#64)
    (n := 8192) (k := 64) (N := 8256) rfl (by bv_omega) (by decide)
  have h2 := memRegion_split' (b := sp - 64#64) (b' := sp - 16#64)
    (n := 48) (k := 16) (N := 64) rfl (by bv_omega) (by decide)
  have hsp : sp - 64#64 - 8192#64 = sp - 8256#64 := by bv_omega
  rw [hsp, h1, h2]
  ac_rfl

theorem decodeVarintSlow_hookOk {A : RustAlloc} {fromHook : State → State}
    (hFrom : HookOk fromHook (decodeErrorFromSpec A)) :
    HookOk (decodeVarintSlowHook fromHook) (decodeVarintSlowSpec A) := by
  intro x R s0 hrun hpre hsp
  simp only [decodeVarintSlowSpec, sliceCursorAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen_lt⟩, hmem⟩
  have hslot : s0.mem.read64 x.bufRef = x.slot := (IsBlock.pointsTo64 x.bufRef x.slot).read hmem
  have hmem_slot : s0.mem ⊨ (x.slot ↦₆₄ x.ptr) ∗
      ((x.bufRef ↦₆₄ x.slot) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s0.sp decodeVarintSlowStack ∗ R) :=
    Satisfies.of_eq hmem
  have hptr : s0.mem.read64 x.slot = x.ptr := (IsBlock.pointsTo64 x.slot x.ptr).read hmem_slot
  have hmem_len : s0.mem ⊨ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      ((x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s0.sp decodeVarintSlowStack ∗ R) :=
    Satisfies.of_eq hmem
  have hlen_read : s0.mem.read64 (x.slot + 8#64) = BitVec.ofNat 64 x.bs.length :=
    (IsBlock.pointsTo64 (x.slot + 8#64) (BitVec.ofNat 64 x.bs.length)).read hmem_len
  have hlen_nat : (BitVec.ofNat 64 x.bs.length).toNat = x.bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmem_bs : s0.mem ⊨ (x.ptr ↦ₛ x.bs) ∗
      ((x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        A.pool ∗ stackAt s0.sp decodeVarintSlowStack ∗ R) :=
    Satisfies.of_eq hmem
  have hread_bs : s0.mem.readBytes x.ptr (min 10 x.bs.length) = x.bs.take (min 10 x.bs.length) :=
    readBytes_min_10_of_pointsToBytes hmem_bs
  have hvs : varintSlow (s0.mem.readBytes x.ptr (min 10 x.bs.length)) =
      (decodeVarint x.bs).map (fun p => (p.1, x.bs.length - p.2.length)) := by
    rw [hread_bs, varintSlow_take_min_10, decodeVarint_eq_varintSlow]
  have hadv : ∀ k : Nat,
      let m1 := (s0.mem.write64 x.slot (x.ptr + BitVec.ofNat 64 k)).write64
        (x.slot + 8#64) (BitVec.ofNat 64 (x.bs.length - k))
      s0.mem.KeepsFrozen m1 ∧
      (m1 ⊨ (x.bufRef ↦₆₄ x.slot) ∗
        (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 k)) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (x.bs.length - k)) ∗
        (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s0.sp decodeVarintSlowStack ∗ R) := by
    intro k
    have hkf1 := keepsFrozen_write64_pointsTo64 (x.ptr + BitVec.ofNat 64 k) hmem_slot
    have hm1 := satisfies_write64_pointsTo64 (x.ptr + BitVec.ofNat 64 k) hmem_slot
    have hm1' : s0.mem.write64 x.slot (x.ptr + BitVec.ofNat 64 k) ⊨
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        ((x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 k)) ∗
          (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s0.sp decodeVarintSlowStack ∗ R) :=
      Satisfies.of_eq hm1
    have hkf2 := keepsFrozen_write64_pointsTo64 (BitVec.ofNat 64 (x.bs.length - k)) hm1'
    have hm2 := satisfies_write64_pointsTo64 (BitVec.ofNat 64 (x.bs.length - k)) hm1'
    exact ⟨hkf1.trans hkf2, Satisfies.of_eq hm2⟩
  dsimp only [decodeVarintSlowHook]
  rw [hx0, hslot, hptr, hlen_read, hlen_nat, hvs]
  cases hd : decodeVarint x.bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only [Option.map]
    obtain ⟨hkf, hm_adv⟩ := hadv (x.bs.length - rest.length)
    obtain ⟨k, _, hkl, hrest_eq⟩ := decodeVarintAux_suffix x.bs 0 0#64 v rest hd
    have hlen_sub : x.bs.length - (x.bs.length - rest.length) = rest.length := by
      rw [hrest_eq, List.length_drop]; omega
    rw [hlen_sub] at hm_adv
    refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    simp only [decodeVarintSlowSpec, hd, sliceCursorAfter, hlen_sub, retHook,
      arm64_norm, pure_true, emp_sepConj, sepConj_assoc, true_and]
    exact Satisfies.of_eq hm_adv
  | none =>
    dsimp only [Option.map]
    obtain ⟨hkf_adv, hm_adv⟩ := hadv (min 10 x.bs.length)
    have hm_fold : ((s0.mem.write64 x.slot (x.ptr + BitVec.ofNat 64 (min 10 x.bs.length))).write64
        (x.slot + 8#64) (BitVec.ofNat 64 (x.bs.length - min 10 x.bs.length))) ⊨
        stackAt s0.sp decodeVarintSlowStack ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ R := by
      have hm_adv' : ((s0.mem.write64 x.slot (x.ptr + BitVec.ofNat 64 (min 10 x.bs.length))).write64
          (x.slot + 8#64) (BitVec.ofNat 64 (x.bs.length - min 10 x.bs.length))) ⊨
          ((x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (min 10 x.bs.length))) ∗
            ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (x.bs.length - min 10 x.bs.length))) ∗
          (stackAt s0.sp decodeVarintSlowStack ∗ (x.bufRef ↦₆₄ x.slot) ∗
            (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ R) :=
        Satisfies.of_eq hm_adv
      have hm_adv'' := Satisfies.mono
        (sepConj_mono_left (pointsTo64_pair_entails_memRegion16 x.slot _ _)) hm_adv'
      exact Satisfies.of_eq hm_adv''
    rw [stackAt_decodeVarintSlow_split, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      sepExists_sepConj_left, satisfies_sepExists] at hm_fold
    obtain ⟨v_stk, hm_stk⟩ := hm_fold
    have hkf_stk := keepsFrozen_write64_pointsTo64 invalidVarintWord hm_stk
    have hm_stk' := satisfies_write64_pointsTo64 invalidVarintWord hm_stk
    let s1 : State :=
      { s0 with
        sp := s0.sp - 64#64
        mem := (((s0.mem.write64 x.slot (x.ptr + BitVec.ofNat 64 (min 10 x.bs.length))).write64
          (x.slot + 8#64) (BitVec.ofNat 64 (x.bs.length - min 10 x.bs.length))).write64
          (s0.sp - 64#64) invalidVarintWord) }.writeReg64 .x0 (s0.sp - 64#64)
    let R_frame : SepProp :=
      memRegion (s0.sp - 16#64) 16 ∗ (x.bufRef ↦₆₄ x.slot) ∗
        memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
    have hsp1 : s1.spAligned = true := by
      have hsp1_eq : s1.sp = s0.sp - 64#64 := rfl
      simp only [State.spAligned, hsp1_eq] at hsp ⊢
      revert hsp; bv_bits
    have hpre_from : s1.mem ⊨ (decodeErrorFromSpec A).pre (s0.sp - 64#64, invalidVarintWord) s1 ∗ (R_frame ∗ R) := by
      simp only [decodeErrorFromSpec, s1, R_frame, arm64_norm, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨by decide, ?_⟩
      exact Satisfies.of_eq hm_stk'
    obtain ⟨hkf_from, hsym_from, hout_from⟩ :=
      hFrom (s0.sp - 64#64, invalidVarintWord) (R_frame ∗ R) s1 hrun hpre_from hsp1
    have hkf_all : s0.mem.KeepsFrozen (fromHook s1).mem := (hkf_adv.trans hkf_stk).trans hkf_from
    rcases hout_from with ⟨⟨hpc2, hsp2, hrun2⟩, ⟨_, hcs2⟩, hpost2⟩ | ⟨hpan2, hpost2⟩ | ⟨code, hex2, hpost2⟩ | ⟨hoom2, hpost2⟩
    · dsimp only [s1] at hrun2 hcs2 hpost2
      rw [hrun2]
      dsimp only
      refine ⟨hkf_all, hsym_from, Or.inl ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, ?_⟩, ?_⟩⟩
      · simp only [CalleeSavedPreserved, arm64_norm] at hcs2 ⊢
        exact hcs2
      · simp only [decodeErrorFromSpec, R_frame, arm64_norm,
          sepConj_assoc, satisfies_pure_sepConj] at hpost2
        rcases hpost2 with ⟨⟨he_ne, htr2⟩, hmem2⟩
        simp only [decodeVarintSlowSpec, hd, arm64_norm, htr2, ne_eq, he_ne,
          not_false_eq_true, pure_true, emp_sepConj, sepConj_assoc]
        have hjoin := stackAt_decodeVarintSlow_join s0.sp
        exact Satisfies.of_eq hmem2 (by rw [← hjoin]; ac_rfl)
    · dsimp only [s1] at hpan2 hpost2
      rw [hpan2]
      refine ⟨hkf_all, hsym_from, Or.inr (Or.inl ⟨hpan2, ?_⟩)⟩
      dsimp only [decodeErrorFromSpec] at hpost2
      rw [← sepConj_assoc] at hpost2
      dsimp only [decodeVarintSlowSpec]
      exact allowPanic_frame (allocFailedIn_trans rfl) hpost2
    · exact False.elim (not_satisfies_false_sepConj hpost2)
    · exact False.elim (not_satisfies_false_sepConj hpost2)

theorem stackAt_decodeVarintSlowExt_split (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 8128 ∗ stackAt sp decodeVarintSlowStack := by
  change memRegion (sp - 16384#64) 16384 =
    memRegion (sp - 16384#64) 8128 ∗ memRegion (sp - 8256#64) 8256
  exact memRegion_split' (b := sp - 16384#64) (b' := sp - 8256#64)
    (n := 8128) (k := 8256) (N := 16384) rfl (by bv_omega) (by decide)

theorem fnAddr_rebase_offset {b : BitVec 64} {H : String → Option (State → State)}
    {name1 name2 : String} {off1 off2 k : Nat}
    (h1 : libsignalSessionCode.fnOff name1 = off1)
    (h2 : libsignalSessionCode.fnOff name2 = off2)
    (hk : off1 + k = off2) :
    (libsignalSessionCode.rebase b H).fnAddr name1 + BitVec.ofNat 64 k =
      (libsignalSessionCode.rebase b H).fnAddr name2 := by
  change (b + BitVec.ofNat 64 (libsignalSessionCode.fnOff name1)) + BitVec.ofNat 64 k =
    b + BitVec.ofNat 64 (libsignalSessionCode.fnOff name2)
  rw [h1, h2, ← hk, BitVec.ofNat_add, BitVec.add_assoc]

/-- Stack-parameterized contract of `prost::encoding::varint::decode_varint_slow::<&mut &[u8]>` (`0x47f64`)
in terms of `decodeVarint` (`= decodeVarintSlowSpec A` at `decodeErrorHookStack`,
`= decodeVarintSlowSpecX A` at `decodeErrorHookStackX`). -/
def decodeVarintSlowSpecGen (A : RustAlloc) (errStack : Nat) : Spec DecodeVarintSlowGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp (0x40 + errStack)
  post := fun x s0 sf =>
    (match decodeVarint x.bs with
      | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
      | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
      ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp (0x40 + errStack) ∗
      match decodeVarint x.bs with
      | some (_, rest) =>
        sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem decodeVarintSlowGen_ok_of_session2 {oimg : Option Obj.Image} {A : RustAlloc}
    {prog : Program} {entry : BitVec 64} {errStack : Nat}
    (hSlow : subroutine_ok prog entry
      (specWithOptInv oimg
        (CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack A (0x40 + errStack)))) :
    subroutine_ok prog entry (specWithOptInv oimg (decodeVarintSlowSpecGen A errStack)) := by
  refine subroutine_ok_map_panic hSlow fun y R s0 hpre => ?_
  refine ⟨(y.bufRef, y.slot, y.ptr, y.bs), R, ?_, ?_, fun _ h => h⟩
  · simp only [decodeVarintSlowSpecGen,
      CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack,
      sliceCursorAt, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨hpre.1, ⟨hpre.2.1.1, by omega⟩, hpre.2.2⟩
  · intro sf hpost
    have hvs : varintSlow y.bs =
        (decodeVarint y.bs).map (fun p => (p.1, y.bs.length - p.2.length)) :=
      decodeVarint_eq_varintSlow y.bs
    dsimp only [specWithOptInv, CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack,
      decodeVarintSlowSpecGen] at hpost ⊢
    rw [hvs] at hpost
    cases hd : decodeVarint y.bs with
    | some p =>
      rcases p with ⟨v, rest⟩
      rw [hd] at hpost
      dsimp only [Option.map, sliceCursorAfter] at hpost ⊢
      obtain ⟨k, _, _, hrest_eq⟩ := decodeVarintAux_suffix y.bs 0 0#64 v rest hd
      have hlen_sub : y.bs.length - (y.bs.length - rest.length) = rest.length := by
        rw [hrest_eq, List.length_drop]; omega
      rw [hlen_sub] at hpost
      exact Satisfies.of_eq hpost
    | none =>
      rw [hd] at hpost
      dsimp only [Option.map] at hpost ⊢
      have hpost1 : sf.mem ⊨
          ((y.slot ↦₆₄ (y.ptr + BitVec.ofNat 64 (min 10 y.bs.length))) ∗
            ((y.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (y.bs.length - min 10 y.bs.length))) ∗
          (⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
            ⌜sf.trace = s0.trace⌝ ∗
            (y.bufRef ↦₆₄ y.slot) ∗ A.pool ∗ stackAt s0.sp (0x40 + errStack) ∗
            decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗ (y.ptr ↦ₛ y.bs) ∗ R) :=
        Satisfies.of_eq hpost
      have hmem1 := Satisfies.mono
        (sepConj_mono_left (pointsTo64_pair_entails_memRegion16 y.slot _ _)) hpost1
      have hmem2 : sf.mem ⊨
          ⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
          (⌜sf.trace = s0.trace⌝ ∗ (y.bufRef ↦₆₄ y.slot) ∗ A.pool ∗
            stackAt s0.sp (0x40 + errStack) ∗
            decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
            memRegion y.slot 16 ∗ (y.ptr ↦ₛ y.bs) ∗ R) :=
        Satisfies.of_eq hmem1
      rw [satisfies_pure_sepConj] at hmem2
      rcases hmem2 with ⟨⟨hx0, hx1⟩, hmem3⟩
      have hmem4 : sf.mem ⊨
          ⌜sf.readReg64 .x0 = 1#64⌝ ∗
          (⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
            (⌜sf.trace = s0.trace⌝ ∗ (y.bufRef ↦₆₄ y.slot) ∗ A.pool ∗
              stackAt s0.sp (0x40 + errStack) ∗
              decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
              memRegion y.slot 16 ∗ (y.ptr ↦ₛ y.bs) ∗ R)) := by
        rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
        exact ⟨hx0, hx1, hmem3⟩
      exact Satisfies.of_eq hmem4

theorem decodeVarintSlow_ok_of_session2 {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    (hSlow : subroutine_ok prog entry (CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpec A)) :
    subroutine_ok prog entry (decodeVarintSlowSpec A) :=
  subroutine_ok_of_optNone
    (decodeVarintSlowGen_ok_of_session2 (oimg := none) (errStack := decodeErrorHookStack)
      (subroutine_ok_to_optNone hSlow))

theorem decodeVarintSlow_ok_at_of_contract {A : RustAlloc} {b : BitVec 64}
    {H : String → Option (State → State)}
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>"))
    (hSlow : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr varintSlowName)
      (decodeVarintSlowSpec A)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k)
      (decodeVarintSlowSpec A) := by
  rw [fnAddr_rebase_offset hfn (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>") hk]
  exact hSlow

theorem decodeVarintSlow_ok_at_ext {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext)
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (decodeVarintSlowSpec A) :=
  decodeVarintSlow_ok_at_of_contract hfn hk (decodeVarintSlow_ok_of_session2 hC.decode_varint_slow)

/-- Restates the in-image `decode_varint_slow` contract at `fnAddr name + k` in terms of
`decodeVarint` and `sliceCursorAt`. -/
theorem decodeVarintSlow_ok_at {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hFrom : AllocHooks A abs)
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (decodeVarintSlowSpec A) :=
  decodeVarintSlow_ok_at_of_contract hfn hk
    (decodeVarintSlow_ok_of_session2 (LibsignalTripleRatchet.decodeVarintSlow_ok b C A ctl abs hFrom))

/-! ## Helper lemmas for `int32::merge::<&mut &[u8]>` -/

theorem fnAddr_tripleRatchetProgAt_offset {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {name1 name2 : String} {off1 off2 k : Nat}
    (h1 : libsignalSessionCode.fnOff name1 = off1)
    (h2 : libsignalSessionCode.fnOff name2 = off2)
    (hk : off1 + k = off2) :
    (tripleRatchetProgAt b C ctl abs).fnAddr name1 + BitVec.ofNat 64 k =
      (tripleRatchetProgAt b C ctl abs).fnAddr name2 :=
  fnAddr_rebase_offset h1 h2 hk

theorem memRegion_four (a : BitVec 64) : memRegion a 4 = ∃∗ v : BitVec 32, a ↦₃₂ v :=
  IsBlock.eq (IsBlock.memRegion a 4)
    (IsBlock.sepExists fun v => IsBlock.pointsTo32 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem pointsTo8_entails_memRegion1 (a : BitVec 64) (v : BitVec 8) :
    (a ↦₈ v) ⊢ memRegion a 1 := by
  rw [memRegion_one]
  exact Entails.sepExists_intro v

theorem pointsTo32_entails_memRegion4 (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) ⊢ memRegion a 4 := by
  rw [memRegion_four]
  exact Entails.sepExists_intro v

theorem stackAt_int32MergeGen {errStack : Nat} (herr : 0x50 + (0x50 + errStack) ≤ 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (0x50 + (0x50 + errStack)) =
      stackAt (sp - 80#64) (0x50 + errStack) ∗
        memRegion (sp - 80#64) 48 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  have h0 := stackAt_split_cells sp (0x50 + errStack) 10 (by omega)
  rw [← memRegion_cells (sp - BitVec.ofNat 64 (8 * 10)) 10 (by decide)] at h0
  rw [show 0x50 + (0x50 + errStack) = (0x50 + errStack) + 8 * 10 by omega, h0]
  change stackAt (sp - 80#64) (0x50 + errStack) ∗ memRegion (sp - 80#64) 80 = _
  have s1 := memRegion_split (sp - 80#64) 48 32 (by decide)
  rw [bv_sub_add_lit sp 80 48] at s1
  have s2 := memRegion_split (sp - 32#64) 8 24 (by decide)
  rw [bv_sub_add_lit sp 32 8] at s2
  have s3 := memRegion_split (sp - 24#64) 8 16 (by decide)
  rw [bv_sub_add_lit sp 24 8] at s3
  have s4 := memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s4
  rw [s1, s2, s3, s4,
    memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64),
    memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem stackAt_int32Merge (sp : BitVec 64) :
    stackAt sp int32MergeStack =
      stackAt (sp - 80#64) decodeVarintSliceStack ∗
        memRegion (sp - 80#64) 48 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) :=
  stackAt_int32MergeGen (errStack := decodeErrorHookStack) (by decide) sp

/-- Opaque bottom-of-slice address `sp - (0x50 + errStack)` preserved untouched by `[arm64_norm]`. -/
def sliceBot (sp : BitVec 64) (errStack : Nat) : BitVec 64 :=
  sp - BitVec.ofNat 64 (0x50 + errStack)

theorem stackAt_sliceGen_eq_errorHookGen {errStack : Nat} (herr : 0x50 + errStack ≤ 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (0x50 + errStack) =
      memRegion (sliceBot sp errStack) 80 ∗ stackAt sp errStack := by
  unfold sliceBot
  rw [show 0x50 + errStack = errStack + 80 by omega]
  exact ProofLib.stackAt_split_bottom sp errStack 80 (by omega)

theorem stackAt_sliceGen_eq_slowGen {errStack : Nat} (herr : 0x50 + errStack ≤ 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (0x50 + errStack) =
      memRegion (sliceBot sp errStack) 16 ∗ stackAt sp (0x40 + errStack) := by
  unfold sliceBot
  rw [show 0x50 + errStack = (0x40 + errStack) + 16 by omega]
  exact ProofLib.stackAt_split_bottom sp (0x40 + errStack) 16 (by omega)

theorem memRegion_48_wtErr (sp : BitVec 64) :
    memRegion (sp - 80#64) 48 =
      (∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8, ∃∗ v0 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₈ b0) ∗ ((sp - 71#64) ↦₈ b1)) ∗
        memRegion (sp - 70#64) 38 := by
  have s1 := memRegion_split (sp - 80#64) 8 40 (by decide)
  rw [bv_sub_add_lit sp 80 8] at s1
  have s2 := memRegion_split (sp - 72#64) 1 39 (by decide)
  rw [bv_sub_add_lit sp 72 1] at s2
  have s3 := memRegion_split (sp - 71#64) 1 38 (by decide)
  rw [bv_sub_add_lit sp 71 1] at s3
  change memRegion (sp - 71#64) 39 = memRegion (sp - 71#64) 1 ∗ memRegion (sp - 70#64) 38 at s3
  rw [s1, s2, s3, memRegion_eight (sp - 80#64), memRegion_one (sp - 72#64), memRegion_one (sp - 71#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

theorem wtErr_entails_memRegion40 (sp : BitVec 64) (b0 b1 : BitVec 8) :
    ((sp - 72#64) ↦₈ b0) ∗ ((sp - 71#64) ↦₈ b1) ∗ memRegion (sp - 70#64) 38 ⊢
      memRegion (sp - 72#64) 40 := by
  have s2 := memRegion_split (sp - 72#64) 1 39 (by decide)
  rw [bv_sub_add_lit sp 72 1] at s2
  have s3 := memRegion_split (sp - 71#64) 1 38 (by decide)
  rw [bv_sub_add_lit sp 71 1] at s3
  rw [s2, s3]
  exact sepConj_mono (pointsTo8_entails_memRegion1 _ b0)
    (sepConj_mono (pointsTo8_entails_memRegion1 _ b1) (Entails.refl _))

theorem memRegion_48_slice (sp : BitVec 64) :
    memRegion (sp - 80#64) 48 =
      memRegion (sp - 80#64) 24 ∗ memRegion (sp - 56#64) 24 := by
  have s1 := memRegion_split (sp - 80#64) 24 24 (by decide)
  rw [bv_sub_add_lit sp 80 24] at s1
  exact s1

theorem sliceErr_entails_memRegion48 (sp v0 v1 : BitVec 64) :
    ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
      memRegion (sp - 64#64) 8 ∗ memRegion (sp - 56#64) 24 ⊢
      memRegion (sp - 80#64) 48 := by
  have s1 := memRegion_split (sp - 80#64) 8 40 (by decide)
  rw [bv_sub_add_lit sp 80 8] at s1
  have s2 := memRegion_split (sp - 72#64) 8 32 (by decide)
  rw [bv_sub_add_lit sp 72 8] at s2
  have s3 := memRegion_split (sp - 64#64) 8 24 (by decide)
  rw [bv_sub_add_lit sp 64 8] at s3
  rw [s1, s2, s3]
  exact sepConj_mono (pointsTo64_entails_memRegion8 _ v0)
    (sepConj_mono (pointsTo64_entails_memRegion8 _ v1) (Entails.refl _))

theorem sliceOk_entails_memRegion48 (sp v0 v1 v2 : BitVec 64) :
    ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
      ((sp - 64#64) ↦₆₄ v2) ∗ memRegion (sp - 56#64) 24 ⊢
      memRegion (sp - 80#64) 48 := by
  refine Entails.trans ?_ (sliceErr_entails_memRegion48 sp v0 v1)
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion8 _ v2)))

theorem wt_beq_zero_of_varint {w : BitVec 64} (h : w.setWidth 8 = 0#8) :
    (BitVec.truncate 32 w &&& 255#32 == 0#32) = true := by
  revert h; bv_bits

theorem wt_beq_zero_of_ne_varint {w : BitVec 64} {wt : WireType}
    (h : w.setWidth 8 = BitVec.ofNat 8 wt.toNat) (hne : wt ≠ .varint) :
    (BitVec.truncate 32 w &&& 255#32 == 0#32) = false := by
  cases wt <;> first | contradiction | (dsimp [WireType.toNat] at h; revert h; bv_bits)

theorem mergeUint32_ne_varint {wt : WireType} (bs : List (BitVec 8)) (hne : wt ≠ .varint) :
    mergeUint32 wt bs = none := by
  cases wt <;> first | contradiction | rfl

theorem mergeUint32_varint_1 {b0 : BitVec 8} (bs1 : List (BitVec 8)) (hb0 : b0 ≤ 0x7f#8) :
    mergeUint32 .varint (b0 :: bs1) =
      some (BitVec.truncate 32 (BitVec.signExtend 64 b0), bs1) := by
  have hd : decodeVarint (b0 :: bs1) = some ((b0 &&& 0x7f#8).zeroExtend 64, bs1) := by
    rw [decodeVarint, decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0]
  simp only [mergeUint32, ne_eq, not_true_eq_false, ite_false, hd,
    Option.some.injEq, Prod.mk.injEq, and_true]
  revert hb0; bv_bits

theorem cbz_len_cons_false {b0 : BitVec 8} {bs1 : List (BitVec 8)}
    (hlen : (b0 :: bs1).length < 2 ^ 63) :
    (BitVec.ofNat 64 (b0 :: bs1).length == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  simp at h1

theorem ult_10_of_ge_11 {n : Nat} (h11 : 11 ≤ n) (hlt : n < 2 ^ 63) :
    (10#64).ult (BitVec.ofNat 64 n) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_true_eq]
  omega

theorem ult_10_of_lt_11 {n : Nat} (h11 : ¬ 11 ≤ n) (_hlt : n < 2 ^ 63) :
    (10#64).ult (BitVec.ofNat 64 n) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

theorem len_ult_consumed_false {bs rest : List (BitVec 8)} (_hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 (bs.length - rest.length)) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : bs.length - rest.length < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

theorem bv_len_sub_consumed {bs rest : List (BitVec 8)} {v : BitVec 64}
    (hd : decodeVarint bs = some (v, rest)) :
    BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (bs.length - rest.length) =
      BitVec.ofNat 64 rest.length := by
  obtain ⟨k, _, hkl, hrest_eq⟩ := decodeVarintAux_suffix bs 0 0#64 v rest hd
  have hsplit : bs.length = rest.length + (bs.length - rest.length) := by
    rw [hrest_eq, List.length_drop]; omega
  conv => lhs; arg 1; rw [hsplit]
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem len_cons_sub_one (b0 : BitVec 8) (bs1 : List (BitVec 8)) :
    BitVec.ofNat 64 (b0 :: bs1).length - 1#64 = BitVec.ofNat 64 bs1.length := by
  change BitVec.ofNat 64 (bs1.length + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 bs1.length
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

/-! ## Main proof of `prost::encoding::int32::merge::<&mut &[u8]>` (`0x2bc4`) -/

/-- Stack-parameterized `int32MergeSpec` (`= int32MergeSpec A` at `decodeErrorHookStack`,
`= int32MergeSpecX A` at `decodeErrorHookStackX`, `= int32MergeSpecW A` at `decodeErrorHookStackW`). -/
def int32MergeSpecGen (A : RustAlloc) (errStack : Nat) : Spec Int32MergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63⌝ ∗
      memRegion x.valPtr 4 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp (0x50 + (0x50 + errStack))
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp (0x50 + (0x50 + errStack)) ∗
      match mergeUint32 x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ (x.valPtr ↦₃₂ v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.valPtr 4 ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

section
attribute [local irreducible] _root_.Arm64.Program.fnOff

theorem int32Merge_ok_of_hooks_gen {oimg : Option Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)} {errStack : Nat}
    (herr : 0x50 + (0x50 + errStack) ≤ 2 ^ 64)
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr int32MergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
      (specWithOptInv oimg (decodeErrorFromSpecWithStack A errStack)))
    (hSlowCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr int32MergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
      (specWithOptInv oimg (decodeVarintSlowSpecGen A errStack)))
    (hSlice : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr decodeVarintSliceName)
      (specWithOptInv oimg (decodeVarintSliceSpecGen A errStack))) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr int32MergeName)
      (specWithOptInv oimg (int32MergeSpecGen A errStack)) := by
  have herrSlice : 0x50 + errStack ≤ 2 ^ 64 := by omega
  have hfn := (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")
  have hfn_slice := (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")
  have hSliceCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr int32MergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
      (specWithOptInv oimg (decodeVarintSliceSpecGen A errStack)) := by
    rw [fnAddr_rebase_offset hfn hfn_slice (by decide)]
    exact hSlice
  clear hSlice hfn_slice
  tripleRatchet_fetches b H hfn (num% (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) 300
  clear hfn
  conv =>
    arg 3; arg 2
    unfold int32MergeSpecGen
    simp only [sliceCursorAt, stackAt_int32MergeGen herr, sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_optImage x s0 hinv0
  rcases x with ⟨wt, valPtr, bufRef, slot, ptr, bs⟩
  dsimp only at *
  examples_generalize_entry
  examples_hide_fetches
  by_cases hwt : wt = .varint
  · subst hwt
    have hwt_br := wt_beq_zero_of_varint h_1
    cases bs with
    | nil =>
      simp only [mergeUint32, decodeVarint, decodeVarintAux, ne_eq, not_true_eq_false, ite_false]
      apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) hinv0
      conv => arg 4; rw [memRegion_48_split (s0.sp - 80#64), bv_sub_add_lit s0.sp 80 8]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v_err0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr 0#64) (by sep_focus)
      conv => arg 4; rw [stackAt_sliceGen_eq_errorHookGen herrSlice (s0.sp - 80#64)]
      wp_reach
      intro hinv1
      refine SepWPp.call_frame_optImage (oimg := oimg) (spec := decodeErrorFromSpecWithStack A errStack)
        (x := (s0.sp - 80#64, 0x8000000000000001#64))
        (ret_pc := entry + bv% (52)) hFromCall hinv1
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
        (by simp only [arm64_norm])
        (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
        (⟨rfl, by decide⟩ : s0.sp - 80#64 = s0.sp - 80#64 ∧ KindNoHeap 0x8000000000000001#64)
        (by sep_focus)
        (fun _ _ _ _ hex => allowPanic_not_exited hex)
        (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
      intro sm hpcm hrunm hspm hcsm _
      apply SepWPp.of_sepWP_ret
      simp only [decodeErrorFromSpecWithStack, arm64_norm]
      apply SepWP.fold (Entails.of_eq (stackAt_sliceGen_eq_errorHookGen herrSlice (s0.sp - 80#64)).symm) (by sep_focus)
      wp_steps
      wp_done
    | cons b0 bs1 =>
      have hcbz := cbz_len_cons_false h
      by_cases hb0 : b0 ≤ 0x7f#8
      · have hbit0 := signExtend64_getLsbD_63_of_le hb0
        rw [mergeUint32_varint_1 bs1 hb0]
        apply SepWPp.of_sepWP_ret
        conv => arg 4; rw [pointsToBytes_cons, memRegion_four valPtr]
        simp only [sepExists_sepConj_left]
        apply SepWP.exists_elim; intro v_val
        wp_steps
        conv => arg 4; rw [len_cons_sub_one b0 bs1, ← pointsToBytes_cons]
        simp only [sliceCursorAfter, List.length_cons, Nat.add_sub_cancel_left]
        wp_done
      · have hbit0 := signExtend64_getLsbD_63_of_gt hb0
        have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        apply SepWPp.of_sepWP_optImage (mid := entry + bv% (144)) hinv0
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps
        wp_reach
        intro hinv1
        by_cases h11 : 11 ≤ (b0 :: bs1).length
        · have hhi := ult_10_of_ge_11 h11 h
          have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inl h11
          apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) hinv1
          conv => arg 4; rw [memRegion_48_slice s0.sp]
          wp_steps
          wp_reach
          intro hinv2
          refine SepWPp.call_frame_optImage (oimg := oimg) (spec := decodeVarintSliceSpecGen A errStack)
            (x := ⟨s0.sp - 80#64, ptr, b0 :: bs1⟩)
            (ret_pc := entry + bv% (176)) hSliceCall hinv2
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [decodeVarintSliceSpecGen, arm64_norm]; rfl)
            (⟨rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
              s0.sp - 80#64 = s0.sp - 80#64 ∧ ptr = ptr ∧
                (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
            (by sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
          intro sm hpcm hrunm hspm hcsm _
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          apply SepWPp.of_sepWP_ret
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            simp only [decodeVarintSliceSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false, varintSliceResultAt,
              sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
            apply SepWP.exists_elim; intro e_err
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
            apply SepWP.fold (sliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
            wp_done
          | some p =>
            rcases p with ⟨v, rest⟩
            have hcc := len_ult_consumed_false (rest := rest) h
            have hsub_len := bv_len_sub_consumed hd
            simp only [decodeVarintSliceSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false, varintSliceResultAt,
              sliceCursorAfter, arm64_norm]
            conv => arg 4; rw [memRegion_four valPtr]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWP.exists_elim; intro v_val
            wp_steps
            apply SepWP.fold (sliceOk_entails_memRegion48 s0.sp 0#64 v (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
            wp_done
        · have hhi := ult_10_of_lt_11 h11 h
          have hne_cons : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
          apply SepWPp.of_sepWP_optImage (mid := entry + bv% (156)) hinv1
          conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
          wp_steps
          conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
          wp_reach
          intro hinv2
          by_cases hlast : ((b0 :: bs1).getLast hne_cons).toNat ≤ 0x7F
          · have hbit_last := getLsbD_7_of_le hlast
            have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inr ⟨hne_cons, hlast⟩
            apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) hinv2
            conv => arg 4; rw [pointsToBytes_cons, memRegion_48_slice s0.sp]
            wp_steps
            wp_reach
            intro hinv3
            refine SepWPp.call_frame_optImage (oimg := oimg) (spec := decodeVarintSliceSpecGen A errStack)
              (x := ⟨s0.sp - 80#64, ptr, b0 :: bs1⟩)
              (ret_pc := entry + bv% (176)) hSliceCall hinv3
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [decodeVarintSliceSpecGen, arm64_norm]; rfl)
              (⟨rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
                s0.sp - 80#64 = s0.sp - 80#64 ∧ ptr = ptr ∧
                  (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                  (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
              (by sep_focus)
              (fun _ _ _ _ hex => allowPanic_not_exited hex)
              (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
            intro sm hpcm hrunm hspm hcsm _
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            apply SepWPp.of_sepWP_ret
            cases hd : decodeVarint (b0 :: bs1) with
            | none =>
              simp only [decodeVarintSliceSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false, varintSliceResultAt,
                sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
              apply SepWP.exists_elim; intro e_err
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
              apply SepWP.fold (sliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
              wp_done
            | some p =>
              rcases p with ⟨v, rest⟩
              have hcc := len_ult_consumed_false (rest := rest) h
              have hsub_len := bv_len_sub_consumed hd
              simp only [decodeVarintSliceSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false, varintSliceResultAt,
                sliceCursorAfter, arm64_norm]
              conv => arg 4; rw [memRegion_four valPtr]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_val
              wp_steps
              apply SepWP.fold (sliceOk_entails_memRegion48 s0.sp 0#64 v (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
              wp_done
          · have hbit_last := getLsbD_7_of_gt hlast
            apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) hinv2
            wp_steps
            conv => arg 4; rw [stackAt_sliceGen_eq_slowGen herrSlice (s0.sp - 80#64)]
            wp_reach
            intro hinv3
            refine SepWPp.call_frame_optImage (oimg := oimg) (spec := decodeVarintSlowSpecGen A errStack)
              (x := ⟨bufRef, slot, ptr, b0 :: bs1⟩)
              (ret_pc := entry + bv% (268)) hSlowCall hinv3
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [decodeVarintSlowSpecGen, arm64_norm]; rfl)
              (⟨rfl, h⟩ : bufRef = bufRef ∧ (b0 :: bs1).length < 2 ^ 63)
              (by simp only [sliceCursorAt]; sep_focus)
              (fun _ _ _ _ hex => allowPanic_not_exited hex)
              (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
            intro sm hpcm hrunm hspm hcsm _
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            apply SepWPp.of_sepWP_ret
            cases hd : decodeVarint (b0 :: bs1) with
            | none =>
              simp only [decodeVarintSlowSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false,
                sepConj_assoc, arm64_norm]
              apply SepWP.pure_elim; intro hsm0
              apply SepWP.fold (Entails.of_eq (stackAt_sliceGen_eq_slowGen herrSlice (s0.sp - 80#64)).symm) (by sep_focus)
              wp_steps
              wp_done
            | some p =>
              rcases p with ⟨v, rest⟩
              simp only [decodeVarintSlowSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false,
                sepConj_assoc, arm64_norm]
              apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
              apply SepWP.fold (Entails.of_eq (stackAt_sliceGen_eq_slowGen herrSlice (s0.sp - 80#64)).symm) (by sep_focus)
              conv => arg 4; rw [memRegion_four valPtr]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_val
              wp_steps
              wp_done
  · have hwt_br := wt_beq_zero_of_ne_varint h_1 hwt
    rw [mergeUint32_ne_varint bs hwt]
    apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) hinv0
    conv => arg 4; rw [memRegion_48_wtErr s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro b_err1
    apply SepWP.exists_elim; intro b_err0
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (wtErr_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
    conv => arg 4; rw [stackAt_sliceGen_eq_errorHookGen herrSlice (s0.sp - 80#64)]
    wp_reach
    intro hinv1
    refine SepWPp.call_frame_optImage (oimg := oimg) (spec := decodeErrorFromSpecWithStack A errStack)
      (x := (s0.sp - 80#64, 0x8000000000000006#64))
      (ret_pc := entry + bv% (52)) hFromCall hinv1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 80#64 = s0.sp - 80#64 ∧ KindNoHeap 0x8000000000000006#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _
    apply SepWPp.of_sepWP_ret
    simp only [decodeErrorFromSpecWithStack, arm64_norm]
    apply SepWP.fold (Entails.of_eq (stackAt_sliceGen_eq_errorHookGen herrSlice (s0.sp - 80#64)).symm) (by sep_focus)
    wp_steps
    wp_done

end

theorem int32Merge_ok_of_contracts {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr int32MergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
      (decodeErrorFromSpec A))
    (hSlowCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr int32MergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
      (decodeVarintSlowSpec A))
    (hSlice : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr decodeVarintSliceName)
      (decodeVarintSliceSpec A)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr int32MergeName)
      (int32MergeSpec A) :=
  subroutine_ok_of_optNone
    (int32Merge_ok_of_hooks_gen (oimg := none) (errStack := decodeErrorHookStack) (by decide)
      (subroutine_ok_to_optNone hFromCall)
      (subroutine_ok_to_optNone hSlowCall)
      (subroutine_ok_to_optNone hSlice))

theorem int32Merge_ok_ext {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext) :
    Int32MergeOkExt b A ext :=
  int32Merge_ok_of_contracts
    (hC.decode_error_from_ok_at int32MergeName (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
      (by fnoff_eq))
    (decodeVarintSlow_ok_at_ext hC (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>") (k := num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) (by decide))
    (decodeVarintSlice_ok_ext hC)

theorem int32Merge_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hFrom : AllocHooks A abs) :
    Int32MergeOk b C A ctl abs :=
  int32Merge_ok_of_contracts
    (decodeErrorFrom_ok_at (b := b) (C := C) (ctl := ctl)
      hFrom (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>") (k := num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) (by decide))
    (decodeVarintSlow_ok_at (b := b) (C := C) (ctl := ctl)
      hFrom (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>") (k := num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) (by decide))
    (decodeVarintSlice_ok hFrom)

/-! ## Extended-stack variants (`decodeVarintSlowSpecX` and `int32MergeSpecX`) -/

/-- Stack budget for `decode_varint_slow::<&mut &[u8]>` (`0x47f64`) with `decodeErrorHookStackX`. -/
abbrev decodeVarintSlowStackX : Nat := 0x40 + decodeErrorHookStackX

/-- Contract of `prost::encoding::varint::decode_varint_slow::<&mut &[u8]>` (`0x47f64`)
in terms of `decodeVarint` with `decodeVarintSlowStackX`. -/
abbrev decodeVarintSlowSpecX (A : RustAlloc) : Spec DecodeVarintSlowGhost :=
  decodeVarintSlowSpecGen A decodeErrorHookStackX

theorem decodeVarintSlowSpecWithStack_inImage_mono {P : Program} {addr : BitVec 64} {img : Obj.Image}
    {A : RustAlloc} {s1 s2 : Nat}
    (h : subroutine_ok P addr ((CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack A s1).inImage img))
    (hle : s1 ≤ s2 := by decide) (hmax : s2 ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr ((CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack A s2).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨slotA, slot, ptr, bs⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ ((CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack A s1).inImage img).pre
      (slotA, slot, ptr, bs) s0 ∗ R' := by
    dsimp only [Spec.inImage, CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (slotA, slot, ptr, bs) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack, R'] at hpost ⊢
    rw [← sepConj_assoc] at hpost
    exact allowPanic_frame id hpost
  · dsimp only [Spec.inImage, CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [Spec.inImage, CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem decodeVarintSlowX_ok_of_session2 {img : Obj.Image} {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    (hSlow0 : subroutine_ok prog entry
      ((CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack A decodeVarintSlowStackX).inImage img)) :
    subroutine_ok prog entry ((decodeVarintSlowSpecX A).inImage img) :=
  decodeVarintSlowGen_ok_of_session2 (oimg := some img) (errStack := decodeErrorHookStackX) hSlow0

theorem decodeVarintSlowX_ok_at_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((decodeVarintSlowSpecX A).inImage img) := by
  rw [fnAddr_rebase_offset hfn (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>") hk]
  exact decodeVarintSlowX_ok_of_session2 hC.decode_varint_slow

theorem stackAt_int32MergeX (sp : BitVec 64) :
    stackAt sp int32MergeStackX =
      stackAt (sp - 80#64) decodeVarintSliceStackX ∗
        memRegion (sp - 80#64) 48 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) :=
  stackAt_int32MergeGen (errStack := decodeErrorHookStackX) (by decide) sp

theorem int32Merge_ok_of_contracts_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall0 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr int32MergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hSlowCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr int32MergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
      ((decodeVarintSlowSpecX A).inImage img))
    (hSlice : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarintSliceName)
      ((decodeVarintSliceSpecX A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr int32MergeName)
      ((int32MergeSpecX A).inImage img) :=
  int32Merge_ok_of_hooks_gen (oimg := some img) (errStack := decodeErrorHookStackX)
    (by decide) hFromCall0 hSlowCall hSlice

theorem int32Merge_ok_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    Int32MergeOkExtX img A ext :=
  int32Merge_ok_of_contracts_x
    (hC.decode_error_from_ok_at int32MergeName (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
      (by fnoff_eq))
    (decodeVarintSlowX_ok_at_ext hC (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>") (k := num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) (by decide))
    (decodeVarintSlice_ok_ext_x hC)

/-! ## Relocatable per-block proofs (blocks 8 and 293) -/

theorem subroutine_ok_lscl_of_sepWPp {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {pl : Obj.MultiPlacement}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      LibsignalCodeLoaded pl s0.mem →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPp prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_comm (spec.pre x s0), sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h x R s0 hpc hrun hpre.1 hpre.2 hsp

open Lean Elab Tactic Meta in
elab "wpp_init_lscl " a:ident s0:ident hcl:ident : tactic => do
  let rId := mkIdent `R
  let hpcId := mkIdent `hpc
  let hrunId := mkIdent `hrun
  let hpreId := mkIdent `hpre
  let hspId := mkIdent `hsp_align
  evalTactic (← `(tactic| (
    apply subroutine_ok_lscl_of_sepWPp
    wp_unfold_specs
    intro $a:ident $rId:ident $s0:ident $hpcId:ident $hrunId:ident $hcl:ident $hpreId:ident $hspId:ident)))
  wpSplitAndNormHyps (unpackProds := false)
  let g ← getMainGoal
  let (pExpr, fExpr) ← g.withContext do
    let lctx ← getLCtx
    let rFVar := (lctx.findFromUserName? rId.getId).map (·.toExpr)
    let mut fullPreOpt : Option Expr := none
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``SepProp.Satisfies 2 then
          fullPreOpt := some (ty.getArg! 0)
          break
    let fullPre := fullPreOpt.getD (rFVar.getD (mkConst ``SepProp.emp))
    let atoms := SepSolver.atoms fullPre
    let spatial := atoms.filter (fun (e : Expr) => rFVar != some e)
    let conj : Expr :=
      if spatial.isEmpty then mkConst ``SepProp.emp
      else
        let n := spatial.size
        (List.range (n - 1)).foldr
          (fun i acc => mkApp2 (mkConst ``SepProp.sepConj) spatial[i]! acc) spatial[n - 1]!
    Pure.pure (conj, rFVar.getD (mkConst ``SepProp.emp))
  let pStx ← g.withContext (PrettyPrinter.delab pExpr)
  let fStx ← g.withContext (PrettyPrinter.delab fExpr)
  evalTactic (← `(tactic| (
    refine ⟨$pStx, $fStx, ?_, ?_⟩
    wp_focus_close arm64_sep_close)))

theorem int32_merge_placed_ok_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {errStack : Nat}
    (herr : 0x50 + (0x50 + errStack) ≤ 2 ^ 64)
    (hFromCall : subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A errStack)))
    (hSlowCall : subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowSpecGen A errStack)))
    (hSliceCall : subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpecGen A errStack))) :
    subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
      (blkPl_8).base
      (withLsCodeLoaded lsmpl (int32MergeSpecGen A errStack)) := by
  have herrSlice : 0x50 + errStack ≤ 2 ^ 64 := by omega
  conv =>
    arg 3; arg 2
    unfold int32MergeSpecGen
    simp only [sliceCursorAt, stackAt_int32MergeGen herr, sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_lscl x s0 hcl0
  rcases x with ⟨wt, valPtr, bufRef, slot, ptr, bs⟩
  dsimp only at *
  by_cases hwt : wt = .varint
  · subst hwt
    have hwt_br := wt_beq_zero_of_varint h_1
    cases bs with
    | nil =>
      simp only [mergeUint32, decodeVarint, decodeVarintAux, ne_eq, not_true_eq_false, ite_false]
      apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
      conv => arg 4; rw [memRegion_48_split (s0.sp - 80#64), bv_sub_add_lit s0.sp 80 8]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v_err0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr 0#64) (by sep_focus)
      conv => arg 4; rw [stackAt_sliceGen_eq_errorHookGen herrSlice (s0.sp - 80#64)]
      wp_reach
      intro hcl1
      refine SepWPp.call_frame_lscl (pl := lsmpl) (spec := decodeErrorFromSpecWithStack A errStack)
        (x := (s0.sp - 80#64, 0x8000000000000001#64))
        (ret_pc := (blkPl_8).base + bv% (52)) hFromCall hcl1
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
        (by simp only [arm64_norm])
        (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
        (⟨rfl, by decide⟩ : s0.sp - 80#64 = s0.sp - 80#64 ∧ KindNoHeap 0x8000000000000001#64)
        (by sep_focus)
        (fun _ _ _ _ hex => allowPanic_not_exited hex)
        (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
      intro sm hpcm hrunm hspm hcsm _
      apply SepWPp.of_sepWP_ret
      simp only [decodeErrorFromSpecWithStack, arm64_norm]
      apply SepWP.fold (Entails.of_eq (stackAt_sliceGen_eq_errorHookGen herrSlice (s0.sp - 80#64)).symm) (by sep_focus)
      wp_steps
      wp_done
    | cons b0 bs1 =>
      have hcbz := cbz_len_cons_false h
      by_cases hb0 : b0 ≤ 0x7f#8
      · have hbit0 := signExtend64_getLsbD_63_of_le hb0
        rw [mergeUint32_varint_1 bs1 hb0]
        apply SepWPp.of_sepWP_ret
        conv => arg 4; rw [pointsToBytes_cons, memRegion_four valPtr]
        simp only [sepExists_sepConj_left]
        apply SepWP.exists_elim; intro v_val
        wp_steps
        conv => arg 4; rw [len_cons_sub_one b0 bs1, ← pointsToBytes_cons]
        simp only [sliceCursorAfter, List.length_cons, Nat.add_sub_cancel_left]
        wp_done
      · have hbit0 := signExtend64_getLsbD_63_of_gt hb0
        have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_8).base + bv% (144)) hcl0
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps
        wp_reach
        intro hcl1
        by_cases h11 : 11 ≤ (b0 :: bs1).length
        · have hhi := ult_10_of_ge_11 h11 h
          have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inl h11
          apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl1
          conv => arg 4; rw [memRegion_48_slice s0.sp]
          wp_steps
          wp_reach
          intro hcl2
          refine SepWPp.call_frame_lscl (pl := lsmpl) (spec := decodeVarintSliceSpecGen A errStack)
            (x := ⟨s0.sp - 80#64, ptr, b0 :: bs1⟩)
            (ret_pc := (blkPl_8).base + bv% (176)) hSliceCall hcl2
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [decodeVarintSliceSpecGen, arm64_norm]; rfl)
            (⟨rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
              s0.sp - 80#64 = s0.sp - 80#64 ∧ ptr = ptr ∧
                (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
            (by sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
          intro sm hpcm hrunm hspm hcsm _
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          apply SepWPp.of_sepWP_ret
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            simp only [decodeVarintSliceSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false, varintSliceResultAt,
              sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
            apply SepWP.exists_elim; intro e_err
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
            apply SepWP.fold (sliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
            wp_done
          | some p =>
            rcases p with ⟨v, rest⟩
            have hcc := len_ult_consumed_false (rest := rest) h
            have hsub_len := bv_len_sub_consumed hd
            simp only [decodeVarintSliceSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false, varintSliceResultAt,
              sliceCursorAfter, arm64_norm]
            conv => arg 4; rw [memRegion_four valPtr]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWP.exists_elim; intro v_val
            wp_steps
            apply SepWP.fold (sliceOk_entails_memRegion48 s0.sp 0#64 v (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
            wp_done
        · have hhi := ult_10_of_lt_11 h11 h
          have hne_cons : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
          apply SepWPp.of_sepWP_lscl (mid := (blkPl_8).base + bv% (156)) hcl1
          conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
          wp_steps
          conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
          wp_reach
          intro hcl2
          by_cases hlast : ((b0 :: bs1).getLast hne_cons).toNat ≤ 0x7F
          · have hbit_last := getLsbD_7_of_le hlast
            have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inr ⟨hne_cons, hlast⟩
            apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl2
            conv => arg 4; rw [pointsToBytes_cons, memRegion_48_slice s0.sp]
            wp_steps
            wp_reach
            intro hcl3
            refine SepWPp.call_frame_lscl (pl := lsmpl) (spec := decodeVarintSliceSpecGen A errStack)
              (x := ⟨s0.sp - 80#64, ptr, b0 :: bs1⟩)
              (ret_pc := (blkPl_8).base + bv% (176)) hSliceCall hcl3
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [decodeVarintSliceSpecGen, arm64_norm]; rfl)
              (⟨rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
                s0.sp - 80#64 = s0.sp - 80#64 ∧ ptr = ptr ∧
                  (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                  (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
              (by sep_focus)
              (fun _ _ _ _ hex => allowPanic_not_exited hex)
              (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
            intro sm hpcm hrunm hspm hcsm _
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            apply SepWPp.of_sepWP_ret
            cases hd : decodeVarint (b0 :: bs1) with
            | none =>
              simp only [decodeVarintSliceSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false, varintSliceResultAt,
                sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
              apply SepWP.exists_elim; intro e_err
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
              apply SepWP.fold (sliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
              wp_done
            | some p =>
              rcases p with ⟨v, rest⟩
              have hcc := len_ult_consumed_false (rest := rest) h
              have hsub_len := bv_len_sub_consumed hd
              simp only [decodeVarintSliceSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false, varintSliceResultAt,
                sliceCursorAfter, arm64_norm]
              conv => arg 4; rw [memRegion_four valPtr]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_val
              wp_steps
              apply SepWP.fold (sliceOk_entails_memRegion48 s0.sp 0#64 v (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
              wp_done
          · have hbit_last := getLsbD_7_of_gt hlast
            apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 293) hcl2
            wp_steps
            conv => arg 4; rw [stackAt_sliceGen_eq_slowGen herrSlice (s0.sp - 80#64)]
            wp_reach
            intro hcl3
            refine SepWPp.call_frame_lscl (pl := lsmpl) (spec := decodeVarintSlowSpecGen A errStack)
              (x := ⟨bufRef, slot, ptr, b0 :: bs1⟩)
              (ret_pc := (blkPl_8).base + bv% (268)) hSlowCall hcl3
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [decodeVarintSlowSpecGen, arm64_norm]; rfl)
              (⟨rfl, h⟩ : bufRef = bufRef ∧ (b0 :: bs1).length < 2 ^ 63)
              (by simp only [sliceCursorAt]; sep_focus)
              (fun _ _ _ _ hex => allowPanic_not_exited hex)
              (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
            intro sm hpcm hrunm hspm hcsm _
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            apply SepWPp.of_sepWP_ret
            cases hd : decodeVarint (b0 :: bs1) with
            | none =>
              simp only [decodeVarintSlowSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false,
                sepConj_assoc, arm64_norm]
              apply SepWP.pure_elim; intro hsm0
              apply SepWP.fold (Entails.of_eq (stackAt_sliceGen_eq_slowGen herrSlice (s0.sp - 80#64)).symm) (by sep_focus)
              wp_steps
              wp_done
            | some p =>
              rcases p with ⟨v, rest⟩
              simp only [decodeVarintSlowSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false,
                sepConj_assoc, arm64_norm]
              apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
              apply SepWP.fold (Entails.of_eq (stackAt_sliceGen_eq_slowGen herrSlice (s0.sp - 80#64)).symm) (by sep_focus)
              conv => arg 4; rw [memRegion_four valPtr]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_val
              wp_steps
              wp_done
  · have hwt_br := wt_beq_zero_of_ne_varint h_1 hwt
    rw [mergeUint32_ne_varint bs hwt]
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
    conv => arg 4; rw [memRegion_48_wtErr s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro b_err1
    apply SepWP.exists_elim; intro b_err0
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (wtErr_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
    conv => arg 4; rw [stackAt_sliceGen_eq_errorHookGen herrSlice (s0.sp - 80#64)]
    wp_reach
    intro hcl1
    refine SepWPp.call_frame_lscl (pl := lsmpl) (spec := decodeErrorFromSpecWithStack A errStack)
      (x := (s0.sp - 80#64, 0x8000000000000006#64))
      (ret_pc := (blkPl_8).base + bv% (52)) hFromCall hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 80#64 = s0.sp - 80#64 ∧ KindNoHeap 0x8000000000000006#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _
    apply SepWPp.of_sepWP_ret
    simp only [decodeErrorFromSpecWithStack, arm64_norm]
    apply SepWP.fold (Entails.of_eq (stackAt_sliceGen_eq_errorHookGen herrSlice (s0.sp - 80#64)).symm) (by sep_focus)
    wp_steps
    wp_done

section VarintSlowPlaced

open CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow

theorem stackAt_varintSlowGen {errStack : Nat} (herr : 0x40 + errStack ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (0x40 + errStack) =
      stackAt (sp - 64#64) errStack ∗
        memRegion (sp - 56#64) 40 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v8 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v8) ∗ ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  have h0 := ProofLib.stackAt_split_cells sp errStack 8 (by omega)
  rw [← ProofLib.memRegion_cells (sp - BitVec.ofNat 64 (8 * 8)) 8 (by decide)] at h0
  rw [show 0x40 + errStack = errStack + 8 * 8 by omega, h0]
  change stackAt (sp - 64#64) errStack ∗ memRegion (sp - 64#64) 64 = _
  have s1 := ProofLib.memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [bv_sub_add_lit sp 64 8] at s1
  have s2 := ProofLib.memRegion_split (sp - 56#64) 40 16 (by decide)
  rw [bv_sub_add_lit sp 56 40] at s2
  have s3 := ProofLib.memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s3
  rw [s1, s2, s3,
    ProofLib.memRegion_eight (sp - 64#64), ProofLib.memRegion_eight (sp - 16#64), ProofLib.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

theorem decode_varint_slow_placed_ok_with_stack [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {errStack : Nat}
    (herr_stk : 0x40 + errStack ≤ 2 ^ 64)
    (hFromCall : subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A errStack))) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack A (0x40 + errStack))) := by
  conv =>
    arg 3; arg 2
    unfold CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack
    simp only [stackAt_varintSlowGen herr_stk, sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_lscl x s0 hinv0
  obtain ⟨slotA, slot, ptr, bs⟩ := x
  dsimp only at *
  have herr : ∀ {s : State} (k : Nat),
      varintSlow bs = none →
      min 10 bs.length = k →
      StateAt s0 s ((blkPl_293).base + bv% (76)) →
      LibsignalCodeLoaded lsmpl s.mem →
      SepWPp ((blkPC_293).rebase (blkPl_293).base H) (s0.readReg64 Reg.lr) s
        (slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗ A.pool ∗
          stackAt (s0.sp - 64#64) errStack ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
              sf.mem ⊨
                (∃∗ x, ∃∗ x_1, ∃∗ x_2,
                  ⌜sf.trace = s0.trace⌝ ∗
                    slotA ↦₆₄ slot ∗ ptr ↦ₛ bs ∗ A.pool ∗
                    (stackAt (s0.sp - 64#64) errStack ∗
                      memRegion (s0.sp - 56#64) 40 ∗
                      (s0.sp - 64#64) ↦₆₄ x_2 ∗
                      (s0.sp - 16#64) ↦₆₄ x_1 ∗
                      (s0.sp - 8#64) ↦₆₄ x) ∗
                    match varintSlow bs with
                    | some (v, k) =>
                      ⌜sf.readReg64 Reg.x0 = 0#64 ∧ sf.readReg64 Reg.x1 = v⌝ ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)
                    | none =>
                      ⌜sf.readReg64 Reg.x0 = 1#64 ∧ sf.readReg64 Reg.x1 ≠ 0#64⌝ ∗
                        decodeErrorAtStackLen A (sf.readReg64 Reg.x1) 0 ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length)) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length)) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) := by
    intro s k hnone hk ⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ hinv_s
    subst hk
    simp only [hnone]
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hinv_s
    wp_steps
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hruns])
    intro hinv_call
    refine SepWPp.call_frame_lscl (pl := lsmpl) (spec := decodeErrorFromSpecWithStack A errStack)
      (x := (s0.sp - 64#64, 0x8000000000000001#64))
      (ret_pc := (blkPl_293).base + bv% (92)) hFromCall hinv_call
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hruns])
      (by simp only [State.spAligned, arm64_norm, hsps]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromSpecWithStack, arm64_norm, hsps]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hm => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm, htrs])) hm) ?_
    intro sm hpcm hrunm hspm hcsm _
    apply SepWPp.of_sepWP_ret
    simp only [decodeErrorFromSpecWithStack, memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm, hsps]
    apply SepWP.exists_elim; intro v_err
    wp_steps
    wp_done
  have hok : ∀ {s : State} (v : BitVec 64) (k : Nat),
      varintSlow bs = some (v, k) →
      StateAt s0 s ((blkPl_293).base + bv% (52)) ∧ s.readReg64 (Reg.gpr 1#5) = v →
      SepWPp ((blkPC_293).rebase (blkPl_293).base H) (s0.readReg64 Reg.lr) s
        (slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗ A.pool ∗
          stackAt (s0.sp - 64#64) errStack ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
              sf.mem ⊨
                (∃∗ x, ∃∗ x_1, ∃∗ x_2,
                  ⌜sf.trace = s0.trace⌝ ∗
                    slotA ↦₆₄ slot ∗ ptr ↦ₛ bs ∗ A.pool ∗
                    (stackAt (s0.sp - 64#64) errStack ∗
                      memRegion (s0.sp - 56#64) 40 ∗
                      (s0.sp - 64#64) ↦₆₄ x_2 ∗
                      (s0.sp - 16#64) ↦₆₄ x_1 ∗
                      (s0.sp - 8#64) ↦₆₄ x) ∗
                    match varintSlow bs with
                    | some (v, k) =>
                      ⌜sf.readReg64 Reg.x0 = 0#64 ∧ sf.readReg64 Reg.x1 = v⌝ ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)
                    | none =>
                      ⌜sf.readReg64 Reg.x0 = 1#64 ∧ sf.readReg64 Reg.x1 ≠ 0#64⌝ ∗
                        decodeErrorAtStackLen A (sf.readReg64 Reg.x1) 0 ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length)) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length)) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) := by
    intro s v k hsome ⟨⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩, hx1⟩
    simp only [hsome]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done
  have hok9 : ∀ {s : State} (v : BitVec 64) (k : Nat),
      varintSlow bs = some (v, k) →
      StateAt s0 s ((blkPl_293).base + bv% (432)) ∧ s.readReg64 (Reg.gpr 1#5) = v →
      SepWPp ((blkPC_293).rebase (blkPl_293).base H) (s0.readReg64 Reg.lr) s
        (slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗ A.pool ∗
          stackAt (s0.sp - 64#64) errStack ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
              sf.mem ⊨
                (∃∗ x, ∃∗ x_1, ∃∗ x_2,
                  ⌜sf.trace = s0.trace⌝ ∗
                    slotA ↦₆₄ slot ∗ ptr ↦ₛ bs ∗ A.pool ∗
                    (stackAt (s0.sp - 64#64) errStack ∗
                      memRegion (s0.sp - 56#64) 40 ∗
                      (s0.sp - 64#64) ↦₆₄ x_2 ∗
                      (s0.sp - 16#64) ↦₆₄ x_1 ∗
                      (s0.sp - 8#64) ↦₆₄ x) ∗
                    match varintSlow bs with
                    | some (v, k) =>
                      ⌜sf.readReg64 Reg.x0 = 0#64 ∧ sf.readReg64 Reg.x1 = v⌝ ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)
                    | none =>
                      ⌜sf.readReg64 Reg.x0 = 1#64 ∧ sf.readReg64 Reg.x1 ≠ 0#64⌝ ∗
                        decodeErrorAtStackLen A (sf.readReg64 Reg.x1) 0 ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length)) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length)) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) := by
    intro s v k hsome ⟨⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩, hx1⟩
    simp only [hsome]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done
  apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (20)) hinv0
  wp_steps
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  intro hinv20
  by_cases hbs0 : bs = []
  · have hlen0 : BitVec.ofNat 64 bs.length = 0#64 := by simp [hbs0]
    apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv20
    wp_steps
    conv => arg 4; rw [show (slot ↦₆₄ ptr) = (slot ↦₆₄ (ptr + BitVec.ofNat 64 0)) by simp,
      show ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) =
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - 0)) by simp]
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    intro hinv76
    apply herr 0 (by simp [hbs0, varintSlow, varintSlowAux]) (by simp [hbs0])
    exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
    exact hinv76
  · obtain ⟨b0, bs1, hcons0'⟩ := List.exists_cons_of_ne_nil hbs0
    have hcons0 : ([] : List (BitVec 8)) ++ b0 :: bs1 = bs := hcons0'.symm
    clear hcons0' hbs0
    have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
      ofNat_ne_ofNat (by rw [← hcons0]; simp) h (by decide)
    have hpts0 : (ptr ↦ₛ bs) = (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ bs1) := by
      rw [← hcons0, List.nil_append, pointsToBytes_cons]
    apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (48)) hinv20
    conv => arg 4; rw [hpts0]
    wp_steps
    conv => arg 4; rw [← hpts0, ofNat_sub_ofNat_of_le (k := 1) (by rw [← hcons0]; simp) h]
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    intro hinv48
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := getLsbD_7_of_le hb0
      apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      apply hok (vAcc1 b0) 1 (by rw [← hcons0]; exact varintSlow_1 b0 bs1 hb0)
      exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩, by simp only [arm64_norm, vAcc1, zeroExtend64_and_127]⟩
    · have hbit0 := getLsbD_7_of_gt hb0
      apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (68)) hinv48
      wp_steps
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      intro hinv68
      by_cases hbs1 : bs1 = []
      · have hlen1 : BitVec.ofNat 64 bs.length = 1#64 := by rw [← hcons0, hbs1]; rfl
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv68
        wp_steps
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        intro hinv76
        apply herr 1 (by rw [← hcons0, hbs1]; exact varintSlow_none_1 b0 hb0) (by rw [← hcons0, hbs1]; rfl)
        exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
        exact hinv76
      · obtain ⟨b1, bs2, hcons1'⟩ := List.exists_cons_of_ne_nil hbs1
        have hcons1 : [b0] ++ b1 :: bs2 = bs := by rw [← hcons0, hcons1']; rfl
        clear hcons1' hbs1 hcons0
        have hlen_ne1 : BitVec.ofNat 64 bs.length ≠ 1#64 :=
          ofNat_ne_ofNat (by rw [← hcons1]; simp) h (by decide)
        have hpts1 := pointsToBytes_extract_at ptr bs [b0] bs2 b1 1 hcons1 rfl
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (136)) hinv68
        conv => arg 4; rw [hpts1]
        wp_steps
        conv => arg 4; rw [← hpts1, ofNat_sub_ofNat_of_le (k := 2) (by rw [← hcons1]; simp) h]
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        intro hinv136
        by_cases hb1 : b1 ≤ 0x7f#8
        · have hbit1 := getLsbD_7_of_le hb1
          apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
          wp_steps
          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          apply hok (vAcc2 b0 b1) 2 (by rw [← hcons1]; exact varintSlow_2 b0 b1 bs2 hb0 hb1)
          exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩, by simp only [arm64_norm, vAcc2, vAcc1, zeroExtend64_and_127]⟩
        · have hbit1 := getLsbD_7_of_gt hb1
          apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (140)) hinv136
          wp_steps
          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          intro hinv140
          by_cases hbs2 : bs2 = []
          · have hlen2 : BitVec.ofNat 64 bs.length = 2#64 := by rw [← hcons1, hbs2]; rfl
            apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv140
            wp_steps
            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            intro hinv76
            apply herr 2 (by rw [← hcons1, hbs2]; exact varintSlow_none_2 b0 b1 hb0 hb1) (by rw [← hcons1, hbs2]; rfl)
            exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
            exact hinv76
          · obtain ⟨b2, bs3, hcons2'⟩ := List.exists_cons_of_ne_nil hbs2
            have hcons2 : [b0, b1] ++ b2 :: bs3 = bs := by rw [← hcons1, hcons2']; rfl
            clear hcons2' hbs2 hcons1
            have hlen_ne2 : BitVec.ofNat 64 bs.length ≠ 2#64 :=
              ofNat_ne_ofNat (by rw [← hcons2]; simp) h (by decide)
            have hpts2 := pointsToBytes_extract_at ptr bs [b0, b1] bs3 b2 2 hcons2 rfl
            apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (172)) hinv140
            conv => arg 4; rw [hpts2]
            wp_steps
            conv => arg 4; rw [← hpts2, ofNat_sub_ofNat_of_le (k := 3) (by rw [← hcons2]; simp) h]
            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            intro hinv172
            by_cases hb2 : b2 ≤ 0x7f#8
            · have hbit2 := getLsbD_7_of_le hb2
              apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
              wp_steps
              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              apply hok (vAcc3 b0 b1 b2) 3 (by rw [← hcons2]; exact varintSlow_3 b0 b1 b2 bs3 hb0 hb1 hb2)
              exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩, by simp only [arm64_norm, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩
            · have hbit2 := getLsbD_7_of_gt hb2
              apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (176)) hinv172
              wp_steps
              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              intro hinv176
              by_cases hbs3 : bs3 = []
              · have hlen3 : BitVec.ofNat 64 bs.length = 3#64 := by rw [← hcons2, hbs3]; rfl
                apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv176
                wp_steps
                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                intro hinv76
                apply herr 3 (by rw [← hcons2, hbs3]; exact varintSlow_none_3 b0 b1 b2 hb0 hb1 hb2) (by rw [← hcons2, hbs3]; rfl)
                exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                exact hinv76
              · obtain ⟨b3, bs4, hcons3'⟩ := List.exists_cons_of_ne_nil hbs3
                have hcons3 : [b0, b1, b2] ++ b3 :: bs4 = bs := by rw [← hcons2, hcons3']; rfl
                clear hcons3' hbs3 hcons2
                have hlen_ne3 : BitVec.ofNat 64 bs.length ≠ 3#64 :=
                  ofNat_ne_ofNat (by rw [← hcons3]; simp) h (by decide)
                have hpts3 := pointsToBytes_extract_at ptr bs [b0, b1, b2] bs4 b3 3 hcons3 rfl
                apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (208)) hinv176
                conv => arg 4; rw [hpts3]
                wp_steps
                conv => arg 4; rw [← hpts3, ofNat_sub_ofNat_of_le (k := 4) (by rw [← hcons3]; simp) h]
                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                intro hinv208
                by_cases hb3 : b3 ≤ 0x7f#8
                · have hbit3 := getLsbD_7_of_le hb3
                  apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
                  wp_steps
                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                  apply hok (vAcc4 b0 b1 b2 b3) 4 (by rw [← hcons3]; exact varintSlow_4 b0 b1 b2 b3 bs4 hb0 hb1 hb2 hb3)
                  exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩, by simp only [arm64_norm, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩
                · have hbit3 := getLsbD_7_of_gt hb3
                  apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (212)) hinv208
                  wp_steps
                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                  intro hinv212
                  by_cases hbs4 : bs4 = []
                  · have hlen4 : BitVec.ofNat 64 bs.length = 4#64 := by rw [← hcons3, hbs4]; rfl
                    apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv212
                    wp_steps
                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                    intro hinv76
                    apply herr 4 (by rw [← hcons3, hbs4]; exact varintSlow_none_4 b0 b1 b2 b3 hb0 hb1 hb2 hb3) (by rw [← hcons3, hbs4]; rfl)
                    exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                    exact hinv76
                  · obtain ⟨b4, bs5, hcons4'⟩ := List.exists_cons_of_ne_nil hbs4
                    have hcons4 : [b0, b1, b2, b3] ++ b4 :: bs5 = bs := by rw [← hcons3, hcons4']; rfl
                    clear hcons4' hbs4 hcons3
                    have hlen_ne4 : BitVec.ofNat 64 bs.length ≠ 4#64 :=
                      ofNat_ne_ofNat (by rw [← hcons4]; simp) h (by decide)
                    have hpts4 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3] bs5 b4 4 hcons4 rfl
                    apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (244)) hinv212
                    conv => arg 4; rw [hpts4]
                    wp_steps
                    conv => arg 4; rw [← hpts4, ofNat_sub_ofNat_of_le (k := 5) (by rw [← hcons4]; simp) h]
                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                    intro hinv244
                    by_cases hb4 : b4 ≤ 0x7f#8
                    · have hbit4 := getLsbD_7_of_le hb4
                      apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
                      wp_steps
                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                      apply hok (vAcc5 b0 b1 b2 b3 b4) 5 (by rw [← hcons4]; exact varintSlow_5 b0 b1 b2 b3 b4 bs5 hb0 hb1 hb2 hb3 hb4)
                      exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩, by simp only [arm64_norm, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩
                    · have hbit4 := getLsbD_7_of_gt hb4
                      apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (248)) hinv244
                      wp_steps
                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                      intro hinv248
                      by_cases hbs5 : bs5 = []
                      · have hlen5 : BitVec.ofNat 64 bs.length = 5#64 := by rw [← hcons4, hbs5]; rfl
                        apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv248
                        wp_steps
                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                        intro hinv76
                        apply herr 5 (by rw [← hcons4, hbs5]; exact varintSlow_none_5 b0 b1 b2 b3 b4 hb0 hb1 hb2 hb3 hb4) (by rw [← hcons4, hbs5]; rfl)
                        exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                        exact hinv76
                      · obtain ⟨b5, bs6, hcons5'⟩ := List.exists_cons_of_ne_nil hbs5
                        have hcons5 : [b0, b1, b2, b3, b4] ++ b5 :: bs6 = bs := by rw [← hcons4, hcons5']; rfl
                        clear hcons5' hbs5 hcons4
                        have hlen_ne5 : BitVec.ofNat 64 bs.length ≠ 5#64 :=
                          ofNat_ne_ofNat (by rw [← hcons5]; simp) h (by decide)
                        have hpts5 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4] bs6 b5 5 hcons5 rfl
                        apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (280)) hinv248
                        conv => arg 4; rw [hpts5]
                        wp_steps
                        conv => arg 4; rw [← hpts5, ofNat_sub_ofNat_of_le (k := 6) (by rw [← hcons5]; simp) h]
                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                        intro hinv280
                        by_cases hb5 : b5 ≤ 0x7f#8
                        · have hbit5 := getLsbD_7_of_le hb5
                          apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
                          wp_steps
                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                          apply hok (vAcc6 b0 b1 b2 b3 b4 b5) 6 (by rw [← hcons5]; exact varintSlow_6 b0 b1 b2 b3 b4 b5 bs6 hb0 hb1 hb2 hb3 hb4 hb5)
                          exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩, by simp only [arm64_norm, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩
                        · have hbit5 := getLsbD_7_of_gt hb5
                          apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (284)) hinv280
                          wp_steps
                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                          intro hinv284
                          by_cases hbs6 : bs6 = []
                          · have hlen6 : BitVec.ofNat 64 bs.length = 6#64 := by rw [← hcons5, hbs6]; rfl
                            apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv284
                            wp_steps
                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                            intro hinv76
                            apply herr 6 (by rw [← hcons5, hbs6]; exact varintSlow_none_6 b0 b1 b2 b3 b4 b5 hb0 hb1 hb2 hb3 hb4 hb5) (by rw [← hcons5, hbs6]; rfl)
                            exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                            exact hinv76
                          · obtain ⟨b6, bs7, hcons6'⟩ := List.exists_cons_of_ne_nil hbs6
                            have hcons6 : [b0, b1, b2, b3, b4, b5] ++ b6 :: bs7 = bs := by rw [← hcons5, hcons6']; rfl
                            clear hcons6' hbs6 hcons5
                            have hlen_ne6 : BitVec.ofNat 64 bs.length ≠ 6#64 :=
                              ofNat_ne_ofNat (by rw [← hcons6]; simp) h (by decide)
                            have hpts6 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5] bs7 b6 6 hcons6 rfl
                            apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (316)) hinv284
                            conv => arg 4; rw [hpts6]
                            wp_steps
                            conv => arg 4; rw [← hpts6, ofNat_sub_ofNat_of_le (k := 7) (by rw [← hcons6]; simp) h]
                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                            intro hinv316
                            by_cases hb6 : b6 ≤ 0x7f#8
                            · have hbit6 := getLsbD_7_of_le hb6
                              apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
                              wp_steps
                              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                              apply hok (vAcc7 b0 b1 b2 b3 b4 b5 b6) 7 (by rw [← hcons6]; exact varintSlow_7 b0 b1 b2 b3 b4 b5 b6 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6)
                              exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩, by simp only [arm64_norm, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩
                            · have hbit6 := getLsbD_7_of_gt hb6
                              apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (320)) hinv316
                              wp_steps
                              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                              intro hinv320
                              by_cases hbs7 : bs7 = []
                              · have hlen7 : BitVec.ofNat 64 bs.length = 7#64 := by rw [← hcons6, hbs7]; rfl
                                apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv320
                                wp_steps
                                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                intro hinv76
                                apply herr 7 (by rw [← hcons6, hbs7]; exact varintSlow_none_7 b0 b1 b2 b3 b4 b5 b6 hb0 hb1 hb2 hb3 hb4 hb5 hb6) (by rw [← hcons6, hbs7]; rfl)
                                exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                                exact hinv76
                              · obtain ⟨b7, bs8, hcons7'⟩ := List.exists_cons_of_ne_nil hbs7
                                have hcons7 : [b0, b1, b2, b3, b4, b5, b6] ++ b7 :: bs8 = bs := by rw [← hcons6, hcons7']; rfl
                                clear hcons7' hbs7 hcons6
                                have hlen_ne7 : BitVec.ofNat 64 bs.length ≠ 7#64 :=
                                  ofNat_ne_ofNat (by rw [← hcons7]; simp) h (by decide)
                                have hpts7 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6] bs8 b7 7 hcons7 rfl
                                apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (352)) hinv320
                                conv => arg 4; rw [hpts7]
                                wp_steps
                                conv => arg 4; rw [← hpts7, ofNat_sub_ofNat_of_le (k := 8) (by rw [← hcons7]; simp) h]
                                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                intro hinv352
                                by_cases hb7 : b7 ≤ 0x7f#8
                                · have hbit7 := getLsbD_7_of_le hb7
                                  apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
                                  wp_steps
                                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                  apply hok (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7) 8 (by rw [← hcons7]; exact varintSlow_8 b0 b1 b2 b3 b4 b5 b6 b7 bs8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7)
                                  exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩, by simp only [arm64_norm, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩
                                · have hbit7 := getLsbD_7_of_gt hb7
                                  apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (356)) hinv352
                                  wp_steps
                                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                  intro hinv356
                                  by_cases hbs8 : bs8 = []
                                  · have hlen8 : BitVec.ofNat 64 bs.length = 8#64 := by rw [← hcons7, hbs8]; rfl
                                    apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv356
                                    wp_steps
                                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                    intro hinv76
                                    apply herr 8 (by rw [← hcons7, hbs8]; exact varintSlow_none_8 b0 b1 b2 b3 b4 b5 b6 b7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7) (by rw [← hcons7, hbs8]; rfl)
                                    exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                                    exact hinv76
                                  · obtain ⟨b8, bs9, hcons8'⟩ := List.exists_cons_of_ne_nil hbs8
                                    have hcons8 : [b0, b1, b2, b3, b4, b5, b6, b7] ++ b8 :: bs9 = bs := by rw [← hcons7, hcons8']; rfl
                                    clear hcons8' hbs8 hcons7
                                    have hlen_ne8 : BitVec.ofNat 64 bs.length ≠ 8#64 :=
                                      ofNat_ne_ofNat (by rw [← hcons8]; simp) h (by decide)
                                    have hpts8 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6, b7] bs9 b8 8 hcons8 rfl
                                    apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (388)) hinv356
                                    conv => arg 4; rw [hpts8]
                                    wp_steps
                                    conv => arg 4; rw [← hpts8, ofNat_sub_ofNat_of_le (k := 9) (by rw [← hcons8]; simp) h]
                                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                    intro hinv388
                                    by_cases hb8 : b8 ≤ 0x7f#8
                                    · have hbit8 := getLsbD_7_of_le hb8
                                      apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
                                      wp_steps
                                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                      apply hok (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8) 9 (by rw [← hcons8]; exact varintSlow_9 b0 b1 b2 b3 b4 b5 b6 b7 b8 bs9 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8)
                                      exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩, by simp only [arm64_norm, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩
                                    · have hbit8 := getLsbD_7_of_gt hb8
                                      apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (392)) hinv388
                                      wp_steps
                                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                      intro hinv392
                                      by_cases hbs9 : bs9 = []
                                      · have hlen9 : BitVec.ofNat 64 bs.length = 9#64 := by rw [← hcons8, hbs9]; rfl
                                        apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv392
                                        wp_steps
                                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                        intro hinv76
                                        apply herr 9 (by rw [← hcons8, hbs9]; exact varintSlow_none_9 b0 b1 b2 b3 b4 b5 b6 b7 b8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8) (by rw [← hcons8, hbs9]; rfl)
                                        exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                                        exact hinv76
                                      · obtain ⟨b9, bs10, hcons9'⟩ := List.exists_cons_of_ne_nil hbs9
                                        have hcons9 : [b0, b1, b2, b3, b4, b5, b6, b7, b8] ++ b9 :: bs10 = bs := by rw [← hcons8, hcons9']; rfl
                                        clear hcons9' hbs9 hcons8
                                        have hlen_ne9 : BitVec.ofNat 64 bs.length ≠ 9#64 :=
                                          ofNat_ne_ofNat (by rw [← hcons9]; simp) h (by decide)
                                        have hpts9 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6, b7, b8] bs10 b9 9 hcons9 rfl
                                        apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (416)) hinv392
                                        conv => arg 4; rw [hpts9]
                                        wp_steps
                                        conv => arg 4; rw [← hpts9, ofNat_sub_ofNat_of_le (k := 10) (by rw [← hcons9]; simp) h]
                                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                        intro hinv416
                                        by_cases hb9 : b9 ≤ 0x7f#8
                                        · have hbit9 := signExtend64_getLsbD_63_of_le hb9
                                          apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (424)) hinv416
                                          wp_steps
                                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                          intro hinv424
                                          by_cases hb9_ovf : 2#8 ≤ b9
                                          · have hovf := byte9_hi_of_ge hb9_ovf
                                            apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv424
                                            wp_steps
                                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                            intro hinv76
                                            apply herr 10 (by rw [← hcons9]; exact varintSlow_none_10_ovf b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb9_ovf) (by rw [← hcons9]; simp)
                                            exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                                            exact hinv76
                                          · have hovf := byte9_hi_of_lt hb9 hb9_ovf
                                            apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (432))
                                            wp_steps
                                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                            apply hok9 (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 10
                                              (by rw [← hcons9]; exact varintSlow_10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb9_ovf)
                                            exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩, by simp only [arm64_norm, vAcc10, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127, signExtend64_shiftLeft_63]⟩
                                        · have hbit9 := signExtend64_getLsbD_63_of_gt hb9
                                          apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv416
                                          wp_steps
                                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                          intro hinv76
                                          apply herr 10 (by rw [← hcons9]; exact varintSlow_none_10_gt b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9) (by rw [← hcons9]; simp)
                                          exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                                          exact hinv76

end VarintSlowPlaced

theorem decode_varint_slow_placed_ok_with_stack_of_contract [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {errStack : Nat}
    (herr_stk : 0x40 + errStack ≤ 2 ^ 64 := by decide)
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpecWithStack A errStack)) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack A (0x40 + errStack))) :=
  decode_varint_slow_placed_ok_with_stack herr_stk
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_293).rebase (blkPl_293).base H) hFrom)

theorem decode_varint_slow_placed_ok_with_stack_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {errStack : Nat}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked)
    (hle : decodeErrorHookStack ≤ errStack := by decide)
    (herr_stk : 0x40 + errStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack A (0x40 + errStack))) :=
  decode_varint_slow_placed_ok_with_stack_of_contract herr_stk
    (decode_error_from_placed_ok_gen hshim halloc hpanic hle (by omega))

theorem decodeVarintSlowGen_lscl_ok_of_session2 {pl : Obj.MultiPlacement} {A : RustAlloc}
    {prog : Program} {entry : BitVec 64} {errStack : Nat}
    (hSlow : subroutine_ok prog entry
      (withLsCodeLoaded pl
        (CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack A (0x40 + errStack)))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (decodeVarintSlowSpecGen A errStack)) := by
  refine subroutine_ok_map_panic hSlow fun y R s0 hpre => ?_
  refine ⟨(y.bufRef, y.slot, y.ptr, y.bs), R, ?_, ?_, fun _ h => h⟩
  · simp only [decodeVarintSlowSpecGen,
      CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack,
      sliceCursorAt, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, by omega⟩, hpre.2⟩
  · intro sf hpost
    have hvs : varintSlow y.bs =
        (decodeVarint y.bs).map (fun p => (p.1, y.bs.length - p.2.length)) :=
      decodeVarint_eq_varintSlow y.bs
    dsimp only [withLsCodeLoaded, CryptoVerification.LibsignalTripleRatchet.decodeVarintSlowSpecWithStack,
      decodeVarintSlowSpecGen] at hpost ⊢
    rw [hvs] at hpost
    cases hd : decodeVarint y.bs with
    | some p =>
      rcases p with ⟨v, rest⟩
      rw [hd] at hpost
      dsimp only [Option.map, sliceCursorAfter] at hpost ⊢
      obtain ⟨k, _, _, hrest_eq⟩ := decodeVarintAux_suffix y.bs 0 0#64 v rest hd
      have hlen_sub : y.bs.length - (y.bs.length - rest.length) = rest.length := by
        rw [hrest_eq, List.length_drop]; omega
      rw [hlen_sub] at hpost
      exact Satisfies.of_eq hpost
    | none =>
      rw [hd] at hpost
      dsimp only [Option.map] at hpost ⊢
      have hpost1 : sf.mem ⊨
          ((y.slot ↦₆₄ (y.ptr + BitVec.ofNat 64 (min 10 y.bs.length))) ∗
            ((y.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (y.bs.length - min 10 y.bs.length))) ∗
          (⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
            ⌜sf.trace = s0.trace⌝ ∗
            (y.bufRef ↦₆₄ y.slot) ∗ A.pool ∗ stackAt s0.sp (0x40 + errStack) ∗
            decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗ (y.ptr ↦ₛ y.bs) ∗ R) :=
        Satisfies.of_eq hpost
      have hmem1 := Satisfies.mono
        (sepConj_mono_left (pointsTo64_pair_entails_memRegion16 y.slot _ _)) hpost1
      have hmem2 : sf.mem ⊨
          ⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
          (⌜sf.trace = s0.trace⌝ ∗ (y.bufRef ↦₆₄ y.slot) ∗ A.pool ∗
            stackAt s0.sp (0x40 + errStack) ∗
            decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
            memRegion y.slot 16 ∗ (y.ptr ↦ₛ y.bs) ∗ R) :=
        Satisfies.of_eq hmem1
      rw [satisfies_pure_sepConj] at hmem2
      rcases hmem2 with ⟨⟨hx0, hx1⟩, hmem3⟩
      have hmem4 : sf.mem ⊨
          ⌜sf.readReg64 .x0 = 1#64⌝ ∗
          (⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
            (⌜sf.trace = s0.trace⌝ ∗ (y.bufRef ↦₆₄ y.slot) ∗ A.pool ∗
              stackAt s0.sp (0x40 + errStack) ∗
              decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
              memRegion y.slot 16 ∗ (y.ptr ↦ₛ y.bs) ∗ R)) := by
        rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
        exact ⟨hx0, hx1, hmem3⟩
      exact Satisfies.of_eq hmem4

theorem decode_varint_slow_placed_ok_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {errStack : Nat}
    (herr_stk : 0x40 + errStack ≤ 2 ^ 64 := by decide)
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpecWithStack A errStack)) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecGen A errStack)) :=
  decodeVarintSlowGen_lscl_ok_of_session2
    (decode_varint_slow_placed_ok_with_stack_of_contract herr_stk hFrom)

theorem decode_varint_slow_placed_ok_of_contract [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpec A)) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpec A)) :=
  decode_varint_slow_placed_ok_gen (errStack := decodeErrorHookStack) (by decide) hFrom

theorem decode_varint_slow_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpec A)) :=
  decode_varint_slow_placed_ok_of_contract (decode_error_from_placed_ok hshim halloc hpanic)

theorem decode_varint_slow_placed_ok_of_contract_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpecWithStack A decodeErrorHookStackX)) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A)) :=
  decode_varint_slow_placed_ok_gen (errStack := decodeErrorHookStackX) (by decide) hFrom

theorem decode_varint_slow_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A)) :=
  decode_varint_slow_placed_ok_of_contract_x (decode_error_from_placed_ok_x hshim halloc hpanic)

theorem int32_merge_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpec A))
    (hSlow : subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpec A)))
    (hSlice : subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpec A))) :
    subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
      (blkPl_8).base
      (withLsCodeLoaded lsmpl (int32MergeSpec A)) :=
  int32_merge_placed_ok_gen (errStack := decodeErrorHookStack) (by decide)
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_8).rebase (blkPl_8).base H) hFrom)
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_8).rebase (blkPl_8).base H) hSlow)
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_8).rebase (blkPl_8).base H) hSlice)

theorem int32_merge_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
      (blkPl_8).base
      (withLsCodeLoaded lsmpl (int32MergeSpec A)) :=
  int32_merge_placed_ok_of_contracts
    (decode_error_from_placed_ok hshim halloc hpanic)
    (decode_varint_slow_placed_ok hshim halloc hpanic)
    (decode_varint_slice_placed_ok hshim halloc hpanic)

theorem int32_merge_placed_ok_of_contracts_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpecWithStack A decodeErrorHookStackX))
    (hSlow : subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A)))
    (hSlice : subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A))) :
    subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
      (blkPl_8).base
      (withLsCodeLoaded lsmpl (int32MergeSpecX A)) :=
  int32_merge_placed_ok_gen (errStack := decodeErrorHookStackX) (by decide)
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_8).rebase (blkPl_8).base H) hFrom)
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_8).rebase (blkPl_8).base H) hSlow)
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_8).rebase (blkPl_8).base H) hSlice)

theorem int32_merge_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
      (blkPl_8).base
      (withLsCodeLoaded lsmpl (int32MergeSpecX A)) :=
  int32_merge_placed_ok_of_contracts_x
    (decode_error_from_placed_ok_x hshim halloc hpanic)
    (decode_varint_slow_placed_ok_x hshim halloc hpanic)
    (decode_varint_slice_placed_ok_x hshim halloc hpanic)

end CryptoVerification.LibsignalTripleRatchet.Prost
