/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6a
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 6 (`HeaderReceived`, `+1464`) — Part D

`PolyDecoder` 400-byte layout word/qword unpacking, stack realignment helpers, and the 77-instruction
`Ok(dec)` staging block (`+10000 -> +8180`) for `InnerState.headerReceived`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

/-! ## 1. `PolyDecoder` Word/Qword Unpacking and Realignment (`v6hr_*`) -/

/-- First 8 words (`+0..+64`) of `PolyDecoder`. -/
structure v6hr_DecG0 where
  w0 : BitVec 64
  w8 : BitVec 64
  w16 : BitVec 64
  w24 : BitVec 64
  w32 : BitVec 64
  w40 : BitVec 64
  w48 : BitVec 64
  w56 : BitVec 64

structure v6hr_DecG1 where
  w64 : BitVec 64
  w72 : BitVec 64
  q80 : BitVec 128
  q96 : BitVec 128
  q112 : BitVec 128
  q128 : BitVec 128
  q144 : BitVec 128
  q160 : BitVec 128

structure v6hr_DecG2 where
  q176 : BitVec 128
  q192 : BitVec 128
  q208 : BitVec 128
  q224 : BitVec 128
  q240 : BitVec 128
  q256 : BitVec 128
  q272 : BitVec 128
  q288 : BitVec 128

structure v6hr_DecG3 where
  u304 : BitVec 64
  u312 : BitVec 64
  u320 : BitVec 64
  u328 : BitVec 64
  u336 : BitVec 64
  u344 : BitVec 64

structure v6hr_DecG4 where
  u352 : BitVec 64
  u360 : BitVec 64
  u368 : BitVec 64
  u376 : BitVec 64
  u384 : BitVec 64
  u392 : BitVec 64

/-- The 36 words/qwords covering the 400-byte `PolyDecoder` layout for Variant 6 (`HeaderReceived`),
grouped into ≤8-field chunks. -/
structure v6hr_DecWords where
  g0 : v6hr_DecG0
  g1 : v6hr_DecG1
  g2 : v6hr_DecG2
  g3 : v6hr_DecG3
  g4 : v6hr_DecG4

def v6hr_decoderTriples (dw : v6hr_DecWords) : List (BitVec 64 × BitVec 64 × BitVec 64) :=
  [ (dw.g0.w0, dw.g0.w8, dw.g0.w16),
    (dw.g0.w24, dw.g0.w32, dw.g0.w40),
    (dw.g0.w48, dw.g0.w56, dw.g1.w64),
    (dw.g1.w72, dw.g1.q80.extractLsb' 0 64, dw.g1.q80.extractLsb' 64 64),
    (dw.g1.q96.extractLsb' 0 64, dw.g1.q96.extractLsb' 64 64, dw.g1.q112.extractLsb' 0 64),
    (dw.g1.q112.extractLsb' 64 64, dw.g1.q128.extractLsb' 0 64, dw.g1.q128.extractLsb' 64 64),
    (dw.g1.q144.extractLsb' 0 64, dw.g1.q144.extractLsb' 64 64, dw.g1.q160.extractLsb' 0 64),
    (dw.g1.q160.extractLsb' 64 64, dw.g2.q176.extractLsb' 0 64, dw.g2.q176.extractLsb' 64 64),
    (dw.g2.q192.extractLsb' 0 64, dw.g2.q192.extractLsb' 64 64, dw.g2.q208.extractLsb' 0 64),
    (dw.g2.q208.extractLsb' 64 64, dw.g2.q224.extractLsb' 0 64, dw.g2.q224.extractLsb' 64 64),
    (dw.g2.q240.extractLsb' 0 64, dw.g2.q240.extractLsb' 64 64, dw.g2.q256.extractLsb' 0 64),
    (dw.g2.q256.extractLsb' 64 64, dw.g2.q272.extractLsb' 0 64, dw.g2.q272.extractLsb' 64 64),
    (dw.g2.q288.extractLsb' 0 64, dw.g2.q288.extractLsb' 64 64, dw.g3.u304),
    (dw.g3.u312, dw.g3.u320, dw.g3.u328),
    (dw.g3.u336, dw.g3.u344, dw.g4.u352),
    (dw.g4.u360, dw.g4.u368, dw.g4.u376) ]

def v6hr_triplesWordsAt : BitVec 64 → List (BitVec 64 × BitVec 64 × BitVec 64) → SepProp
  | _, [] => emp
  | a, (c, p, l) :: ts =>
    (a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ l) ∗
    v6hr_triplesWordsAt (a + 24#64) ts

def v6hr_triplesHeapAt (A : RustAlloc) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List SortedSetPt → SepProp
  | [], [] => emp
  | (c, p, l) :: ts, s :: ss =>
    ⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 s.vec.length⌝ ∗
    sortedSetPtBuf A c p s ∗
    v6hr_triplesHeapAt A ts ss
  | _, _ => ⌜False⌝

def v6hr_decWordsAt (a : BitVec 64) (dw : v6hr_DecWords) : SepProp :=
  (a ↦₆₄ dw.g0.w0) ∗ ((a + 8#64) ↦₆₄ dw.g0.w8) ∗ ((a + 16#64) ↦₆₄ dw.g0.w16) ∗
  ((a + 24#64) ↦₆₄ dw.g0.w24) ∗ ((a + 32#64) ↦₆₄ dw.g0.w32) ∗
  ((a + 40#64) ↦₆₄ dw.g0.w40) ∗ ((a + 48#64) ↦₆₄ dw.g0.w48) ∗
  ((a + 56#64) ↦₆₄ dw.g0.w56) ∗ ((a + 64#64) ↦₆₄ dw.g1.w64) ∗
  ((a + 72#64) ↦₆₄ dw.g1.w72) ∗
  ((a + 80#64) ↦₁₂₈ dw.g1.q80) ∗ ((a + 96#64) ↦₁₂₈ dw.g1.q96) ∗
  ((a + 112#64) ↦₁₂₈ dw.g1.q112) ∗ ((a + 128#64) ↦₁₂₈ dw.g1.q128) ∗
  ((a + 144#64) ↦₁₂₈ dw.g1.q144) ∗ ((a + 160#64) ↦₁₂₈ dw.g1.q160) ∗
  ((a + 176#64) ↦₁₂₈ dw.g2.q176) ∗ ((a + 192#64) ↦₁₂₈ dw.g2.q192) ∗
  ((a + 208#64) ↦₁₂₈ dw.g2.q208) ∗ ((a + 224#64) ↦₁₂₈ dw.g2.q224) ∗
  ((a + 240#64) ↦₁₂₈ dw.g2.q240) ∗ ((a + 256#64) ↦₁₂₈ dw.g2.q256) ∗
  ((a + 272#64) ↦₁₂₈ dw.g2.q272) ∗ ((a + 288#64) ↦₁₂₈ dw.g2.q288) ∗
  ((a + 304#64) ↦₆₄ dw.g3.u304) ∗ ((a + 312#64) ↦₆₄ dw.g3.u312) ∗
  ((a + 320#64) ↦₆₄ dw.g3.u320) ∗ ((a + 328#64) ↦₆₄ dw.g3.u328) ∗
  ((a + 336#64) ↦₆₄ dw.g3.u336) ∗ ((a + 344#64) ↦₆₄ dw.g3.u344) ∗
  ((a + 352#64) ↦₆₄ dw.g4.u352) ∗ ((a + 360#64) ↦₆₄ dw.g4.u360) ∗
  ((a + 368#64) ↦₆₄ dw.g4.u368) ∗ ((a + 376#64) ↦₆₄ dw.g4.u376) ∗
  ((a + 384#64) ↦₆₄ dw.g4.u384) ∗ ((a + 392#64) ↦₆₄ dw.g4.u392)

def v6hr_decHeap (A : RustAlloc) (dec : PolyDecoder) (dw : v6hr_DecWords) : SepProp :=
  ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64 ∧
    dw.g0.w0.toNat < 2 ^ 63 ∧
    dw.g4.u384 = BitVec.ofNat 64 dec.ptsNeeded ∧
    dw.g4.u392.extractLsb' 0 8 = boolByte dec.isComplete⌝ ∗
  v6hr_triplesHeapAt A (v6hr_decoderTriples dw) dec.pts

theorem v6hr_bv_add_lit_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem v6hr_triplesWordsAt_decoderTriples_eq (a : BitVec 64) (dw : v6hr_DecWords) :
    v6hr_triplesWordsAt a (v6hr_decoderTriples dw) ∗
      ((a + 384#64) ↦₆₄ dw.g4.u384) ∗ ((a + 392#64) ↦₆₄ dw.g4.u392) =
      v6hr_decWordsAt a dw := by
  unfold v6hr_decoderTriples v6hr_decWordsAt
  simp only [v6hr_triplesWordsAt, pointsTo128_eq_pair64, v6hr_bv_add_lit_add_lit, sepConj_emp, sepConj_assoc]

theorem v6hr_sortedSetPtOf_unpack (A : RustAlloc) (a : BitVec 64) (s : SortedSetPt) :
    sortedSetPtOf A a s ⊢
      ∃∗ c : BitVec 64, ∃∗ p : BitVec 64, ∃∗ l : BitVec 64,
        ((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ l)) ∗
        (⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 s.vec.length⌝ ∗
         sortedSetPtBuf A c p s) := by
  unfold sortedSetPtOf vecOf vecAt vecHeader
  apply Entails.sepExists_elim; intro c
  apply Entails.sepExists_elim; intro p
  have hcap : vecBuf A ptStride ptAlign ptAt c p s.vec ⊢
      ⌜c.toNat < 2 ^ 63⌝ ∗ sortedSetPtBuf A c p s := by
    unfold sortedSetPtBuf vecBuf
    apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    have hc : c.toNat < 2 ^ 63 := by dsimp only [ptStride] at hlt; omega
    exact Entails.pure_right hc (Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _))
  refine Entails.trans (sepConj_mono_right hcap) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜c.toNat < 2 ^ 63⌝ ∗
    ((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
     sortedSetPtBuf A c p s) by ac_rfl)) ?_
  apply Entails.pure_left; intro hc
  refine Entails.sepExists_right c (Entails.sepExists_right p
    (Entails.sepExists_right (BitVec.ofNat 64 s.vec.length) ?_))
  have hp : c.toNat < 2 ^ 63 ∧ BitVec.ofNat 64 s.vec.length = BitVec.ofNat 64 s.vec.length :=
    ⟨hc, rfl⟩
  exact Entails.trans (Entails.pure_right hp (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v6hr_sortedSetPtOf_pack (A : RustAlloc) (b c p l : BitVec 64) (s : SortedSetPt) :
    ((b ↦₆₄ c) ∗ ((b + 8#64) ↦₆₄ p) ∗ ((b + 16#64) ↦₆₄ l)) ∗
      (⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 s.vec.length⌝ ∗
       sortedSetPtBuf A c p s) ⊢
      sortedSetPtOf A b s := by
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 s.vec.length⌝ ∗
    ((b ↦₆₄ c) ∗ ((b + 8#64) ↦₆₄ p) ∗ ((b + 16#64) ↦₆₄ l) ∗
     sortedSetPtBuf A c p s) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨_, rfl⟩
  unfold sortedSetPtOf vecOf vecAt vecHeader sortedSetPtBuf
  exact Entails.sepExists_right c (Entails.sepExists_right p (Entails.of_eq (by ac_rfl)))

theorem v6hr_sortedSetPtListOf_unpack (A : RustAlloc) :
    ∀ (pts : List SortedSetPt) (a : BitVec 64),
      sortedSetPtListOf A a pts ⊢
        ∃∗ ts : List (BitVec 64 × BitVec 64 × BitVec 64),
          ⌜ts.length = pts.length⌝ ∗
          v6hr_triplesWordsAt a ts ∗
          v6hr_triplesHeapAt A ts pts
  | [], a => by
    simp only [sortedSetPtListOf, arrayAt]
    refine Entails.sepExists_right [] ?_
    dsimp only [List.length_nil, v6hr_triplesWordsAt, v6hr_triplesHeapAt]
    rw [sepConj_emp]
    exact Entails.pure_right rfl (Entails.refl _)
  | s :: ss, a => by
    simp only [sortedSetPtListOf, arrayAt, Poly.vecHeaderBytes]
    refine Entails.trans (sepConj_mono (v6hr_sortedSetPtOf_unpack A a s)
      (v6hr_sortedSetPtListOf_unpack A ss (a + 24#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ts
    apply Entails.sepExists_elim; intro c
    apply Entails.sepExists_elim; intro p
    apply Entails.sepExists_elim; intro l
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜ts.length = ss.length⌝ ∗
      (((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ l) ∗ v6hr_triplesWordsAt (a + 24#64) ts) ∗
       (⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 s.vec.length⌝ ∗
        sortedSetPtBuf A c p s ∗ v6hr_triplesHeapAt A ts ss)) by ac_rfl)) ?_
    apply Entails.pure_left; intro hlen
    refine Entails.sepExists_right ((c, p, l) :: ts) ?_
    have hlen' : ((c, p, l) :: ts).length = (s :: ss).length := by simp [hlen]
    exact Entails.pure_right hlen' (Entails.of_eq (by dsimp only [v6hr_triplesWordsAt, v6hr_triplesHeapAt]))

theorem v6hr_sortedSetPtListOf_pack (A : RustAlloc) :
    ∀ (ts : List (BitVec 64 × BitVec 64 × BitVec 64)) (pts : List SortedSetPt) (b : BitVec 64),
      v6hr_triplesWordsAt b ts ∗ v6hr_triplesHeapAt A ts pts ⊢
        sortedSetPtListOf A b pts
  | [], [], b => by
    simp only [v6hr_triplesWordsAt, v6hr_triplesHeapAt, sortedSetPtListOf, arrayAt, sepConj_emp]
    exact Entails.refl _
  | [], _ :: _, _ => by
    dsimp only [v6hr_triplesWordsAt, v6hr_triplesHeapAt]
    rw [emp_sepConj, ← sepConj_emp ⌜False⌝]
    exact Entails.pure_left False.elim
  | _ :: _, [], _ => by
    dsimp only [v6hr_triplesWordsAt, v6hr_triplesHeapAt]
    rw [sepConj_comm]
    exact Entails.pure_left False.elim
  | (c, p, l) :: ts, s :: ss, b => by
    simp only [v6hr_triplesWordsAt, v6hr_triplesHeapAt, sortedSetPtListOf, arrayAt, Poly.vecHeaderBytes]
    refine Entails.trans (Entails.of_eq (show _ =
      (((b ↦₆₄ c) ∗ ((b + 8#64) ↦₆₄ p) ∗ ((b + 16#64) ↦₆₄ l)) ∗
       (⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 s.vec.length⌝ ∗ sortedSetPtBuf A c p s)) ∗
      (v6hr_triplesWordsAt (b + 24#64) ts ∗ v6hr_triplesHeapAt A ts ss) by ac_rfl)) ?_
    exact sepConj_mono (v6hr_sortedSetPtOf_pack A b c p l s)
      (v6hr_sortedSetPtListOf_pack A ts ss (b + 24#64))

theorem v6hr_list_cons_of_length_succ {α : Type} {n : Nat} (xs : List α) (h : xs.length = n + 1) :
    ∃ (x : α) (xs' : List α), xs'.length = n ∧ xs = x :: xs' := by
  cases xs with
  | nil => simp at h
  | cons x xs' => exact ⟨x, xs', Nat.succ.inj h, rfl⟩

theorem v6hr_exists_decWords_of_length_16
    (ts : List (BitVec 64 × BitVec 64 × BitVec 64)) (hts : ts.length = 16)
    (u384 u392 : BitVec 64) :
    ∃ dw : v6hr_DecWords,
      ts = v6hr_decoderTriples dw ∧ dw.g4.u384 = u384 ∧ dw.g4.u392 = u392 := by
  obtain ⟨⟨w0, w8, w16⟩, ts1, h1, rfl⟩ := v6hr_list_cons_of_length_succ ts hts
  obtain ⟨⟨w24, w32, w40⟩, ts2, h2, rfl⟩ := v6hr_list_cons_of_length_succ ts1 h1
  obtain ⟨⟨w48, w56, w64⟩, ts3, h3, rfl⟩ := v6hr_list_cons_of_length_succ ts2 h2
  obtain ⟨⟨w72, w80, w88⟩, ts4, h4, rfl⟩ := v6hr_list_cons_of_length_succ ts3 h3
  obtain ⟨⟨w96, w104, w112⟩, ts5, h5, rfl⟩ := v6hr_list_cons_of_length_succ ts4 h4
  obtain ⟨⟨w120, w128, w136⟩, ts6, h6, rfl⟩ := v6hr_list_cons_of_length_succ ts5 h5
  obtain ⟨⟨w144, w152, w160⟩, ts7, h7, rfl⟩ := v6hr_list_cons_of_length_succ ts6 h6
  obtain ⟨⟨w168, w176, w184⟩, ts8, h8, rfl⟩ := v6hr_list_cons_of_length_succ ts7 h7
  obtain ⟨⟨w192, w200, w208⟩, ts9, h9, rfl⟩ := v6hr_list_cons_of_length_succ ts8 h8
  obtain ⟨⟨w216, w224, w232⟩, ts10, h10, rfl⟩ := v6hr_list_cons_of_length_succ ts9 h9
  obtain ⟨⟨w240, w248, w256⟩, ts11, h11, rfl⟩ := v6hr_list_cons_of_length_succ ts10 h10
  obtain ⟨⟨w264, w272, w280⟩, ts12, h12, rfl⟩ := v6hr_list_cons_of_length_succ ts11 h11
  obtain ⟨⟨w288, w296, u304⟩, ts13, h13, rfl⟩ := v6hr_list_cons_of_length_succ ts12 h12
  obtain ⟨⟨u312, u320, u328⟩, ts14, h14, rfl⟩ := v6hr_list_cons_of_length_succ ts13 h13
  obtain ⟨⟨u336, u344, u352⟩, ts15, h15, rfl⟩ := v6hr_list_cons_of_length_succ ts14 h14
  obtain ⟨⟨u360, u368, u376⟩, ts16, h16, rfl⟩ := v6hr_list_cons_of_length_succ ts15 h15
  have hnil : ts16 = [] := List.eq_nil_of_length_eq_zero h16
  subst hnil
  refine ⟨⟨⟨w0, w8, w16, w24, w32, w40, w48, w56⟩,
    ⟨w64, w72, w88 ++ w80, w104 ++ w96, w120 ++ w112, w136 ++ w128, w152 ++ w144, w168 ++ w160⟩,
    ⟨w184 ++ w176, w200 ++ w192, w216 ++ w208, w232 ++ w224, w248 ++ w240, w264 ++ w256, w280 ++ w272, w296 ++ w288⟩,
    ⟨u304, u312, u320, u328, u336, u344⟩,
    ⟨u352, u360, u368, u376, u384, u392⟩⟩, ?_, rfl, rfl⟩
  simp only [v6hr_decoderTriples, extractLsb'_0_64_append, extractLsb'_64_64_append]

theorem v6hr_triplesHeapAt_head_cap_lt (A : RustAlloc) (c p l : BitVec 64)
    (ts : List (BitVec 64 × BitVec 64 × BitVec 64)) (pts : List SortedSetPt) :
    v6hr_triplesHeapAt A ((c, p, l) :: ts) pts ⊢
      ⌜c.toNat < 2 ^ 63⌝ ∗ v6hr_triplesHeapAt A ((c, p, l) :: ts) pts := by
  cases pts with
  | nil =>
    dsimp only [v6hr_triplesHeapAt]
    rw [← sepConj_emp ⌜False⌝]
    exact Entails.pure_left False.elim
  | cons s ss =>
    dsimp only [v6hr_triplesHeapAt]
    apply Entails.pure_left; rintro ⟨hc, hl⟩
    exact Entails.pure_right hc (Entails.pure_right ⟨hc, hl⟩ (Entails.refl _))

theorem v6hr_byte_pad7_entails_word64 (p : BitVec 64) (b0 : BitVec 8) :
    (p ↦₈ b0) ∗ memRegion (p + 1#64) 7 ⊢
      ∃∗ w : BitVec 64, ⌜w.extractLsb' 0 8 = b0⌝ ∗ (p ↦₆₄ w) := by
  rw [ProofLib.memRegion_eq_exists_bytes (p + 1#64) 7 (by decide), sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜bs.length = 7⌝ ∗ ((p ↦₈ b0) ∗ ((p + 1#64) ↦ₛ bs)) by ac_rfl)) ?_
  apply Entails.pure_left; intro hlen
  have h8 : (b0 :: bs).length = 8 := by simp [hlen]
  obtain ⟨w, hw⟩ := ProofLib.exists_unpack64_of_length_8 h8
  have hcell : (p ↦₈ b0) ∗ ((p + 1#64) ↦ₛ bs) = (p ↦₆₄ w) := by
    rw [← ProofLib.pointsToBytes_cons p b0 bs, hw, ← ProofLib.pointsTo64_eq_pointsToBytes]
  have hb0 : w.extractLsb' 0 8 = b0 := by
    have hhd := congrArg List.head? hw
    simpa [unpack64] using hhd.symm
  rw [hcell]
  exact Entails.sepExists_right w (Entails.pure_right hb0 (Entails.refl _))

theorem v6hr_word64_entails_byte_pad7 (p : BitVec 64) (w : BitVec 64) (b0 : BitVec 8)
    (hb : w.extractLsb' 0 8 = b0) :
    (p ↦₆₄ w) ⊢ (p ↦₈ b0) ∗ memRegion (p + 1#64) 7 := by
  rw [pointsTo64_eq_pointsToBytes p w, EncoderFromPb.unpack64_eq_loByte_cons_hiBytes7 w,
      ProofLib.pointsToBytes_cons]
  have hlo : EncoderFromPb.loByte w = b0 := hb
  rw [hlo]
  exact sepConj_mono_right
    (EncoderFromPb.length_hiBytes7 w ▸ pointsToBytes_entails_memRegion (p + 1#64) (EncoderFromPb.hiBytes7 w))

theorem v6hr_polyDecoderAt_unpack (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A a dec ⊢
      ∃∗ dw : v6hr_DecWords,
        v6hr_decWordsAt a dw ∗ v6hr_decHeap A dec dw := by
  unfold polyDecoderAt polyDecoderPtsNeededOff polyDecoderIsCompleteOff
    polyDecoderPadOff polyDecoderPadSize
  apply Entails.pure_left; rintro ⟨hlen, hneed⟩
  have hpad : ((a + 392#64) ↦₈ boolByte dec.isComplete) ∗ memRegion (a + 393#64) 7 ⊢
      ∃∗ u392 : BitVec 64,
        ⌜u392.extractLsb' 0 8 = boolByte dec.isComplete⌝ ∗ ((a + 392#64) ↦₆₄ u392) := by
    have h393 : a + 393#64 = (a + 392#64) + 1#64 := by bv_omega
    rw [h393]
    exact v6hr_byte_pad7_entails_word64 (a + 392#64) (boolByte dec.isComplete)
  refine Entails.trans (sepConj_mono (v6hr_sortedSetPtListOf_unpack A dec.pts a)
    (sepConj_mono_right hpad)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u392
  apply Entails.sepExists_elim; intro ts
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜ts.length = dec.pts.length⌝ ∗
    (⌜u392.extractLsb' 0 8 = boolByte dec.isComplete⌝ ∗
     (v6hr_triplesWordsAt a ts ∗
      ((a + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
      ((a + 392#64) ↦₆₄ u392)) ∗
     v6hr_triplesHeapAt A ts dec.pts) by ac_rfl)) ?_
  apply Entails.pure_left; intro hts_len
  apply Entails.pure_left; intro hu392
  have hts16 : ts.length = 16 := by rw [hts_len, hlen]; rfl
  obtain ⟨dw, rfl, hu384, rfl⟩ :=
    v6hr_exists_decWords_of_length_16 ts hts16 (BitVec.ofNat 64 dec.ptsNeeded) u392
  rw [← hu384, v6hr_triplesWordsAt_decoderTriples_eq a dw]
  have hcap := v6hr_triplesHeapAt_head_cap_lt A dw.g0.w0 dw.g0.w8 dw.g0.w16
    (v6hr_decoderTriples dw).tail dec.pts
  refine Entails.trans (sepConj_mono_right hcap) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜dw.g0.w0.toNat < 2 ^ 63⌝ ∗
    (v6hr_decWordsAt a dw ∗ v6hr_triplesHeapAt A (v6hr_decoderTriples dw) dec.pts) by
    dsimp only [v6hr_decoderTriples, List.tail]; ac_rfl)) ?_
  apply Entails.pure_left; intro hw0
  refine Entails.sepExists_right dw ?_
  unfold v6hr_decHeap
  have hpure : dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64 ∧
      dw.g0.w0.toNat < 2 ^ 63 ∧
      dw.g4.u384 = BitVec.ofNat 64 dec.ptsNeeded ∧
      dw.g4.u392.extractLsb' 0 8 = boolByte dec.isComplete :=
    ⟨hlen, hneed, hw0, hu384, hu392⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v6hr_polyDecoderAt_pack (A : RustAlloc) (b : BitVec 64) (dec : PolyDecoder) (dw : v6hr_DecWords) :
    v6hr_decWordsAt b dw ∗ v6hr_decHeap A dec dw ⊢ polyDecoderAt A b dec := by
  unfold v6hr_decHeap
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64 ∧
      dw.g0.w0.toNat < 2 ^ 63 ∧
      dw.g4.u384 = BitVec.ofNat 64 dec.ptsNeeded ∧
      dw.g4.u392.extractLsb' 0 8 = boolByte dec.isComplete⌝ ∗
    (v6hr_decWordsAt b dw ∗ v6hr_triplesHeapAt A (v6hr_decoderTriples dw) dec.pts) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hlen, hneed, _, hu384, hu392⟩
  rw [← v6hr_triplesWordsAt_decoderTriples_eq b dw, hu384]
  have hpad : ((b + 392#64) ↦₆₄ dw.g4.u392) ⊢
      ((b + 392#64) ↦₈ boolByte dec.isComplete) ∗ memRegion (b + 393#64) 7 := by
    have h393 : b + 393#64 = (b + 392#64) + 1#64 := by bv_omega
    rw [h393]
    exact v6hr_word64_entails_byte_pad7 (b + 392#64) dw.g4.u392 (boolByte dec.isComplete) hu392
  refine Entails.trans (Entails.of_eq (show _ =
    (v6hr_triplesWordsAt b (v6hr_decoderTriples dw) ∗
     v6hr_triplesHeapAt A (v6hr_decoderTriples dw) dec.pts) ∗
    ((b + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
    ((b + 392#64) ↦₆₄ dw.g4.u392) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono (v6hr_sortedSetPtListOf_pack A (v6hr_decoderTriples dw) dec.pts b)
    (sepConj_mono_right hpad)) ?_
  unfold polyDecoderAt polyDecoderPtsNeededOff polyDecoderIsCompleteOff
    polyDecoderPadOff polyDecoderPadSize
  have hp : dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64 := ⟨hlen, hneed⟩
  exact Entails.trans (Entails.pure_right hp (Entails.refl _)) (Entails.of_eq (by ac_rfl))

/-! ## 2. Realignment Helpers for `+10000 -> +8180` and `epilogueOutFull` -/

theorem v6hr_hiBytes7_append_loByte_eq_unpack64_unshiftWord (u1 u2 : BitVec 64) :
    EncoderFromPb.hiBytes7 u1 ++ [loByte u2] = unpack64 (unshiftWord u1 (loByte u2)) := by
  simp only [EncoderFromPb.hiBytes7, unpack64, loByte, unshiftWord, List.drop,
    List.cons_append, List.nil_append, List.cons.injEq]
  refine ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem v6hr_tail7_word_to_word_tail7 (a u1 u2 : BitVec 64) :
    ((a ↦ₛ EncoderFromPb.hiBytes7 u1) ∗ ((a + 7#64) ↦₆₄ u2)) =
      ((a ↦₆₄ unshiftWord u1 (loByte u2)) ∗ ((a + 8#64) ↦ₛ EncoderFromPb.hiBytes7 u2)) := by
  have hleft :
      ((a ↦ₛ EncoderFromPb.hiBytes7 u1) ∗ ((a + 7#64) ↦₈ loByte u2)) =
        (a ↦₆₄ unshiftWord u1 (loByte u2)) := by
    rw [pointsTo64_eq_pointsToBytes a (unshiftWord u1 (loByte u2)),
        ← v6hr_hiBytes7_append_loByte_eq_unpack64_unshiftWord u1 u2,
        ProofLib.pointsToBytes_append a (EncoderFromPb.hiBytes7 u1) [loByte u2],
        EncoderFromPb.length_hiBytes7]
    simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]
  rw [pointsTo64_eq_pointsToBytes (a + 7#64) u2,
      EncoderFromPb.unpack64_eq_loByte_cons_hiBytes7 u2,
      ← List.singleton_append (x := loByte u2),
      ProofLib.pointsToBytes_append (a + 7#64) [loByte u2] (EncoderFromPb.hiBytes7 u2)]
  have h1 : (a + 7#64) + BitVec.ofNat 64 ([loByte u2].length) = a + 8#64 := by
    simp only [List.length_singleton]; bv_omega
  rw [h1, ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp,
      ← sepConj_assoc, hleft]

theorem v6hr_triple64_to_byte_q128_tail7 (a : BitVec 64) (u0 u1 u2 : BitVec 64) :
    (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) =
      (a ↦₈ loByte u0) ∗
      ((a + 1#64) ↦₁₂₈ (unshiftWord u1 (loByte u2) ++ unshiftWord u0 (loByte u1))) ∗
      ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 u2) := by
  rw [show (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) =
        ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1)) ∗ ((a + 16#64) ↦₆₄ u2) by ac_rfl,
      EncoderFromPb.pair64_to_byte_word_tail7 a u0 u1,
      show ((a ↦₈ loByte u0) ∗ ((a + 1#64) ↦₆₄ unshiftWord u0 (loByte u1)) ∗ ((a + 9#64) ↦ₛ EncoderFromPb.hiBytes7 u1)) ∗ ((a + 16#64) ↦₆₄ u2) =
        (a ↦₈ loByte u0) ∗ ((a + 1#64) ↦₆₄ unshiftWord u0 (loByte u1)) ∗
        (((a + 9#64) ↦ₛ EncoderFromPb.hiBytes7 u1) ∗ ((a + 16#64) ↦₆₄ u2)) by ac_rfl,
      show a + 16#64 = (a + 9#64) + 7#64 by bv_omega,
      v6hr_tail7_word_to_word_tail7 (a + 9#64) u1 u2]
  rw [pointsTo128_eq_pair64 (a + 1#64) (unshiftWord u1 (loByte u2) ++ unshiftWord u0 (loByte u1)),
      extractLsb'_0_64_append, extractLsb'_64_64_append]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem v6hr_byte_q128_tail7_to_byte_word_tail7_word (a : BitVec 64) (u0 u1 u2 : BitVec 64) :
    (a ↦₈ loByte u0) ∗
    ((a + 1#64) ↦₁₂₈ (unshiftWord u1 (loByte u2) ++ unshiftWord u0 (loByte u1))) ∗
    ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 u2) =
      (a ↦₈ loByte u0) ∗
      ((a + 1#64) ↦₆₄ unshiftWord u0 (loByte u1)) ∗
      ((a + 9#64) ↦ₛ EncoderFromPb.hiBytes7 u1) ∗
      ((a + 16#64) ↦₆₄ u2) := by
  rw [pointsTo128_eq_pair64 (a + 1#64) (unshiftWord u1 (loByte u2) ++ unshiftWord u0 (loByte u1)),
      extractLsb'_0_64_append, extractLsb'_64_64_append]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [show (a ↦₈ loByte u0) ∗ (((a + 1#64) ↦₆₄ unshiftWord u0 (loByte u1)) ∗ ((a + 9#64) ↦₆₄ unshiftWord u1 (loByte u2))) ∗ ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 u2) =
        (a ↦₈ loByte u0) ∗ ((a + 1#64) ↦₆₄ unshiftWord u0 (loByte u1)) ∗
        (((a + 9#64) ↦₆₄ unshiftWord u1 (loByte u2)) ∗ ((a + 9#64 + 8#64) ↦ₛ EncoderFromPb.hiBytes7 u2)) by
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc],
      ← v6hr_tail7_word_to_word_tail7 (a + 9#64) u1 u2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem v6hr_overlapWord7_unshift (u1 u2 : BitVec 64) :
    overlapWord7 (unshiftWord u1 (loByte u2)) (u2 >>> 8) = u2 := by
  unfold overlapWord7 unshiftWord loByte
  bv_slice

def v6hr_midQ128 (w56 w64 w72 : BitVec 64) : BitVec 128 :=
  unshiftWord w64 (loByte w72) ++ unshiftWord w56 (loByte w64)

theorem v6hr_overlapWord7_midQ128_lsr8 (w56 w64 w72 : BitVec 64) :
    overlapWord7 ((v6hr_midQ128 w56 w64 w72).extractLsb' 64 64) (w72 >>> 8) = w72 := by
  have hhi : (v6hr_midQ128 w56 w64 w72).extractLsb' 64 64 = unshiftWord w64 (loByte w72) :=
    extractLsb'_64_64_append (unshiftWord w64 (loByte w72)) (unshiftWord w56 (loByte w64))
  rw [hhi]
  exact v6hr_overlapWord7_unshift w64 w72

@[local arm64_norm, local wp_norm]
theorem v6hr_orr_x27_w8 (w8 : BitVec 64) :
    ((w8.extractLsb' 8 32).zeroExtend 64 |||
      ((((w8.extractLsb' 40 16).zeroExtend 32 |||
        ((w8.extractLsb' 56 8).zeroExtend 32 <<< 16#64)).zeroExtend 64) <<< 32#64)) =
      (w8.extractLsb' 8 56).zeroExtend 64 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v6hr_w8_d97 (w8 : BitVec 64) :
    ((w8.extractLsb' 8 56).zeroExtend 64).setWidth 32 = w8.extractLsb' 8 32 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v6hr_w8_h101 (w8 : BitVec 64) :
    ((((w8.extractLsb' 8 56).zeroExtend 64) >>> 32).setWidth 32).setWidth 16 =
      w8.extractLsb' 40 16 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v6hr_w8_b103 (w8 : BitVec 64) :
    ((((w8.extractLsb' 8 56).zeroExtend 64) >>> 48).setWidth 32).setWidth 8 =
      w8.extractLsb' 56 8 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v6hr_zext32_setWidth8 (b : BitVec 8) :
    (b.zeroExtend 32).setWidth 8 = b := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v6hr_fsp_1888_add_9 (fsp : BitVec 64) :
    (fsp + 1888#64) + 9#64 = fsp + 1897#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v6hr_fsp_1888_add_13 (fsp : BitVec 64) :
    (fsp + 1888#64) + 13#64 = fsp + 1901#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v6hr_fsp_1888_add_33 (fsp : BitVec 64) :
    (fsp + 1888#64) + 33#64 = fsp + 1921#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v6hr_fsp_1888_add_57 (fsp : BitVec 64) :
    (fsp + 1888#64) + 57#64 = fsp + 1945#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v6hr_fsp_848_add_39 (fsp : BitVec 64) :
    (fsp + 848#64) + 39#64 = fsp + 887#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v6hr_fsp_848_add_15 (fsp : BitVec 64) :
    (fsp + 848#64) + 15#64 = fsp + 863#64 := by bv_omega

theorem v6hr_fsp_1896_split_rest (fsp w8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1896#64) ↦₆₄ w8) ∗ Rest =
      ((fsp + 1896#64) ↦₈ w8.extractLsb' 0 8) ∗
      ((fsp + 1897#64) ↦₃₂ w8.extractLsb' 8 32) ∗
      ((fsp + 1901#64) ↦₁₆ w8.extractLsb' 40 16) ∗
      ((fsp + 1903#64) ↦₈ w8.extractLsb' 56 8) ∗ Rest := by
  have h := v6hr_pointsTo64_split_1_4_2_1 (fsp + 1896#64) w8
  have ha1 : (fsp + 1896#64) + 1#64 = fsp + 1897#64 := by bv_omega
  have ha5 : (fsp + 1896#64) + 5#64 = fsp + 1901#64 := by bv_omega
  have ha7 : (fsp + 1896#64) + 7#64 = fsp + 1903#64 := by bv_omega
  rw [ha1, ha5, ha7] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v6hr_fsp_1896_unsplit_rest (fsp w8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1896#64) ↦₈ w8.extractLsb' 0 8) ∗
      ((fsp + 1897#64) ↦₃₂ w8.extractLsb' 8 32) ∗
      ((fsp + 1901#64) ↦₁₆ w8.extractLsb' 40 16) ∗
      ((fsp + 1903#64) ↦₈ w8.extractLsb' 56 8) ∗ Rest =
      ((fsp + 1896#64) ↦₆₄ w8) ∗ Rest :=
  (v6hr_fsp_1896_split_rest fsp w8 Rest).symm

theorem v6hr_fsp_1920_realign_rest (fsp w32 w40 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1920#64) ↦₆₄ w32) ∗ ((fsp + 1928#64) ↦₆₄ w40) ∗ Rest =
      ((fsp + 1920#64) ↦₈ loByte w32) ∗
      ((fsp + 1921#64) ↦₆₄ unshiftWord w32 (loByte w40)) ∗
      ((fsp + 1929#64) ↦ₛ EncoderFromPb.hiBytes7 w40) ∗ Rest := by
  have h := pair64_to_byte_word_tail7 (fsp + 1920#64) w32 w40
  have ha8 : (fsp + 1920#64) + 8#64 = fsp + 1928#64 := by bv_omega
  have ha1 : (fsp + 1920#64) + 1#64 = fsp + 1921#64 := by bv_omega
  have ha9 : (fsp + 1920#64) + 9#64 = fsp + 1929#64 := by bv_omega
  rw [ha8, ha1, ha9] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v6hr_fsp_1920_unrealign_rest (fsp w32 w40 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1920#64) ↦₈ loByte w32) ∗
      ((fsp + 1921#64) ↦₆₄ unshiftWord w32 (loByte w40)) ∗
      ((fsp + 1929#64) ↦ₛ EncoderFromPb.hiBytes7 w40) ∗ Rest =
      ((fsp + 1920#64) ↦₆₄ w32) ∗ ((fsp + 1928#64) ↦₆₄ w40) ∗ Rest :=
  (v6hr_fsp_1920_realign_rest fsp w32 w40 Rest).symm

theorem v6hr_fsp_1920_split_1_7_rest (fsp w32 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1920#64) ↦₆₄ w32) ∗ Rest =
      ((fsp + 1920#64) ↦₈ loByte w32) ∗
      ((fsp + 1921#64) ↦ₛ EncoderFromPb.hiBytes7 w32) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 1920#64) w32
  have ha1 : (fsp + 1920#64) + 1#64 = fsp + 1921#64 := by bv_omega
  rw [ha1] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v6hr_fsp_1920_unsplit_1_7_rest (fsp w32 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1920#64) ↦₈ loByte w32) ∗
      ((fsp + 1921#64) ↦ₛ EncoderFromPb.hiBytes7 w32) ∗ Rest =
      ((fsp + 1920#64) ↦₆₄ w32) ∗ Rest :=
  (v6hr_fsp_1920_split_1_7_rest fsp w32 Rest).symm

theorem v6hr_fsp_1944_realign_rest (fsp w56 w64 w72 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1944#64) ↦₆₄ w56) ∗ ((fsp + 1952#64) ↦₆₄ w64) ∗ ((fsp + 1960#64) ↦₆₄ w72) ∗ Rest =
      ((fsp + 1944#64) ↦₈ loByte w56) ∗
      ((fsp + 1945#64) ↦₆₄ (v6hr_midQ128 w56 w64 w72).extractLsb' 0 64) ∗
      ((fsp + 1953#64) ↦₆₄ (v6hr_midQ128 w56 w64 w72).extractLsb' 64 64) ∗
      ((fsp + 1961#64) ↦ₛ EncoderFromPb.hiBytes7 w72) ∗ Rest := by
  have h := v6hr_triple64_to_byte_q128_tail7 (fsp + 1944#64) w56 w64 w72
  have ha8 : (fsp + 1944#64) + 8#64 = fsp + 1952#64 := by bv_omega
  have ha16 : (fsp + 1944#64) + 16#64 = fsp + 1960#64 := by bv_omega
  have ha1 : (fsp + 1944#64) + 1#64 = fsp + 1945#64 := by bv_omega
  have ha17 : (fsp + 1944#64) + 17#64 = fsp + 1961#64 := by bv_omega
  have ha1953 : (fsp + 1945#64) + 8#64 = fsp + 1953#64 := by bv_omega
  rw [ha8, ha16, ha1, ha17] at h
  change _ = ((fsp + 1944#64) ↦₈ loByte w56) ∗
    ((fsp + 1945#64) ↦₁₂₈ v6hr_midQ128 w56 w64 w72) ∗
    ((fsp + 1961#64) ↦ₛ EncoderFromPb.hiBytes7 w72) at h
  unfold pointsTo128 at h
  rw [ha1953] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v6hr_fsp_1944_unrealign_rest (fsp w56 w64 w72 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1944#64) ↦₈ loByte w56) ∗
      ((fsp + 1945#64) ↦₆₄ (v6hr_midQ128 w56 w64 w72).extractLsb' 0 64) ∗
      ((fsp + 1953#64) ↦₆₄ (v6hr_midQ128 w56 w64 w72).extractLsb' 64 64) ∗
      ((fsp + 1961#64) ↦ₛ EncoderFromPb.hiBytes7 w72) ∗ Rest =
    ((fsp + 1944#64) ↦₆₄ w56) ∗ ((fsp + 1952#64) ↦₆₄ w64) ∗ ((fsp + 1960#64) ↦₆₄ w72) ∗ Rest :=
  (v6hr_fsp_1944_realign_rest fsp w56 w64 w72 Rest).symm

theorem v6hr_fsp_1944_split_1_7_rest (fsp w56 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1944#64) ↦₆₄ w56) ∗ Rest =
      ((fsp + 1944#64) ↦₈ loByte w56) ∗
      ((fsp + 1945#64) ↦ₛ EncoderFromPb.hiBytes7 w56) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 1944#64) w56
  have ha1 : (fsp + 1944#64) + 1#64 = fsp + 1945#64 := by bv_omega
  rw [ha1] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v6hr_fsp_1944_unsplit_1_7_rest (fsp w56 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1944#64) ↦₈ loByte w56) ∗
      ((fsp + 1945#64) ↦ₛ EncoderFromPb.hiBytes7 w56) ∗ Rest =
      ((fsp + 1944#64) ↦₆₄ w56) ∗ Rest :=
  (v6hr_fsp_1944_split_1_7_rest fsp w56 Rest).symm

theorem v6hr_fsp_880_realign_rest (fsp w880 u888 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 u888) ∗ Rest =
      ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
      ((fsp + 887#64) ↦₆₄ overlapWord7 w880 u888) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 880#64) w880 u888
  have ha8 : (fsp + 880#64) + 8#64 = fsp + 888#64 := by bv_omega
  have ha7 : (fsp + 880#64) + 7#64 = fsp + 887#64 := by bv_omega
  rw [ha8, ha7] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v6hr_fsp_880_unrealign_unshift_rest (fsp w32 w40 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w32 (loByte w40))) ∗
      ((fsp + 887#64) ↦₆₄ w40) ∗ Rest =
    ((fsp + 880#64) ↦₆₄ unshiftWord w32 (loByte w40)) ∗
      ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (w40 >>> 8)) ∗ Rest := by
  have h := (v6hr_fsp_880_realign_rest fsp (unshiftWord w32 (loByte w40)) (w40 >>> 8) Rest).symm
  rwa [v6hr_overlapWord7_unshift w32 w40] at h

theorem v6hr_fsp_856_realign_rest (fsp w856 u864 : BitVec 64) (Rest : SepProp) :
    ((fsp + 856#64) ↦₆₄ w856) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864) ∗ Rest =
      ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 w856) ∗
      ((fsp + 863#64) ↦₆₄ overlapWord7 w856 u864) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 856#64) w856 u864
  have ha8 : (fsp + 856#64) + 8#64 = fsp + 864#64 := by bv_omega
  have ha7 : (fsp + 856#64) + 7#64 = fsp + 863#64 := by bv_omega
  rw [ha8, ha7] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v6hr_fsp_856_unrealign_midQ128_rest (fsp w56 w64 w72 : BitVec 64) (Rest : SepProp) :
    ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 ((v6hr_midQ128 w56 w64 w72).extractLsb' 64 64)) ∗
      ((fsp + 863#64) ↦₆₄ w72) ∗ Rest =
    ((fsp + 856#64) ↦₆₄ (v6hr_midQ128 w56 w64 w72).extractLsb' 64 64) ∗
      ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (w72 >>> 8)) ∗ Rest := by
  have h := (v6hr_fsp_856_realign_rest fsp ((v6hr_midQ128 w56 w64 w72).extractLsb' 64 64)
    (w72 >>> 8) Rest).symm
  rwa [v6hr_overlapWord7_midQ128_lsr8 w56 w64 w72] at h

/-! ## 3. Step `+10000 -> +8180` (`0x5c7b4 -> 0x5c8e4`, 77 instructions) -/

def v6hr_stagingSlotsPre (fsp : BitVec 64)
    (u160 : BitVec 64) (d172 : BitVec 32) (u208 u224 u232 : BitVec 64)
    (uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 : BitVec 128)
    (u832 : BitVec 64) (uq848 : BitVec 128) (u864 u880 u888 : BitVec 64) : SepProp :=
  ((fsp + 160#64) ↦₆₄ u160) ∗
  ((fsp + 172#64) ↦₃₂ d172) ∗
  ((fsp + 208#64) ↦₆₄ u208) ∗
  ((fsp + 224#64) ↦₆₄ u224) ∗
  ((fsp + 232#64) ↦₆₄ u232) ∗
  ((fsp + 608#64) ↦₁₂₈ uq608) ∗ ((fsp + 624#64) ↦₁₂₈ uq624) ∗
  ((fsp + 640#64) ↦₁₂₈ uq640) ∗ ((fsp + 656#64) ↦₁₂₈ uq656) ∗
  ((fsp + 672#64) ↦₁₂₈ uq672) ∗ ((fsp + 688#64) ↦₁₂₈ uq688) ∗
  ((fsp + 704#64) ↦₁₂₈ uq704) ∗ ((fsp + 720#64) ↦₁₂₈ uq720) ∗
  ((fsp + 736#64) ↦₁₂₈ uq736) ∗ ((fsp + 752#64) ↦₁₂₈ uq752) ∗
  ((fsp + 768#64) ↦₁₂₈ uq768) ∗ ((fsp + 784#64) ↦₁₂₈ uq784) ∗
  ((fsp + 800#64) ↦₁₂₈ uq800) ∗ ((fsp + 816#64) ↦₁₂₈ uq816) ∗
  ((fsp + 832#64) ↦₆₄ u832) ∗
  ((fsp + 848#64) ↦₁₂₈ uq848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864) ∗
  ((fsp + 880#64) ↦₆₄ u880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 u888)

def v6hr_stagingSlotsPost (fsp : BitVec 64) (dw : v6hr_DecWords) (p1_new : BitVec 64) : SepProp :=
  ((fsp + 160#64) ↦₆₄ dw.g4.u360) ∗
  ((fsp + 172#64) ↦₃₂ (loByte dw.g0.w56).zeroExtend 32) ∗
  ((fsp + 208#64) ↦₆₄ p1_new) ∗
  ((fsp + 224#64) ↦₆₄ dw.g4.u392) ∗
  ((fsp + 232#64) ↦₆₄ dw.g3.u344) ∗
  ((fsp + 608#64) ↦₁₂₈ dw.g1.q80) ∗
  ((fsp + 624#64) ↦₁₂₈ dw.g1.q96) ∗
  ((fsp + 640#64) ↦₁₂₈ dw.g1.q112) ∗
  ((fsp + 656#64) ↦₁₂₈ dw.g1.q128) ∗
  ((fsp + 672#64) ↦₁₂₈ dw.g1.q144) ∗
  ((fsp + 688#64) ↦₁₂₈ dw.g1.q160) ∗
  ((fsp + 704#64) ↦₁₂₈ dw.g2.q176) ∗
  ((fsp + 720#64) ↦₁₂₈ dw.g2.q192) ∗
  ((fsp + 736#64) ↦₁₂₈ dw.g2.q208) ∗
  ((fsp + 752#64) ↦₁₂₈ dw.g2.q224) ∗
  ((fsp + 768#64) ↦₁₂₈ dw.g2.q240) ∗
  ((fsp + 784#64) ↦₁₂₈ dw.g2.q256) ∗
  ((fsp + 800#64) ↦₁₂₈ dw.g2.q272) ∗
  ((fsp + 816#64) ↦₁₂₈ dw.g2.q288) ∗
  ((fsp + 832#64) ↦₆₄ dw.g3.u304) ∗
  ((fsp + 848#64) ↦₁₂₈ v6hr_midQ128 dw.g0.w56 dw.g1.w64 dw.g1.w72) ∗
  ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (dw.g1.w72 >>> 8)) ∗
  ((fsp + 880#64) ↦₆₄ unshiftWord dw.g0.w32 (loByte dw.g0.w40)) ∗
  ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (dw.g0.w40 >>> 8))

theorem v6hr_cap_add_one_beq_zero_false {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have h1 : cap = noneCap := by
    change cap + 1#64 = 0#64 at h
    bv_omega
  subst h1
  revert hlt; decide

set_option maxHeartbeats 1600000 in
theorem v6hr_step_10000_ok_to_8180
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out c0 p0 l0 l1 p1_new l2 p2_new ep : BitVec 64)
    (dw : v6hr_DecWords)
    (u160 : BitVec 64) (d172 : BitVec 32) (u208 u224 u232 : BitVec 64)
    (uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 : BitVec 128)
    (u832 : BitVec 64) (uq848 : BitVec 128) (u864 u880 u888 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_lt : dw.g0.w0.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10000#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = p1_new)
    (hx26 : s.readReg64 .x26 = l1)
    (hx27 : s.readReg64 .x27 = c0)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8180#64) s
      (((fsp + 80#64) ↦₆₄ l0) ∗
        ((fsp + 128#64) ↦₆₄ ep) ∗
        ((fsp + 136#64) ↦₆₄ p2_new) ∗
        ((fsp + 144#64) ↦₆₄ p0) ∗
        ((fsp + 216#64) ↦₆₄ l2) ∗
        v6hr_stagingSlotsPre fsp u160 d172 u208 u224 u232
          uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
          u832 uq848 u864 u880 u888 ∗
        v6hr_decWordsAt (fsp + 1888#64) dw ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((fsp + 80#64) ↦₆₄ l0) ∗
          ((fsp + 128#64) ↦₆₄ ep) ∗
          ((fsp + 136#64) ↦₆₄ p2_new) ∗
          ((fsp + 144#64) ↦₆₄ p0) ∗
          ((fsp + 216#64) ↦₆₄ l2) ∗
          v6hr_stagingSlotsPost fsp dw p1_new ∗
          v6hr_decWordsAt (fsp + 1888#64) dw ∗
          Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x6 = fsp + 576#64 ∧
        s2.readReg64 .x8 = 8#64 ∧
        s2.readReg64 .x15 = l1 ∧
        s2.readReg64 .x20 = l1 ∧
        s2.readReg64 .x13 = l2 ∧
        s2.readReg64 .x25 = p2_new ∧
        s2.readReg64 .x30 = l2 ∧
        s2.readReg64 .x9 = c0 ∧
        s2.readReg64 .x14 = p0 ∧
        s2.readReg64 .x18 = l0 ∧
        s2.readReg64 .x17 = ep ∧
        s2.readReg64 .x0 = dw.g0.w0 ∧
        (s2.readReg32 .x3).setWidth 8 = dw.g0.w8.extractLsb' 0 8 ∧
        s2.readReg32 .x27 = dw.g0.w8.extractLsb' 8 32 ∧
        ((s2.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = dw.g0.w8.extractLsb' 40 16 ∧
        ((s2.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = dw.g0.w8.extractLsb' 56 8 ∧
        s2.readReg64 .x4 = dw.g0.w16 ∧
        s2.readReg64 .x5 = dw.g0.w24 ∧
        (s2.readReg32 .x21).setWidth 8 = loByte dw.g0.w32 ∧
        s2.readReg64 .x7 = dw.g0.w48 ∧
        s2.readReg64 .x2 = dw.g3.u312 ∧
        s2.readReg64 .x11 = dw.g3.u320 ∧
        s2.readReg64 .x22 = dw.g3.u328 ∧
        s2.readReg64 .x24 = dw.g3.u336 ∧
        s2.readReg64 .x10 = dw.g4.u352 ∧
        s2.readReg64 .x26 = dw.g4.u368 ∧
        s2.readReg64 .x12 = dw.g4.u376 ∧
        s2.readReg64 .x1 = dw.g4.u384 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x23 = fsp + 848#64 ∧
        TraceCalleeSaved s2 s0) := by
  subst hsp
  have hw0_ne1 := v6hr_cap_add_one_beq_zero_false hw0_lt
  unfold v6hr_stagingSlotsPre v6hr_stagingSlotsPost v6hr_decWordsAt
  simp only [pointsTo128, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 10000 308
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre only [v6hr_fsp_1896_split_rest, v6hr_fsp_1920_realign_rest,
    v6hr_fsp_1944_realign_rest, sepConj_assoc]
  iterate 13 wp_step
  wp_simp_pre only [v6hr_fsp_1920_unrealign_rest, v6hr_fsp_1920_split_1_7_rest,
    v6hr_fsp_880_realign_rest, sepConj_assoc]
  iterate 18 wp_step
  wp_simp_pre only [v6hr_fsp_1944_unrealign_rest, v6hr_fsp_1944_split_1_7_rest,
    v6hr_fsp_856_realign_rest, sepConj_assoc]
  iterate 46 wp_step
  wp_simp_pre only [v6hr_fsp_856_unrealign_midQ128_rest, v6hr_fsp_880_unrealign_unshift_rest,
    v6hr_fsp_1896_unsplit_rest, v6hr_fsp_1920_unsplit_1_7_rest,
    v6hr_fsp_1944_unsplit_1_7_rest, sepConj_assoc]
  wp_done

/-! ## 4. Stack Splitting Helpers for `+9936` and `+10000` -/

theorem v6hr_memRegion_8_entails_loBytes7_and_1 (a : BitVec 64) :
    memRegion a 8 ⊢
      (∃∗ u : BitVec 64, (a ↦ₛ EncoderFromPb.loBytes7 u)) ∗ memRegion (a + 7#64) 1 := by
  rw [ProofLib.memRegion_eight a, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro u
  rw [pointsTo64_split_7_1 a u]
  exact Entails.sepExists_right u
    (sepConj_mono_right (pointsTo8_entails_memRegion (a + 7#64) (EncoderFromPb.hiByte u)))

theorem v6hr_memRegion_entails_loBytes7_and_tail (a o1 o2 : BitVec 64) (k : Nat)
    (ho : o1 + 7#64 = o2 := by rfl)
    (hk : 8 + k ≤ 2 ^ 64 := by decide) :
    memRegion (a + o1) (8 + k) ⊢
      (∃∗ u : BitVec 64, ((a + o1) ↦ₛ EncoderFromPb.loBytes7 u)) ∗ memRegion (a + o2) (1 + k) := by
  rw [ProofLib.memRegion_split (a + o1) 8 k hk]
  have h1k : memRegion ((a + o1) + 7#64) 1 ∗ memRegion ((a + o1) + 8#64) k =
      memRegion (a + o2) (1 + k) := by
    have ha7 : a + o2 = (a + o1) + 7#64 := by rw [BitVec.add_assoc, ho]
    rw [ha7, ← ProofLib.memRegion_split' (b := (a + o1) + 7#64) (n := 1) (k := k)
      (b' := (a + o1) + 8#64) rfl (by bv_omega) (by omega)]
  rw [← h1k, ← sepConj_assoc]
  exact sepConj_mono_left (v6hr_memRegion_8_entails_loBytes7_and_1 (a + o1))

theorem v6hr_memRegion_2064_split_9936 (sp0 : BitVec 64) :
    memRegion (sp0 - 2160#64) 2064 ⊢
      memRegion ((sp0 - 2400#64) + 1392#64) 40 ∗
      memRegion ((sp0 - 2400#64) + 1888#64) 400 ∗
      (memRegion ((sp0 - 2400#64) + 240#64) 1152 ∗
       memRegion ((sp0 - 2400#64) + 1432#64) 456 ∗
       memRegion ((sp0 - 2400#64) + 2288#64) 16) := by
  have hbase : sp0 - 2160#64 = (sp0 - 2400#64) + 240#64 := by bv_omega
  rw [hbase]
  have h : memRegion ((sp0 - 2400#64) + 240#64) 2064 ⊢
      memRegion ((sp0 - 2400#64) + 240#64) 1152 ∗
      memRegion ((sp0 - 2400#64) + 1392#64) 40 ∗
      memRegion ((sp0 - 2400#64) + 1432#64) 456 ∗
      memRegion ((sp0 - 2400#64) + 1888#64) 400 ∗
      memRegion ((sp0 - 2400#64) + 2288#64) 16 := by
    exact split_top <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      Entails.refl _
  exact Entails.trans h (Entails.of_eq (by ac_rfl))

theorem v6hr_memRegion_2064_unsplit_9936 (sp0 : BitVec 64) :
    memRegion ((sp0 - 2400#64) + 1392#64) 40 ∗
      memRegion ((sp0 - 2400#64) + 1888#64) 400 ∗
      (memRegion ((sp0 - 2400#64) + 240#64) 1152 ∗
       memRegion ((sp0 - 2400#64) + 1432#64) 456 ∗
       memRegion ((sp0 - 2400#64) + 2288#64) 16) ⊢
      memRegion (sp0 - 2160#64) 2064 := by
  have hbase : sp0 - 2160#64 = (sp0 - 2400#64) + 240#64 := by bv_omega
  rw [hbase]
  have h :
      memRegion ((sp0 - 2400#64) + 240#64) 1152 ∗
      memRegion ((sp0 - 2400#64) + 1392#64) 40 ∗
      memRegion ((sp0 - 2400#64) + 1432#64) 456 ∗
      memRegion ((sp0 - 2400#64) + 1888#64) 400 ∗
      memRegion ((sp0 - 2400#64) + 2288#64) 16 ⊢
      memRegion ((sp0 - 2400#64) + 240#64) 2064 := by
    exact collapse_top <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      Entails.refl _
  exact Entails.trans (Entails.of_eq (by ac_rfl)) h

def v6hr_stackRest10000 (fsp : BitVec 64) : SepProp :=
  memRegion fsp 80 ∗
  memRegion (fsp + 88#64) 40 ∗
  memRegion (fsp + 152#64) 8 ∗
  memRegion (fsp + 168#64) 4 ∗
  memRegion (fsp + 176#64) 32 ∗
  memRegion (fsp + 240#64) 368 ∗
  memRegion (fsp + 840#64) 8 ∗
  memRegion (fsp + 871#64) 9 ∗
  memRegion (fsp + 895#64) 993 ∗
  memRegion (fsp + 2288#64) 16

theorem v6hr_lowStack_152_208_split (fsp : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32) :
    memRegion (fsp + 152#64) 32 ∗
      ((fsp + 184#64) ↦₃₂ d184) ∗
      memRegion (fsp + 188#64) 4 ∗
      ((fsp + 192#64) ↦₆₄ v192) ∗
      ((fsp + 200#64) ↦₃₂ d200) ∗
      memRegion (fsp + 204#64) 4 ⊢
      (∃∗ u160 : BitVec 64, ∃∗ d172 : BitVec 32,
        ((fsp + 160#64) ↦₆₄ u160) ∗
        ((fsp + 172#64) ↦₃₂ d172)) ∗
      memRegion (fsp + 152#64) 8 ∗
      memRegion (fsp + 168#64) 4 ∗
      memRegion (fsp + 176#64) 32 := by
  have h56 :
      memRegion (fsp + 152#64) 32 ∗
      ((fsp + 184#64) ↦₃₂ d184) ∗
      memRegion (fsp + 188#64) 4 ∗
      ((fsp + 192#64) ↦₆₄ v192) ∗
      ((fsp + 200#64) ↦₃₂ d200) ∗
      memRegion (fsp + 204#64) 4 ⊢
      memRegion (fsp + 152#64) 56 := by
    exact collapse_top <|
      collapse_step (Entails.refl _) <|
      collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
      Entails.refl _
  have hsplit :
      memRegion (fsp + 152#64) 56 ⊢
      memRegion (fsp + 152#64) 8 ∗
      (∃∗ u160 : BitVec 64, ((fsp + 160#64) ↦₆₄ u160)) ∗
      memRegion (fsp + 168#64) 4 ∗
      (∃∗ d172 : BitVec 32, ((fsp + 172#64) ↦₃₂ d172)) ∗
      memRegion (fsp + 176#64) 32 := by
    exact split_top <|
      split_step (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem32_entails _) <|
      Entails.refl _
  refine Entails.trans h56 (Entails.trans hsplit ?_)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d172
  apply Entails.sepExists_elim; intro u160
  exact Entails.sepExists_right u160 (Entails.sepExists_right d172 (Entails.of_eq (by ac_rfl)))

set_option maxHeartbeats 800000 in
theorem v6hr_midStack_240_1888_split (fsp : BitVec 64) :
    memRegion (fsp + 1392#64) 40 ∗
      memRegion (fsp + 240#64) 1152 ∗
      memRegion (fsp + 1432#64) 456 ⊢
      (∃∗ uq608 : BitVec 128, ∃∗ uq624 : BitVec 128, ∃∗ uq640 : BitVec 128,
       ∃∗ uq656 : BitVec 128, ∃∗ uq672 : BitVec 128, ∃∗ uq688 : BitVec 128,
       ∃∗ uq704 : BitVec 128, ∃∗ uq720 : BitVec 128, ∃∗ uq736 : BitVec 128,
       ∃∗ uq752 : BitVec 128, ∃∗ uq768 : BitVec 128, ∃∗ uq784 : BitVec 128,
       ∃∗ uq800 : BitVec 128, ∃∗ uq816 : BitVec 128, ∃∗ u832 : BitVec 64,
       ∃∗ uq848 : BitVec 128, ∃∗ u864 : BitVec 64, ∃∗ u880 : BitVec 64, ∃∗ u888 : BitVec 64,
        ((fsp + 608#64) ↦₁₂₈ uq608) ∗ ((fsp + 624#64) ↦₁₂₈ uq624) ∗
        ((fsp + 640#64) ↦₁₂₈ uq640) ∗ ((fsp + 656#64) ↦₁₂₈ uq656) ∗
        ((fsp + 672#64) ↦₁₂₈ uq672) ∗ ((fsp + 688#64) ↦₁₂₈ uq688) ∗
        ((fsp + 704#64) ↦₁₂₈ uq704) ∗ ((fsp + 720#64) ↦₁₂₈ uq720) ∗
        ((fsp + 736#64) ↦₁₂₈ uq736) ∗ ((fsp + 752#64) ↦₁₂₈ uq752) ∗
        ((fsp + 768#64) ↦₁₂₈ uq768) ∗ ((fsp + 784#64) ↦₁₂₈ uq784) ∗
        ((fsp + 800#64) ↦₁₂₈ uq800) ∗ ((fsp + 816#64) ↦₁₂₈ uq816) ∗
        ((fsp + 832#64) ↦₆₄ u832) ∗
        ((fsp + 848#64) ↦₁₂₈ uq848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864) ∗
        ((fsp + 880#64) ↦₆₄ u880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 u888)) ∗
      memRegion (fsp + 240#64) 368 ∗
      memRegion (fsp + 840#64) 8 ∗
      memRegion (fsp + 871#64) 9 ∗
      memRegion (fsp + 895#64) 993 := by
  have h1648 :
      memRegion (fsp + 240#64) 1152 ∗
      memRegion (fsp + 1392#64) 40 ∗
      memRegion (fsp + 1432#64) 456 ⊢
      memRegion (fsp + 240#64) 1648 := by
    exact collapse_top <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      Entails.refl _
  have hsplit :
      memRegion (fsp + 240#64) 1648 ⊢
      memRegion (fsp + 240#64) 368 ∗
      (∃∗ uq608 : BitVec 128, ((fsp + 608#64) ↦₁₂₈ uq608)) ∗
      (∃∗ uq624 : BitVec 128, ((fsp + 624#64) ↦₁₂₈ uq624)) ∗
      (∃∗ uq640 : BitVec 128, ((fsp + 640#64) ↦₁₂₈ uq640)) ∗
      (∃∗ uq656 : BitVec 128, ((fsp + 656#64) ↦₁₂₈ uq656)) ∗
      (∃∗ uq672 : BitVec 128, ((fsp + 672#64) ↦₁₂₈ uq672)) ∗
      (∃∗ uq688 : BitVec 128, ((fsp + 688#64) ↦₁₂₈ uq688)) ∗
      (∃∗ uq704 : BitVec 128, ((fsp + 704#64) ↦₁₂₈ uq704)) ∗
      (∃∗ uq720 : BitVec 128, ((fsp + 720#64) ↦₁₂₈ uq720)) ∗
      (∃∗ uq736 : BitVec 128, ((fsp + 736#64) ↦₁₂₈ uq736)) ∗
      (∃∗ uq752 : BitVec 128, ((fsp + 752#64) ↦₁₂₈ uq752)) ∗
      (∃∗ uq768 : BitVec 128, ((fsp + 768#64) ↦₁₂₈ uq768)) ∗
      (∃∗ uq784 : BitVec 128, ((fsp + 784#64) ↦₁₂₈ uq784)) ∗
      (∃∗ uq800 : BitVec 128, ((fsp + 800#64) ↦₁₂₈ uq800)) ∗
      (∃∗ uq816 : BitVec 128, ((fsp + 816#64) ↦₁₂₈ uq816)) ∗
      (∃∗ u832 : BitVec 64, ((fsp + 832#64) ↦₆₄ u832)) ∗
      memRegion (fsp + 840#64) 8 ∗
      (∃∗ uq848 : BitVec 128, ((fsp + 848#64) ↦₁₂₈ uq848)) ∗
      ((∃∗ u864 : BitVec 64, ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864)) ∗
       memRegion (fsp + 871#64) 9) ∗
      (∃∗ u880 : BitVec 64, ((fsp + 880#64) ↦₆₄ u880)) ∗
      ((∃∗ u888 : BitVec 64, ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 u888)) ∗
       memRegion (fsp + 895#64) 993) := by
    exact split_top <|
      split_step (Entails.refl _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem128_entails _) <|
      split_step (v6hr_memRegion_entails_loBytes7_and_tail fsp 864#64 871#64 8) <|
      split_step (mem64_entails _) <|
      v6hr_memRegion_entails_loBytes7_and_tail fsp 888#64 895#64 992
  refine Entails.trans (Entails.of_eq (by ac_rfl)) (Entails.trans h1648 (Entails.trans hsplit ?_))
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u888; apply Entails.sepExists_elim; intro u880
  apply Entails.sepExists_elim; intro u864; apply Entails.sepExists_elim; intro uq848
  apply Entails.sepExists_elim; intro u832; apply Entails.sepExists_elim; intro uq816
  apply Entails.sepExists_elim; intro uq800; apply Entails.sepExists_elim; intro uq784
  apply Entails.sepExists_elim; intro uq768; apply Entails.sepExists_elim; intro uq752
  apply Entails.sepExists_elim; intro uq736; apply Entails.sepExists_elim; intro uq720
  apply Entails.sepExists_elim; intro uq704; apply Entails.sepExists_elim; intro uq688
  apply Entails.sepExists_elim; intro uq672; apply Entails.sepExists_elim; intro uq656
  apply Entails.sepExists_elim; intro uq640; apply Entails.sepExists_elim; intro uq624
  apply Entails.sepExists_elim; intro uq608
  exact Entails.sepExists_right uq608 (Entails.sepExists_right uq624 (Entails.sepExists_right uq640
    (Entails.sepExists_right uq656 (Entails.sepExists_right uq672 (Entails.sepExists_right uq688
      (Entails.sepExists_right uq704 (Entails.sepExists_right uq720 (Entails.sepExists_right uq736
        (Entails.sepExists_right uq752 (Entails.sepExists_right uq768 (Entails.sepExists_right uq784
          (Entails.sepExists_right uq800 (Entails.sepExists_right uq816 (Entails.sepExists_right u832
            (Entails.sepExists_right uq848 (Entails.sepExists_right u864 (Entails.sepExists_right u880
              (Entails.sepExists_right u888 (Entails.of_eq (by ac_rfl))))))))))))))))))))

set_option maxHeartbeats 800000 in
theorem v6hr_stack_10000_ok_entails (sp0 l0 ep p2_new p0 : BitVec 64)
    (d184 : BitVec 32) (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 l2 v224 v232 : BitVec 64) :
    v6hr_lowStackAt sp0 l0 ep p2_new p0 d184 v192 d200 v208 l2 v224 v232 ∗
      memRegion ((sp0 - 2400#64) + 1392#64) 40 ∗
      (memRegion ((sp0 - 2400#64) + 240#64) 1152 ∗
       memRegion ((sp0 - 2400#64) + 1432#64) 456 ∗
       memRegion ((sp0 - 2400#64) + 2288#64) 16) ⊢
      ∃∗ u160 : BitVec 64, ∃∗ d172 : BitVec 32,
      ∃∗ uq608 : BitVec 128, ∃∗ uq624 : BitVec 128, ∃∗ uq640 : BitVec 128,
      ∃∗ uq656 : BitVec 128, ∃∗ uq672 : BitVec 128, ∃∗ uq688 : BitVec 128,
      ∃∗ uq704 : BitVec 128, ∃∗ uq720 : BitVec 128, ∃∗ uq736 : BitVec 128,
      ∃∗ uq752 : BitVec 128, ∃∗ uq768 : BitVec 128, ∃∗ uq784 : BitVec 128,
      ∃∗ uq800 : BitVec 128, ∃∗ uq816 : BitVec 128, ∃∗ u832 : BitVec 64,
      ∃∗ uq848 : BitVec 128, ∃∗ u864 : BitVec 64, ∃∗ u880 : BitVec 64, ∃∗ u888 : BitVec 64,
        (((sp0 - 2400#64) + 80#64) ↦₆₄ l0) ∗
        (((sp0 - 2400#64) + 128#64) ↦₆₄ ep) ∗
        (((sp0 - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
        (((sp0 - 2400#64) + 144#64) ↦₆₄ p0) ∗
        (((sp0 - 2400#64) + 216#64) ↦₆₄ l2) ∗
        v6hr_stagingSlotsPre (sp0 - 2400#64) u160 d172 v208 v224 v232
          uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
          u832 uq848 u864 u880 u888 ∗
        v6hr_stackRest10000 (sp0 - 2400#64) := by
  have hlow := v6hr_lowStack_152_208_split (sp0 - 2400#64) d184 v192 d200
  rw [show (sp0 - 2400#64) + 152#64 = sp0 - 2248#64 by bv_omega,
      show (sp0 - 2400#64) + 184#64 = sp0 - 2216#64 by bv_omega,
      show (sp0 - 2400#64) + 188#64 = sp0 - 2212#64 by bv_omega,
      show (sp0 - 2400#64) + 192#64 = sp0 - 2208#64 by bv_omega,
      show (sp0 - 2400#64) + 200#64 = sp0 - 2200#64 by bv_omega,
      show (sp0 - 2400#64) + 204#64 = sp0 - 2196#64 by bv_omega] at hlow
  have hmid := v6hr_midStack_240_1888_split (sp0 - 2400#64)
  unfold v6hr_lowStackAt v6hr_lowStackGaps
  refine Entails.trans
    (Entails.of_eq (show _ =
      (memRegion (sp0 - 2248#64) 32 ∗
       ((sp0 - 2216#64) ↦₃₂ d184) ∗
       memRegion (sp0 - 2212#64) 4 ∗
       ((sp0 - 2208#64) ↦₆₄ v192) ∗
       ((sp0 - 2200#64) ↦₃₂ d200) ∗
       memRegion (sp0 - 2196#64) 4) ∗
      (memRegion ((sp0 - 2400#64) + 1392#64) 40 ∗
       memRegion ((sp0 - 2400#64) + 240#64) 1152 ∗
       memRegion ((sp0 - 2400#64) + 1432#64) 456) ∗
      (((sp0 - 2320#64) ↦₆₄ l0) ∗
       ((sp0 - 2272#64) ↦₆₄ ep) ∗
       ((sp0 - 2264#64) ↦₆₄ p2_new) ∗
       ((sp0 - 2256#64) ↦₆₄ p0) ∗
       ((sp0 - 2192#64) ↦₆₄ v208) ∗
       ((sp0 - 2184#64) ↦₆₄ l2) ∗
       ((sp0 - 2176#64) ↦₆₄ v224) ∗
       ((sp0 - 2168#64) ↦₆₄ v232) ∗
       memRegion (sp0 - 2400#64) 80 ∗
       memRegion (sp0 - 2312#64) 40 ∗
       memRegion ((sp0 - 2400#64) + 2288#64) 16) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hlow (sepConj_mono_left hmid)) ?_
  rw [show sp0 - 2320#64 = (sp0 - 2400#64) + 80#64 by bv_omega,
      show sp0 - 2272#64 = (sp0 - 2400#64) + 128#64 by bv_omega,
      show sp0 - 2264#64 = (sp0 - 2400#64) + 136#64 by bv_omega,
      show sp0 - 2256#64 = (sp0 - 2400#64) + 144#64 by bv_omega,
      show sp0 - 2192#64 = (sp0 - 2400#64) + 208#64 by bv_omega,
      show sp0 - 2184#64 = (sp0 - 2400#64) + 216#64 by bv_omega,
      show sp0 - 2176#64 = (sp0 - 2400#64) + 224#64 by bv_omega,
      show sp0 - 2168#64 = (sp0 - 2400#64) + 232#64 by bv_omega,
      show sp0 - 2312#64 = (sp0 - 2400#64) + 88#64 by bv_omega,
      show sp0 - 2248#64 = (sp0 - 2400#64) + 152#64 by bv_omega]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro uq608; apply Entails.sepExists_elim; intro uq624
  apply Entails.sepExists_elim; intro uq640; apply Entails.sepExists_elim; intro uq656
  apply Entails.sepExists_elim; intro uq672; apply Entails.sepExists_elim; intro uq688
  apply Entails.sepExists_elim; intro uq704; apply Entails.sepExists_elim; intro uq720
  apply Entails.sepExists_elim; intro uq736; apply Entails.sepExists_elim; intro uq752
  apply Entails.sepExists_elim; intro uq768; apply Entails.sepExists_elim; intro uq784
  apply Entails.sepExists_elim; intro uq800; apply Entails.sepExists_elim; intro uq816
  apply Entails.sepExists_elim; intro u832; apply Entails.sepExists_elim; intro uq848
  apply Entails.sepExists_elim; intro u864; apply Entails.sepExists_elim; intro u880
  apply Entails.sepExists_elim; intro u888
  apply Entails.sepExists_elim; intro u160; apply Entails.sepExists_elim; intro d172
  refine Entails.sepExists_right u160 (Entails.sepExists_right d172
    (Entails.sepExists_right uq608 (Entails.sepExists_right uq624 (Entails.sepExists_right uq640
      (Entails.sepExists_right uq656 (Entails.sepExists_right uq672 (Entails.sepExists_right uq688
        (Entails.sepExists_right uq704 (Entails.sepExists_right uq720 (Entails.sepExists_right uq736
          (Entails.sepExists_right uq752 (Entails.sepExists_right uq768 (Entails.sepExists_right uq784
            (Entails.sepExists_right uq800 (Entails.sepExists_right uq816 (Entails.sepExists_right u832
              (Entails.sepExists_right uq848 (Entails.sepExists_right u864 (Entails.sepExists_right u880
                (Entails.sepExists_right u888 ?_))))))))))))))))))))
  unfold v6hr_stagingSlotsPre v6hr_stackRest10000
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.FromPb
