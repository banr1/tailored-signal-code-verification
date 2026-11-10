/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9b
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 9 (`Ct1Acknowledged`, `+444`) — Part C

Completes the Variant 9 stepping (`+2864 -> +6904`, `+2864 -> +35448 -> +3044.. -> +8180 / +8588`)
and epilogue reconstruction for `.ok (.ct1Acknowledged ...)`.
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

@[local simp, local arm64_norm, local wp_norm]
theorem v9_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-! ## 1. `PolyDecoder` Cell Unpacking and Relocation (`fsp + 1888 -> out + 136`) -/

/-- Pack 8 bytes (little-endian) from `bs` into a `BitVec 64`. -/
def v9_pack64 (bs : List (BitVec 8)) : BitVec 64 :=
  (bs.getD 7 0#8) ++ (bs.getD 6 0#8) ++ (bs.getD 5 0#8) ++ (bs.getD 4 0#8) ++
  (bs.getD 3 0#8) ++ (bs.getD 2 0#8) ++ (bs.getD 1 0#8) ++ (bs.getD 0 0#8)

theorem v9_unpack64_pack64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    unpack64 (v9_pack64 bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at h; done)
  change [_, _, _, _, _, _, _, _] = [b0, b1, b2, b3, b4, b5, b6, b7]
  dsimp only [v9_pack64, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
         by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem v9_pack64_unpack64 (w : BitVec 64) :
    v9_pack64 (unpack64 w) = w := by
  dsimp only [v9_pack64, unpack64, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  bv_kernel

theorem v9_pointsToBytes_eq_pack64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ v9_pack64 bs) := by
  rw [pointsTo64_eq_pointsToBytes, v9_unpack64_pack64 bs h]

/-- Pack 16 bytes (little-endian) from `bs` into a `BitVec 128`. -/
def v9_pack128 (bs : List (BitVec 8)) : BitVec 128 :=
  v9_pack64 (bs.drop 8) ++ v9_pack64 (bs.take 8)

theorem v9_pointsToBytes_eq_pack128 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 16) :
    (a ↦ₛ bs) = (a ↦₁₂₈ v9_pack128 bs) := by
  have h1 : (bs.take 8).length = 8 := by simp [h]
  have h2 : (bs.drop 8).length = 8 := by simp [h]
  nth_rw 1 [← List.take_append_drop 8 bs]
  rw [ProofLib.pointsToBytes_append a (bs.take 8) (bs.drop 8), h1]
  change (a ↦ₛ bs.take 8) ∗ ((a + 8#64) ↦ₛ bs.drop 8) = (a ↦₁₂₈ v9_pack128 bs)
  rw [v9_pointsToBytes_eq_pack64 a (bs.take 8) h1,
      v9_pointsToBytes_eq_pack64 (a + 8#64) (bs.drop 8) h2,
      pointsTo64_pair_eq_pointsTo128]
  rfl

/-- 8-byte word at byte offset `i` within `bs`. -/
def v9_wordAt (bs : List (BitVec 8)) (i : Nat) : BitVec 64 :=
  v9_pack64 ((bs.drop i).take 8)

/-- 16-byte quadword at byte offset `i` within `bs`. -/
def v9_quadAt (bs : List (BitVec 8)) (i : Nat) : BitVec 128 :=
  v9_pack128 ((bs.drop i).take 16)

theorem v9_bs_drop_step8_zero {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a : BitVec 64) {Q : SepProp}
    (hrest : ((a + 8#64) ↦ₛ bs.drop 8) = Q) :
    (a ↦ₛ bs.drop 0) = (a ↦₆₄ v9_wordAt bs 0) ∗ Q := by
  have htake_len : ((bs.drop 0).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hbs]; omega
  have hsplit : bs.drop 0 = (bs.drop 0).take 8 ++ bs.drop 8 :=
    (List.take_append_drop 8 bs).symm
  rw [hsplit, ProofLib.pointsToBytes_append a ((bs.drop 0).take 8) (bs.drop 8),
      htake_len, v9_pointsToBytes_eq_pack64 a ((bs.drop 0).take 8) htake_len, hrest]
  rfl

theorem v9_bs_drop_step8 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 o2 : BitVec 64) (i : Nat) {Q : SepProp}
    (hrest : ((a + o2) ↦ₛ bs.drop (i + 8)) = Q)
    (hi : i + 8 ≤ 384 := by decide)
    (ho : o1 + 8#64 = o2 := by rfl) :
    ((a + o1) ↦ₛ bs.drop i) = ((a + o1) ↦₆₄ v9_wordAt bs i) ∗ Q := by
  have htake_len : ((bs.drop i).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hbs]; omega
  have hsplit : bs.drop i = (bs.drop i).take 8 ++ bs.drop (i + 8) := by
    rw [← List.drop_drop, List.take_append_drop]
  have ha : (a + o1) + BitVec.ofNat 64 ((bs.drop i).take 8).length = a + o2 := by
    rw [htake_len, BitVec.add_assoc, ho]
  rw [hsplit, ProofLib.pointsToBytes_append (a + o1) ((bs.drop i).take 8) (bs.drop (i + 8)),
      ha, v9_pointsToBytes_eq_pack64 (a + o1) ((bs.drop i).take 8) htake_len, hrest]
  rfl

theorem v9_bs_drop_step16 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 o2 : BitVec 64) (i : Nat) {Q : SepProp}
    (hrest : ((a + o2) ↦ₛ bs.drop (i + 16)) = Q)
    (hi : i + 16 ≤ 384 := by decide)
    (ho : o1 + 16#64 = o2 := by rfl) :
    ((a + o1) ↦ₛ bs.drop i) = ((a + o1) ↦₁₂₈ v9_quadAt bs i) ∗ Q := by
  have htake_len : ((bs.drop i).take 16).length = 16 := by
    rw [List.length_take, List.length_drop, hbs]; omega
  have hsplit : bs.drop i = (bs.drop i).take 16 ++ bs.drop (i + 16) := by
    rw [← List.drop_drop, List.take_append_drop]
  have ha : (a + o1) + BitVec.ofNat 64 ((bs.drop i).take 16).length = a + o2 := by
    rw [htake_len, BitVec.add_assoc, ho]
  rw [hsplit, ProofLib.pointsToBytes_append (a + o1) ((bs.drop i).take 16) (bs.drop (i + 16)),
      ha, v9_pointsToBytes_eq_pack128 (a + o1) ((bs.drop i).take 16) htake_len, hrest]
  rfl

theorem v9_bs_drop_end8 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 : BitVec 64) :
    ((a + o1) ↦ₛ bs.drop 376) = ((a + o1) ↦₆₄ v9_wordAt bs 376) := by
  have hlen : (bs.drop 376).length = 8 := by rw [List.length_drop, hbs]
  have htake : (bs.drop 376).take 8 = bs.drop 376 := List.take_of_length_le (by omega)
  rw [v9_pointsToBytes_eq_pack64 (a + o1) (bs.drop 376) hlen]
  unfold v9_wordAt
  rw [htake]

/-- The 384-byte `PolyDecoder` `pts` vector-headers region at `a..a + 384` decomposed into
the exact 64-bit and 128-bit cells accessed at `+3044..+3340` (`a = fsp + 1888`) and
written by `epilogueOutFull` (`a = out + 136`). -/
def v9_decCellsAt (a : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (a ↦₆₄ v9_wordAt bs 0) ∗ ((a + 8#64) ↦₆₄ v9_wordAt bs 8) ∗ ((a + 16#64) ↦₆₄ v9_wordAt bs 16) ∗
  ((a + 24#64) ↦₆₄ v9_wordAt bs 24) ∗ ((a + 32#64) ↦₁₂₈ v9_quadAt bs 32) ∗ ((a + 48#64) ↦₁₂₈ v9_quadAt bs 48) ∗
  ((a + 64#64) ↦₁₂₈ v9_quadAt bs 64) ∗ ((a + 80#64) ↦₁₂₈ v9_quadAt bs 80) ∗ ((a + 96#64) ↦₁₂₈ v9_quadAt bs 96) ∗
  ((a + 112#64) ↦₁₂₈ v9_quadAt bs 112) ∗ ((a + 128#64) ↦₁₂₈ v9_quadAt bs 128) ∗ ((a + 144#64) ↦₁₂₈ v9_quadAt bs 144) ∗
  ((a + 160#64) ↦₁₂₈ v9_quadAt bs 160) ∗ ((a + 176#64) ↦₁₂₈ v9_quadAt bs 176) ∗ ((a + 192#64) ↦₁₂₈ v9_quadAt bs 192) ∗
  ((a + 208#64) ↦₁₂₈ v9_quadAt bs 208) ∗ ((a + 224#64) ↦₁₂₈ v9_quadAt bs 224) ∗ ((a + 240#64) ↦₁₂₈ v9_quadAt bs 240) ∗
  ((a + 256#64) ↦₆₄ v9_wordAt bs 256) ∗ ((a + 264#64) ↦₆₄ v9_wordAt bs 264) ∗ ((a + 272#64) ↦₆₄ v9_wordAt bs 272) ∗
  ((a + 280#64) ↦₆₄ v9_wordAt bs 280) ∗ ((a + 288#64) ↦₆₄ v9_wordAt bs 288) ∗ ((a + 296#64) ↦₆₄ v9_wordAt bs 296) ∗
  ((a + 304#64) ↦₆₄ v9_wordAt bs 304) ∗ ((a + 312#64) ↦₆₄ v9_wordAt bs 312) ∗ ((a + 320#64) ↦₆₄ v9_wordAt bs 320) ∗
  ((a + 328#64) ↦₆₄ v9_wordAt bs 328) ∗ ((a + 336#64) ↦₆₄ v9_wordAt bs 336) ∗ ((a + 344#64) ↦₆₄ v9_wordAt bs 344) ∗
  ((a + 352#64) ↦₆₄ v9_wordAt bs 352) ∗ ((a + 360#64) ↦₆₄ v9_wordAt bs 360) ∗ ((a + 368#64) ↦₆₄ v9_wordAt bs 368) ∗
  ((a + 376#64) ↦₆₄ v9_wordAt bs 376)

theorem v9_bs384_eq_decCells (bs : List (BitVec 8)) (hbs : bs.length = 384) (a : BitVec 64) :
    (a ↦ₛ bs) = v9_decCellsAt a bs := by
  unfold v9_decCellsAt
  change (a ↦ₛ bs.drop 0) = _
  exact
    v9_bs_drop_step8_zero hbs a <| v9_bs_drop_step8 hbs a 8#64 16#64 8 <|
    v9_bs_drop_step8 hbs a 16#64 24#64 16 <| v9_bs_drop_step8 hbs a 24#64 32#64 24 <|
    v9_bs_drop_step16 hbs a 32#64 48#64 32 <| v9_bs_drop_step16 hbs a 48#64 64#64 48 <|
    v9_bs_drop_step16 hbs a 64#64 80#64 64 <| v9_bs_drop_step16 hbs a 80#64 96#64 80 <|
    v9_bs_drop_step16 hbs a 96#64 112#64 96 <| v9_bs_drop_step16 hbs a 112#64 128#64 112 <|
    v9_bs_drop_step16 hbs a 128#64 144#64 128 <| v9_bs_drop_step16 hbs a 144#64 160#64 144 <|
    v9_bs_drop_step16 hbs a 160#64 176#64 160 <| v9_bs_drop_step16 hbs a 176#64 192#64 176 <|
    v9_bs_drop_step16 hbs a 192#64 208#64 192 <| v9_bs_drop_step16 hbs a 208#64 224#64 208 <|
    v9_bs_drop_step16 hbs a 224#64 240#64 224 <| v9_bs_drop_step16 hbs a 240#64 256#64 240 <|
    v9_bs_drop_step8 hbs a 256#64 264#64 256 <| v9_bs_drop_step8 hbs a 264#64 272#64 264 <|
    v9_bs_drop_step8 hbs a 272#64 280#64 272 <| v9_bs_drop_step8 hbs a 280#64 288#64 280 <|
    v9_bs_drop_step8 hbs a 288#64 296#64 288 <| v9_bs_drop_step8 hbs a 296#64 304#64 296 <|
    v9_bs_drop_step8 hbs a 304#64 312#64 304 <| v9_bs_drop_step8 hbs a 312#64 320#64 312 <|
    v9_bs_drop_step8 hbs a 320#64 328#64 320 <| v9_bs_drop_step8 hbs a 328#64 336#64 328 <|
    v9_bs_drop_step8 hbs a 336#64 344#64 336 <| v9_bs_drop_step8 hbs a 344#64 352#64 344 <|
    v9_bs_drop_step8 hbs a 352#64 360#64 352 <| v9_bs_drop_step8 hbs a 360#64 368#64 360 <|
    v9_bs_drop_step8 hbs a 368#64 376#64 368 <| v9_bs_drop_end8 hbs a 376#64

/-- Concatenated 24-byte `Vec` headers for `pins` and `SortedSetPt` slices. -/
def v9_ptHeadersBytesOf : List VecPin → List SortedSetPt → List (BitVec 8)
  | [], _ => []
  | _, [] => []
  | pin :: pins, s :: ss => vecHeaderBytesOf pin s.vec.length ++ v9_ptHeadersBytesOf pins ss

theorem v9_length_ptHeadersBytesOf :
    ∀ (pins : List VecPin) (ss : List SortedSetPt),
      pins.length = ss.length →
      (v9_ptHeadersBytesOf pins ss).length = ss.length * 24
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | pin :: pins, s :: ss, h => by
    simp only [List.length_cons] at h
    have ih := v9_length_ptHeadersBytesOf pins ss (Nat.succ.inj h)
    simp only [v9_ptHeadersBytesOf, List.length_append, length_vecHeaderBytesOf, ih, List.length_cons]
    omega

/-- Separating conjunction of `vecBuf A ptStride ptAlign ptAt` across `pins` and `ss`. -/
def v9_ptHeapList (A : RustAlloc) : List VecPin → List SortedSetPt → SepProp
  | [], _ => emp
  | _, [] => emp
  | pin :: pins, s :: ss =>
    vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec ∗ v9_ptHeapList A pins ss

theorem v9_sortedSetPtOf_entails_pin (A : RustAlloc) (a : BitVec 64) (s : SortedSetPt) :
    sortedSetPtOf A a s ⊢
      ∃∗ pin : VecPin,
        ⌜pin.cap.toNat < 2 ^ 63⌝ ∗
        (a ↦ₛ vecHeaderBytesOf pin s.vec.length) ∗
        vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec := by
  unfold sortedSetPtOf vecOf vecAt
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ⟨cap, ptr⟩ ?_
  rw [← vecHeader_eq_pointsToBytes a ⟨cap, ptr⟩ s.vec.length]
  have hcap : vecBuf A ptStride ptAlign ptAt cap ptr s.vec ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗ vecBuf A ptStride ptAlign ptAt cap ptr s.vec := by
    unfold vecBuf ptStride
    apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
    have hlt' : cap.toNat < 2 ^ 63 := by omega
    exact Entails.pure_right hlt' (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))
  exact Entails.trans (sepConj_mono_right hcap) (Entails.of_eq (by ac_rfl))

theorem v9_pin_entails_sortedSetPtOf (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (s : SortedSetPt) :
    (a ↦ₛ vecHeaderBytesOf pin s.vec.length) ∗
      vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec ⊢
      sortedSetPtOf A a s := by
  rw [← vecHeader_eq_pointsToBytes a pin s.vec.length]
  unfold sortedSetPtOf vecOf vecAt
  exact Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr (Entails.refl _))

theorem v9_sortedSetPtListOf_entails_headers_heaps (A : RustAlloc) :
    ∀ (ss : List SortedSetPt) (a : BitVec 64),
      sortedSetPtListOf A a ss ⊢
        ∃∗ pins : List VecPin,
          ⌜pins.length = ss.length ∧ (∀ pin ∈ pins.head?, pin.cap.toNat < 2 ^ 63)⌝ ∗
          (a ↦ₛ v9_ptHeadersBytesOf pins ss) ∗
          v9_ptHeapList A pins ss
  | [], a => by
    simp only [sortedSetPtListOf, arrayAt]
    refine Entails.sepExists_right [] ?_
    simp [v9_ptHeadersBytesOf, v9_ptHeapList, ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | s :: ss, a => by
    simp only [sortedSetPtListOf, arrayAt, Poly.vecHeaderBytes]
    refine Entails.trans (sepConj_mono (v9_sortedSetPtOf_entails_pin A a s)
      (v9_sortedSetPtListOf_entails_headers_heaps A ss (a + 24#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro pins
    apply Entails.sepExists_elim; intro pin
    apply Entails.pure_left; intro hcap0
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, _⟩
    refine Entails.sepExists_right (pin :: pins) ?_
    have hlen' : (pin :: pins).length = (s :: ss).length := by simp [hlen]
    have hhead : ∀ p ∈ (pin :: pins).head?, p.cap.toNat < 2 ^ 63 := by
      intro p hp; simp at hp; subst hp; exact hcap0
    refine Entails.pure_right ⟨hlen', hhead⟩ ?_
    simp only [v9_ptHeadersBytesOf, v9_ptHeapList]
    rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin s.vec.length) (v9_ptHeadersBytesOf pins ss),
        length_vecHeaderBytesOf]
    exact Entails.of_eq (by ac_rfl)

theorem v9_headers_heaps_entails_sortedSetPtListOf (A : RustAlloc) :
    ∀ (pins : List VecPin) (ss : List SortedSetPt) (a : BitVec 64),
      pins.length = ss.length →
      (a ↦ₛ v9_ptHeadersBytesOf pins ss) ∗ v9_ptHeapList A pins ss ⊢
        sortedSetPtListOf A a ss
  | [], [], a, _ => by
    simp [v9_ptHeadersBytesOf, v9_ptHeapList, sortedSetPtListOf, arrayAt, ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | _ :: _, [], _, h => by simp at h
  | [], _ :: _, _, h => by simp at h
  | pin :: pins, s :: ss, a, h => by
    simp only [List.length_cons] at h
    simp only [v9_ptHeadersBytesOf, v9_ptHeapList, sortedSetPtListOf, arrayAt, Poly.vecHeaderBytes]
    rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin s.vec.length) (v9_ptHeadersBytesOf pins ss),
        length_vecHeaderBytesOf]
    refine Entails.trans (Entails.of_eq (show
      ((a ↦ₛ vecHeaderBytesOf pin s.vec.length) ∗ ((a + 24#64) ↦ₛ v9_ptHeadersBytesOf pins ss)) ∗
        (vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec ∗ v9_ptHeapList A pins ss) =
      ((a ↦ₛ vecHeaderBytesOf pin s.vec.length) ∗ vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr s.vec) ∗
        (((a + 24#64) ↦ₛ v9_ptHeadersBytesOf pins ss) ∗ v9_ptHeapList A pins ss) by ac_rfl)) ?_
    exact sepConj_mono (v9_pin_entails_sortedSetPtOf A a pin s)
      (v9_headers_heaps_entails_sortedSetPtListOf A pins ss (a + 24#64) (Nat.succ.inj h))

theorem v9_wordAt_0_ptHeadersBytesOf (pin : VecPin) (pins : List VecPin)
    (s : SortedSetPt) (ss : List SortedSetPt) :
    v9_wordAt (v9_ptHeadersBytesOf (pin :: pins) (s :: ss)) 0 = pin.cap := by
  unfold v9_wordAt v9_ptHeadersBytesOf vecHeaderBytesOf
  rw [List.drop_zero, List.append_assoc, List.append_assoc,
      List.take_append_of_le_length (by rw [unpack64_length]),
      List.take_of_length_le (by rw [unpack64_length]),
      v9_pack64_unpack64]

theorem v9_polyDecoderAt_relocate (A : RustAlloc) (a1 a2 : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A a1 dec ⊢
      ∃∗ bs : { l : List (BitVec 8) // l.length = 384 }, ∃∗ w392 : BitVec 64, ∃∗ P_heap : SepProp,
        ⌜(v9_wordAt bs.val 0).toNat < 2 ^ 63 ∧ EncoderFromPb.loByte w392 = boolByte dec.isComplete ∧
          ((a2 ↦ₛ bs.val) ∗ ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
           ((a2 + 392#64) ↦₆₄ w392) ∗ P_heap ⊢ polyDecoderAt A a2 dec)⌝ ∗
        (a1 ↦ₛ bs.val) ∗ ((a1 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((a1 + 392#64) ↦₆₄ w392) ∗ P_heap := by
  unfold polyDecoderAt polyDecoderPtsNeededOff polyDecoderIsCompleteOff polyDecoderPadOff polyDecoderPadSize
  have ha1_393 : a1 + 0x189#64 = (a1 + 0x188#64) + 1#64 := by bv_omega
  rw [ha1_393]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (v9_sortedSetPtListOf_entails_headers_heaps A dec.pts a1)
      (sepConj_mono_right (v9_byte_pad7_entails_64 (a1 + 0x188#64) (boolByte dec.isComplete))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w392; apply Entails.sepExists_elim; intro pins
  apply Entails.pure_left; rintro ⟨hpts_len, hpts_lt⟩; apply Entails.pure_left; rintro ⟨hpins_len, hpin0⟩
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hw392
  have hbs_len : (v9_ptHeadersBytesOf pins dec.pts).length = 384 := by
    rw [v9_length_ptHeadersBytesOf pins dec.pts hpins_len, hpts_len]; rfl
  have hw0_lt : (v9_wordAt (v9_ptHeadersBytesOf pins dec.pts) 0).toNat < 2 ^ 63 := by
    rcases pins with _ | ⟨pin, pins'⟩
    · rw [hpts_len] at hpins_len; simp [NUM_POLYS, CHUNK_SIZE] at hpins_len
    · rcases hpts : dec.pts with _ | ⟨s, ss⟩
      · rw [hpts] at hpts_len; simp [NUM_POLYS, CHUNK_SIZE] at hpts_len
      · rw [v9_wordAt_0_ptHeadersBytesOf]; exact hpin0 pin rfl
  refine Entails.sepExists_right ⟨v9_ptHeadersBytesOf pins dec.pts, hbs_len⟩
    (Entails.sepExists_right w392 (Entails.sepExists_right (v9_ptHeapList A pins dec.pts) ?_))
  change _ ⊢ ⌜(v9_wordAt (v9_ptHeadersBytesOf pins dec.pts) 0).toNat < 2 ^ 63 ∧
      EncoderFromPb.loByte w392 = boolByte dec.isComplete ∧
      ((a2 ↦ₛ v9_ptHeadersBytesOf pins dec.pts) ∗ ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
       ((a2 + 392#64) ↦₆₄ w392) ∗ v9_ptHeapList A pins dec.pts ⊢
        ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗ sortedSetPtListOf A a2 dec.pts ∗
        ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((a2 + 392#64) ↦₈ boolByte dec.isComplete) ∗
        memRegion (a2 + 393#64) 7)⌝ ∗
    (a1 ↦ₛ v9_ptHeadersBytesOf pins dec.pts) ∗ ((a1 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
    ((a1 + 392#64) ↦₆₄ w392) ∗ v9_ptHeapList A pins dec.pts
  refine Entails.pure_right ⟨hw0_lt, hw392, ?_⟩ (Entails.of_eq (by ac_rfl))
  have hss2 := v9_headers_heaps_entails_sortedSetPtListOf A pins dec.pts a2 hpins_len
  have ha2_393 : (a2 + 392#64) + 1#64 = a2 + 393#64 := by bv_omega
  have hm392 := v9_pointsTo64_entails_byte_pad7 (a2 + 392#64) w392 (boolByte dec.isComplete) hw392
  rw [ha2_393] at hm392
  refine Entails.trans (Entails.of_eq (show _ =
    ((a2 ↦ₛ v9_ptHeadersBytesOf pins dec.pts) ∗ v9_ptHeapList A pins dec.pts) ∗
    ((a2 + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((a2 + 392#64) ↦₆₄ w392) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hss2 (sepConj_mono_right hm392)) ?_
  exact Entails.pure_right ⟨hpts_len, hpts_lt⟩ (Entails.of_eq (by ac_rfl))

theorem v9_resultPolyDecoder_err_entails_tag_392 (A : RustAlloc) (fsp : BitVec 64)
    (err : PolynomialError) :
    resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err) ⊢
      ((fsp + 1888#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 1896#64) 392 := by
  dsimp only [resultPolyDecoderFromPbAt, resultPolyDecoderErrByteOff, resultPolyDecoderErrTailSize]
  have hm8 : ((fsp + 1896#64) ↦₈ polynomialErrorByte err) ∗ memRegion (fsp + 1897#64) 391 ⊢
      memRegion (fsp + 1896#64) 392 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1896#64) (n := 1) (k := 391) (b' := fsp + 1897#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (fsp + 1896#64) (polynomialErrorByte err))
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  have ha1897 : (fsp + 1888#64) + 9#64 = fsp + 1897#64 := by bv_omega
  rw [ha1896, ha1897]; exact sepConj_mono_right hm8

/-! ## 2. Output Realignment & `epilogueOutFull` Packing for `Ct1Acknowledged` -/

theorem v9_ct1SentAt_pack (A : RustAlloc) {F : ShaCompress} (base : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    v9_optProtoUcWordsAt base rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
    v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ⊢
      unchunkedCt1SentAt A base uc := by
  dsimp only [unchunkedCt1SentAt, authenticatorAt, v9_optProtoUcWordsAt, v9_ct1SentHeap]
  have hrk := v9_vecU8_pack A base uc.auth.rootKey rkCap rkPtr rkLen
  have hmk := v9_vecU8_pack A (base + 24#64) uc.auth.macKey mkCap mkPtr mkLen
  have hhdr := v9_vecU8_pack A (base + 48#64) uc.hdr hdrCap hdrPtr hdrLen
  have hes := v9_vecU8_pack A (base + 72#64) uc.es esCap esPtr esLen
  have hct1 := v9_vecU8_pack A (base + 96#64) uc.ct1 ct1Cap ct1Ptr ct1Len
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrk hmk hhdr hes hct1 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    (((base ↦₆₄ rkCap) ∗ ((base + 8#64) ↦₆₄ rkPtr) ∗ ((base + 16#64) ↦₆₄ rkLen)) ∗
     v9_vecU8Heap A uc.auth.rootKey rkCap rkPtr rkLen) ∗
    ((((base + 24#64) ↦₆₄ mkCap) ∗ ((base + 32#64) ↦₆₄ mkPtr) ∗ ((base + 40#64) ↦₆₄ mkLen)) ∗
     v9_vecU8Heap A uc.auth.macKey mkCap mkPtr mkLen) ∗
    ((((base + 48#64) ↦₆₄ hdrCap) ∗ ((base + 56#64) ↦₆₄ hdrPtr) ∗ ((base + 64#64) ↦₆₄ hdrLen)) ∗
     v9_vecU8Heap A uc.hdr hdrCap hdrPtr hdrLen) ∗
    ((((base + 72#64) ↦₆₄ esCap) ∗ ((base + 80#64) ↦₆₄ esPtr) ∗ ((base + 88#64) ↦₆₄ esLen)) ∗
     v9_vecU8Heap A uc.es esCap esPtr esLen) ∗
    ((((base + 96#64) ↦₆₄ ct1Cap) ∗ ((base + 104#64) ↦₆₄ ct1Ptr) ∗ ((base + 112#64) ↦₆₄ ct1Len)) ∗
     v9_vecU8Heap A uc.ct1 ct1Cap ct1Ptr ct1Len) ∗
    ((base + 120#64) ↦₆₄ uc.epoch) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono hrk (sepConj_mono hmk (sepConj_mono hhdr (sepConj_mono hes (sepConj_mono_left hct1))))) ?_
  exact Entails.of_eq (by ac_rfl)

/-- The 128-bit quadword loaded from `fsp + 1897` (`x24 + 9`) and stored to `fsp + 848`. -/
def v9_midQ128 (w8 w16 w24 : BitVec 64) : BitVec 128 :=
  EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24) ++
    EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)

theorem v9_lsr8_lsl8 (v : BitVec 64) : (v >>> 8) <<< 8 = v &&& 0xffffffffffffff00#64 := by bv_kernel

theorem v9_unshift_lsr56 (w0 v : BitVec 64) :
    (EncoderFromPb.unshiftWord w0 (EncoderFromPb.loByte v)) >>> 56 = v &&& 0xff#64 := by
  unfold EncoderFromPb.unshiftWord EncoderFromPb.loByte; bv_kernel

theorem v9_overlapWord7_unshift_lsr8 (w0 w8 : BitVec 64) :
    overlapWord7 (EncoderFromPb.unshiftWord w0 (EncoderFromPb.loByte w8)) (w8 >>> 8) = w8 := by
  unfold overlapWord7; rw [v9_unshift_lsr56 w0 w8, v9_lsr8_lsl8 w8]; bv_kernel

theorem v9_overlapWord7_midQ128_lsr8 (w8 w16 w24 : BitVec 64) :
    overlapWord7 ((v9_midQ128 w8 w16 w24).extractLsb' 64 64) (w24 >>> 8) = w24 := by
  have hhi : (v9_midQ128 w8 w16 w24).extractLsb' 64 64 =
      EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24) := by unfold v9_midQ128; bv_kernel
  rw [hhi]; exact v9_overlapWord7_unshift_lsr8 w16 w24

theorem v9_overlapLow7_unshift (w0 w8 : BitVec 64) :
    overlapLow7 (EncoderFromPb.unshiftWord w0 (EncoderFromPb.loByte w8)) w8 =
      EncoderFromPb.unshiftWord w0 (EncoderFromPb.loByte w8) := by
  unfold overlapLow7 EncoderFromPb.unshiftWord EncoderFromPb.loByte; bv_kernel

@[local arm64_norm, local wp_norm]
theorem v9_zext32_setWidth8 (b : BitVec 8) : (b.zeroExtend 32).setWidth 8 = b := by bv_kernel
@[local arm64_norm, local wp_norm]
theorem v9_lsr8_d97 (w : BitVec 64) : (w >>> 8).setWidth 32 = w.extractLsb' 8 32 := by bv_kernel
@[local arm64_norm, local wp_norm]
theorem v9_lsr8_h101 (w : BitVec 64) : (((w >>> 8) >>> 32).setWidth 32).setWidth 16 = w.extractLsb' 40 16 := by bv_kernel
@[local arm64_norm, local wp_norm]
theorem v9_lsr8_b103 (w : BitVec 64) : (((w >>> 8) >>> 48).setWidth 32).setWidth 8 = w.extractLsb' 56 8 := by bv_kernel
@[local arm64_norm, local wp_norm]
theorem v9_w_setWidth8_eq_extract0 (w : BitVec 64) : (w.setWidth 32).setWidth 8 = w.extractLsb' 0 8 := by bv_kernel

theorem v9_out_96_realign (out w80 : BitVec 64) :
    ((out + 96#64) ↦₈ w80.extractLsb' 0 8) ∗ ((out + 97#64) ↦₃₂ w80.extractLsb' 8 32) ∗
      ((out + 101#64) ↦₁₆ w80.extractLsb' 40 16) ∗ ((out + 103#64) ↦₈ w80.extractLsb' 56 8) =
    (out + 96#64) ↦₆₄ w80 := by
  have h := (v9_pointsTo64_split_1_4_2_1 (out + 96#64) w80).symm
  have ha97 : (out + 96#64) + 1#64 = out + 97#64 := by bv_omega
  have ha101 : (out + 96#64) + 5#64 = out + 101#64 := by bv_omega
  have ha103 : (out + 96#64) + 7#64 = out + 103#64 := by bv_omega
  rw [ha97, ha101, ha103] at h; exact h

theorem v9_out_120_realign (out w104 w112 : BitVec 64) :
    ((out + 120#64) ↦₈ EncoderFromPb.loByte w104) ∗
      ((out + 121#64) ↦₆₄ EncoderFromPb.unshiftWord w104 (EncoderFromPb.loByte w112)) ∗
      ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 (EncoderFromPb.unshiftWord w104 (EncoderFromPb.loByte w112)) (w112 >>> 8))) =
    ((out + 120#64) ↦₆₄ w104) ∗ ((out + 128#64) ↦₆₄ w112) := by
  rw [v9_overlapWord7_unshift_lsr8 w104 w112]
  have h := (pair64_to_byte_word_tail7 (out + 120#64) w104 w112).symm
  have ha121 : (out + 120#64) + 1#64 = out + 121#64 := by bv_omega
  have ha129 : (out + 120#64) + 9#64 = out + 129#64 := by bv_omega
  have ha128 : (out + 120#64) + 8#64 = out + 128#64 := by bv_omega
  rw [ha121, ha129, ha128] at h
  exact h

theorem v9_out_144_realign (out w8 w16 w24 : BitVec 64) :
    ((out + 144#64) ↦₈ ((EncoderFromPb.loByte w8).zeroExtend 32).setWidth 8) ∗
      ((out + 145#64) ↦₆₄ (v9_midQ128 w8 w16 w24).extractLsb' 0 64) ∗
      ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 ((v9_midQ128 w8 w16 w24).extractLsb' 64 64)) ∗
      ((out + 160#64) ↦₆₄
        overlapWord7 ((v9_midQ128 w8 w16 w24).extractLsb' 64 64) (w24 >>> 8)) =
    ((out + 144#64) ↦₆₄ w8) ∗ ((out + 152#64) ↦₆₄ w16) ∗ ((out + 160#64) ↦₆₄ w24) := by
  rw [v9_zext32_setWidth8 (EncoderFromPb.loByte w8)]
  have hlo : (v9_midQ128 w8 w16 w24).extractLsb' 0 64 =
      EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16) := by
    unfold v9_midQ128; bv_kernel
  have hhi : (v9_midQ128 w8 w16 w24).extractLsb' 64 64 =
      EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24) := by
    unfold v9_midQ128; bv_kernel
  rw [hlo, hhi, v9_overlapWord7_unshift_lsr8 w16 w24]
  have hdst := v9_dst24_realign_final (out + 144#64) w8 w16 w24
  have hd145 : (out + 144#64) + 1#64 = out + 145#64 := by bv_omega
  have hd153 : (out + 144#64) + 9#64 = out + 153#64 := by bv_omega
  have hd160 : (out + 144#64) + 16#64 = out + 160#64 := by bv_omega
  have hd152 : (out + 144#64) + 8#64 = out + 152#64 := by bv_omega
  rw [hd145, hd153, hd160, hd152] at hdst
  exact hdst

def v9_outDecTail (out : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ((out + 168#64) ↦₁₂₈ v9_quadAt bs 32) ∗ ((out + 184#64) ↦₁₂₈ v9_quadAt bs 48) ∗
  ((out + 200#64) ↦₁₂₈ v9_quadAt bs 64) ∗ ((out + 216#64) ↦₁₂₈ v9_quadAt bs 80) ∗
  ((out + 232#64) ↦₁₂₈ v9_quadAt bs 96) ∗ ((out + 248#64) ↦₁₂₈ v9_quadAt bs 112) ∗
  ((out + 264#64) ↦₁₂₈ v9_quadAt bs 128) ∗ ((out + 280#64) ↦₁₂₈ v9_quadAt bs 144) ∗
  ((out + 296#64) ↦₁₂₈ v9_quadAt bs 160) ∗ ((out + 312#64) ↦₁₂₈ v9_quadAt bs 176) ∗
  ((out + 328#64) ↦₁₂₈ v9_quadAt bs 192) ∗ ((out + 344#64) ↦₁₂₈ v9_quadAt bs 208) ∗
  ((out + 360#64) ↦₁₂₈ v9_quadAt bs 224) ∗ ((out + 376#64) ↦₁₂₈ v9_quadAt bs 240) ∗
  ((out + 392#64) ↦₆₄ v9_wordAt bs 256) ∗ ((out + 400#64) ↦₆₄ v9_wordAt bs 264) ∗
  ((out + 408#64) ↦₆₄ v9_wordAt bs 272) ∗ ((out + 416#64) ↦₆₄ v9_wordAt bs 280) ∗
  ((out + 424#64) ↦₆₄ v9_wordAt bs 288) ∗ ((out + 432#64) ↦₆₄ v9_wordAt bs 296) ∗
  ((out + 440#64) ↦₆₄ v9_wordAt bs 304) ∗ ((out + 448#64) ↦₆₄ v9_wordAt bs 312) ∗
  ((out + 456#64) ↦₆₄ v9_wordAt bs 320) ∗ ((out + 464#64) ↦₆₄ v9_wordAt bs 328) ∗
  ((out + 472#64) ↦₆₄ v9_wordAt bs 336) ∗ ((out + 480#64) ↦₆₄ v9_wordAt bs 344) ∗
  ((out + 488#64) ↦₆₄ v9_wordAt bs 352) ∗ ((out + 496#64) ↦₆₄ v9_wordAt bs 360) ∗
  ((out + 504#64) ↦₆₄ v9_wordAt bs 368) ∗ ((out + 512#64) ↦₆₄ v9_wordAt bs 376)

theorem v9_outDecTail_eq (out : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) :
    ((out + 168#64) ↦₁₂₈ v9_quadAt bs 32) ∗ ((out + 184#64) ↦₁₂₈ v9_quadAt bs 48) ∗
      ((out + 200#64) ↦₁₂₈ v9_quadAt bs 64) ∗ ((out + 216#64) ↦₁₂₈ v9_quadAt bs 80) ∗
      ((out + 232#64) ↦₁₂₈ v9_quadAt bs 96) ∗ ((out + 248#64) ↦₁₂₈ v9_quadAt bs 112) ∗
      ((out + 264#64) ↦₁₂₈ v9_quadAt bs 128) ∗ ((out + 280#64) ↦₁₂₈ v9_quadAt bs 144) ∗
      ((out + 296#64) ↦₁₂₈ v9_quadAt bs 160) ∗ ((out + 312#64) ↦₁₂₈ v9_quadAt bs 176) ∗
      ((out + 328#64) ↦₁₂₈ v9_quadAt bs 192) ∗ ((out + 344#64) ↦₁₂₈ v9_quadAt bs 208) ∗
      ((out + 360#64) ↦₁₂₈ v9_quadAt bs 224) ∗ ((out + 376#64) ↦₁₂₈ v9_quadAt bs 240) ∗
      ((out + 392#64) ↦₆₄ v9_wordAt bs 256) ∗ ((out + 400#64) ↦₆₄ v9_wordAt bs 264) ∗
      ((out + 408#64) ↦₆₄ v9_wordAt bs 272) ∗ ((out + 416#64) ↦₆₄ v9_wordAt bs 280) ∗
      ((out + 424#64) ↦₆₄ v9_wordAt bs 288) ∗ ((out + 432#64) ↦₆₄ v9_wordAt bs 296) ∗
      ((out + 440#64) ↦₆₄ v9_wordAt bs 304) ∗ ((out + 448#64) ↦₆₄ v9_wordAt bs 312) ∗
      ((out + 456#64) ↦₆₄ v9_wordAt bs 320) ∗ ((out + 464#64) ↦₆₄ v9_wordAt bs 328) ∗
      ((out + 472#64) ↦₆₄ v9_wordAt bs 336) ∗ ((out + 480#64) ↦₆₄ v9_wordAt bs 344) ∗
      ((out + 488#64) ↦₆₄ v9_wordAt bs 352) ∗ ((out + 496#64) ↦₆₄ v9_wordAt bs 360) ∗
      ((out + 504#64) ↦₆₄ v9_wordAt bs 368) ∗ ((out + 512#64) ↦₆₄ v9_wordAt bs 376) ∗ Rest =
    v9_outDecTail out bs ∗ Rest := by
  unfold v9_outDecTail; simp only [sepConj_assoc]

theorem v9_out_136_to_520_eq_bs (out : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384) :
    ((out + 136#64) ↦₆₄ v9_wordAt bs 0) ∗
      (((out + 144#64) ↦₈ ((EncoderFromPb.loByte (v9_wordAt bs 8)).zeroExtend 32).setWidth 8) ∗
       ((out + 145#64) ↦₆₄
         (v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
         ((v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)).extractLsb' 64 64)) ∗
       ((out + 160#64) ↦₆₄
         overlapWord7
           ((v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)).extractLsb' 64 64)
           (v9_wordAt bs 24 >>> 8))) ∗
      v9_outDecTail out bs =
    (out + 136#64) ↦ₛ bs := by
  unfold v9_outDecTail
  rw [v9_out_144_realign out (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24),
      v9_bs384_eq_decCells bs hbs (out + 136#64)]
  unfold v9_decCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem v9_epilogueOutFull_entails_ct1Acknowledged (A : RustAlloc) {F : ShaCompress}
    (out rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (w392 : BitVec 64) (dec : PolyDecoder) (P_heap : SepProp)
    (hreloc :
      ((out + 136#64) ↦ₛ bs) ∗ (((out + 136#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        (((out + 136#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢ polyDecoderAt A (out + 136#64) dec)
    (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    epilogueOutFull out
      11#64 rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr
      (esLen.extractLsb' 0 8) (esLen.extractLsb' 8 32)
      (esLen.extractLsb' 40 16) (esLen.extractLsb' 56 8)
      ct1Cap ct1Ptr (EncoderFromPb.loByte ct1Len)
      (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))
      (overlapWord7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) (uc.epoch >>> 8))
      (v9_wordAt bs 0) (((EncoderFromPb.loByte (v9_wordAt bs 8)).zeroExtend 32).setWidth 8)
      (v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24))
      (overlapWord7
        ((v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)).extractLsb' 64 64)
        (v9_wordAt bs 24 >>> 8))
      (v9_quadAt bs 32) (v9_quadAt bs 48) (v9_quadAt bs 64) (v9_quadAt bs 80)
      (v9_quadAt bs 96) (v9_quadAt bs 112) (v9_quadAt bs 128) (v9_quadAt bs 144)
      (v9_quadAt bs 160) (v9_quadAt bs 176) (v9_quadAt bs 192) (v9_quadAt bs 208)
      (v9_quadAt bs 224) (v9_quadAt bs 240)
      (v9_wordAt bs 256) (v9_wordAt bs 264) (v9_wordAt bs 272) (v9_wordAt bs 280)
      (v9_wordAt bs 288) (v9_wordAt bs 296) (v9_wordAt bs 304) (v9_wordAt bs 312)
      (v9_wordAt bs 320) (v9_wordAt bs 328) (v9_wordAt bs 336) (v9_wordAt bs 344)
      (v9_wordAt bs 352) (v9_wordAt bs 360) (v9_wordAt bs 368) (v9_wordAt bs 376)
      (BitVec.ofNat 64 dec.ptsNeeded) w392 b536 q537 w552 bs240 q888 q904 w920 ∗
      v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
      P_heap ⊢
    resultChunkedStatesAt A (F := F) out (.ok (.ct1Acknowledged { uc := uc, receiving_ek := dec })) := by
  dsimp only [resultChunkedStatesAt, chunkedStatesAt, chunkedCt1AcknowledgedAt]
  have ha136 : (out + 8#64) + 128#64 = out + 136#64 := by bv_omega
  have ha520 : (out + 136#64) + 384#64 = out + 520#64 := by bv_omega
  have ha528 : (out + 136#64) + 392#64 = out + 528#64 := by bv_omega
  rw [ha136, sepConj_assoc (unchunkedCt1SentAt A (out + 8#64) uc)]
  rw [ha520, ha528] at hreloc
  unfold epilogueOutFull
  have hbs_eq := v9_out_136_to_520_eq_bs out bs hbs
  have huc := v9_ct1SentAt_pack A (F := F) (out + 8#64)
    rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
  dsimp only [v9_optProtoUcWordsAt] at huc
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at huc
  have htail := epilogueOut_tail_536_entails_392 out b536 q537 w552 bs240 hbs240 q888 q904 w920
  rw [v9_outDecTail_eq out bs]
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 11#64) ∗
    (((out + 8#64) ↦₆₄ rkCap) ∗ ((out + 16#64) ↦₆₄ rkPtr) ∗ ((out + 24#64) ↦₆₄ rkLen) ∗
     ((out + 32#64) ↦₆₄ mkCap) ∗ ((out + 40#64) ↦₆₄ mkPtr) ∗ ((out + 48#64) ↦₆₄ mkLen) ∗
     ((out + 56#64) ↦₆₄ hdrCap) ∗ ((out + 64#64) ↦₆₄ hdrPtr) ∗ ((out + 72#64) ↦₆₄ hdrLen) ∗
     ((out + 80#64) ↦₆₄ esCap) ∗ ((out + 88#64) ↦₆₄ esPtr) ∗
     (((out + 96#64) ↦₈ esLen.extractLsb' 0 8) ∗ ((out + 97#64) ↦₃₂ esLen.extractLsb' 8 32) ∗
      ((out + 101#64) ↦₁₆ esLen.extractLsb' 40 16) ∗ ((out + 103#64) ↦₈ esLen.extractLsb' 56 8)) ∗
     ((out + 104#64) ↦₆₄ ct1Cap) ∗ ((out + 112#64) ↦₆₄ ct1Ptr) ∗
     (((out + 120#64) ↦₈ EncoderFromPb.loByte ct1Len) ∗
      ((out + 121#64) ↦₆₄ EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) ∗
      ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) (uc.epoch >>> 8)))) ∗
     v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc) ∗
    ((((out + 136#64) ↦₆₄ v9_wordAt bs 0) ∗
      (((out + 144#64) ↦₈ ((EncoderFromPb.loByte (v9_wordAt bs 8)).zeroExtend 32).setWidth 8) ∗
       ((out + 145#64) ↦₆₄ (v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
         ((v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)).extractLsb' 64 64)) ∗
       ((out + 160#64) ↦₆₄
         overlapWord7
           ((v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)).extractLsb' 64 64)
           (v9_wordAt bs 24 >>> 8))) ∗
      v9_outDecTail out bs) ∗
     ((out + 520#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((out + 528#64) ↦₆₄ w392) ∗ P_heap) ∗
    (((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗
     ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗ ((out + 560#64) ↦ₛ bs240) ∗
     ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920)) by ac_rfl)) ?_
  rw [v9_out_96_realign out esLen, v9_out_120_realign out ct1Len uc.epoch, hbs_eq]
  have huc_align :
      ((out + 8#64) ↦₆₄ rkCap) ∗ ((out + 16#64) ↦₆₄ rkPtr) ∗ ((out + 24#64) ↦₆₄ rkLen) ∗
      ((out + 32#64) ↦₆₄ mkCap) ∗ ((out + 40#64) ↦₆₄ mkPtr) ∗ ((out + 48#64) ↦₆₄ mkLen) ∗
      ((out + 56#64) ↦₆₄ hdrCap) ∗ ((out + 64#64) ↦₆₄ hdrPtr) ∗ ((out + 72#64) ↦₆₄ hdrLen) ∗
      ((out + 80#64) ↦₆₄ esCap) ∗ ((out + 88#64) ↦₆₄ esPtr) ∗ ((out + 96#64) ↦₆₄ esLen) ∗
      ((out + 104#64) ↦₆₄ ct1Cap) ∗ ((out + 112#64) ↦₆₄ ct1Ptr) ∗
      (((out + 120#64) ↦₆₄ ct1Len) ∗ ((out + 128#64) ↦₆₄ uc.epoch)) ∗
      v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc =
      (((out + 8#64) ↦₆₄ rkCap) ∗ ((out + 16#64) ↦₆₄ rkPtr) ∗ ((out + 24#64) ↦₆₄ rkLen) ∗
       ((out + 32#64) ↦₆₄ mkCap) ∗ ((out + 40#64) ↦₆₄ mkPtr) ∗ ((out + 48#64) ↦₆₄ mkLen) ∗
       ((out + 56#64) ↦₆₄ hdrCap) ∗ ((out + 64#64) ↦₆₄ hdrPtr) ∗ ((out + 72#64) ↦₆₄ hdrLen) ∗
       ((out + 80#64) ↦₆₄ esCap) ∗ ((out + 88#64) ↦₆₄ esPtr) ∗ ((out + 96#64) ↦₆₄ esLen) ∗
       ((out + 104#64) ↦₆₄ ct1Cap) ∗ ((out + 112#64) ↦₆₄ ct1Ptr) ∗
       ((out + 120#64) ↦₆₄ ct1Len) ∗ ((out + 128#64) ↦₆₄ uc.epoch)) ∗
      v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc := by ac_rfl
  rw [huc_align]
  exact sepConj_mono_right (sepConj_mono huc (sepConj_mono hreloc htail))

/-! ## 3. Stepping Lemmas for `+2864 -> +6904 | +3040` and `+3044 -> +8588 | +8180` -/

theorem v9_hiBytes7_eq_loBytes7_lsr8 (w : BitVec 64) :
    EncoderFromPb.hiBytes7 w = EncoderFromPb.loBytes7 (w >>> 8) := by
  change [_, _, _, _, _, _, _] = [_, _, _, _, _, _, _]
  refine congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (_ :: ·)
    (congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (· :: []) ?_))))))
  all_goals bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v9_x25_add_209 (fsp : BitVec 64) : (fsp + 1792#64) + 209#64 = fsp + 2001#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v9_x25_add_209_sext (fsp : BitVec 64) : (fsp + 1792#64) + (209#64).signExtend 64 = fsp + 2001#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v9_pbA_add_145 (pbA : BitVec 64) : pbA + (145#64).signExtend 64 = pbA + 145#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v9_x21_add_57 (fsp : BitVec 64) : (fsp + 848#64) + 57#64 = fsp + 905#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v9_x21_add_57_sext (fsp : BitVec 64) : (fsp + 848#64) + (57#64).signExtend 64 = fsp + 905#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v9_x24_add_9 (fsp : BitVec 64) : (fsp + 1888#64) + 9#64 = fsp + 1897#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v9_x24_add_9_sext (fsp : BitVec 64) : (fsp + 1888#64) + (9#64).signExtend 64 = fsp + 1897#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v9_x21_add_15 (fsp : BitVec 64) : (fsp + 848#64) + 15#64 = fsp + 863#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v9_x21_add_15_sext (fsp : BitVec 64) : (fsp + 848#64) + (15#64).signExtend 64 = fsp + 863#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v9_x21_add_39 (fsp : BitVec 64) : (fsp + 848#64) + 39#64 = fsp + 887#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem v9_x21_add_39_sext (fsp : BitVec 64) : (fsp + 848#64) + (39#64).signExtend 64 = fsp + 887#64 := by bv_kernel
@[local simp, local arm64_norm, local wp_norm]
theorem v9_fsp_add_247_sext (fsp : BitVec 64) : fsp + (247#64).signExtend 64 = fsp + 247#64 := by bv_kernel

theorem v9_fsp_2000_realign_rest (fsp w112 w120 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2000#64) ↦₆₄ w112) ∗ ((fsp + 2008#64) ↦₆₄ w120) ∗ Rest =
      ((fsp + 2000#64) ↦₈ EncoderFromPb.loByte w112) ∗
      ((fsp + 2001#64) ↦₆₄ EncoderFromPb.unshiftWord w112 (EncoderFromPb.loByte w120)) ∗
      ((fsp + 2009#64) ↦ₛ EncoderFromPb.hiBytes7 w120) ∗ Rest := by
  have h := pair64_to_byte_word_tail7 (fsp + 2000#64) w112 w120
  have ha8 : (fsp + 2000#64) + 8#64 = fsp + 2008#64 := by bv_omega
  have ha1 : (fsp + 2000#64) + 1#64 = fsp + 2001#64 := by bv_omega
  have ha9 : (fsp + 2000#64) + 9#64 = fsp + 2009#64 := by bv_omega
  rw [ha8, ha1, ha9] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v9_fsp_2000_unrealign_rest (fsp w112 w120 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2000#64) ↦₈ EncoderFromPb.loByte w112) ∗
      ((fsp + 2001#64) ↦₆₄ EncoderFromPb.unshiftWord w112 (EncoderFromPb.loByte w120)) ∗
      ((fsp + 2009#64) ↦ₛ EncoderFromPb.hiBytes7 w120) ∗ Rest =
      ((fsp + 2000#64) ↦₆₄ w112) ∗ ((fsp + 2008#64) ↦₆₄ w120) ∗ Rest :=
  (v9_fsp_2000_realign_rest fsp w112 w120 Rest).symm

theorem v9_fsp_240_realign_64_rest (fsp w240 w248 : BitVec 64) (Rest : SepProp) :
    ((fsp + 240#64) ↦₆₄ w240) ∗ ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 w248) ∗ Rest =
      ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 w240) ∗
      ((fsp + 247#64) ↦₆₄ overlapWord7 w240 w248) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 240#64) w240 w248
  have ha7 : (fsp + 240#64) + 7#64 = fsp + 247#64 := by bv_omega
  have ha8 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_omega
  rw [ha7, ha8] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v9_fsp_240_realign_overlap_rest (fsp ct1Len ep : BitVec 64) (Rest : SepProp) :
    ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep))) ∗
      ((fsp + 247#64) ↦₆₄ ep) ∗ Rest =
    ((fsp + 240#64) ↦₆₄ EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep)) ∗
      ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 (ep >>> 8)) ∗ Rest := by
  have h := loBytes7_pointsTo64_eq_overlap (fsp + 240#64)
    (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep)) ep
  have ha7 : (fsp + 240#64) + 7#64 = fsp + 247#64 := by bv_omega
  have ha8 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_omega
  rw [ha7, ha8, v9_overlapLow7_unshift ct1Len ep, v9_hiBytes7_eq_loBytes7_lsr8 ep] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v9_memRegion_896_40_split (fsp : BitVec 64) :
    memRegion (fsp + 896#64) 40 ⊢
      (∃∗ z0 : BitVec 64, (fsp + 896#64) ↦₆₄ z0) ∗
      (∃∗ z8 : BitVec 64, (fsp + 904#64) ↦₆₄ z8) ∗
      (∃∗ z16 : BitVec 64, (fsp + 912#64) ↦₆₄ z16) ∗
      (∃∗ z24 : BitVec 64, (fsp + 920#64) ↦₆₄ z24) ∗
      (∃∗ z32 : BitVec 64, (fsp + 928#64) ↦₆₄ z32) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    mem64_entails _

theorem v9_fsp_904_triple_rest (fsp z8 z16 z24 : BitVec 64) (R : SepProp) :
    ((fsp + 904#64) ↦₆₄ z8) ∗ ((fsp + 912#64) ↦₆₄ z16) ∗ ((fsp + 920#64) ↦₆₄ z24) ∗ R =
      ((fsp + 904#64) ↦₈ EncoderFromPb.loByte z8) ∗
      ((fsp + 905#64) ↦₆₄ EncoderFromPb.unshiftWord z8 (EncoderFromPb.loByte z16)) ∗
      ((fsp + 913#64) ↦₆₄ EncoderFromPb.unshiftWord z16 (EncoderFromPb.loByte z24)) ∗
      ((fsp + 921#64) ↦ₛ EncoderFromPb.hiBytes7 z24) ∗ R := by
  have h := v9_triple64_eq_byte_q128_tail7 (fsp + 904#64) z8 z16 z24
  rw [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128 ((fsp + 904#64) + 1#64)
        (EncoderFromPb.unshiftWord z8 (EncoderFromPb.loByte z16))
        (EncoderFromPb.unshiftWord z16 (EncoderFromPb.loByte z24))] at h
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [show ((fsp + 904#64) ↦₆₄ z8) ∗ ((fsp + 912#64) ↦₆₄ z16) ∗ ((fsp + 920#64) ↦₆₄ z24) ∗ R =
        (((fsp + 904#64) ↦₆₄ z8) ∗ ((fsp + 912#64) ↦₆₄ z16) ∗ ((fsp + 920#64) ↦₆₄ z24)) ∗ R by ac_rfl,
      h]
  simp only [sepConj_assoc]

theorem v9_pointsTo32_pair_eq_pointsTo64 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes]
  change (a ↦ₛ unpack32 lo) ∗ ((a + BitVec.ofNat 64 (unpack32 lo).length) ↦ₛ unpack32 hi) = _
  rw [← ProofLib.pointsToBytes_append a (unpack32 lo) (unpack32 hi)]
  congr 1
  unfold unpack64 unpack32
  simp only [List.singleton_append, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
         by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem v9_pbA_144_triple_rest (pbA w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (R : SepProp) :
    ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗
      ((pbA + 160#64) ↦₃₂ d24) ∗ ((pbA + 164#64) ↦₃₂ d28) ∗ R =
      ((pbA + 144#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((pbA + 145#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
      ((pbA + 153#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte (d28 ++ d24))) ∗
      ((pbA + 161#64) ↦ₛ EncoderFromPb.hiBytes7 (d28 ++ d24)) ∗ R := by
  have hp32 := v9_pointsTo32_pair_eq_pointsTo64 (pbA + 160#64) d24 d28
  have ha164 : (pbA + 160#64) + 4#64 = pbA + 164#64 := by bv_omega
  rw [ha164] at hp32
  have h144 := v9_triple64_eq_byte_q128_tail7 (pbA + 144#64) w8 w16 (d28 ++ d24)
  rw [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128 ((pbA + 144#64) + 1#64)
        (EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16))
        (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte (d28 ++ d24)))] at h144
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h144
  rw [show ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗
        ((pbA + 160#64) ↦₃₂ d24) ∗ ((pbA + 164#64) ↦₃₂ d28) ∗ R =
        (((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗
         (((pbA + 160#64) ↦₃₂ d24) ∗ ((pbA + 164#64) ↦₃₂ d28))) ∗ R by ac_rfl,
      hp32, h144]
  simp only [sepConj_assoc]

theorem v9_pbA_160_pair32_eq_64_rest (pbA : BitVec 64) (d24 d28 : BitVec 32) (R : SepProp) :
    ((pbA + 160#64) ↦₃₂ d24) ∗ ((pbA + 164#64) ↦₃₂ d28) ∗ R =
      ((pbA + 160#64) ↦₆₄ (d28 ++ d24)) ∗ R := by
  have hp32 := v9_pointsTo32_pair_eq_pointsTo64 (pbA + 160#64) d24 d28
  have ha164 : (pbA + 160#64) + 4#64 = pbA + 164#64 := by bv_omega
  rw [ha164] at hp32
  rw [← sepConj_assoc, hp32]

theorem v9_fsp_913_realign_rest (fsp u1 z24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 913#64) ↦₆₄ u1) ∗
      ((fsp + 921#64) ↦ₛ EncoderFromPb.hiBytes7 z24) ∗ Rest =
      ((fsp + 913#64) ↦ₛ EncoderFromPb.loBytes7 u1) ∗
      ((fsp + 920#64) ↦₆₄ overlapWord7 u1 (z24 >>> 8)) ∗ Rest := by
  have ha920 : (fsp + 913#64) + 7#64 = fsp + 920#64 := by bv_omega
  have ha921 : (fsp + 913#64) + 8#64 = fsp + 921#64 := by bv_omega
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 913#64) u1 (z24 >>> 8)
  rw [ha921, ha920, ← v9_hiBytes7_eq_loBytes7_lsr8 z24] at h
  rw [← sepConj_assoc ((fsp + 913#64) ↦₆₄ u1), h]
  simp only [sepConj_assoc]

theorem v9_fsp_1896_realign_rest (fsp w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1896#64) ↦₆₄ w8) ∗ ((fsp + 1904#64) ↦₆₄ w16) ∗ ((fsp + 1912#64) ↦₆₄ w24) ∗ Rest =
      ((fsp + 1896#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 1897#64) ↦₆₄ (v9_midQ128 w8 w16 w24).extractLsb' 0 64) ∗
      ((fsp + 1905#64) ↦₆₄ (v9_midQ128 w8 w16 w24).extractLsb' 64 64) ∗
      ((fsp + 1913#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗ Rest := by
  have h := v9_triple64_eq_byte_q128_tail7 (fsp + 1896#64) w8 w16 w24
  have ha8 : (fsp + 1896#64) + 8#64 = fsp + 1904#64 := by bv_omega
  have ha16 : (fsp + 1896#64) + 16#64 = fsp + 1912#64 := by bv_omega
  have ha1 : (fsp + 1896#64) + 1#64 = fsp + 1897#64 := by bv_omega
  have ha17 : (fsp + 1896#64) + 17#64 = fsp + 1913#64 := by bv_omega
  have ha1905 : (fsp + 1897#64) + 8#64 = fsp + 1905#64 := by bv_omega
  rw [ha8, ha16, ha1, ha17] at h
  change _ = ((fsp + 1896#64) ↦₈ EncoderFromPb.loByte w8) ∗
    ((fsp + 1897#64) ↦₁₂₈ v9_midQ128 w8 w16 w24) ∗
    ((fsp + 1913#64) ↦ₛ EncoderFromPb.hiBytes7 w24) at h
  unfold pointsTo128 at h
  rw [ha1905] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v9_fsp_1896_unrealign_rest (fsp w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1896#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 1897#64) ↦₆₄ (v9_midQ128 w8 w16 w24).extractLsb' 0 64) ∗
      ((fsp + 1905#64) ↦₆₄ (v9_midQ128 w8 w16 w24).extractLsb' 64 64) ∗
      ((fsp + 1913#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗ Rest =
    ((fsp + 1896#64) ↦₆₄ w8) ∗ ((fsp + 1904#64) ↦₆₄ w16) ∗ ((fsp + 1912#64) ↦₆₄ w24) ∗ Rest :=
  (v9_fsp_1896_realign_rest fsp w8 w16 w24 Rest).symm

theorem v9_fsp_1896_split_1_7_rest (fsp w8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1896#64) ↦₆₄ w8) ∗ Rest =
      ((fsp + 1896#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 1897#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 1896#64) w8
  have ha1 : (fsp + 1896#64) + 1#64 = fsp + 1897#64 := by bv_omega
  rw [ha1] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v9_fsp_1896_unsplit_1_7_rest (fsp w8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1896#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 1897#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗ Rest =
      ((fsp + 1896#64) ↦₆₄ w8) ∗ Rest :=
  (v9_fsp_1896_split_1_7_rest fsp w8 Rest).symm

theorem v9_fsp_856_realign_rest (fsp w856 u864 : BitVec 64) (Rest : SepProp) :
    ((fsp + 856#64) ↦₆₄ w856) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864) ∗ Rest =
      ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 w856) ∗
      ((fsp + 863#64) ↦₆₄ overlapWord7 w856 u864) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 856#64) w856 u864
  have ha8 : (fsp + 856#64) + 8#64 = fsp + 864#64 := by bv_omega
  have ha7 : (fsp + 856#64) + 7#64 = fsp + 863#64 := by bv_omega
  rw [ha8, ha7] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v9_fsp_856_unrealign_midQ128_rest (fsp w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 ((v9_midQ128 w8 w16 w24).extractLsb' 64 64)) ∗
      ((fsp + 863#64) ↦₆₄ w24) ∗ Rest =
    ((fsp + 856#64) ↦₆₄ (v9_midQ128 w8 w16 w24).extractLsb' 64 64) ∗
      ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (w24 >>> 8)) ∗ Rest := by
  have h := (v9_fsp_856_realign_rest fsp ((v9_midQ128 w8 w16 w24).extractLsb' 64 64)
    (w24 >>> 8) Rest).symm
  rwa [v9_overlapWord7_midQ128_lsr8 w8 w16 w24] at h

theorem v9_fsp_880_realign_64_rest (fsp w880 w888 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗ Rest =
      ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
      ((fsp + 887#64) ↦₆₄ overlapWord7 w880 w888) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 880#64) w880 w888
  have ha7 : (fsp + 880#64) + 7#64 = fsp + 887#64 := by bv_omega
  have ha8 : (fsp + 880#64) + 8#64 = fsp + 888#64 := by bv_omega
  rw [ha7, ha8] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v9_fsp_880_realign_rest (fsp u880 w112 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880) ∗ ((fsp + 887#64) ↦₆₄ w112) ∗ Rest =
      ((fsp + 880#64) ↦₆₄ overlapLow7 u880 w112) ∗
      ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (w112 >>> 8)) ∗ Rest := by
  have h := loBytes7_pointsTo64_eq_overlap (fsp + 880#64) u880 w112
  have ha7 : (fsp + 880#64) + 7#64 = fsp + 887#64 := by bv_omega
  have ha8 : (fsp + 880#64) + 8#64 = fsp + 888#64 := by bv_omega
  rw [ha7, ha8, v9_hiBytes7_eq_loBytes7_lsr8 w112] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v9_fsp_1888_entails_epilogue (fsp w2272 w2280 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) :
    v9_decCellsAt (fsp + 1888#64) bs ∗
      ((fsp + 2272#64) ↦₆₄ w2272) ∗
      ((fsp + 2280#64) ↦₆₄ w2280) ∗
      memRegion (fsp + 2288#64) 16 ⊢
    ((fsp + 1888#64) ↦₁₂₈ (v9_wordAt bs 8 ++ v9_wordAt bs 0)) ∗
      ((fsp + 1904#64) ↦₁₂₈ (v9_wordAt bs 24 ++ v9_wordAt bs 16)) ∗
      ((fsp + 1920#64) ↦₆₄ v9_wordAt bs 32) ∗
      memRegion (fsp + 1928#64) 376 := by
  rw [← v9_bs384_eq_decCells bs hbs (fsp + 1888#64)]
  have hbs_split : ((fsp + 1888#64) ↦ₛ bs) =
      ((fsp + 1888#64) ↦₆₄ v9_wordAt bs 0) ∗
      ((fsp + 1896#64) ↦₆₄ v9_wordAt bs 8) ∗
      ((fsp + 1904#64) ↦₆₄ v9_wordAt bs 16) ∗
      ((fsp + 1912#64) ↦₆₄ v9_wordAt bs 24) ∗
      ((fsp + 1920#64) ↦₆₄ v9_wordAt bs 32) ∗
      ((fsp + 1928#64) ↦ₛ bs.drop 40) := by
    have h :=
      v9_bs_drop_step8 hbs (fsp + 1888#64) 0#64 8#64 0 <|
      v9_bs_drop_step8 hbs (fsp + 1888#64) 8#64 16#64 8 <|
      v9_bs_drop_step8 hbs (fsp + 1888#64) 16#64 24#64 16 <|
      v9_bs_drop_step8 hbs (fsp + 1888#64) 24#64 32#64 24 <|
      v9_bs_drop_step8 hbs (fsp + 1888#64) 32#64 40#64 32 rfl
    change (((fsp + 1888#64) + 0#64) ↦ₛ bs) = _ at h
    simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd, sepConj_assoc] at h
    exact h
  rw [hbs_split]
  have hq1888 : ((fsp + 1888#64) ↦₆₄ v9_wordAt bs 0) ∗ ((fsp + 1896#64) ↦₆₄ v9_wordAt bs 8) =
      ((fsp + 1888#64) ↦₁₂₈ (v9_wordAt bs 8 ++ v9_wordAt bs 0)) := by
    have ha : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
    rw [← ha, EncoderFromPb.pointsTo64_pair_eq_pointsTo128]
  have hq1904 : ((fsp + 1904#64) ↦₆₄ v9_wordAt bs 16) ∗ ((fsp + 1912#64) ↦₆₄ v9_wordAt bs 24) =
      ((fsp + 1904#64) ↦₁₂₈ (v9_wordAt bs 24 ++ v9_wordAt bs 16)) := by
    have ha : (fsp + 1904#64) + 8#64 = fsp + 1912#64 := by bv_omega
    rw [← ha, EncoderFromPb.pointsTo64_pair_eq_pointsTo128]
  have hlen344 : (bs.drop 40).length = 344 := by rw [List.length_drop, hbs]
  have hm344 : ((fsp + 1928#64) ↦ₛ bs.drop 40) ⊢ memRegion (fsp + 1928#64) 344 :=
    hlen344 ▸ ProofLib.pointsToBytes_entails_memRegion (fsp + 1928#64) (bs.drop 40)
  have hm376 : ((fsp + 1928#64) ↦ₛ bs.drop 40) ∗
      ((fsp + 2272#64) ↦₆₄ w2272) ∗
      ((fsp + 2280#64) ↦₆₄ w2280) ∗ memRegion (fsp + 2288#64) 16 ⊢
      memRegion (fsp + 1928#64) 376 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1928#64) (n := 344) (k := 32)
          (b' := fsp + 2272#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 2272#64) (n := 8) (k := 24)
          (b' := fsp + 2280#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 2280#64) (n := 8) (k := 16)
          (b' := fsp + 2288#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono hm344
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 2272#64) w2272)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 2280#64) w2280)))
  refine Entails.trans (Entails.of_eq (show _ =
    (((fsp + 1888#64) ↦₆₄ v9_wordAt bs 0) ∗ ((fsp + 1896#64) ↦₆₄ v9_wordAt bs 8)) ∗
    (((fsp + 1904#64) ↦₆₄ v9_wordAt bs 16) ∗ ((fsp + 1912#64) ↦₆₄ v9_wordAt bs 24)) ∗
    ((fsp + 1920#64) ↦₆₄ v9_wordAt bs 32) ∗
    (((fsp + 1928#64) ↦ₛ bs.drop 40) ∗ ((fsp + 2272#64) ↦₆₄ w2272) ∗
     ((fsp + 2280#64) ↦₆₄ w2280) ∗ memRegion (fsp + 2288#64) 16) by ac_rfl)) ?_
  rw [hq1888, hq1904]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm376))

/-- At `+2864`, when `ct1SentFromPb` returned `Ok(uc)` (`rkCap.toNat < 2 ^ 63`) and
    `receivingEk = none` (`x21 = noneCap`), spills `hdr`, `es`, `ct1Len`, and `uc.epoch`
    and branches at `+2968` (`b.eq +6904`) to `+6904`. -/
theorem v9_step_2864_ok_none_to_6904
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep : BitVec 64)
    (w72 w128 w144 w152 w240 w248 : BitVec 64) (d96 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hrk_lt : rkCap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2864#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = noneCap) (hx25 : s.readReg64 .x25 = fsp + 1792#64) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6904#64) s
      (((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗ ((fsp + 128#64) ↦₆₄ w128) ∗
        ((fsp + 144#64) ↦₆₄ w144) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
        ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 w248) ∗
        v9_optProtoUcWordsAt (fsp + 1888#64)
          rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep ∗
        Rest)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap) ∗
          ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep))) ∗
          ((fsp + 247#64) ↦₆₄ ep) ∗ memRegion (fsp + 1888#64) 128 ∗ Rest) ∧
        s1.sp = fsp ∧ s1.readReg64 .x0 = mkPtr ∧ s1.readReg64 .x1 = mkCap ∧
        s1.readReg64 .x10 = rkCap ∧ s1.readReg64 .x13 = ct1Cap ∧ s1.readReg64 .x14 = ct1Ptr ∧
        s1.readReg64 .x19 = out ∧ s1.readReg64 .x28 = rkPtr ∧ TraceCalleeSaved s1 s0) := by
  subst hsp
  have hrk_ne : (rkCap + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hrk_lt)
  dsimp only [v9_optProtoUcWordsAt, noneCap] at hx21 ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 2864 108
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  iterate 21 wp_step
  wp_conv_pre => rw [v9_fsp_2000_realign_rest s.sp ct1Len ep]
  wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v9_fsp_240_realign_64_rest s.sp (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep)) w248,
        v9_fsp_2000_unrealign_rest s.sp ct1Len ep]
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hm1888 := v9_optProtoUcWordsAt_entails_128 (s.sp + 1888#64)
      rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep
    dsimp only [v9_optProtoUcWordsAt] at hm1888
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm1888
    refine Entails.trans (Entails.of_eq (show _ =
      ((s.sp + 72#64) ↦₆₄ esPtr) ∗ ((s.sp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
      ((s.sp + 128#64) ↦₆₄ esCap) ∗ ((s.sp + 144#64) ↦₆₄ hdrPtr) ∗ ((s.sp + 152#64) ↦₆₄ hdrCap) ∗
      ((s.sp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep))) ∗
      ((s.sp + 247#64) ↦₆₄ ep) ∗
      (((s.sp + 1888#64) ↦₆₄ rkCap) ∗ ((s.sp + 1896#64) ↦₆₄ rkPtr) ∗ ((s.sp + 1904#64) ↦₆₄ rkLen) ∗
       ((s.sp + 1912#64) ↦₆₄ mkCap) ∗ ((s.sp + 1920#64) ↦₆₄ mkPtr) ∗ ((s.sp + 1928#64) ↦₆₄ mkLen) ∗
       ((s.sp + 1936#64) ↦₆₄ hdrCap) ∗ ((s.sp + 1944#64) ↦₆₄ hdrPtr) ∗ ((s.sp + 1952#64) ↦₆₄ hdrLen) ∗
       ((s.sp + 1960#64) ↦₆₄ esCap) ∗ ((s.sp + 1968#64) ↦₆₄ esPtr) ∗ ((s.sp + 1976#64) ↦₆₄ esLen) ∗
       ((s.sp + 1984#64) ↦₆₄ ct1Cap) ∗ ((s.sp + 1992#64) ↦₆₄ ct1Ptr) ∗ ((s.sp + 2000#64) ↦₆₄ ct1Len) ∗
       ((s.sp + 2008#64) ↦₆₄ ep)) ∗ Rest by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hm1888)))))))
  · wp_done

theorem v9_fsp_6904_entails_2304 (fsp esPtr esCap hdrPtr hdrCap : BitVec 64) :
    memRegion fsp 72 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ memRegion (fsp + 80#64) 48 ∗
      ((fsp + 128#64) ↦₆₄ esCap) ∗ memRegion (fsp + 136#64) 8 ∗
      ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap) ∗
      memRegion (fsp + 160#64) 2144 ⊢ memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _

theorem v9_fsp_8588_entails_2304
    (fsp ct1Cap rkCap esPtr esCap mkPtr hdrPtr hdrCap ct1Ptr mkCap : BitVec 64) :
    memRegion fsp 48 ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
      memRegion (fsp + 64#64) 8 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ memRegion (fsp + 80#64) 48 ∗
      ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗
      ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap) ∗
      memRegion (fsp + 160#64) 40 ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗
      memRegion (fsp + 208#64) 8 ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
      memRegion (fsp + 224#64) 2080 ⊢ memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _

theorem v9_memRegion_3044_split_ok (fsp : BitVec 64) :
    memRegion (fsp + 88#64) 8 ∗ memRegion (fsp + 100#64) 28 ∗
      memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
      memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ⊢
      (memRegion (fsp + 88#64) 4 ∗ (∃∗ d92 : BitVec 32, ((fsp + 92#64) ↦₃₂ d92))) ∗
      (memRegion (fsp + 100#64) 4 ∗
       (∃∗ w104 : BitVec 64, ((fsp + 104#64) ↦₆₄ w104)) ∗
       (∃∗ w112 : BitVec 64, ((fsp + 112#64) ↦₆₄ w112)) ∗
       (∃∗ w120 : BitVec 64, ((fsp + 120#64) ↦₆₄ w120))) ∗
      ((∃∗ w160 : BitVec 64, ((fsp + 160#64) ↦₆₄ w160)) ∗ memRegion (fsp + 168#64) 4 ∗
       (∃∗ d172 : BitVec 32, ((fsp + 172#64) ↦₃₂ d172)) ∗ memRegion (fsp + 176#64) 16 ∗
       (∃∗ w192 : BitVec 64, ((fsp + 192#64) ↦₆₄ w192))) ∗
      (∃∗ w208 : BitVec 64, ((fsp + 208#64) ↦₆₄ w208)) ∗
      ((∃∗ w224 : BitVec 64, ((fsp + 224#64) ↦₆₄ w224)) ∗
       (∃∗ w232 : BitVec 64, ((fsp + 232#64) ↦₆₄ w232))) ∗
      (memRegion (fsp + 255#64) 313 ∗ memRegion (fsp + 568#64) 8 ∗
       (∃∗ q576 : BitVec 128, ((fsp + 576#64) ↦₁₂₈ q576)) ∗
       ((∃∗ w592 : BitVec 64, ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗ memRegion (fsp + 599#64) 9) ∗
       (∃∗ q608 : BitVec 128, ((fsp + 608#64) ↦₁₂₈ q608)) ∗ (∃∗ q624 : BitVec 128, ((fsp + 624#64) ↦₁₂₈ q624)) ∗
       (∃∗ q640 : BitVec 128, ((fsp + 640#64) ↦₁₂₈ q640)) ∗ (∃∗ q656 : BitVec 128, ((fsp + 656#64) ↦₁₂₈ q656)) ∗
       (∃∗ q672 : BitVec 128, ((fsp + 672#64) ↦₁₂₈ q672)) ∗ (∃∗ q688 : BitVec 128, ((fsp + 688#64) ↦₁₂₈ q688)) ∗
       (∃∗ q704 : BitVec 128, ((fsp + 704#64) ↦₁₂₈ q704)) ∗ (∃∗ q720 : BitVec 128, ((fsp + 720#64) ↦₁₂₈ q720)) ∗
       (∃∗ q736 : BitVec 128, ((fsp + 736#64) ↦₁₂₈ q736)) ∗ (∃∗ q752 : BitVec 128, ((fsp + 752#64) ↦₁₂₈ q752)) ∗
       (∃∗ q768 : BitVec 128, ((fsp + 768#64) ↦₁₂₈ q768)) ∗ (∃∗ q784 : BitVec 128, ((fsp + 784#64) ↦₁₂₈ q784)) ∗
       (∃∗ q800 : BitVec 128, ((fsp + 800#64) ↦₁₂₈ q800)) ∗ (∃∗ q816 : BitVec 128, ((fsp + 816#64) ↦₁₂₈ q816)) ∗
       (∃∗ w832 : BitVec 64, ((fsp + 832#64) ↦₆₄ w832)) ∗ memRegion (fsp + 840#64) 8 ∗
       (∃∗ q848 : BitVec 128, ((fsp + 848#64) ↦₁₂₈ q848)) ∗
       ((∃∗ w864 : BitVec 64, ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864)) ∗ memRegion (fsp + 871#64) 9) ∗
       (∃∗ w880 : BitVec 64, ((fsp + 880#64) ↦₆₄ w880)) ∗
       ((∃∗ w888 : BitVec 64, ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888)) ∗ memRegion (fsp + 895#64) 1)) := by
  refine sepConj_mono ?_ (sepConj_mono ?_ (sepConj_mono ?_ (sepConj_mono (mem64_entails _)
    (sepConj_mono ?_ (v9_memRegion_255_641_split_ok fsp)))))
  · exact split_top <| split_step (Entails.refl _) <| mem32_entails _
  · exact split_top <| split_step (Entails.refl _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| mem64_entails _
  · exact split_top <| split_step (mem64_entails _) <| split_step (Entails.refl _) <|
      split_step (mem32_entails _) <| split_step (Entails.refl _) <| mem64_entails _
  · exact split_top <| split_step (mem64_entails _) <| mem64_entails _

theorem v9_fsp_8180_gaps_collapse
    (fsp mkLen ct1Cap rkCap esPtr hdrLen esCap mkPtr hdrPtr hdrCap ct1Ptr mkCap : BitVec 64)
    (d96 : BitVec 32) :
    (memRegion fsp 40 ∗ ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗
     ((fsp + 56#64) ↦₆₄ rkCap) ∗ memRegion (fsp + 64#64) 8 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
     ((fsp + 80#64) ↦₆₄ hdrLen) ∗ memRegion (fsp + 88#64) 4) ∗
    (((fsp + 96#64) ↦₃₂ d96) ∗ memRegion (fsp + 100#64) 4) ∗
    (((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗
     ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap)) ∗
    ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
    (memRegion (fsp + 895#64) 1 ∗ memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952) ⊢
    memRegion fsp 92 ∗ memRegion (fsp + 96#64) 8 ∗ memRegion (fsp + 128#64) 32 ∗
      memRegion (fsp + 200#64) 8 ∗ memRegion (fsp + 216#64) 8 ∗ memRegion (fsp + 895#64) 993 := by
  refine sepConj_mono ?_ (sepConj_mono ?_ (sepConj_mono ?_
    (sepConj_mono (Drop.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Drop.pointsTo64_entails_memRegion _ _) ?_))))
  · exact collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  · exact collapse_top <| collapse_step (pointsTo32_entails_memRegion_4 _ _) <| Entails.refl _
  · exact collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Drop.pointsTo64_entails_memRegion _ _
  · exact collapse_top <| collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <| Entails.refl _

theorem v9_ct1SentHeap_rkCap_lt (A : RustAlloc) {F : ShaCompress}
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ⊢
      ⌜rkCap.toNat < 2 ^ 63⌝ ∗
        v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc := by
  unfold v9_ct1SentHeap v9_vecU8Heap vecU8Payload
  rw [sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; intro hlen
  apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
  exact Entails.pure_right hlt (Entails.pure_right hlen (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _)))

theorem v9_fsp_2864_none_collapse (fsp w240 ep : BitVec 64) (d96 : BitVec 32) :
    (memRegion (fsp + 80#64) 16 ∗ ((fsp + 96#64) ↦₃₂ d96) ∗ memRegion (fsp + 100#64) 28) ∗
      (memRegion (fsp + 160#64) 80 ∗ ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 w240) ∗
       ((fsp + 247#64) ↦₆₄ ep) ∗ memRegion (fsp + 255#64) 1633 ∗
       memRegion (fsp + 1888#64) 128 ∗ memRegion (fsp + 2016#64) 288) ⊢
    memRegion (fsp + 80#64) 48 ∗ memRegion (fsp + 160#64) 2144 := by
  refine sepConj_mono ?_ ?_
  · exact collapse_top <| collapse_step (Entails.refl _) <|
      collapse_step (pointsTo32_entails_memRegion_4 _ _) <| Entails.refl _
  · exact collapse_top <| collapse_step (Entails.refl _) <|
      collapse_step (loBytes7_entails_memRegion_7 _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _

theorem v9_memRegion_1888_2016_eq_400_16 (fsp : BitVec 64) :
    memRegion (fsp + 1888#64) 128 ∗ memRegion (fsp + 2016#64) 288 =
      memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16 := by
  rw [← ProofLib.memRegion_split' (b := fsp + 1888#64) (n := 128) (k := 288) (b' := fsp + 2016#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1888#64) (n := 400) (k := 16) (b' := fsp + 2288#64)
        rfl (by bv_omega) (by decide)]

end CryptoVerification.SpqrV1.States.FromPb


