/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.GrowOneSpecs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderRepr
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParams
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlaced
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneSysrootExt
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Shared Infrastructure & Contracts for `PolynomialDecoder::merge` and `PolynomialEncoder::merge`

Provides `Vec<Vec<u8>>` buffer and `<RawVec<Vec<u8>>>::grow_one` separation-logic bridges,
160-byte stack-frame splitting (`polyMergeStack = 160 + skipField3Stack 97`), Hoare contracts
(`polyDecoderMergeSpec`, `polyEncoderMergeSpec`), pure `mergeField` / `mergeMessage` length-bound
lemmas, and shared exit/skip lemmas for `PolynomialDecoder::merge` (`0x4e10c`, Block `296`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[simp, arm64_norm]
theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[simp, arm64_norm]
theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

@[simp, arm64_norm]
theorem bv64_add24_add8 (a : BitVec 64) : a + 24#64 + 8#64 = a + 32#64 := by bv_omega

@[simp, arm64_norm]
theorem bv64_add24_add16 (a : BitVec 64) : a + 24#64 + 16#64 = a + 40#64 := by bv_omega

/-! ## 1. `Vec<Vec<u8>>` Buffer & `grow_one` Bridge Lemmas -/

/-- The 24 little-endian bytes of a `Vec<u8>` header `{cap, ptr, len}`. -/
def vecU8ElemBytes (pin : VecPin) (bs : List (BitVec 8)) : List (BitVec 8) :=
  unpack64 pin.cap ++ unpack64 pin.ptr ++ unpack64 (BitVec.ofNat 64 bs.length)

@[simp]
theorem vecU8ElemBytes_length (pin : VecPin) (bs : List (BitVec 8)) :
    (vecU8ElemBytes pin bs).length = 24 := by
  simp [vecU8ElemBytes]

theorem vecHeader_eq_pointsToBytes_elem (v : BitVec 64) (pin : VecPin) (bs : List (BitVec 8)) :
    vecHeader v pin.cap pin.ptr (BitVec.ofNat 64 bs.length) = (v ↦ₛ vecU8ElemBytes pin bs) := by
  unfold vecHeader vecU8ElemBytes
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack64_length]
  rw [← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
  have h16 : v + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = v + 16#64 := by bv_omega
  rw [h16]

/-- Detached heap buffer of a `Vec<u8>`. -/
def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_header_sep_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs = vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8At vecU8Buf; ac_rfl

/-- Concatenated 24-byte `Vec<u8>` headers for `pins` and `bss`. -/
def vecU8ArrayBytes : List VecPin → List (List (BitVec 8)) → List (BitVec 8)
  | pin :: pins, bs :: bss => vecU8ElemBytes pin bs ++ vecU8ArrayBytes pins bss
  | _, _ => []

theorem vecU8ArrayBytes_length {pins : List VecPin} {bss : List (List (BitVec 8))}
    (h : pins.length = bss.length) :
    (vecU8ArrayBytes pins bss).length = bss.length * 24 := by
  induction pins generalizing bss with
  | nil => cases bss <;> simp_all [vecU8ArrayBytes]
  | cons pin pins ih =>
    cases bss with
    | nil => simp at h
    | cons bs bss =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [vecU8ArrayBytes, List.length_append, vecU8ElemBytes_length, ih h, List.length_cons]; omega

/-- Detached heap buffers of a list of `Vec<u8>` elements. -/
def vecU8ArrayHeaps (A : RustAlloc) : List VecPin → List (List (BitVec 8)) → SepProp
  | pin :: pins, bs :: bss => vecU8Buf A pin.cap pin.ptr bs ∗ vecU8ArrayHeaps A pins bss
  | _, _ => emp

theorem arrayAt_vecU8_entails_bytes (A : RustAlloc) (base : BitVec 64) (bss : List (List (BitVec 8))) :
    arrayAt (fun bs addr => vecU8 A addr bs) 24 base bss ⊢
      ∃∗ pins : List VecPin, ⌜pins.length = bss.length⌝ ∗
        (base ↦ₛ vecU8ArrayBytes pins bss) ∗ vecU8ArrayHeaps A pins bss := by
  induction bss generalizing base with
  | nil =>
    simp only [arrayAt]; refine Entails.trans ?_ (Entails.sepExists_intro ([] : List VecPin))
    simp [vecU8ArrayBytes, vecU8ArrayHeaps, pointsToBytes_nil]; exact Entails.refl _
  | cons bs bss ih =>
    simp only [arrayAt]; unfold vecU8
    rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun cap => ?_
    rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun ptr => ?_
    rw [vecU8At_eq_header_sep_buf, vecHeader_eq_pointsToBytes_elem base ⟨cap, ptr⟩ bs]
    refine Entails.trans (sepConj_mono_right (ih (base + BitVec.ofNat 64 24))) ?_
    rw [sepExists_sepConj_right]; refine Entails.sepExists_elim fun pins => ?_
    have hpull :
        ((base ↦ₛ vecU8ElemBytes ⟨cap, ptr⟩ bs) ∗ vecU8Buf A cap ptr bs) ∗
          (⌜pins.length = bss.length⌝ ∗ ((base + BitVec.ofNat 64 24) ↦ₛ vecU8ArrayBytes pins bss) ∗ vecU8ArrayHeaps A pins bss) =
        ⌜pins.length = bss.length⌝ ∗
          (((base ↦ₛ vecU8ElemBytes ⟨cap, ptr⟩ bs) ∗ ((base + BitVec.ofNat 64 24) ↦ₛ vecU8ArrayBytes pins bss)) ∗
           (vecU8Buf A cap ptr bs ∗ vecU8ArrayHeaps A pins bss)) := by ac_rfl
    rw [hpull]; refine Entails.pure_left fun hlen => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro (⟨cap, ptr⟩ :: pins))
    have hlen' : (⟨cap, ptr⟩ :: pins).length = (bs :: bss).length := by simp [hlen]
    rw [pure_sepConj_of_true hlen']
    simp only [vecU8ArrayBytes, vecU8ArrayHeaps, pointsToBytes_append, vecU8ElemBytes_length]; exact Entails.refl _

theorem arrayAt_vecU8_of_bytes (A : RustAlloc) (base : BitVec 64)
    (pins : List VecPin) (bss : List (List (BitVec 8))) (hlen : pins.length = bss.length) :
    (base ↦ₛ vecU8ArrayBytes pins bss) ∗ vecU8ArrayHeaps A pins bss ⊢
      arrayAt (fun bs addr => vecU8 A addr bs) 24 base bss := by
  induction pins generalizing base bss with
  | nil =>
    cases bss with
    | nil => simp [vecU8ArrayBytes, vecU8ArrayHeaps, arrayAt, pointsToBytes_nil]; exact Entails.refl _
    | cons _ _ => simp at hlen
  | cons pin pins ih =>
    cases bss with
    | nil => simp at hlen
    | cons bs bss =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [vecU8ArrayBytes, vecU8ArrayHeaps, arrayAt, pointsToBytes_append, vecU8ElemBytes_length]
      rw [← vecHeader_eq_pointsToBytes_elem base pin bs]
      have hpull :
          (vecHeader base pin.cap pin.ptr (BitVec.ofNat 64 bs.length) ∗ ((base + BitVec.ofNat 64 24) ↦ₛ vecU8ArrayBytes pins bss)) ∗
            (vecU8Buf A pin.cap pin.ptr bs ∗ vecU8ArrayHeaps A pins bss) =
          (vecHeader base pin.cap pin.ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A pin.cap pin.ptr bs) ∗
            (((base + BitVec.ofNat 64 24) ↦ₛ vecU8ArrayBytes pins bss) ∗ vecU8ArrayHeaps A pins bss) := by ac_rfl
      rw [hpull, ← vecU8At_eq_header_sep_buf]
      have helem : vecU8At A base pin.cap pin.ptr bs ⊢ vecU8 A base bs := by
        unfold vecU8
        refine Entails.trans ?_ (Entails.sepExists_intro (P := fun cap => ∃∗ ptr, vecU8At A base cap ptr bs) pin.cap)
        exact Entails.sepExists_intro (P := fun ptr => vecU8At A base pin.cap ptr bs) pin.ptr
      exact sepConj_mono helem (ih (base + BitVec.ofNat 64 24) bss hlen)

theorem arrayAt_append_singleton {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) (x : α) :
    arrayAt elem stride base (xs ++ [x]) =
      arrayAt elem stride base xs ∗ elem x (base + BitVec.ofNat 64 (xs.length * stride)) := by
  induction xs generalizing base with
  | nil => simp only [List.nil_append, arrayAt, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, emp_sepConj, sepConj_emp]
  | cons y xs ih =>
    simp only [List.cons_append, arrayAt, List.length_cons, ih (base + BitVec.ofNat 64 stride)]
    have hadd : base + BitVec.ofNat 64 stride + BitVec.ofNat 64 (xs.length * stride) =
        base + BitVec.ofNat 64 ((xs.length + 1) * stride) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul, Nat.add_comm (xs.length * stride) stride]
    rw [hadd, sepConj_assoc]

@[simp, arm64_norm]
theorem extractLsb'_append64_0 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits

@[simp, arm64_norm]
theorem extractLsb'_append64_64 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits

theorem memRegion_split_24_cells (ptr : BitVec 64) (n capNat : Nat)
    (hlt : n < capNat) (hbound : capNat * 24 < 2 ^ 63) :
    memRegion (ptr + BitVec.ofNat 64 (n * 24)) ((capNat - n) * 24) =
      (∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        ((ptr + BitVec.ofNat 64 (n * 24)) ↦₆₄ w0) ∗
        ((ptr + BitVec.ofNat 64 (n * 24) + 8#64) ↦₆₄ w1) ∗
        ((ptr + BitVec.ofNat 64 (n * 24) + 16#64) ↦₆₄ w2)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((n + 1) * 24)) ((capNat - (n + 1)) * 24) := by
  have hsplit : (capNat - n) * 24 = 24 + (capNat - (n + 1)) * 24 := by
    have h1 : capNat - n = 1 + (capNat - (n + 1)) := by omega
    rw [h1, Nat.add_mul, Nat.one_mul]
  have hadd : ptr + BitVec.ofNat 64 (n * 24) + BitVec.ofNat 64 24 = ptr + BitVec.ofNat 64 ((n + 1) * 24) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul]
  rw [hsplit, ProofLib.memRegion_split (ptr + BitVec.ofNat 64 (n * 24)) 24 ((capNat - (n + 1)) * 24) (by omega), hadd]
  congr 1
  rw [show (24 : Nat) = 8 + (8 + 8) from rfl, ProofLib.memRegion_split _ 8 (8 + 8) (by decide),
    ProofLib.memRegion_split _ 8 8 (by decide), ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem vecBuf_vecU8_entails_grow_pre (A : RustAlloc) (cap ptr : BitVec 64)
    (bss : List (List (BitVec 8))) (heq : bss.length = cap.toNat) :
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr bss ∗
       memRegion (ptr + BitVec.ofNat 64 (bss.length * 24)) ((cap.toNat - bss.length) * 24)) ⊢
    ∃∗ pins : List VecPin,
      ⌜pins.length = bss.length ∧ (vecU8ArrayBytes pins bss).length = cap.toNat * 24⌝ ∗
      (if cap = 0 then emp else A.live ptr (vecU8ArrayBytes pins bss).length 8 ∗ (ptr ↦ₛ vecU8ArrayBytes pins bss)) ∗
      vecU8ArrayHeaps A pins bss := by
  by_cases hcap0 : cap = 0
  · subst hcap0; have hbss : bss = [] := List.eq_nil_of_length_eq_zero heq; subst hbss
    simp only [ite_true]; refine Entails.trans ?_ (Entails.sepExists_intro ([] : List VecPin))
    simp [vecU8ArrayBytes, vecU8ArrayHeaps]; exact Entails.refl _
  · simp only [hcap0, ite_false, heq, Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp]
    refine Entails.trans (sepConj_mono_right (arrayAt_vecU8_entails_bytes A ptr bss)) ?_
    rw [sepExists_sepConj_right]; refine Entails.sepExists_elim fun pins => ?_
    have hpull :
        A.live ptr (cap.toNat * 24) 8 ∗ (⌜pins.length = bss.length⌝ ∗ (ptr ↦ₛ vecU8ArrayBytes pins bss) ∗ vecU8ArrayHeaps A pins bss) =
        ⌜pins.length = bss.length⌝ ∗ (A.live ptr (cap.toNat * 24) 8 ∗ (ptr ↦ₛ vecU8ArrayBytes pins bss) ∗ vecU8ArrayHeaps A pins bss) := by ac_rfl
    rw [hpull]; refine Entails.pure_left fun hlen => ?_
    have hbytes_len : (vecU8ArrayBytes pins bss).length = cap.toNat * 24 := by rw [vecU8ArrayBytes_length hlen, heq]
    refine Entails.trans ?_ (Entails.sepExists_intro pins)
    rw [pure_sepConj_of_true ⟨hlen.trans heq, hbytes_len⟩, hbytes_len]; exact Entails.of_eq (by ac_rfl)

theorem grow_post_entails_ready (A : RustAlloc) (cap p' : BitVec 64)
    (pins : List VecPin) (bss : List (List (BitVec 8)))
    (heq : bss.length = cap.toNat) (hpins : pins.length = bss.length)
    (hbound : max (2 * cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63) :
    A.live p' (max (2 * cap.toNat) 4 * 24) 8 ∗ (p' ↦ₛ vecU8ArrayBytes pins bss) ∗
      memRegion (p' + BitVec.ofNat 64 (vecU8ArrayBytes pins bss).length) ((max (2 * cap.toNat) 4 - cap.toNat) * 24) ∗
      vecU8ArrayHeaps A pins bss ⊢
    A.live p' ((newCapVecU8 cap).toNat * 24) 8 ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 p' bss ∗
      memRegion (p' + BitVec.ofNat 64 (bss.length * 24)) (((newCapVecU8 cap).toNat - bss.length) * 24) := by
  have hnew_toNat : (newCapVecU8 cap).toNat = max (2 * cap.toNat) 4 := by
    unfold newCapVecU8; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hnew_toNat, vecU8ArrayBytes_length hpins, ← heq]
  have hpull :
      A.live p' (max (2 * bss.length) 4 * 24) 8 ∗ (p' ↦ₛ vecU8ArrayBytes pins bss) ∗
        memRegion (p' + BitVec.ofNat 64 (bss.length * 24)) ((max (2 * bss.length) 4 - bss.length) * 24) ∗ vecU8ArrayHeaps A pins bss =
      A.live p' (max (2 * bss.length) 4 * 24) 8 ∗ ((p' ↦ₛ vecU8ArrayBytes pins bss) ∗ vecU8ArrayHeaps A pins bss) ∗
        memRegion (p' + BitVec.ofNat 64 (bss.length * 24)) ((max (2 * bss.length) 4 - bss.length) * 24) := by ac_rfl
  rw [hpull]; exact sepConj_mono_right (sepConj_mono_left (arrayAt_vecU8_of_bytes A p' pins bss hpins))

theorem vecU8At_stack_to_cells (A : RustAlloc) (sp cap_e ptr_e : BitVec 64) (v : List (BitVec 8)) :
    vecU8At A (sp - 152#64) cap_e ptr_e v =
      ((sp - 152#64) ↦₆₄ cap_e) ∗ ((sp - 144#64) ↦₆₄ ptr_e) ∗ ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ vecU8Buf A cap_e ptr_e v := by
  rw [vecU8At_eq_header_sep_buf]; unfold vecHeader
  have h8 : sp - 152#64 + 8#64 = sp - 144#64 := by bv_omega
  have h16 : sp - 152#64 + 16#64 = sp - 136#64 := by bv_omega
  rw [h8, h16]; ac_rfl

theorem vecVecU8At_after_push (A : RustAlloc) (vecAddr cap' ptr' cap_e ptr_e : BitVec 64)
    (bss : List (List (BitVec 8))) (v : List (BitVec 8))
    (hlt : bss.length < cap'.toNat) (hbound : cap'.toNat * 24 < 2 ^ 63) (hptr : ptr' ≠ 0) :
    (vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗
      ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1)) ∗
      A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24)) ↦₆₄ cap_e) ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24) + 8#64) ↦₆₄ ptr_e) ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24) + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗
      vecU8Buf A cap_e ptr_e v ∗
      memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24)) ((cap'.toNat - (bss.length + 1)) * 24) ⊢
    vecVecU8At A vecAddr (bss ++ [v]) := by
  unfold vecVecU8At vecHeaderBytes vecOf
  refine Entails.trans ?_ (Entails.sepExists_intro (P := fun c => ∃∗ p, vecAt A 24 8 (fun bs addr => vecU8 A addr bs) vecAddr c p (bss ++ [v])) cap')
  refine Entails.trans ?_ (Entails.sepExists_intro (P := fun p => vecAt A 24 8 (fun bs addr => vecU8 A addr bs) vecAddr cap' p (bss ++ [v])) ptr')
  unfold vecAt vecHeader vecBuf
  have hcap_ne0 : cap' ≠ 0 := by intro h0; subst h0; change bss.length < 0 at hlt; omega
  have hlen_app : (bss ++ [v]).length = bss.length + 1 := by simp
  simp only [hlen_app, hcap_ne0, ite_false]
  rw [pure_sepConj_of_true ⟨by omega, hbound, hptr⟩, arrayAt_append_singleton (fun bs addr => vecU8 A addr bs) 24 ptr' bss v]
  let elemAddr := ptr' + BitVec.ofNat 64 (bss.length * 24)
  have helem : (elemAddr ↦₆₄ cap_e) ∗ ((elemAddr + 8#64) ↦₆₄ ptr_e) ∗ ((elemAddr + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ vecU8Buf A cap_e ptr_e v ⊢ vecU8 A elemAddr v := by
    have hhdr : (elemAddr ↦₆₄ cap_e) ∗ ((elemAddr + 8#64) ↦₆₄ ptr_e) ∗ ((elemAddr + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ vecU8Buf A cap_e ptr_e v =
        vecU8At A elemAddr cap_e ptr_e v := by rw [vecU8At_eq_header_sep_buf]; unfold vecHeader; ac_rfl
    rw [hhdr]; unfold vecU8
    refine Entails.trans ?_ (Entails.sepExists_intro (P := fun c => ∃∗ p, vecU8At A elemAddr c p v) cap_e)
    exact Entails.sepExists_intro (P := fun p => vecU8At A elemAddr cap_e p v) ptr_e
  have hpull1 :
      (vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗ ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1)) ∗
        A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗
        (elemAddr ↦₆₄ cap_e) ∗ ((elemAddr + 8#64) ↦₆₄ ptr_e) ∗ ((elemAddr + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ vecU8Buf A cap_e ptr_e v ∗
        memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24)) ((cap'.toNat - (bss.length + 1)) * 24) =
      ((elemAddr ↦₆₄ cap_e) ∗ ((elemAddr + 8#64) ↦₆₄ ptr_e) ∗ ((elemAddr + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ vecU8Buf A cap_e ptr_e v) ∗
      ((vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗ ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1)) ∗
        A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗
        memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24)) ((cap'.toNat - (bss.length + 1)) * 24)) := by ac_rfl
  have hpull2 :
      ((vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗ ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1))) ∗
        (A.live ptr' (cap'.toNat * 24) 8 ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗ vecU8 A elemAddr v) ∗
          memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24)) ((cap'.toNat - (bss.length + 1)) * 24)) =
      vecU8 A elemAddr v ∗
        ((vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗ ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1)) ∗
          A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗
          memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24)) ((cap'.toNat - (bss.length + 1)) * 24)) := by ac_rfl
  rw [hpull1]; refine Entails.trans (sepConj_mono_left helem) (Entails.of_eq hpull2.symm)

theorem vecVecU8At_after_push_24 (A : RustAlloc) (msgPtr cap' ptr' cap_e ptr_e : BitVec 64)
    (bss : List (List (BitVec 8))) (v : List (BitVec 8))
    (hlt : bss.length < cap'.toNat) (hbound : cap'.toNat * 24 < 2 ^ 63) (hptr : ptr' ≠ 0) :
    ((msgPtr + 24#64) ↦₆₄ cap') ∗ ((msgPtr + 32#64) ↦₆₄ ptr') ∗
      ((msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1)) ∗
      A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24)) ↦₆₄ cap_e) ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24) + 8#64) ↦₆₄ ptr_e) ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24) + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗
      vecU8Buf A cap_e ptr_e v ∗
      memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24)) ((cap'.toNat - (bss.length + 1)) * 24) ⊢
    vecVecU8At A (msgPtr + protoPolynomialEncoderPolysOff) (bss ++ [v]) := by
  simpa only [protoPolynomialEncoderPolysOff, bv64_add24_add8, bv64_add24_add16] using
    vecVecU8At_after_push A (msgPtr + 24#64) cap' ptr' cap_e ptr_e bss v hlt hbound hptr

@[simp, arm64_norm]
theorem madd_24_eq (ptr : BitVec 64) (n : Nat) :
    ptr + BitVec.ofNat 64 n * 24#64 = ptr + BitVec.ofNat 64 (n * 24) := by
  rw [← BitVec.ofNat_mul]

@[simp, arm64_norm]
theorem madd_24_eq' (ptr : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 n * 24#64 + ptr = ptr + BitVec.ofNat 64 (n * 24) := by
  rw [BitVec.add_comm, madd_24_eq]

@[simp, arm64_norm]
theorem bv64_ofNat_add_one (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  rw [← BitVec.ofNat_add]

theorem len_eq_cap_bne_false {len : Nat} {cap : BitVec 64} (heq : len = cap.toNat) :
    (BitVec.ofNat 64 len != cap) = false := by
  have h : BitVec.ofNat 64 len = cap := by rw [heq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp [h]

theorem len_lt_cap_bne_true {len : Nat} {cap : BitVec 64} (hlt : len < cap.toNat) :
    (BitVec.ofNat 64 len != cap) = true := by
  rw [bne_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hlt cap.isLt)] at h1; omega

theorem vecU8At_zero_eq_cells (A : RustAlloc) (sp : BitVec 64) :
    vecU8At A (sp - 152#64) 0#64 1#64 [] =
      ((sp - 152#64) ↦₆₄ 0#64) ∗ ((sp - 144#64) ↦₆₄ 1#64) ∗ ((sp - 136#64) ↦₆₄ 0#64) := by
  rw [vecU8At_eq_header_sep_buf]; unfold vecHeader vecU8Buf
  have h8 : sp - 152#64 + 8#64 = sp - 144#64 := by bv_omega
  have h16 : sp - 152#64 + 16#64 = sp - 136#64 := by bv_omega
  have hpure : ([] : List (BitVec 8)).length ≤ (0#64).toNat ∧ (0#64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 := ⟨by decide, by decide, by decide⟩
  rw [h8, h16, pure_sepConj_of_true hpure]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, eq_self_iff_true, ↓reduceIte, sepConj_emp, sepConj_assoc]

/-! ## 2. 160-Byte Stack Frame & Sub-Stack Splitting Lemmas -/

abbrev polyBelowStack : Nat := skipField3Stack 97
abbrev polyMergeStack : Nat := 160 + polyBelowStack

def polySavedRegs (sp : BitVec 64) (s0 : State) (v_pad : BitVec 64) : SepProp :=
  ((sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((sp - 56#64) ↦₆₄ v_pad) ∗
  ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)

def polySavedRegsAny (sp : BitVec 64) (s0 : State) : SepProp :=
  ∃∗ v_pad : BitVec 64, polySavedRegs sp s0 v_pad

theorem polySavedRegs_entails_any (sp : BitVec 64) (s0 : State) (v_pad : BitVec 64) :
    polySavedRegs sp s0 v_pad ⊢ polySavedRegsAny sp s0 :=
  Entails.sepExists_intro (P := fun v => polySavedRegs sp s0 v) v_pad

theorem stackAt_polyMerge_prologue (sp : BitVec 64) :
    stackAt sp polyMergeStack =
      stackAt (sp - 160#64) polyBelowStack ∗ memRegion (sp - 160#64) 32 ∗ memRegion (sp - 128#64) 48 ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗
        ((sp - 56#64) ↦₆₄ v3) ∗ ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗ ((sp - 16#64) ↦₆₄ v8) ∗
        ((sp - 8#64) ↦₆₄ v9)) := by
  have h1 := ProofLib.stackAt_split_cells sp (80 + polyBelowStack) 10 (by decide)
  change stackAt sp polyMergeStack = stackAt (sp - 80#64) (80 + polyBelowStack) ∗ cells (sp - 80#64) 10 at h1
  have h2 := memRegion_split' (b := sp - 80#64 - BitVec.ofNat 64 (80 + polyBelowStack))
    (b' := sp - 128#64) (n := 32 + polyBelowStack) (k := 48) (N := 80 + polyBelowStack) (by decide) (by bv_omega) (by decide)
  have h2_addr : sp - 80#64 - BitVec.ofNat 64 (80 + polyBelowStack) = sp - 128#64 - BitVec.ofNat 64 (32 + polyBelowStack) := by bv_omega
  change stackAt (sp - 80#64) (80 + polyBelowStack) = _ at h2; rw [h2_addr] at h2
  change stackAt (sp - 80#64) (80 + polyBelowStack) = stackAt (sp - 128#64) (32 + polyBelowStack) ∗ memRegion (sp - 128#64) 48 at h2
  have h3 := memRegion_split' (b := sp - 128#64 - BitVec.ofNat 64 (32 + polyBelowStack))
    (b' := sp - 160#64) (n := polyBelowStack) (k := 32) (N := 32 + polyBelowStack) (by decide) (by bv_omega) (by decide)
  have h3_addr : sp - 128#64 - BitVec.ofNat 64 (32 + polyBelowStack) = sp - 160#64 - BitVec.ofNat 64 polyBelowStack := by bv_omega
  change stackAt (sp - 128#64) (32 + polyBelowStack) = _ at h3; rw [h3_addr] at h3
  change stackAt (sp - 128#64) (32 + polyBelowStack) = stackAt (sp - 160#64) polyBelowStack ∗ memRegion (sp - 160#64) 32 at h3
  have hc10 : cells (sp - 80#64) 10 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗
        ((sp - 56#64) ↦₆₄ v3) ∗ ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗ ((sp - 16#64) ↦₆₄ v8) ∗
        ((sp - 8#64) ↦₆₄ v9)) := by cells_unfold
  rw [h1, h2, h3, hc10]; ac_rfl

theorem stackAt_polyMerge_epilogue (sp : BitVec 64) (s0 : State) (v_pad : BitVec 64) :
    stackAt (sp - 160#64) polyBelowStack ∗ memRegion (sp - 160#64) 32 ∗
      memRegion (sp - 128#64) 48 ∗ polySavedRegs sp s0 v_pad ⊢
    stackAt sp polyMergeStack := by
  rw [stackAt_polyMerge_prologue]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)); unfold polySavedRegs
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x29))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x30))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x25))
  refine Entails.trans ?_ (Entails.sepExists_intro v_pad)
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x24))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x23))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x22))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x21))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x20))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x19))
  exact Entails.refl _

theorem memRegion_32_cells160 (sp : BitVec 64) :
    memRegion (sp - 160#64) 32 =
      ∃∗ v3 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v0 : BitVec 64,
        ((sp - 160#64) ↦₆₄ v0) ∗ ((sp - 152#64) ↦₆₄ v1) ∗ ((sp - 144#64) ↦₆₄ v2) ∗ ((sp - 136#64) ↦₆₄ v3) := by
  have s1 := ProofLib.memRegion_split (sp - 160#64) 8 24 (by decide); rw [ProofLib.bv_sub_add_lit sp 160 8] at s1
  have s2 := ProofLib.memRegion_split (sp - 152#64) 8 16 (by decide); rw [ProofLib.bv_sub_add_lit sp 152 8] at s2
  have s3 := ProofLib.memRegion_split (sp - 144#64) 8 8 (by decide); rw [ProofLib.bv_sub_add_lit sp 144 8] at s3
  change memRegion (sp - 144#64) 16 = memRegion (sp - 144#64) 8 ∗ memRegion (sp - 136#64) 8 at s3
  rw [s1, s2, s3, ProofLib.memRegion_eight (sp - 160#64), ProofLib.memRegion_eight (sp - 152#64),
    ProofLib.memRegion_eight (sp - 144#64), ProofLib.memRegion_eight (sp - 136#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem cells160_entails_memRegion32 (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 160#64) ↦₆₄ v0) ∗ ((sp - 152#64) ↦₆₄ v1) ∗ ((sp - 144#64) ↦₆₄ v2) ∗ ((sp - 136#64) ↦₆₄ v3) ⊢
    memRegion (sp - 160#64) 32 := by
  rw [memRegion_32_cells160]
  refine Entails.trans ?_ (Entails.sepExists_intro v3); refine Entails.trans ?_ (Entails.sepExists_intro v2)
  refine Entails.trans ?_ (Entails.sepExists_intro v1); refine Entails.trans ?_ (Entails.sepExists_intro v0)
  exact Entails.refl _

theorem memRegion_48_wtErr160 (sp : BitVec 64) :
    memRegion (sp - 128#64) 48 =
      (∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8, ∃∗ v0 : BitVec 64,
        ((sp - 128#64) ↦₆₄ v0) ∗ ((sp - 120#64) ↦₈ b0) ∗ ((sp - 119#64) ↦₈ b1)) ∗
        memRegion (sp - 118#64) 38 := by
  have s1 := ProofLib.memRegion_split (sp - 128#64) 8 40 (by decide); rw [ProofLib.bv_sub_add_lit sp 128 8] at s1
  have s2 := ProofLib.memRegion_split (sp - 120#64) 1 39 (by decide); rw [ProofLib.bv_sub_add_lit sp 120 1] at s2
  have s3 := ProofLib.memRegion_split (sp - 119#64) 1 38 (by decide); rw [ProofLib.bv_sub_add_lit sp 119 1] at s3
  change memRegion (sp - 119#64) 39 = memRegion (sp - 119#64) 1 ∗ memRegion (sp - 118#64) 38 at s3
  rw [s1, s2, s3, ProofLib.memRegion_eight (sp - 128#64), ProofLib.memRegion_one (sp - 120#64), ProofLib.memRegion_one (sp - 119#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; ac_rfl

theorem wtErr160_entails_memRegion40 (sp : BitVec 64) (b0 b1 : BitVec 8) :
    ((sp - 120#64) ↦₈ b0) ∗ ((sp - 119#64) ↦₈ b1) ∗ memRegion (sp - 118#64) 38 ⊢ memRegion (sp - 120#64) 40 := by
  have s2 := ProofLib.memRegion_split (sp - 120#64) 1 39 (by decide); rw [ProofLib.bv_sub_add_lit sp 120 1] at s2
  have s3 := ProofLib.memRegion_split (sp - 119#64) 1 38 (by decide); rw [ProofLib.bv_sub_add_lit sp 119 1] at s3
  rw [s2, s3]; exact sepConj_mono (pointsTo8_entails_memRegion1 _ b0) (sepConj_mono (pointsTo8_entails_memRegion1 _ b1) (Entails.refl _))

theorem pointsTo64_memRegion40_entails_48_160 (sp v0 : BitVec 64) :
    ((sp - 128#64) ↦₆₄ v0) ∗ memRegion (sp - 120#64) 40 ⊢ memRegion (sp - 128#64) 48 := by
  have s1 := ProofLib.memRegion_split (sp - 128#64) 8 40 (by decide); rw [ProofLib.bv_sub_add_lit sp 128 8] at s1; rw [s1]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp - 128#64) v0)

theorem memRegion8_memRegion40_entails_48_160 (sp : BitVec 64) :
    memRegion (sp - 128#64) 8 ∗ memRegion (sp - 120#64) 40 ⊢ memRegion (sp - 128#64) 48 := by
  have s1 := ProofLib.memRegion_split (sp - 128#64) 8 40 (by decide); rw [ProofLib.bv_sub_add_lit sp 128 8] at s1; exact Entails.of_eq s1.symm

theorem memRegion_48_cells1_160 (sp : BitVec 64) :
    memRegion (sp - 128#64) 48 = (∃∗ v0 : BitVec 64, ((sp - 128#64) ↦₆₄ v0)) ∗ memRegion (sp - 120#64) 40 := by
  have s1 := ProofLib.memRegion_split (sp - 128#64) 8 40 (by decide); rw [ProofLib.bv_sub_add_lit sp 128 8] at s1
  rw [s1, ProofLib.memRegion_eight (sp - 128#64)]

theorem memRegion_48_cells2_160 (sp : BitVec 64) :
    memRegion (sp - 128#64) 48 =
      (∃∗ v1 : BitVec 64, ∃∗ v0 : BitVec 64, ((sp - 128#64) ↦₆₄ v0) ∗ ((sp - 120#64) ↦₆₄ v1)) ∗ memRegion (sp - 112#64) 32 := by
  have s1 := ProofLib.memRegion_split (sp - 128#64) 8 40 (by decide); rw [ProofLib.bv_sub_add_lit sp 128 8] at s1
  have s2 := ProofLib.memRegion_split (sp - 120#64) 8 32 (by decide); rw [ProofLib.bv_sub_add_lit sp 120 8] at s2
  rw [s1, s2, ProofLib.memRegion_eight (sp - 128#64), ProofLib.memRegion_eight (sp - 120#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; ac_rfl

theorem cells2_memRegion32_entails_40_160 (sp v1 : BitVec 64) :
    ((sp - 120#64) ↦₆₄ v1) ∗ memRegion (sp - 112#64) 32 ⊢ memRegion (sp - 120#64) 40 := by
  have s2 := ProofLib.memRegion_split (sp - 120#64) 8 32 (by decide); rw [ProofLib.bv_sub_add_lit sp 120 8] at s2; rw [s2]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp - 120#64) v1)

abbrev polyBelowRest (sp : BitVec 64) (subStack : Nat) : SepProp :=
  memRegion (sp - 160#64 - BitVec.ofNat 64 polyBelowStack) (polyBelowStack - subStack)

private theorem bv_sub_160_add_cancel (sp u w : BitVec 64) :
    sp - 160#64 - w = sp - 160#64 - (u + w) + u := by bv_omega

theorem polyBelow_split (sp : BitVec 64) (subStack : Nat) (hle : subStack ≤ polyBelowStack) :
    stackAt (sp - 160#64) polyBelowStack = polyBelowRest sp subStack ∗ stackAt (sp - 160#64) subStack := by
  simp only [polyBelowRest, stackAt]
  have hlen : polyBelowStack = (polyBelowStack - subStack) + subStack := by omega
  have hbound : polyBelowStack ≤ 2 ^ 64 := by
    simp only [polyBelowStack, skipField3Stack, decodeVarint2Stack, decodeVarintSlowStack, decodeErrorHookStack, allocHookStack]; omega
  have hbit : BitVec.ofNat 64 polyBelowStack = BitVec.ofNat 64 (polyBelowStack - subStack) + BitVec.ofNat 64 subStack := by
    rw [← BitVec.ofNat_add, ← hlen]
  exact memRegion_split' (b := sp - 160#64 - BitVec.ofNat 64 polyBelowStack)
    (b' := sp - 160#64 - BitVec.ofNat 64 subStack) (n := polyBelowStack - subStack) (k := subStack)
    (N := polyBelowStack) hlen (by rw [hbit]; exact bv_sub_160_add_cancel sp _ _) hbound

theorem polyBelow_entails (sp : BitVec 64) (subStack : Nat) (hle : subStack ≤ polyBelowStack) :
    polyBelowRest sp subStack ∗ stackAt (sp - 160#64) subStack ⊢ stackAt (sp - 160#64) polyBelowStack :=
  Entails.of_eq (polyBelow_split sp subStack hle).symm

theorem polyBelow_decodeVarint2 (sp : BitVec 64) :
    stackAt (sp - 160#64) polyBelowStack = polyBelowRest sp decodeVarint2Stack ∗ stackAt (sp - 160#64) decodeVarint2Stack :=
  polyBelow_split sp decodeVarint2Stack (by decide)

theorem polyBelow_decodeVarint2_entails (sp : BitVec 64) :
    polyBelowRest sp decodeVarint2Stack ∗ stackAt (sp - 160#64) decodeVarint2Stack ⊢ stackAt (sp - 160#64) polyBelowStack :=
  polyBelow_entails sp decodeVarint2Stack (by decide)

theorem polyBelow_decodeErrorHook (sp : BitVec 64) :
    stackAt (sp - 160#64) polyBelowStack = polyBelowRest sp decodeErrorHookStack ∗ stackAt (sp - 160#64) decodeErrorHookStack :=
  polyBelow_split sp decodeErrorHookStack (by decide)

theorem polyBelow_decodeErrorHook_entails (sp : BitVec 64) :
    polyBelowRest sp decodeErrorHookStack ∗ stackAt (sp - 160#64) decodeErrorHookStack ⊢ stackAt (sp - 160#64) polyBelowStack :=
  polyBelow_entails sp decodeErrorHookStack (by decide)

theorem polyBelow_bytesMerge3 (sp : BitVec 64) :
    stackAt (sp - 160#64) polyBelowStack = polyBelowRest sp bytesMerge3Stack ∗ stackAt (sp - 160#64) bytesMerge3Stack :=
  polyBelow_split sp bytesMerge3Stack (by decide)

theorem polyBelow_bytesMerge3_entails (sp : BitVec 64) :
    polyBelowRest sp bytesMerge3Stack ∗ stackAt (sp - 160#64) bytesMerge3Stack ⊢ stackAt (sp - 160#64) polyBelowStack :=
  polyBelow_entails sp bytesMerge3Stack (by decide)

theorem polyBelow_extHook (sp : BitVec 64) :
    stackAt (sp - 160#64) polyBelowStack = polyBelowRest sp extHookStack ∗ stackAt (sp - 160#64) extHookStack :=
  polyBelow_split sp extHookStack (by decide)

theorem polyBelow_extHook_entails (sp : BitVec 64) :
    polyBelowRest sp extHookStack ∗ stackAt (sp - 160#64) extHookStack ⊢ stackAt (sp - 160#64) polyBelowStack :=
  polyBelow_entails sp extHookStack (by decide)

/-! ## 3. Specifications & Pure Model Step Lemmas for `PolynomialDecoder` and `PolynomialEncoder` -/

abbrev polyDecoderToProto (m : PolynomialDecoder) : ProtoPolynomialDecoder :=
  { ptsNeeded := m.ptsNeeded, polys := m.polys, pts := m.pts, isComplete := m.isComplete }

abbrev polyEncoderToProto (m : PolynomialEncoder) : ProtoPolynomialEncoder :=
  { idx := m.idx, pts := m.pts, polys := m.polys }

theorem protoPolynomialDecoderAt_entails_exists (A : RustAlloc) (a : BitVec 64) (m : PolynomialDecoder) :
    protoPolynomialDecoderAt A a (polyDecoderToProto m) ⊢
      ∃∗ m' : PolynomialDecoder, protoPolynomialDecoderAt A a (polyDecoderToProto m') :=
  Entails.sepExists_intro (P := fun m' => protoPolynomialDecoderAt A a (polyDecoderToProto m')) m

theorem protoPolynomialEncoderAt_entails_exists (A : RustAlloc) (a : BitVec 64) (m : PolynomialEncoder) :
    protoPolynomialEncoderAt A a (polyEncoderToProto m) ⊢
      ∃∗ m' : PolynomialEncoder, protoPolynomialEncoderAt A a (polyEncoderToProto m') :=
  Entails.sepExists_intro (P := fun m' => protoPolynomialEncoderAt A a (polyEncoderToProto m')) m

/-- Callee-saved registers `x26..x28` not spilled by the 160-byte prologue (`x19..x25` and `x29, x30` are spilled). -/
def PolyCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

/-- Ghost arguments of `prost::encoding::message::merge::<PolynomialDecoder, &mut &[u8]>` (`0x4e10c`). -/
structure PolyDecoderMergeGhost where
  wt : WireType
  msgPtr : BitVec 64
  msg : PolynomialDecoder
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Contract of `prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>`
(`0x4e10c`, 227 instructions) in terms of `LibsignalSpqrV1.Proto.mergeMessage PolynomialDecoder.mergeField`
and `protoPolynomialDecoderAt` (`Poly/EncoderRepr.lean`).
Bound `x.msg.pts.length + x.bs.length < 2 ^ 56` is discharged by callers (`V1State.Chunked.*::merge`
in `State::deserialize`) from the serialized state slice bound `x.st.bytes.length < 2 ^ 32` (`DEV-SPQR3`
in `spqrSendSpecT` / `spqrRecvSpecExactKeyBounded`) via `polynomialDecoder_mergeMessage_pts_le` (since every element of
`pts` consumes at least 2 wire bytes, `pts.length + rem.length ≤ st.bytes.length < 2 ^ 32 < 2 ^ 56`). -/
def polyDecoderMergeSpec (A : RustAlloc) : Spec PolyDecoderMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧ s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧ x.msg.pts.length + x.bs.length < 2 ^ 56⌝ ∗
      protoPolynomialDecoderAt A x.msgPtr (polyDecoderToProto x.msg) ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt s.sp polyMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp polyMergeStack ∗
      match (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ protoPolynomialDecoderAt A x.msgPtr (polyDecoderToProto m') ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : PolynomialDecoder, protoPolynomialDecoderAt A x.msgPtr (polyDecoderToProto m')) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Ghost arguments of `prost::encoding::message::merge::<PolynomialEncoder, &mut &[u8]>` (`0x4e498`). -/
structure PolyEncoderMergeGhost where
  wt : WireType
  msgPtr : BitVec 64
  msg : PolynomialEncoder
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Contract of `prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>`
(`0x4e498`, 212 instructions) in terms of `LibsignalSpqrV1.Proto.mergeMessage PolynomialEncoder.mergeField`
and `protoPolynomialEncoderAt` (`Poly/EncoderRepr.lean`).
Bounds `x.msg.pts.length + x.bs.length < 2 ^ 56` and `x.msg.polys.length + x.bs.length < 2 ^ 56`
are discharged by callers (`V1State.Chunked.*::merge` in `State::deserialize`) from the serialized state
slice bound `x.st.bytes.length < 2 ^ 32` (`DEV-SPQR3` in `spqrSendSpecT` / `spqrRecvSpecExactKeyBounded`) via
`polynomialEncoder_mergeMessage_pts_polys_le`. -/
def polyEncoderMergeSpec (A : RustAlloc) : Spec PolyEncoderMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧ s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧ x.msg.pts.length + x.bs.length < 2 ^ 56 ∧
      x.msg.polys.length + x.bs.length < 2 ^ 56⌝ ∗
      protoPolynomialEncoderAt A x.msgPtr (polyEncoderToProto x.msg) ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt s.sp polyMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp polyMergeStack ∗
      match (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ protoPolynomialEncoderAt A x.msgPtr (polyEncoderToProto m') ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : PolynomialEncoder, protoPolynomialEncoderAt A x.msgPtr (polyEncoderToProto m')) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem polynomialDecoder_mergeField_tag1 (m : PolynomialDecoder) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (PolynomialDecoder.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then (decodeVarint rest).map (fun (v, rest') => ({ m with ptsNeeded := v.truncate 32 }, rest')) else none := by
  unfold PolynomialDecoder.mergeField Proto.mergeUint32 Proto.checkWireType
  cases iwt <;> simp only [codecWireTypeToProto, beq_self_eq_true, ↓reduceIte]
  case varint =>
    rcases hdv : Proto.decodeVarint rest with e | ⟨v, rest'⟩
    · have hdv' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint rest = some (v, rest') := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  all_goals rfl

theorem polynomialDecoder_mergeField_tag2 (m : PolynomialDecoder) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (PolynomialDecoder.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then (decodeVarint rest).map (fun (v, rest') => ({ m with polys := v.truncate 32 }, rest')) else none := by
  unfold PolynomialDecoder.mergeField Proto.mergeUint32 Proto.checkWireType
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  cases iwt <;> simp only [codecWireTypeToProto, beq_self_eq_true, ↓reduceIte]
  case varint =>
    rcases hdv : Proto.decodeVarint rest with e | ⟨v, rest'⟩
    · have hdv' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint rest = some (v, rest') := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  all_goals rfl

theorem polynomialDecoder_mergeField_tag3 (m : PolynomialDecoder) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (PolynomialDecoder.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with pts := m.pts ++ [v] }, rest')) := by
  unfold PolynomialDecoder.mergeField Proto.mergeRepeatedBytes
  simp only [show (BitVec.ofNat 32 3 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 2#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 3#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [← proto_mergeBytes_codec_toOption]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩ <;> rfl

theorem polynomialDecoder_mergeField_tag4 (m : PolynomialDecoder) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (PolynomialDecoder.mergeField m (BitVec.ofNat 32 4) (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then (decodeVarint rest).map (fun (v, rest') => ({ m with isComplete := v != 0#64 }, rest')) else none := by
  unfold PolynomialDecoder.mergeField Proto.mergeBool Proto.checkWireType
  simp only [show (BitVec.ofNat 32 4 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 4 == 2#32) = false from rfl,
    show (BitVec.ofNat 32 4 == 3#32) = false from rfl,
    show (BitVec.ofNat 32 4 == 4#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  cases iwt <;> simp only [codecWireTypeToProto, beq_self_eq_true, ↓reduceIte]
  case varint =>
    rcases hdv : Proto.decodeVarint rest with e | ⟨v, rest'⟩
    · have hdv' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint rest = some (v, rest') := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  all_goals rfl

theorem polynomialDecoder_mergeField_other (m : PolynomialDecoder) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat)
    (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) (hne3 : tag ≠ 3) (hne4 : tag ≠ 4) :
    (PolynomialDecoder.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have hb3 : (BitVec.ofNat 32 tag == 3#32) = false := (itag_beq_tag_false hne3 htag_lt (by decide)).1
  have hb4 : (BitVec.ofNat 32 tag == 4#32) = false := (itag_beq_tag_false hne4 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold PolynomialDecoder.mergeField; simp only [hb1, hb2, hb3, hb4, Bool.false_eq_true, ↓reduceIte]
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with e | rest' <;> {
    have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }

theorem polynomialDecoder_mergeField_pts_le {m m' : PolynomialDecoder} {tag : BitVec 32}
    {wt : LibsignalSpqrV1.Proto.WireType} {rest rest' : List (BitVec 8)} {depth : Nat}
    (h : PolynomialDecoder.mergeField m tag wt rest depth = .ok (m', rest')) :
    m'.pts.length ≤ m.pts.length + 1 ∧ rest'.length ≤ rest.length := by
  refine ⟨?_, (protoPrefixStep_polynomialDecoder_mergeField m tag wt depth).length_le h⟩
  unfold PolynomialDecoder.mergeField at h
  split at h
  · rcases h1 : Proto.mergeUint32 wt rest with _ | ⟨v, bs'⟩ <;> simp [h1, Bind.bind, Except.bind] at h; rcases h with ⟨rfl, rfl⟩; simp
  · split at h
    · rcases h1 : Proto.mergeUint32 wt rest with _ | ⟨v, bs'⟩ <;> simp [h1, Bind.bind, Except.bind] at h; rcases h with ⟨rfl, rfl⟩; simp
    · split at h
      · unfold Proto.mergeRepeatedBytes at h; rcases h1 : Proto.mergeBytes wt rest with _ | ⟨v, bs'⟩ <;> simp [h1, Bind.bind, Except.bind] at h; rcases h with ⟨rfl, rfl⟩; simp
      · split at h
        · rcases h1 : Proto.mergeBool wt rest with _ | ⟨v, bs'⟩ <;> simp [h1, Bind.bind, Except.bind] at h; rcases h with ⟨rfl, rfl⟩; simp
        · rcases h1 : Proto.skipField wt tag rest depth with _ | bs' <;> simp [h1, Bind.bind, Except.bind] at h; rcases h with ⟨rfl, rfl⟩; simp

theorem polynomialDecoder_mergeLoopBin_pts_le {fuel : Nat} {m m' : PolynomialDecoder}
    {cur : List (BitVec 8)} {limit depth : Nat}
    (h : mergeLoopBin PolynomialDecoder.mergeField fuel m cur limit depth = some m') :
    m'.pts.length + limit ≤ m.pts.length + cur.length := by
  induction fuel generalizing m cur with
  | zero =>
    unfold mergeLoopBin at h; split at h
    · split at h
      · rename_i heq; simp only [beq_iff_eq] at heq; simp only [Option.some.injEq] at h; subst h; omega
      · contradiction
    · contradiction
  | succ fuel ih =>
    unfold mergeLoopBin at h; split at h
    · split at h
      · rename_i heq; simp only [beq_iff_eq] at heq; simp only [Option.some.injEq] at h; subst h; omega
      · contradiction
    · rcases hdk : Proto.decodeKey cur with _ | ⟨⟨tag, wt⟩, rest⟩
      · simp [hdk, Except.toOption] at h
      · simp only [hdk, Except.toOption] at h; have hrest_lt : rest.length < cur.length := decodeKey_length_lt hdk
        rcases hmf : PolynomialDecoder.mergeField m tag wt rest depth with _ | ⟨m1, rest'⟩
        · simp [hmf, Except.toOption] at h
        · simp only [hmf, Except.toOption] at h; obtain ⟨hpts1, hrest1⟩ := polynomialDecoder_mergeField_pts_le hmf; have hih := ih h; omega

theorem polynomialDecoder_mergeMessage_pts_le {wt : LibsignalSpqrV1.Proto.WireType}
    {m m' : PolynomialDecoder} {bs rest : List (BitVec 8)} {depth' : Nat}
    (h : (Proto.mergeMessage PolynomialDecoder.mergeField wt m bs (depth' + 1)).toOption = some (m', rest)) :
    m'.pts.length + rest.length ≤ m.pts.length + bs.length := by
  rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField] at h
  unfold mergeMessageBin at h; split at h
  · contradiction
  · rcases hdv : Proto.decodeVarint bs with _ | ⟨len, rest0⟩
    · simp [hdv, Except.toOption] at h
    · simp only [hdv, Except.toOption] at h; have hrest0_lt : rest0.length < bs.length := decodeVarint_length_lt hdv
      split at h
      · contradiction
      · rcases hloop : mergeLoopBin PolynomialDecoder.mergeField (rest0.length - (rest0.length - len.toNat)) m rest0 (rest0.length - len.toNat) depth' with _ | m1
        · simp [hloop] at h
        · simp only [hloop, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩
          have hpts := polynomialDecoder_mergeLoopBin_pts_le hloop; have hdrop : (rest0.drop len.toNat).length = rest0.length - len.toNat := List.length_drop; omega

theorem polynomialEncoder_mergeField_tag1 (m : PolynomialEncoder) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (PolynomialEncoder.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then (decodeVarint rest).map (fun (v, rest') => ({ m with idx := v.truncate 32 }, rest')) else none := by
  unfold PolynomialEncoder.mergeField Proto.mergeUint32 Proto.checkWireType
  cases iwt <;> simp only [codecWireTypeToProto, beq_self_eq_true, ↓reduceIte]
  case varint =>
    rcases hdv : Proto.decodeVarint rest with e | ⟨v, rest'⟩
    · have hdv' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint rest = some (v, rest') := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  all_goals rfl

theorem polynomialEncoder_mergeField_tag2 (m : PolynomialEncoder) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (PolynomialEncoder.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with pts := m.pts ++ [v] }, rest')) := by
  unfold PolynomialEncoder.mergeField Proto.mergeRepeatedBytes
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [← proto_mergeBytes_codec_toOption]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩ <;> rfl

theorem polynomialEncoder_mergeField_tag3 (m : PolynomialEncoder) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (PolynomialEncoder.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with polys := m.polys ++ [v] }, rest')) := by
  unfold PolynomialEncoder.mergeField Proto.mergeRepeatedBytes
  simp only [show (BitVec.ofNat 32 3 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 2#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 3#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [← proto_mergeBytes_codec_toOption]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩ <;> rfl

theorem polynomialEncoder_mergeField_other (m : PolynomialEncoder) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat)
    (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) (hne3 : tag ≠ 3) :
    (PolynomialEncoder.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have hb3 : (BitVec.ofNat 32 tag == 3#32) = false := (itag_beq_tag_false hne3 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold PolynomialEncoder.mergeField; simp only [hb1, hb2, hb3, Bool.false_eq_true, ↓reduceIte]
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with e | rest' <;> {
    have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }

theorem polynomialEncoder_mergeField_pts_polys_le {m m' : PolynomialEncoder} {tag : BitVec 32}
    {wt : LibsignalSpqrV1.Proto.WireType} {rest rest' : List (BitVec 8)} {depth : Nat}
    (h : PolynomialEncoder.mergeField m tag wt rest depth = .ok (m', rest')) :
    m'.pts.length ≤ m.pts.length + 1 ∧ m'.polys.length ≤ m.polys.length + 1 ∧ rest'.length ≤ rest.length := by
  refine ⟨?_, ?_, (protoPrefixStep_polynomialEncoder_mergeField m tag wt depth).length_le h⟩
  · unfold PolynomialEncoder.mergeField at h
    split at h
    · rcases h1 : Proto.mergeUint32 wt rest with _ | ⟨v, bs'⟩ <;> simp [h1, Bind.bind, Except.bind] at h; rcases h with ⟨rfl, rfl⟩; simp
    · split at h
      · unfold Proto.mergeRepeatedBytes at h; rcases h1 : Proto.mergeBytes wt rest with _ | ⟨v, bs'⟩ <;> simp [h1, Bind.bind, Except.bind] at h; rcases h with ⟨rfl, rfl⟩; simp
      · split at h
        · unfold Proto.mergeRepeatedBytes at h; rcases h1 : Proto.mergeBytes wt rest with _ | ⟨v, bs'⟩ <;> simp [h1, Bind.bind, Except.bind] at h; rcases h with ⟨rfl, rfl⟩; simp
        · rcases h1 : Proto.skipField wt tag rest depth with _ | bs' <;> simp [h1, Bind.bind, Except.bind] at h; rcases h with ⟨rfl, rfl⟩; simp
  · unfold PolynomialEncoder.mergeField at h
    split at h
    · rcases h1 : Proto.mergeUint32 wt rest with _ | ⟨v, bs'⟩ <;> simp [h1, Bind.bind, Except.bind] at h; rcases h with ⟨rfl, rfl⟩; simp
    · split at h
      · unfold Proto.mergeRepeatedBytes at h; rcases h1 : Proto.mergeBytes wt rest with _ | ⟨v, bs'⟩ <;> simp [h1, Bind.bind, Except.bind] at h; rcases h with ⟨rfl, rfl⟩; simp
      · split at h
        · unfold Proto.mergeRepeatedBytes at h; rcases h1 : Proto.mergeBytes wt rest with _ | ⟨v, bs'⟩ <;> simp [h1, Bind.bind, Except.bind] at h; rcases h with ⟨rfl, rfl⟩; simp
        · rcases h1 : Proto.skipField wt tag rest depth with _ | bs' <;> simp [h1, Bind.bind, Except.bind] at h; rcases h with ⟨rfl, rfl⟩; simp

theorem polynomialEncoder_mergeLoopBin_pts_polys_le {fuel : Nat} {m m' : PolynomialEncoder}
    {cur : List (BitVec 8)} {limit depth : Nat}
    (h : mergeLoopBin PolynomialEncoder.mergeField fuel m cur limit depth = some m') :
    m'.pts.length + limit ≤ m.pts.length + cur.length ∧
    m'.polys.length + limit ≤ m.polys.length + cur.length := by
  induction fuel generalizing m cur with
  | zero =>
    unfold mergeLoopBin at h; split at h
    · split at h
      · rename_i heq; simp only [beq_iff_eq] at heq; simp only [Option.some.injEq] at h; subst h; omega
      · contradiction
    · contradiction
  | succ fuel ih =>
    unfold mergeLoopBin at h; split at h
    · split at h
      · rename_i heq; simp only [beq_iff_eq] at heq; simp only [Option.some.injEq] at h; subst h; omega
      · contradiction
    · rcases hdk : Proto.decodeKey cur with _ | ⟨⟨tag, wt⟩, rest⟩
      · simp [hdk, Except.toOption] at h
      · simp only [hdk, Except.toOption] at h; have hrest_lt : rest.length < cur.length := decodeKey_length_lt hdk
        rcases hmf : PolynomialEncoder.mergeField m tag wt rest depth with _ | ⟨m1, rest'⟩
        · simp [hmf, Except.toOption] at h
        · simp only [hmf, Except.toOption] at h
          obtain ⟨hpts1, hpolys1, hrest1⟩ := polynomialEncoder_mergeField_pts_polys_le hmf
          obtain ⟨hih1, hih2⟩ := ih h; omega

theorem polynomialEncoder_mergeMessage_pts_polys_le {wt : LibsignalSpqrV1.Proto.WireType}
    {m m' : PolynomialEncoder} {bs rest : List (BitVec 8)} {depth' : Nat}
    (h : (Proto.mergeMessage PolynomialEncoder.mergeField wt m bs (depth' + 1)).toOption = some (m', rest)) :
    m'.pts.length + rest.length ≤ m.pts.length + bs.length ∧
    m'.polys.length + rest.length ≤ m.polys.length + bs.length := by
  rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialEncoder_mergeField] at h
  unfold mergeMessageBin at h; split at h
  · contradiction
  · rcases hdv : Proto.decodeVarint bs with _ | ⟨len, rest0⟩
    · simp [hdv, Except.toOption] at h
    · simp only [hdv, Except.toOption] at h; have hrest0_lt : rest0.length < bs.length := decodeVarint_length_lt hdv
      split at h
      · contradiction
      · rcases hloop : mergeLoopBin PolynomialEncoder.mergeField (rest0.length - (rest0.length - len.toNat)) m rest0 (rest0.length - len.toNat) depth' with _ | m1
        · simp [hloop] at h
        · simp only [hloop, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩
          obtain ⟨hpts, hpolys⟩ := polynomialEncoder_mergeLoopBin_pts_polys_le hloop
          have hdrop : (rest0.drop len.toNat).length = rest0.length - len.toNat := List.length_drop; omega

/-! ## 4. Shared Arithmetic, Hook, & `PolynomialDecoder` Exit/Skip Lemmas -/

@[simp, arm64_norm]
theorem csinc_boolByte_eq (v : BitVec 64) :
    (if (v == 0#64) = true then 0#8 else 1#8) = boolByte (v != 0#64) := by
  unfold boolByte; cases h : (v == 0#64) <;> simp [bne, h]

theorem mergeBytes_eq_none_of_ne_len {iwt : WireType} {rest : List (BitVec 8)} (h : iwt ≠ .lengthDelimited) :
    mergeBytes iwt rest = none := by
  cases iwt <;> first | exact absurd rfl h | rfl

theorem iwt_bne_two_true_of_ne_len {iwt : WireType} (h : iwt ≠ .lengthDelimited) :
    (BitVec.ofNat 64 iwt.toNat != 2#64) = true ∧ (BitVec.ofNat 32 iwt.toNat != 2#32) = true := by
  cases iwt <;> first | exact absurd rfl h | decide

theorem slt_two_ofNat32_true {n : Nat} (hge3 : 3 ≤ n) (hlt : n < 2 ^ 31) :
    BitVec.slt 2#32 (BitVec.ofNat 32 n) = true ∧
    BitVec.slt 2#32 (BitVec.truncate 32 (BitVec.ofNat 64 n)) = true := by
  have hb : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : BitVec.slt 2#32 (BitVec.ofNat 32 n) = true := by
    rw [BitVec.slt_iff_toInt_lt, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond, hb]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  refine ⟨h1, ?_⟩
  rw [sf_truncate32_ofNat64]; exact h1

theorem growOneVecU8_ok_at_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff growOneVecU8Name := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (growOneVecU8Spec A) :=
  CryptoVerification.SpqrV1.Alloc.growOneVecU8_sysroot_ok_at_ext hA name k hk

theorem growOneVecU8_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneVecU8Name) (growOneVecU8Spec A) :=
  CryptoVerification.SpqrV1.Alloc.growOneVecU8_sysroot_ok_ext hA

theorem growOneVecU8_ok_at_ext_4k (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : CryptoVerification.SpqrV1.Alloc.AllocContracts4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff growOneVecU8Name := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (growOneVecU8Spec A) :=
  CryptoVerification.SpqrV1.Alloc.growOneVecU8_sysroot_ok_at_ext_4k hA name k hk

theorem growOneVecU8_ok_ext_4k (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : CryptoVerification.SpqrV1.Alloc.AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneVecU8Name) (growOneVecU8Spec A) :=
  CryptoVerification.SpqrV1.Alloc.growOneVecU8_sysroot_ok_ext_4k hA

/-- Loop-header separation-logic bundle at `+0x0a4` (`0x4e1b0`). -/
def polyDecoderLoopPre (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : PolynomialDecoder) (bs cur : List (BitVec 8)) : SepProp :=
  stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
    memRegion (s0.sp - 128#64) 48 ∗ polySavedRegsAny s0.sp s0 ∗
    protoPolynomialDecoderAt A msgPtr (polyDecoderToProto m) ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool

/-- Error-exit separation-logic bundle at `+0x070`, `+0x07c`, `+0x380`. -/
def polyDecoderErrFrame (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : PolynomialDecoder) (bs : List (BitVec 8)) : SepProp :=
  polySavedRegsAny s0.sp s0 ∗ protoPolynomialDecoderAt A msgPtr (polyDecoderToProto m) ∗
    (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗ A.pool

/-- Shared exit from `+0x07c` (`entry + 124#64`) when `x1 = err ≠ 0#64` owns `decodeErrorAtStackLen A err 0`. -/
theorem polyDecoder_err0_ret_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {err : BitVec 64}
    (hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 124#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (herr : err ≠ 0#64) (hcs : PolyCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗
        polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  polyDecoderMerge_fetches b H 124 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_ret; unfold WppPost polyDecoderMergeSpec
  simp only [hnone, polyDecoderErrFrame, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A err) (by sep_focus)
  apply SepWP.fold (protoPolynomialDecoderAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
  wp_done

/-- Shared exit from `+0x070` (`entry + 112#64`): calls `DecodeError::from` on `(s0.sp - 128#64, w)`
and returns at `+0x078..+0x098`. -/
theorem polyDecoder_from_err_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 0xffffffffffffcc94#64) (decodeErrorFromSpec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {w : BitVec 64}
    (hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hcs : PolyCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
        polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  polyDecoderMerge_fetches b H 112 44
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 0xffffffffffffcc94#64)
  conv => arg 4; rw [polyBelow_decodeErrorHook s0.sp, polyDecoderErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 128#64, w))
    (ret_pc := entry + 120#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret; unfold WppPost polyDecoderMergeSpec
  simp only [decodeErrorFromSpec, hnone, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A _) (by sep_focus)
  apply SepWP.fold (protoPolynomialDecoderAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
  wp_done

/-- Shared exit from `+0x380` (`entry + 896#64`): calls `DecodeError::push` on `(s0.sp - 128#64, err, 0)`
and returns at `+0x384..+0x388` + `+0x07c..+0x098`. -/
theorem polyDecoder_push_err_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 0xffffffffffffc99c#64) (decodeErrorPushSpec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {err : BitVec 64}
    (hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 896#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err 0 ∗
        memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  polyDecoderMerge_fetches b H 896 12; polyDecoderMerge_fetches b H 124 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 0xffffffffffffc99c#64)
  conv => arg 4; rw [polyBelow_decodeErrorHook s0.sp, polyDecoderErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 128#64, err, 0))
    (ret_pc := entry + 900#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl)
    (by decide : 0 < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret; unfold WppPost polyDecoderMergeSpec
  simp only [decodeErrorPushSpec, hnone, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A err) (by sep_focus)
  apply SepWP.fold (protoPolynomialDecoderAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus)
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
  wp_done

/-- Step lemma for unknown field tags (`tag ∉ {1, 2, 3, 4}`) at `+0x140` (`entry + 320#64`). -/
theorem polyDecoder_skip_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 0xffffffffffffda68#64) (skipField3Spec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32) (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 320#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have herr0_exit := @polyDecoder_err0_ret_exit b A H x R s0
  polyDecoderMerge_fetches b H 320 24
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffda68#64) hinv
  conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf]; simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_keep (x := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 332#64) hSkipCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 97 < 2 ^ 32 ∧ rest.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPp.of_sepWP (mid := entry + 124#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (Entails.of_eq (by dsimp only [polyDecoderErrFrame]; ac_rfl))
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPp.of_sepWP_img (mid := entry + 164#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (Entails.of_eq (by dsimp only [polyDecoderLoopPre]; ac_rfl))
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

/-! ## 5. Relocatable `[LibsignalPlacement]` Exit/Skip Lemmas for `PolynomialDecoder` (Block `296`) -/

/-- Placed shared exit from `+0x07c` (`(blkPl_296).base + 124#64`) when `x1 = err ≠ 0#64` owns `decodeErrorAtStackLen A err 0`. -/
theorem polyDecoder_err0_ret_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {err : BitVec 64}
    (hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_296).base + 124#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (herr : err ≠ 0#64) (hcs : PolyCalleeSaved s0 s) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗
        polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_ret; unfold WppPost polyDecoderMergeSpec
  simp only [hnone, polyDecoderErrFrame, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A err) (by sep_focus)
  apply SepWP.fold (protoPolynomialDecoderAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
  wp_done

/-- Placed shared exit from `+0x070` (`(blkPl_296).base + 112#64`): calls `DecodeError::from` on `(s0.sp - 128#64, w)`
and returns at `+0x078..+0x098`. -/
theorem polyDecoder_from_err_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {w : BitVec 64}
    (hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_296).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hcs : PolyCalleeSaved s0 s) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
        polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [polyBelow_decodeErrorHook s0.sp, polyDecoderErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 128#64, w))
    (ret_pc := (blkPl_296).base + 120#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret; unfold WppPost polyDecoderMergeSpec
  simp only [decodeErrorFromSpec, hnone, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A _) (by sep_focus)
  apply SepWP.fold (protoPolynomialDecoderAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
  wp_done

/-- Placed shared exit from `+0x380` (`(blkPl_296).base + 896#64`): calls `DecodeError::push` on `(s0.sp - 128#64, err, 0)`
and returns at `+0x384..+0x388` + `+0x07c..+0x098`. -/
theorem polyDecoder_push_err_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {err : BitVec 64}
    (hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_296).base + 896#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err 0 ∗
        memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP (mid := lsmpl.base 257)
  conv => arg 4; rw [polyBelow_decodeErrorHook s0.sp, polyDecoderErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 128#64, err, 0))
    (ret_pc := (blkPl_296).base + 900#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl)
    (by decide : 0 < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret; unfold WppPost polyDecoderMergeSpec
  simp only [decodeErrorPushSpec, hnone, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A err) (by sep_focus)
  apply SepWP.fold (protoPolynomialDecoderAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus)
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
  wp_done

/-- Placed step lemma for unknown field tags (`tag ∉ {1, 2, 3, 4}`) at `+0x140` (`(blkPl_296).base + 320#64`). -/
theorem polyDecoder_skip_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263) (skipField3Spec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32) (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_296).base + 320#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have herr0_exit := @polyDecoder_err0_ret_exit_placed _ A H x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) hinv
  conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf]; simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_keep_lscro (x := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_296).base + 332#64) hSkipCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 97 < 2 ^ 32 ∧ rest.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPp.of_sepWP (mid := (blkPl_296).base + 124#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (Entails.of_eq (by dsimp only [polyDecoderErrFrame]; ac_rfl))
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (Entails.of_eq (by dsimp only [polyDecoderLoopPre]; ac_rfl))
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

end CryptoVerification.SpqrV1.Prost.MessageMerge
