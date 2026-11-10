/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WP.StateNorm

/-!
# Representation Predicates and `encoded_len` Specifications for Polynomial Coders and Chunked States

Separation-logic representation predicates, pure `encodedLen` models, `LibsignalSpqrV1.Proto`
bridges, and Hoare specifications for `Vec<Vec<u8>>`, `PolynomialDecoder`, `PolynomialEncoder`,
`V1State.Chunked.Ct1Sampled`, and `V1State.Chunked.HeaderSent`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. `Vec<Vec<u8>>` (`24` bytes header, element stride `24`, align `8`) -/

/-- Heap buffer of `Vec<Vec<u8>>` (element stride `24`, align `8`) detached from its 24-byte `vecHeader`. -/
def vecVecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bss : List (List (BitVec 8))) : SepProp :=
  vecBuf A 24 8 (fun bs addr => rustBytesVecAt A addr bs) cap ptr bss

/-- Pinned `Vec<Vec<u8>>` at `v` (24-byte header `{cap, ptr, len}`, element stride `24`, align `8`). -/
def vecVecU8PinnedAt (A : RustAlloc) (pin : VecPin) (v : BitVec 64)
    (bss : List (List (BitVec 8))) : SepProp :=
  vecAt A 24 8 (fun bs addr => rustBytesVecAt A addr bs) v pin.cap pin.ptr bss

/-- Unpinned `Vec<Vec<u8>>` at `v` (24-byte header `{cap, ptr, len}`, element stride `24`, align `8`). -/
def vecVecU8At (A : RustAlloc) (v : BitVec 64) (bss : List (List (BitVec 8))) : SepProp :=
  vecOf A 24 8 (fun bs addr => rustBytesVecAt A addr bs) v bss

theorem vecVecU8PinnedAt_eq_header_buf (A : RustAlloc) (pin : VecPin) (h : BitVec 64)
    (bss : List (List (BitVec 8))) :
    vecVecU8PinnedAt A pin h bss =
      (h ↦₆₄ pin.cap) ∗ ((h + 8#64) ↦₆₄ pin.ptr) ∗ ((h + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
        vecVecU8Buf A pin.cap pin.ptr bss := by
  simp only [vecVecU8PinnedAt, vecAt, vecHeader, vecVecU8Buf, sepConj_assoc]

theorem vecVecU8Buf_eq_of_ne_zero {A : RustAlloc} {cap ptr : BitVec 64} {bss : List (List (BitVec 8))}
    (hcap : cap ≠ 0) :
    vecVecU8Buf A cap ptr bss =
      arrayAt (fun bs addr => rustBytesVecAt A addr bs) 24 ptr bss ∗
        (⌜bss.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          A.live ptr (cap.toNat * 24) 8 ∗
          memRegion (ptr + BitVec.ofNat 64 (bss.length * 24)) ((cap.toNat - bss.length) * 24)) := by
  unfold vecVecU8Buf vecBuf
  simp only [hcap, ↓reduceIte]
  ac_rfl

theorem vecVecU8Buf_bounds {A : RustAlloc} {cap ptr : BitVec 64} {bss : List (List (BitVec 8))}
    {R : SepProp} {m : Memory} (hm : m ⊨ vecVecU8Buf A cap ptr bss ∗ R) :
    bss.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 := by
  unfold vecVecU8Buf vecBuf at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact ⟨hm.1.1, hm.1.2.1⟩

theorem ofNat_vecVec_length_beq_zero_of_lt {bss : List (List (BitVec 8))} (hlt : bss.length < 2 ^ 64) :
    (BitVec.ofNat 64 bss.length == 0#64) = bss.isEmpty ∧
      (BitVec.ofNat 64 bss.length != 0#64) = !bss.isEmpty := by
  cases bss with
  | nil => exact ⟨rfl, rfl⟩
  | cons bs rest =>
    simp only [List.isEmpty_cons, Bool.not_false]
    have hne : BitVec.ofNat 64 (bs :: rest).length ≠ 0#64 := by
      intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h1
      rw [Nat.mod_eq_of_lt hlt] at h1
      simp only [List.length_cons] at h1
      omega
    exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

/-- Remainder of an element `rustBytesVecAt A p bs` (`cap` at `p`, `ptr` at `p + 8`, and heap buffer)
    detached from its `.len` word at `p + 16#64`. -/
def vecU8ElemRest (A : RustAlloc) (p : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    (p ↦₆₄ cap) ∗ ((p + 8#64) ↦₆₄ ptr) ∗ vecU8Buf A cap ptr bs

theorem rustBytesVecAt_eq_len_sep_rest (A : RustAlloc) (p : BitVec 64) (bs : List (BitVec 8)) :
    rustBytesVecAt A p bs =
      ((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8ElemRest A p bs := by
  simp only [rustBytesVecAt, vecU8, vecU8At_eq_header_sep_buf, vecHeader, vecU8ElemRest,
    sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr =>
      Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl)))
  · exact Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr =>
      Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl)))

theorem vecVecU8At_eq_exists_pin (A : RustAlloc) (v : BitVec 64) (bss : List (List (BitVec 8))) :
    vecVecU8At A v bss = ∃∗ pin : VecPin, vecVecU8PinnedAt A pin v bss := by
  unfold vecVecU8At vecVecU8PinnedAt vecOf
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun c => Entails.sepExists_elim fun p =>
      Entails.sepExists_right ⟨c, p⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨c, p⟩ =>
      Entails.sepExists_right c (Entails.sepExists_right p (Entails.refl _))

/-! ## 2. `PolynomialDecoder` (`40` bytes = `0x28`, align `8`) and `Option<PolynomialDecoder>` -/

/-- Rust ABI `bool` byte encoding (`1#8` for `true`, `0#8` for `false`). -/
def boolByte (b : Bool) : BitVec 8 :=
  if b then 1#8 else 0#8

/-- Ghost `(cap, ptr)` pin for `pts: Vec<Vec<u8>>` of a `PolynomialDecoder` (`40` bytes). -/
structure PolynomialDecoderPBGhost where
  /-- Pin for `pts: Vec<Vec<u8>>` at `+0x00` (tag 3). -/
  pts : VecPin

/-- Pinned `spqr::proto::pq_ratchet::PolynomialDecoder` at `a` (`40` bytes = `0x28`, align `8`):
    * `a + 0x00`: `pts: Vec<Vec<u8>>` (tag 3, 24B)
    * `a + 0x18` (`24`): `pts_needed: u32` (tag 1, 4B)
    * `a + 0x1c` (`28`): `polys: u32` (tag 2, 4B)
    * `a + 0x20` (`32`): `is_complete: bool` (tag 4, 1B, `boolByte pb.isComplete`)
    * `a + 0x21` (`33`): 7 bytes trailing padding (`memRegion (a + 33#64) 7`) -/
def polynomialDecoderPBPinnedAt (A : RustAlloc) (g : PolynomialDecoderPBGhost)
    (a : BitVec 64) (pb : PolynomialDecoder) : SepProp :=
  vecVecU8PinnedAt A g.pts a pb.pts ∗
    ((a + 24#64) ↦₃₂ pb.ptsNeeded) ∗
    ((a + 28#64) ↦₃₂ pb.polys) ∗
    ((a + 32#64) ↦₈ boolByte pb.isComplete) ∗
    memRegion (a + 33#64) 7

/-- Unpinned `spqr::proto::pq_ratchet::PolynomialDecoder` at `a` (`40` bytes = `0x28`, align `8`). -/
def polynomialDecoderPBAt (A : RustAlloc) (a : BitVec 64) (pb : PolynomialDecoder) : SepProp :=
  vecVecU8At A a pb.pts ∗
    ((a + 24#64) ↦₃₂ pb.ptsNeeded) ∗
    ((a + 28#64) ↦₃₂ pb.polys) ∗
    ((a + 32#64) ↦₈ boolByte pb.isComplete) ∗
    memRegion (a + 33#64) 7

/-- Pinned `Option<spqr::proto::pq_ratchet::PolynomialDecoder>` at `a` (`40` bytes = `0x28`, align `8`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 32` (`pts.cap = usize::MAX` niche)
    * `some pb`: `polynomialDecoderPBPinnedAt A g a pb` -/
def optPolynomialDecoderPBPinnedAt (A : RustAlloc) (g : PolynomialDecoderPBGhost)
    (a : BitVec 64) : Option PolynomialDecoder → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 32
  | some pb => polynomialDecoderPBPinnedAt A g a pb

/-- Unpinned `Option<spqr::proto::pq_ratchet::PolynomialDecoder>` at `a` (`40` bytes = `0x28`, align `8`). -/
def optPolynomialDecoderPBAt (A : RustAlloc) (a : BitVec 64) :
    Option PolynomialDecoder → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 32
  | some pb => polynomialDecoderPBAt A a pb

private theorem sepExists_const {α : Sort _} (a₀ : α) (P : SepProp) :
    (∃∗ _ : α, P) = P := by
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun _ => Entails.refl _
  · exact Entails.sepExists_right a₀ (Entails.refl _)

theorem polynomialDecoderPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (pb : PolynomialDecoder) :
    polynomialDecoderPBAt A a pb =
      ∃∗ g : PolynomialDecoderPBGhost, polynomialDecoderPBPinnedAt A g a pb := by
  simp only [polynomialDecoderPBAt, polynomialDecoderPBPinnedAt, vecVecU8At_eq_exists_pin,
    sepExists_sepConj_left]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun p1 => Entails.sepExists_right ⟨p1⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨p1⟩ => Entails.sepExists_right p1 (Entails.refl _)

theorem optPolynomialDecoderPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option PolynomialDecoder) :
    optPolynomialDecoderPBAt A a opt =
      ∃∗ g : PolynomialDecoderPBGhost, optPolynomialDecoderPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    simp only [optPolynomialDecoderPBAt, optPolynomialDecoderPBPinnedAt]
    exact (sepExists_const ⟨⟨0, 0⟩⟩ _).symm
  | some pb =>
    exact polynomialDecoderPBAt_eq_exists_pinned A a pb

/-! ## 3. `PolynomialEncoder` (`56` bytes = `0x38`, align `8`) and `Option<PolynomialEncoder>` -/

/-- Ghost `(cap, ptr)` pins for `pts: Vec<Vec<u8>>` and `polys: Vec<Vec<u8>>` of a
    `PolynomialEncoder` (`56` bytes). -/
structure PolynomialEncoderPBGhost where
  /-- Pin for `pts: Vec<Vec<u8>>` at `+0x00` (tag 2). -/
  pts : VecPin
  /-- Pin for `polys: Vec<Vec<u8>>` at `+0x18` (tag 3). -/
  polys : VecPin

/-- Pinned `spqr::proto::pq_ratchet::PolynomialEncoder` at `a` (`56` bytes = `0x38`, align `8`):
    * `a + 0x00`: `pts: Vec<Vec<u8>>` (tag 2, 24B)
    * `a + 0x18` (`24`): `polys: Vec<Vec<u8>>` (tag 3, 24B)
    * `a + 0x30` (`48`): `idx: u32` (tag 1, 4B)
    * `a + 0x34` (`52`): 4 bytes trailing padding (`memRegion (a + 52#64) 4`) -/
def polynomialEncoderPBPinnedAt (A : RustAlloc) (g : PolynomialEncoderPBGhost)
    (a : BitVec 64) (pb : PolynomialEncoder) : SepProp :=
  vecVecU8PinnedAt A g.pts a pb.pts ∗
    vecVecU8PinnedAt A g.polys (a + 24#64) pb.polys ∗
    ((a + 48#64) ↦₃₂ pb.idx) ∗
    memRegion (a + 52#64) 4

/-- Unpinned `spqr::proto::pq_ratchet::PolynomialEncoder` at `a` (`56` bytes = `0x38`, align `8`). -/
def polynomialEncoderPBAt (A : RustAlloc) (a : BitVec 64) (pb : PolynomialEncoder) : SepProp :=
  vecVecU8At A a pb.pts ∗
    vecVecU8At A (a + 24#64) pb.polys ∗
    ((a + 48#64) ↦₃₂ pb.idx) ∗
    memRegion (a + 52#64) 4

/-- Pinned `Option<spqr::proto::pq_ratchet::PolynomialEncoder>` at `a` (`56` bytes = `0x38`, align `8`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48` (`pts.cap = usize::MAX` niche)
    * `some pb`: `polynomialEncoderPBPinnedAt A g a pb` -/
def optPolynomialEncoderPBPinnedAt (A : RustAlloc) (g : PolynomialEncoderPBGhost)
    (a : BitVec 64) : Option PolynomialEncoder → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48
  | some pb => polynomialEncoderPBPinnedAt A g a pb

/-- Unpinned `Option<spqr::proto::pq_ratchet::PolynomialEncoder>` at `a` (`56` bytes = `0x38`, align `8`). -/
def optPolynomialEncoderPBAt (A : RustAlloc) (a : BitVec 64) :
    Option PolynomialEncoder → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48
  | some pb => polynomialEncoderPBAt A a pb

theorem polynomialEncoderPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (pb : PolynomialEncoder) :
    polynomialEncoderPBAt A a pb =
      ∃∗ g : PolynomialEncoderPBGhost, polynomialEncoderPBPinnedAt A g a pb := by
  simp only [polynomialEncoderPBAt, polynomialEncoderPBPinnedAt, vecVecU8At_eq_exists_pin,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun p2 => Entails.sepExists_elim fun p1 =>
      Entails.sepExists_right ⟨p1, p2⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨p1, p2⟩ =>
      Entails.sepExists_right p2 (Entails.sepExists_right p1 (Entails.refl _))

theorem optPolynomialEncoderPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option PolynomialEncoder) :
    optPolynomialEncoderPBAt A a opt =
      ∃∗ g : PolynomialEncoderPBGhost, optPolynomialEncoderPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    simp only [optPolynomialEncoderPBAt, optPolynomialEncoderPBPinnedAt]
    exact (sepExists_const ⟨⟨0, 0⟩, ⟨0, 0⟩⟩ _).symm
  | some pb =>
    exact polynomialEncoderPBAt_eq_exists_pinned A a pb

/-! ## 4. `Option<Unchunked.Ct1Sent>` (`128`B) and `Option<Unchunked.EkSent>` (`80`B) -/

/-- Pinned `Option<V1State.Unchunked.Ct1Sent>` at `a` (`128` bytes = `0x80`, align `8`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120` (`hdr.cap = usize::MAX` niche at `+0x00`)
    * `some u`: `ct1SentPBPinnedAt A g a u` -/
def optCt1SentPBPinnedAt (A : RustAlloc) (g : Unchunked5PBGhost) (a : BitVec 64) :
    Option V1State.Unchunked.Ct1Sent → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120
  | some u => ct1SentPBPinnedAt A g a u

/-- Unpinned `Option<V1State.Unchunked.Ct1Sent>` at `a` (`128` bytes = `0x80`, align `8`). -/
def optCt1SentPBAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.Ct1Sent → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120
  | some u => ct1SentPBAt A a u

theorem optCt1SentPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.Ct1Sent) :
    optCt1SentPBAt A a opt =
      ∃∗ g : Unchunked5PBGhost, optCt1SentPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    simp only [optCt1SentPBAt, optCt1SentPBPinnedAt]
    exact (sepExists_const ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩ _).symm
  | some u =>
    exact unchunked5At_eq_exists_pinned A a u.epoch u.auth u.hdr u.es u.ct1

/-- Pinned `Option<V1State.Unchunked.EkSent>` at `a` (`80` bytes = `0x50`, align `8`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72` (`dk.cap = usize::MAX` niche at `+0x00`)
    * `some u`: `ekSentPBPinnedAt A g a u` -/
def optEkSentPBPinnedAt (A : RustAlloc) (g : Unchunked3PBGhost) (a : BitVec 64) :
    Option V1State.Unchunked.EkSent → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72
  | some u => ekSentPBPinnedAt A g a u

/-- Unpinned `Option<V1State.Unchunked.EkSent>` at `a` (`80` bytes = `0x50`, align `8`). -/
def optEkSentPBAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.EkSent → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72
  | some u => ekSentPBAt A a u

theorem optEkSentPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.EkSent) :
    optEkSentPBAt A a opt =
      ∃∗ g : Unchunked3PBGhost, optEkSentPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    simp only [optEkSentPBAt, optEkSentPBPinnedAt]
    exact (sepExists_const ⟨⟨0, 0⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩ _).symm
  | some u =>
    exact unchunked3At_eq_exists_pinned A a u.epoch u.auth u.dk

/-! ## 5. `V1State.Chunked.Ct1Sampled` (`224`B) and `V1State.Chunked.HeaderSent` (`176`B) -/

/-- Ghost pins for `V1State.Chunked.Ct1Sampled` (`224` bytes = `0xe0`, align `8`). -/
structure ChunkedCt1SampledPBGhost where
  /-- Pins for `uc: Option<Unchunked.Ct1Sent>` at `+0x00` (tag 1, 128B). -/
  uc : Unchunked5PBGhost
  /-- Pins for `sending_ct1: Option<PolynomialEncoder>` at `+0x80` (`128`, tag 2, 56B). -/
  sendingCt1 : PolynomialEncoderPBGhost
  /-- Pin for `receiving_ek: Option<PolynomialDecoder>` at `+0xb8` (`184`, tag 3, 40B). -/
  receivingEk : PolynomialDecoderPBGhost

/-- Pinned `spqr::proto::pq_ratchet::v1_state::chunked::Ct1Sampled` at `a` (`224` bytes = `0xe0`, align `8`):
    * `a + 0x00` (`0..128`): `uc: Option<Unchunked.Ct1Sent>` (tag 1, 128B)
    * `a + 0x80` (`128..184`): `sending_ct1: Option<PolynomialEncoder>` (tag 2, 56B)
    * `a + 0xb8` (`184..224`): `receiving_ek: Option<PolynomialDecoder>` (tag 3, 40B) -/
def chunkedCt1SampledPBPinnedAt (A : RustAlloc) (g : ChunkedCt1SampledPBGhost)
    (a : BitVec 64) (m : V1State.Chunked.Ct1Sampled) : SepProp :=
  optCt1SentPBPinnedAt A g.uc a m.uc ∗
    optPolynomialEncoderPBPinnedAt A g.sendingCt1 (a + 128#64) m.sendingCt1 ∗
    optPolynomialDecoderPBPinnedAt A g.receivingEk (a + 184#64) m.receivingEk

/-- Unpinned `spqr::proto::pq_ratchet::v1_state::chunked::Ct1Sampled` at `a` (`224` bytes = `0xe0`, align `8`). -/
def chunkedCt1SampledPBAt (A : RustAlloc) (a : BitVec 64) (m : V1State.Chunked.Ct1Sampled) : SepProp :=
  optCt1SentPBAt A a m.uc ∗
    optPolynomialEncoderPBAt A (a + 128#64) m.sendingCt1 ∗
    optPolynomialDecoderPBAt A (a + 184#64) m.receivingEk

theorem chunkedCt1SampledPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.Ct1Sampled) :
    chunkedCt1SampledPBAt A a m =
      ∃∗ g : ChunkedCt1SampledPBGhost, chunkedCt1SampledPBPinnedAt A g a m := by
  simp only [chunkedCt1SampledPBAt, chunkedCt1SampledPBPinnedAt,
    optCt1SentPBAt_eq_exists_pinned, optPolynomialEncoderPBAt_eq_exists_pinned,
    optPolynomialDecoderPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun g3 => Entails.sepExists_elim fun g2 =>
      Entails.sepExists_elim fun g1 => Entails.sepExists_right ⟨g1, g2, g3⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨g1, g2, g3⟩ =>
      Entails.sepExists_right g3 (Entails.sepExists_right g2 (Entails.sepExists_right g1 (Entails.refl _)))

/-- Ghost pins for `V1State.Chunked.HeaderSent` (`176` bytes = `0xb0`, align `8`). -/
structure ChunkedHeaderSentPBGhost where
  /-- Pins for `uc: Option<Unchunked.EkSent>` at `+0x00` (tag 1, 80B). -/
  uc : Unchunked3PBGhost
  /-- Pins for `sending_ek: Option<PolynomialEncoder>` at `+0x50` (`80`, tag 2, 56B). -/
  sendingEk : PolynomialEncoderPBGhost
  /-- Pin for `receiving_ct1: Option<PolynomialDecoder>` at `+0x88` (`136`, tag 3, 40B). -/
  receivingCt1 : PolynomialDecoderPBGhost

/-- Pinned `spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent` at `a` (`176` bytes = `0xb0`, align `8`):
    * `a + 0x00` (`0..80`): `uc: Option<Unchunked.EkSent>` (tag 1, 80B)
    * `a + 0x50` (`80..136`): `sending_ek: Option<PolynomialEncoder>` (tag 2, 56B)
    * `a + 0x88` (`136..176`): `receiving_ct1: Option<PolynomialDecoder>` (tag 3, 40B) -/
def chunkedHeaderSentPBPinnedAt (A : RustAlloc) (g : ChunkedHeaderSentPBGhost)
    (a : BitVec 64) (m : V1State.Chunked.HeaderSent) : SepProp :=
  optEkSentPBPinnedAt A g.uc a m.uc ∗
    optPolynomialEncoderPBPinnedAt A g.sendingEk (a + 80#64) m.sendingEk ∗
    optPolynomialDecoderPBPinnedAt A g.receivingCt1 (a + 136#64) m.receivingCt1

/-- Unpinned `spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent` at `a` (`176` bytes = `0xb0`, align `8`). -/
def chunkedHeaderSentPBAt (A : RustAlloc) (a : BitVec 64) (m : V1State.Chunked.HeaderSent) : SepProp :=
  optEkSentPBAt A a m.uc ∗
    optPolynomialEncoderPBAt A (a + 80#64) m.sendingEk ∗
    optPolynomialDecoderPBAt A (a + 136#64) m.receivingCt1

theorem chunkedHeaderSentPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.HeaderSent) :
    chunkedHeaderSentPBAt A a m =
      ∃∗ g : ChunkedHeaderSentPBGhost, chunkedHeaderSentPBPinnedAt A g a m := by
  simp only [chunkedHeaderSentPBAt, chunkedHeaderSentPBPinnedAt,
    optEkSentPBAt_eq_exists_pinned, optPolynomialEncoderPBAt_eq_exists_pinned,
    optPolynomialDecoderPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun g3 => Entails.sepExists_elim fun g2 =>
      Entails.sepExists_elim fun g1 => Entails.sepExists_right ⟨g1, g2, g3⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨g1, g2, g3⟩ =>
      Entails.sepExists_right g3 (Entails.sepExists_right g2 (Entails.sepExists_right g1 (Entails.refl _)))

/-! ## 6. Pure `encodedLen` Models & `LibsignalSpqrV1.Proto` Bridge Lemmas -/

/-- Proto3 encoded length of a `bool` field with a 1-byte tag (`tag ∈ 1..15`):
    `2` when `v = true`, `0` when `v = false`. -/
def boolFieldEncodedLen (v : Bool) : Nat :=
  if v then 2 else 0

/-- Per-element body length (without 1-byte tag) of `bs : List (BitVec 8)` in a repeated `bytes` field:
    `bs.length + varintLen (BitVec.ofNat 64 bs.length)`. -/
def bytesElemBodyEncodedLen (bs : List (BitVec 8)) : Nat :=
  bs.length + varintLen (BitVec.ofNat 64 bs.length)

/-- Sum of `bytesElemBodyEncodedLen` over `vs : List (List (BitVec 8))`. -/
def repeatedBytesBodiesEncodedLen (vs : List (List (BitVec 8))) : Nat :=
  vs.foldl (fun acc bs => acc + bytesElemBodyEncodedLen bs) 0

/-- Proto3 encoded length of a `repeated bytes` (`Vec<Vec<u8>>`) field with a 1-byte tag (`tag ∈ 1..15`):
    `repeatedBytesBodiesEncodedLen vs + vs.length`. -/
def repeatedBytesFieldEncodedLen (vs : List (List (BitVec 8))) : Nat :=
  repeatedBytesBodiesEncodedLen vs + vs.length

private theorem foldl_bytesElemBody_add (init : Nat) (vs : List (List (BitVec 8))) :
    vs.foldl (fun acc bs => acc + bytesElemBodyEncodedLen bs) init =
      init + vs.foldl (fun acc bs => acc + bytesElemBodyEncodedLen bs) 0 := by
  induction vs generalizing init with
  | nil => simp
  | cons bs rest ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (init + bytesElemBodyEncodedLen bs), ih (bytesElemBodyEncodedLen bs)]
    omega

theorem repeatedBytesBodiesEncodedLen_cons (bs : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    repeatedBytesBodiesEncodedLen (bs :: rest) =
      bytesElemBodyEncodedLen bs + repeatedBytesBodiesEncodedLen rest := by
  unfold repeatedBytesBodiesEncodedLen
  simp only [List.foldl_cons, Nat.zero_add]
  exact foldl_bytesElemBody_add (bytesElemBodyEncodedLen bs) rest

private theorem protoEncodeKey_len_one (tag : BitVec 32) (wt : Proto.WireType)
    (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeKey tag wt).length = 1 := by
  have hlt : ((tag <<< 3) ||| wt.toU32).zeroExtend 64 < 0x80#64 := by
    rcases htag with ⟨_, h2⟩
    cases wt <;> dsimp [Proto.WireType.toU32] <;> bv_bits
  dsimp only [Proto.encodeKey, Proto.encodeVarint, Proto.encodeVarintAux]
  split
  · rfl
  · contradiction

theorem boolFieldEncodedLen_eq_proto (tag : BitVec 32) (v : Bool)
    (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeBoolField tag v).length = boolFieldEncodedLen v := by
  unfold Proto.encodeBoolField boolFieldEncodedLen
  cases v
  · rfl
  · simp only [↓reduceIte, List.length_append, List.length_singleton,
      protoEncodeKey_len_one tag .varint htag]

theorem repeatedBytesFieldEncodedLen_eq_proto (tag : BitVec 32) (vs : List (List (BitVec 8)))
    (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeRepeatedBytes tag vs).length = repeatedBytesFieldEncodedLen vs := by
  unfold repeatedBytesFieldEncodedLen
  induction vs with
  | nil => rfl
  | cons bs rest ih =>
    change (Proto.encodeBytesUncond tag bs ++ Proto.encodeRepeatedBytes tag rest).length =
      repeatedBytesBodiesEncodedLen (bs :: rest) + (bs :: rest).length
    rw [List.length_append, List.length_cons, repeatedBytesBodiesEncodedLen_cons, ih]
    unfold Proto.encodeBytesUncond bytesElemBodyEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]
    omega

/-- Encoded length of `spqr::proto::pq_ratchet::PolynomialDecoder`:
    tag 1 `pts_needed: u32` + tag 2 `polys: u32` + tag 3 `pts: Vec<Vec<u8>>` + tag 4 `is_complete: bool`. -/
def polynomialDecoderPBEncodedLen (pb : PolynomialDecoder) : Nat :=
  u32VarintFieldEncodedLen pb.ptsNeeded +
    u32VarintFieldEncodedLen pb.polys +
    repeatedBytesFieldEncodedLen pb.pts +
    boolFieldEncodedLen pb.isComplete

/-- Encoded length of an optional `PolynomialDecoder` field with a 1-byte tag (`tag ∈ 1..15`). -/
def optPolynomialDecoderPBFieldEncodedLen : Option PolynomialDecoder → Nat
  | none => 0
  | some pb =>
    let len := polynomialDecoderPBEncodedLen pb
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem polynomialDecoderPBEncodedLen_eq_proto (pb : PolynomialDecoder) :
    PolynomialDecoder.encodedLen pb = polynomialDecoderPBEncodedLen pb := by
  unfold PolynomialDecoder.encodedLen PolynomialDecoder.encodeRaw polynomialDecoderPBEncodedLen
  simp only [List.length_append,
    u32VarintFieldEncodedLen_eq_proto 1#32 pb.ptsNeeded ⟨by decide, by decide⟩,
    u32VarintFieldEncodedLen_eq_proto 2#32 pb.polys ⟨by decide, by decide⟩,
    repeatedBytesFieldEncodedLen_eq_proto 3#32 pb.pts ⟨by decide, by decide⟩,
    boolFieldEncodedLen_eq_proto 4#32 pb.isComplete ⟨by decide, by decide⟩]

theorem optPolynomialDecoderPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option PolynomialDecoder) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage PolynomialDecoder.encodeRaw tag opt).length =
      optPolynomialDecoderPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some pb =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optPolynomialDecoderPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← polynomialDecoderPBEncodedLen_eq_proto, PolynomialDecoder.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-- Encoded length of `spqr::proto::pq_ratchet::PolynomialEncoder`:
    tag 1 `idx: u32` + tag 2 `pts: Vec<Vec<u8>>` + tag 3 `polys: Vec<Vec<u8>>`. -/
def polynomialEncoderPBEncodedLen (pb : PolynomialEncoder) : Nat :=
  u32VarintFieldEncodedLen pb.idx +
    repeatedBytesFieldEncodedLen pb.pts +
    repeatedBytesFieldEncodedLen pb.polys

/-- Encoded length of an optional `PolynomialEncoder` field with a 1-byte tag (`tag ∈ 1..15`). -/
def optPolynomialEncoderPBFieldEncodedLen : Option PolynomialEncoder → Nat
  | none => 0
  | some pb =>
    let len := polynomialEncoderPBEncodedLen pb
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem polynomialEncoderPBEncodedLen_eq_proto (pb : PolynomialEncoder) :
    PolynomialEncoder.encodedLen pb = polynomialEncoderPBEncodedLen pb := by
  unfold PolynomialEncoder.encodedLen PolynomialEncoder.encodeRaw polynomialEncoderPBEncodedLen
  simp only [List.length_append,
    u32VarintFieldEncodedLen_eq_proto 1#32 pb.idx ⟨by decide, by decide⟩,
    repeatedBytesFieldEncodedLen_eq_proto 2#32 pb.pts ⟨by decide, by decide⟩,
    repeatedBytesFieldEncodedLen_eq_proto 3#32 pb.polys ⟨by decide, by decide⟩]

theorem optPolynomialEncoderPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option PolynomialEncoder) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage PolynomialEncoder.encodeRaw tag opt).length =
      optPolynomialEncoderPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some pb =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optPolynomialEncoderPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← polynomialEncoderPBEncodedLen_eq_proto, PolynomialEncoder.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-- Encoded length of an optional `Unchunked.Ct1Sent` field with a 1-byte tag (`tag ∈ 1..15`). -/
def optCt1SentPBFieldEncodedLen : Option V1State.Unchunked.Ct1Sent → Nat
  | none => 0
  | some u =>
    let len := ct1SentPBEncodedLen u
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem optCt1SentPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option V1State.Unchunked.Ct1Sent) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw tag opt).length =
      optCt1SentPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some u =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optCt1SentPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← ct1SentPBEncodedLen_eq_proto, V1State.Unchunked.Ct1Sent.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-- Encoded length of an optional `Unchunked.EkSent` field with a 1-byte tag (`tag ∈ 1..15`). -/
def optEkSentPBFieldEncodedLen : Option V1State.Unchunked.EkSent → Nat
  | none => 0
  | some u =>
    let len := ekSentPBEncodedLen u
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem optEkSentPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option V1State.Unchunked.EkSent) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage V1State.Unchunked.EkSent.encodeRaw tag opt).length =
      optEkSentPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some u =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optEkSentPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← ekSentPBEncodedLen_eq_proto, V1State.Unchunked.EkSent.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-- Encoded length of `V1State.Chunked.Ct1Sampled`:
    tag 1 `uc: Option<Unchunked.Ct1Sent>` + tag 2 `sending_ct1: Option<PolynomialEncoder>` +
    tag 3 `receiving_ek: Option<PolynomialDecoder>`. -/
def chunkedCt1SampledPBEncodedLen (m : V1State.Chunked.Ct1Sampled) : Nat :=
  optCt1SentPBFieldEncodedLen m.uc +
    optPolynomialEncoderPBFieldEncodedLen m.sendingCt1 +
    optPolynomialDecoderPBFieldEncodedLen m.receivingEk

theorem chunkedCt1SampledPBEncodedLen_eq_proto (m : V1State.Chunked.Ct1Sampled) :
    V1State.Chunked.Ct1Sampled.encodedLen m = chunkedCt1SampledPBEncodedLen m := by
  unfold V1State.Chunked.Ct1Sampled.encodedLen V1State.Chunked.Ct1Sampled.encodeRaw
    chunkedCt1SampledPBEncodedLen
  simp only [List.length_append,
    optCt1SentPBFieldEncodedLen_eq_proto 1#32 m.uc ⟨by decide, by decide⟩,
    optPolynomialEncoderPBFieldEncodedLen_eq_proto 2#32 m.sendingCt1 ⟨by decide, by decide⟩,
    optPolynomialDecoderPBFieldEncodedLen_eq_proto 3#32 m.receivingEk ⟨by decide, by decide⟩]

/-- Encoded length of `V1State.Chunked.HeaderSent`:
    tag 1 `uc: Option<Unchunked.EkSent>` + tag 2 `sending_ek: Option<PolynomialEncoder>` +
    tag 3 `receiving_ct1: Option<PolynomialDecoder>`. -/
def chunkedHeaderSentPBEncodedLen (m : V1State.Chunked.HeaderSent) : Nat :=
  optEkSentPBFieldEncodedLen m.uc +
    optPolynomialEncoderPBFieldEncodedLen m.sendingEk +
    optPolynomialDecoderPBFieldEncodedLen m.receivingCt1

theorem chunkedHeaderSentPBEncodedLen_eq_proto (m : V1State.Chunked.HeaderSent) :
    V1State.Chunked.HeaderSent.encodedLen m = chunkedHeaderSentPBEncodedLen m := by
  unfold V1State.Chunked.HeaderSent.encodedLen V1State.Chunked.HeaderSent.encodeRaw
    chunkedHeaderSentPBEncodedLen
  simp only [List.length_append,
    optEkSentPBFieldEncodedLen_eq_proto 1#32 m.uc ⟨by decide, by decide⟩,
    optPolynomialEncoderPBFieldEncodedLen_eq_proto 2#32 m.sendingEk ⟨by decide, by decide⟩,
    optPolynomialDecoderPBFieldEncodedLen_eq_proto 3#32 m.receivingCt1 ⟨by decide, by decide⟩]

/-! ## 7. Symbol Names, Stack Budgets, and Hoare `Spec`s -/

abbrev polynomialDecoderEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#1]"
abbrev polynomialDecoderEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#2]"

abbrev polynomialEncoderEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#1]"
abbrev polynomialEncoderEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#2]"

abbrev chunkedCt1SampledEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Sampled as prost::message::Message>::encoded_len [local#1]"
abbrev chunkedCt1SampledEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Sampled as prost::message::Message>::encoded_len [local#2]"

abbrev chunkedHeaderSentEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent as prost::message::Message>::encoded_len [local#1]"
abbrev chunkedHeaderSentEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent as prost::message::Message>::encoded_len [local#2]"

/-- Stack budget for `PolynomialDecoder::encoded_len` and `PolynomialEncoder::encoded_len` (`0x10` bytes). -/
abbrev polyEncodedLenStack : Nat := 0x10

/-- Own stack frame of `chunked::Ct1Sampled::encoded_len` and `chunked::HeaderSent::encoded_len` (`0x20` bytes). -/
abbrev chunkedEncodedLenFrame : Nat := 0x20

/-- Total stack budget for `chunked::Ct1Sampled::encoded_len` and `chunked::HeaderSent::encoded_len`:
    own `0x20`-byte frame plus `0x10` bytes for leaf callees (`0x30` bytes). -/
abbrev chunkedEncodedLenStack : Nat := chunkedEncodedLenFrame + polyEncodedLenStack

abbrev PolynomialDecoderEncodedLenPinnedGhost := PinnedEncLenGhost PolynomialDecoderPBGhost PolynomialDecoder
abbrev PolynomialDecoderEncodedLenGhost := UnpinnedEncLenGhost PolynomialDecoder

def polynomialDecoderEncodedLenPinnedSpec (A : RustAlloc) : Spec PolynomialDecoderEncodedLenPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ polynomialDecoderPBEncodedLen x.m < 2 ^ 64⌝ ∗
      polynomialDecoderPBPinnedAt A x.g x.a x.m ∗ stackAt s.sp polyEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialDecoderPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      polynomialDecoderPBPinnedAt A x.g x.a x.m ∗ stackAt s0.sp polyEncodedLenStack

def polynomialDecoderEncodedLenSpec (A : RustAlloc) : Spec PolynomialDecoderEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ polynomialDecoderPBEncodedLen x.m < 2 ^ 64⌝ ∗
      polynomialDecoderPBAt A x.a x.m ∗ stackAt s.sp polyEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialDecoderPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      polynomialDecoderPBAt A x.a x.m ∗ stackAt s0.sp polyEncodedLenStack

abbrev PolynomialEncoderEncodedLenPinnedGhost := PinnedEncLenGhost PolynomialEncoderPBGhost PolynomialEncoder
abbrev PolynomialEncoderEncodedLenGhost := UnpinnedEncLenGhost PolynomialEncoder

def polynomialEncoderEncodedLenPinnedSpec (A : RustAlloc) : Spec PolynomialEncoderEncodedLenPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ polynomialEncoderPBEncodedLen x.m < 2 ^ 64⌝ ∗
      polynomialEncoderPBPinnedAt A x.g x.a x.m ∗ stackAt s.sp polyEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialEncoderPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      polynomialEncoderPBPinnedAt A x.g x.a x.m ∗ stackAt s0.sp polyEncodedLenStack

def polynomialEncoderEncodedLenSpec (A : RustAlloc) : Spec PolynomialEncoderEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ polynomialEncoderPBEncodedLen x.m < 2 ^ 64⌝ ∗
      polynomialEncoderPBAt A x.a x.m ∗ stackAt s.sp polyEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialEncoderPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      polynomialEncoderPBAt A x.a x.m ∗ stackAt s0.sp polyEncodedLenStack

abbrev ChunkedCt1SampledEncodedLenPinnedGhost := PinnedEncLenGhost ChunkedCt1SampledPBGhost V1State.Chunked.Ct1Sampled
abbrev ChunkedCt1SampledEncodedLenGhost := UnpinnedEncLenGhost V1State.Chunked.Ct1Sampled

def chunkedCt1SampledEncodedLenPinnedSpec (A : RustAlloc) : Spec ChunkedCt1SampledEncodedLenPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ chunkedCt1SampledPBEncodedLen x.m < 2 ^ 64⌝ ∗
      chunkedCt1SampledPBPinnedAt A x.g x.a x.m ∗ stackAt s.sp chunkedEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      chunkedCt1SampledPBPinnedAt A x.g x.a x.m ∗ stackAt s0.sp chunkedEncodedLenStack

def chunkedCt1SampledEncodedLenSpec (A : RustAlloc) : Spec ChunkedCt1SampledEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ chunkedCt1SampledPBEncodedLen x.m < 2 ^ 64⌝ ∗
      chunkedCt1SampledPBAt A x.a x.m ∗ stackAt s.sp chunkedEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      chunkedCt1SampledPBAt A x.a x.m ∗ stackAt s0.sp chunkedEncodedLenStack

abbrev ChunkedHeaderSentEncodedLenPinnedGhost := PinnedEncLenGhost ChunkedHeaderSentPBGhost V1State.Chunked.HeaderSent
abbrev ChunkedHeaderSentEncodedLenGhost := UnpinnedEncLenGhost V1State.Chunked.HeaderSent

def chunkedHeaderSentEncodedLenPinnedSpec (A : RustAlloc) : Spec ChunkedHeaderSentEncodedLenPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ chunkedHeaderSentPBEncodedLen x.m < 2 ^ 64⌝ ∗
      chunkedHeaderSentPBPinnedAt A x.g x.a x.m ∗ stackAt s.sp chunkedEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (chunkedHeaderSentPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      chunkedHeaderSentPBPinnedAt A x.g x.a x.m ∗ stackAt s0.sp chunkedEncodedLenStack

def chunkedHeaderSentEncodedLenSpec (A : RustAlloc) : Spec ChunkedHeaderSentEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ chunkedHeaderSentPBEncodedLen x.m < 2 ^ 64⌝ ∗
      chunkedHeaderSentPBAt A x.a x.m ∗ stackAt s.sp chunkedEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (chunkedHeaderSentPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      chunkedHeaderSentPBAt A x.a x.m ∗ stackAt s0.sp chunkedEncodedLenStack

end CryptoVerification.SpqrV1.ProtoRepr
