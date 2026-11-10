/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedRepr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPoly
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Drop Glue for Protobuf Chunked States (`Ct1Received`, `NoHeaderReceived`)

**Checked by Lean.**

Representation predicates and specifications for all five
`spqr::proto::pq_ratchet::v1_state::chunked::*` drop-glue types, together with subroutine proofs
for:
- `core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>` (`0x4cb70`, Block `282`)
- `core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>` (`0x4cce4`, Block `284`)
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L14

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option hygiene false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## Representation Predicates for `V1State.Chunked.*` -/

def protoChunkedCt1ReceivedSize : Nat := 160

/-- `spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received` at `a` (`160` bytes = `0xa0`, align `8`):
    * `+0..+104`: `uc: Option<V1State.Unchunked.EkSentCt1Received>` (`104`B)
    * `+104..+160`: `sending_ek: Option<PolynomialEncoder>` (`56`B) -/
def protoChunkedCt1ReceivedAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Chunked.Ct1Received) : SepProp :=
  optProtoUnchunkedEkSentCt1ReceivedAt A a st.uc ∗
    optProtoPolynomialEncoderAt A (a + 104#64) (st.sendingEk.map pbToProtoPolyEncoder)

def protoChunkedNoHeaderReceivedSize : Nat := 96

/-- `spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived` at `a` (`96` bytes = `0x60`, align `8`):
    * `+0..+40`: `receiving_hdr: Option<PolynomialDecoder>` (`40`B)
    * `+40..+96`: `uc: Option<V1State.Unchunked.NoHeaderReceived>` (`56`B) -/
def protoChunkedNoHeaderReceivedAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Chunked.NoHeaderReceived) : SepProp :=
  optProtoPolynomialDecoderAt A a (st.receivingHdr.map pbToProtoPolyDecoder) ∗
    optProtoUnchunkedNoHeaderReceivedAt A (a + 40#64) st.uc

def protoChunkedHeaderReceivedSize : Nat := 120

/-- `spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived` at `a` (`120` bytes = `0x78`, align `8`):
    * `+0..+80`: `uc: Option<V1State.Unchunked.HeaderReceived>` (`80`B)
    * `+80..+120`: `receiving_ek: Option<PolynomialDecoder>` (`40`B) -/
def protoChunkedHeaderReceivedAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Chunked.HeaderReceived) : SepProp :=
  optProtoUnchunkedHeaderReceivedAt A a st.uc ∗
    optProtoPolynomialDecoderAt A (a + 80#64) (st.receivingEk.map pbToProtoPolyDecoder)

def protoChunkedEkSentCt1ReceivedSize : Nat := 144

/-- `spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received` at `a` (`144` bytes = `0x90`, align `8`):
    * `+0..+104`: `uc: Option<V1State.Unchunked.EkSentCt1Received>` (`104`B)
    * `+104..+144`: `receiving_ct2: Option<PolynomialDecoder>` (`40`B) -/
def protoChunkedEkSentCt1ReceivedAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Chunked.EkSentCt1Received) : SepProp :=
  optProtoUnchunkedEkSentCt1ReceivedAt A a st.uc ∗
    optProtoPolynomialDecoderAt A (a + 104#64) (st.receivingCt2.map pbToProtoPolyDecoder)

def protoChunkedHeaderSentSize : Nat := 176

/-- `spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent` at `a` (`176` bytes = `0xb0`, align `8`):
    * `+0..+80`: `uc: Option<V1State.Unchunked.EkSent>` (`80`B)
    * `+80..+136`: `sending_ek: Option<PolynomialEncoder>` (`56`B)
    * `+136..+176`: `receiving_ct1: Option<PolynomialDecoder>` (`40`B) -/
def protoChunkedHeaderSentAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Chunked.HeaderSent) : SepProp :=
  optProtoUnchunkedEkSentAt A a st.uc ∗
    optProtoPolynomialEncoderAt A (a + 80#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
    optProtoPolynomialDecoderAt A (a + 136#64) (st.receivingCt1.map pbToProtoPolyDecoder)

/-! ## `ProtoPolynomialEncoder` and `ProtoPolynomialDecoder` Deallocation Helpers -/

@[simp]
theorem optProtoPolynomialEncoderAt_none' (A : RustAlloc) (d : BitVec 64) :
    optProtoPolynomialEncoderAt A d none =
      ((d ↦₆₄ noneCap) ∗ memRegion (d + 8#64) 48) := rfl

@[simp]
theorem optProtoPolynomialEncoderAt_some' (A : RustAlloc) (d : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    optProtoPolynomialEncoderAt A d (some pb) = protoPolynomialEncoderAt A d pb := rfl

@[simp]
theorem optProtoPolynomialDecoderAt_none' (A : RustAlloc) (d : BitVec 64) :
    optProtoPolynomialDecoderAt A d none =
      ((d ↦₆₄ noneCap) ∗ memRegion (d + 8#64) 32) := rfl

@[simp]
theorem optProtoPolynomialDecoderAt_some' (A : RustAlloc) (d : BitVec 64)
    (pb : ProtoPolynomialDecoder) :
    optProtoPolynomialDecoderAt A d (some pb) = protoPolynomialDecoderAt A d pb := rfl

/-- Remainder of `protoPolynomialEncoderAt A d pb` when the initial `pts.cap` cell `d ↦₆₄ cap` is split out. -/
def protoPolynomialEncoderRestAt (A : RustAlloc) (d cap ptr : BitVec 64)
    (pb : ProtoPolynomialEncoder) : SepProp :=
  ((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) cap ptr pb.pts ∗
    vecVecU8At A (d + protoPolynomialEncoderPolysOff) pb.polys ∗
    ((d + protoPolynomialEncoderIdxOff) ↦₃₂ pb.idx) ∗
    memRegion (d + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize

theorem protoPolynomialEncoderAt_expose_cap (A : RustAlloc) (d : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    protoPolynomialEncoderAt A d pb ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat < 2 ^ 63⌝ ∗
        (d ↦₆₄ cap) ∗
        protoPolynomialEncoderRestAt A d cap ptr pb := by
  unfold protoPolynomialEncoderAt
  nth_rw 1 [vecVecU8At]
  unfold vecOf
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold protoPolynomialEncoderRestAt vecAt vecHeader vecBuf
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜pb.pts.length ≤ cap.toNat ∧ cap.toNat * vecHeaderBytes < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((d ↦₆₄ cap) ∗
        (((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * vecHeaderBytes) 8 ∗
             arrayAt (fun bs addr => vecU8 A addr bs) vecHeaderBytes ptr pb.pts ∗
             memRegion (ptr + BitVec.ofNat 64 (pb.pts.length * vecHeaderBytes))
               ((cap.toNat - pb.pts.length) * vecHeaderBytes)) ∗
          vecVecU8At A (d + protoPolynomialEncoderPolysOff) pb.polys ∗
          ((d + protoPolynomialEncoderIdxOff) ↦₃₂ pb.idx) ∗
          memRegion (d + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize)) by ac_rfl)) ?_
  apply Entails.pure_left; intro hp
  have hcap_lt : cap.toNat < 2 ^ 63 := by
    have hlt := hp.2.1; unfold vecHeaderBytes at hlt; omega
  refine Entails.pure_right hcap_lt ?_
  refine Entails.trans ?_
    (Entails.of_eq (show
      ⌜pb.pts.length ≤ cap.toNat ∧ cap.toNat * vecHeaderBytes < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((d ↦₆₄ cap) ∗
        (((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * vecHeaderBytes) 8 ∗
             arrayAt (fun bs addr => vecU8 A addr bs) vecHeaderBytes ptr pb.pts ∗
             memRegion (ptr + BitVec.ofNat 64 (pb.pts.length * vecHeaderBytes))
               ((cap.toNat - pb.pts.length) * vecHeaderBytes)) ∗
          vecVecU8At A (d + protoPolynomialEncoderPolysOff) pb.polys ∗
          ((d + protoPolynomialEncoderIdxOff) ↦₃₂ pb.idx) ∗
          memRegion (d + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize)) = _ by ac_rfl))
  exact Entails.pure_right hp (Entails.refl _)

theorem protoPolynomialEncoderAt_unexpose_cap (A : RustAlloc) (d cap ptr : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    (d ↦₆₄ cap) ∗ protoPolynomialEncoderRestAt A d cap ptr pb ⊢
      protoPolynomialEncoderAt A d pb := by
  unfold protoPolynomialEncoderAt
  nth_rw 1 [vecVecU8At]
  unfold vecOf
  refine Entails.trans ?_
    (sepConj_mono_left (Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))))
  unfold protoPolynomialEncoderRestAt vecAt vecHeader
  exact Entails.of_eq (by ac_rfl)

theorem protoPolyDecoderTail_entails_memRegion_16 (d : BitVec 64)
    (ptsNeeded polys : BitVec 32) (isComplete : Bool) :
    ((d + protoPolynomialDecoderPtsNeededOff) ↦₃₂ ptsNeeded) ∗
      ((d + protoPolynomialDecoderPolysOff) ↦₃₂ polys) ∗
      ((d + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte isComplete) ∗
      memRegion (d + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize ⊢
    memRegion (d + 24#64) 16 := by
  unfold protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
    protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
    protoPolynomialDecoderPadSize
  rw [show (24#64 : BitVec 64) = 0x18#64 from rfl,
      ProofLib.memRegion_split' (b := d + 0x18#64) (n := 4) (k := 12)
        (b' := d + 0x1c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := d + 0x1c#64) (n := 4) (k := 8)
        (b' := d + 0x20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := d + 0x20#64) (n := 1) (k := 7)
        (b' := d + 0x21#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo8_entails_memRegion _ _)))

theorem protoPolyDecoderAt_entails_dealloc (A : RustAlloc) (d : BitVec 64)
    (pb : ProtoPolynomialDecoder) :
    protoPolynomialDecoderAt A d pb ⊢
      ∃∗ g : VecPin,
        ⌜pb.pts.length ≤ g.cap.toNat ∧ g.cap.toNat * 24 < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        (d ↦₆₄ g.cap) ∗ ((d + 8#64) ↦₆₄ g.ptr) ∗
        ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if g.cap = 0 then emp
         else A.live g.ptr (g.cap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr pb.pts ∗
           memRegion (g.ptr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((g.cap.toNat - pb.pts.length) * 24)) ∗
        memRegion (d + 24#64) 16 := by
  unfold protoPolynomialDecoderAt vecVecU8At vecOf vecHeaderBytes
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptsCap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptsPtr
  refine Entails.sepExists_right ⟨ptsCap, ptsPtr⟩ ?_
  unfold vecAt vecBuf vecHeader
  have htl := protoPolyDecoderTail_entails_memRegion_16 d pb.ptsNeeded pb.polys pb.isComplete
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜pb.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
      ((d ↦₆₄ ptsCap) ∗ ((d + 8#64) ↦₆₄ ptsPtr) ∗
        ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if ptsCap = 0 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((ptsCap.toNat - pb.pts.length) * 24)) ∗
        (((d + protoPolynomialDecoderPtsNeededOff) ↦₃₂ pb.ptsNeeded) ∗
          ((d + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
          ((d + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
          memRegion (d + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
  refine Entails.pure_right ⟨h1, h2, h3⟩ ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right htl)))

theorem protoPolyDecoderHeaders_entails_memRegion_40 (d ptsCap ptsPtr ptsLen : BitVec 64) :
    (d ↦₆₄ ptsCap) ∗ ((d + 8#64) ↦₆₄ ptsPtr) ∗ ((d + 16#64) ↦₆₄ ptsLen) ∗
      memRegion (d + 24#64) 16 ⊢
    memRegion d 40 := by
  rw [ProofLib.memRegion_split' (b := d) (n := 8) (k := 32) (b' := d + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := d + 8#64) (n := 8) (k := 24) (b' := d + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := d + 16#64) (n := 8) (k := 16) (b' := d + 24#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))

theorem optProtoPolyDecoder_none_entails_memRegion_40 (d : BitVec 64) :
    ((d ↦₆₄ noneCap) ∗ memRegion (d + 8#64) 32) ⊢ memRegion d 40 := by
  rw [ProofLib.memRegion_split' (b := d) (n := 8) (k := 32) (b' := d + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion d noneCap)

/-! ### Flat-offset `ProtoAuthenticator` headers at `+24`, `+40`, `+48` -/

def auth24HeadersAt (a : BitVec 64) (ga : TwoVecGhost) : SepProp :=
  ((a + 24#64) ↦₆₄ ga.v1.cap) ∗ ((a + 32#64) ↦₆₄ ga.v1.ptr) ∗ memRegion (a + 40#64) 8 ∗
  ((a + 48#64) ↦₆₄ ga.v2.cap) ∗ ((a + 56#64) ↦₆₄ ga.v2.ptr) ∗ memRegion (a + 64#64) 8

theorem twoVecHeadersAt_24_eq (a : BitVec 64) (ga : TwoVecGhost) :
    twoVecHeadersAt (a + 24#64) ga = auth24HeadersAt a ga := by
  unfold twoVecHeadersAt auth24HeadersAt
  rw [BitVec.add_assoc a 24#64 8#64, BitVec.add_assoc a 24#64 16#64,
      BitVec.add_assoc a 24#64 24#64, BitVec.add_assoc a 24#64 32#64,
      BitVec.add_assoc a 24#64 40#64]
  rfl

theorem auth24HeadersAt_entails_memRegion_48 (a : BitVec 64) (ga : TwoVecGhost) :
    ((a + 24#64) ↦₆₄ ga.v1.cap) ∗ ((a + 32#64) ↦₆₄ ga.v1.ptr) ∗ memRegion (a + 40#64) 8 ∗
      ((a + 48#64) ↦₆₄ ga.v2.cap) ∗ ((a + 56#64) ↦₆₄ ga.v2.ptr) ∗ memRegion (a + 64#64) 8 ⊢
    memRegion (a + 24#64) 48 := by
  change auth24HeadersAt a ga ⊢ memRegion (a + 24#64) 48
  rw [← twoVecHeadersAt_24_eq]
  exact twoVecHeadersAt_entails_memRegion_48 (a + 24#64) ga

theorem optProtoAuthenticatorAt_24_none (A : RustAlloc) (a : BitVec 64) :
    optProtoAuthenticatorAt A (a + 24#64) none =
      ((a + 24#64) ↦₆₄ noneCap) ∗ memRegion (a + 32#64) 40 := by
  rw [optProtoAuthenticatorAt_none, BitVec.add_assoc a 24#64 8#64]; rfl

theorem optProtoAuthenticatorAt_24_none_entails_memRegion_48 (A : RustAlloc) (a : BitVec 64) :
    ((a + 24#64) ↦₆₄ noneCap) ∗ memRegion (a + 32#64) 40 ⊢ memRegion (a + 24#64) 48 := by
  have h1 : (a + 24#64) + 8#64 = a + 32#64 := BitVec.add_assoc a 24#64 8#64
  rw [← h1]
  exact optProtoAuthenticatorAt_none_entails_memRegion_48 A (a + 24#64)

def auth40HeadersAt (a : BitVec 64) (ga : TwoVecGhost) : SepProp :=
  ((a + 40#64) ↦₆₄ ga.v1.cap) ∗ ((a + 48#64) ↦₆₄ ga.v1.ptr) ∗ memRegion (a + 56#64) 8 ∗
  ((a + 64#64) ↦₆₄ ga.v2.cap) ∗ ((a + 72#64) ↦₆₄ ga.v2.ptr) ∗ memRegion (a + 80#64) 8

theorem twoVecHeadersAt_40_eq (a : BitVec 64) (ga : TwoVecGhost) :
    twoVecHeadersAt (a + 40#64) ga = auth40HeadersAt a ga := by
  unfold twoVecHeadersAt auth40HeadersAt
  rw [BitVec.add_assoc a 40#64 8#64, BitVec.add_assoc a 40#64 16#64,
      BitVec.add_assoc a 40#64 24#64, BitVec.add_assoc a 40#64 32#64,
      BitVec.add_assoc a 40#64 40#64]
  rfl

theorem auth40HeadersAt_entails_memRegion_56 (a : BitVec 64) (ga : TwoVecGhost) (epoch : BitVec 64) :
    ((a + 40#64) ↦₆₄ ga.v1.cap) ∗ ((a + 48#64) ↦₆₄ ga.v1.ptr) ∗ memRegion (a + 56#64) 8 ∗
      ((a + 64#64) ↦₆₄ ga.v2.cap) ∗ ((a + 72#64) ↦₆₄ ga.v2.ptr) ∗ memRegion (a + 80#64) 8 ∗
      (((a + 40#64) + 48#64) ↦₆₄ epoch) ⊢ memRegion (a + 40#64) 56 := by
  refine Entails.trans
    (Entails.of_eq (show _ = auth40HeadersAt a ga ∗ (((a + 40#64) + 48#64) ↦₆₄ epoch) by
      unfold auth40HeadersAt; ac_rfl)) ?_
  rw [← twoVecHeadersAt_40_eq,
      ProofLib.memRegion_split' (b := a + 40#64) (n := 48) (k := 8)
        (b' := (a + 40#64) + 48#64) rfl rfl (by decide)]
  exact sepConj_mono (twoVecHeadersAt_entails_memRegion_48 (a + 40#64) ga)
    (pointsTo64_entails_memRegion _ _)

theorem optProtoAuthenticatorAt_40_none_entails_memRegion_56 (A : RustAlloc) (a : BitVec 64) (epoch : BitVec 64) :
    ((a + 40#64) ↦₆₄ noneCap) ∗ memRegion (a + 48#64) 40 ∗ (((a + 40#64) + 48#64) ↦₆₄ epoch) ⊢
      memRegion (a + 40#64) 56 := by
  have hnone40 : optProtoAuthenticatorAt A (a + 40#64) none =
      ((a + 40#64) ↦₆₄ noneCap) ∗ memRegion (a + 48#64) 40 := by
    rw [optProtoAuthenticatorAt_none, BitVec.add_assoc a 40#64 8#64]; rfl
  rw [← sepConj_assoc, ← hnone40,
      ProofLib.memRegion_split' (b := a + 40#64) (n := 48) (k := 8)
        (b' := (a + 40#64) + 48#64) rfl rfl (by decide)]
  exact sepConj_mono (optProtoAuthenticatorAt_none_entails_memRegion_48 A (a + 40#64))
    (pointsTo64_entails_memRegion _ _)

def auth48HeadersAt (a : BitVec 64) (ga : TwoVecGhost) : SepProp :=
  ((a + 48#64) ↦₆₄ ga.v1.cap) ∗ ((a + 56#64) ↦₆₄ ga.v1.ptr) ∗ memRegion (a + 64#64) 8 ∗
  ((a + 72#64) ↦₆₄ ga.v2.cap) ∗ ((a + 80#64) ↦₆₄ ga.v2.ptr) ∗ memRegion (a + 88#64) 8

theorem twoVecHeadersAt_48_eq (a : BitVec 64) (ga : TwoVecGhost) :
    twoVecHeadersAt (a + 48#64) ga = auth48HeadersAt a ga := by
  unfold twoVecHeadersAt auth48HeadersAt
  rw [BitVec.add_assoc a 48#64 8#64, BitVec.add_assoc a 48#64 16#64,
      BitVec.add_assoc a 48#64 24#64, BitVec.add_assoc a 48#64 32#64,
      BitVec.add_assoc a 48#64 40#64]
  rfl

theorem auth48HeadersAt_entails_memRegion_48 (a : BitVec 64) (ga : TwoVecGhost) :
    ((a + 48#64) ↦₆₄ ga.v1.cap) ∗ ((a + 56#64) ↦₆₄ ga.v1.ptr) ∗ memRegion (a + 64#64) 8 ∗
      ((a + 72#64) ↦₆₄ ga.v2.cap) ∗ ((a + 80#64) ↦₆₄ ga.v2.ptr) ∗ memRegion (a + 88#64) 8 ⊢
    memRegion (a + 48#64) 48 := by
  change auth48HeadersAt a ga ⊢ memRegion (a + 48#64) 48
  rw [← twoVecHeadersAt_48_eq]
  exact twoVecHeadersAt_entails_memRegion_48 (a + 48#64) ga

theorem optProtoAuthenticatorAt_48_none (A : RustAlloc) (a : BitVec 64) :
    optProtoAuthenticatorAt A (a + 48#64) none =
      ((a + 48#64) ↦₆₄ noneCap) ∗ memRegion (a + 56#64) 40 := by
  rw [optProtoAuthenticatorAt_none, BitVec.add_assoc a 48#64 8#64]; rfl

theorem optProtoAuthenticatorAt_48_none_entails_memRegion_48 (A : RustAlloc) (a : BitVec 64) :
    ((a + 48#64) ↦₆₄ noneCap) ∗ memRegion (a + 56#64) 40 ⊢ memRegion (a + 48#64) 48 := by
  have h1 : (a + 48#64) + 8#64 = a + 56#64 := BitVec.add_assoc a 48#64 8#64
  rw [← h1]
  exact optProtoAuthenticatorAt_none_entails_memRegion_48 A (a + 48#64)

theorem protoUnchunked2VecHeadersAt_entails_memRegion_104' (a : BitVec 64) (g : TwoVecGhost) :
    (a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
      ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8 ∗
      memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ⊢
    memRegion a 104 := by
  refine Entails.trans
    (Entails.of_eq (show _ = protoUnchunked2VecHeadersAt a g ∗ memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 by
      unfold protoUnchunked2VecHeadersAt twoVecHeadersAt; ac_rfl)) ?_
  exact protoUnchunked2VecHeadersAt_entails_memRegion_104 a g

theorem protoUnchunked1VecHeadersAt_entails_memRegion_80' (a : BitVec 64) (v1 : VecPin) :
    (a ↦₆₄ v1.cap) ∗ ((a + 8#64) ↦₆₄ v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
      memRegion (a + 24#64) 48 ∗ memRegion (a + 72#64) 8 ⊢
    memRegion a 80 := by
  refine Entails.trans
    (Entails.of_eq (show _ = protoUnchunked1VecHeadersAt a v1 ∗ memRegion (a + 24#64) 48 ∗ memRegion (a + 72#64) 8 by
      unfold protoUnchunked1VecHeadersAt; ac_rfl)) ?_
  exact protoUnchunked1VecHeadersAt_entails_memRegion_80 a v1

theorem optProtoUnchunked2Vec_none_entails_memRegion_104 (a : BitVec 64) :
    (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96 ⊢ memRegion a 104 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 96) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a noneCap)

theorem optProtoUnchunked1Vec_none_entails_memRegion_80 (a : BitVec 64) :
    (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72 ⊢ memRegion a 80 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 72) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a noneCap)

/-! ### Stack Frame Split for `0x4cb70` (`32`B frame inside `dropStack48`) -/

theorem stackAt_dropStack48_split32 (sp : BitVec 64) :
    stackAt sp dropStack48 =
      stackAt (sp - 32#64) (allocHookStack + 16) ∗ cells (sp - 32#64) 4 :=
  stackAt_split_cells sp (allocHookStack + 16) 4 (by decide)

theorem stackAt_allocHook16_split_bottom (sp : BitVec 64) :
    stackAt sp (allocHookStack + 16) = memRegion (sp - 4112#64) 16 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 16 (by decide)

theorem stack_restore_48_from_32 (sp fp lr x20 x19 : BitVec 64) :
    (memRegion (sp - 4144#64) 16 ∗ stackAt (sp - 32#64) allocHookStack) ∗
      (((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropStack48 := by
  have hsub : (sp - 32#64) - 4112#64 = sp - 4144#64 := by bv_omega
  rw [stackAt_dropStack48_split32 sp, stackAt_allocHook16_split_bottom (sp - 32#64), hsub]
  exact sepConj_mono_right (cells4_sub32_entails sp fp lr x20 x19)

/-! ## Specifications for PB Chunked Drop Glue -/

structure DropProtoChunkedCt1ReceivedGhost where
  a : BitVec 64
  st : V1State.Chunked.Ct1Received

def dropProtoChunkedCt1ReceivedSpec (A : RustAlloc) :
    Spec DropProtoChunkedCt1ReceivedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoChunkedCt1ReceivedAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStack48
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a protoChunkedCt1ReceivedSize ∗
      A.pool ∗ stackAt s0.sp dropStack48

structure DropProtoChunkedNoHeaderReceivedGhost where
  a : BitVec 64
  st : V1State.Chunked.NoHeaderReceived

def dropProtoChunkedNoHeaderReceivedSpec (A : RustAlloc) :
    Spec DropProtoChunkedNoHeaderReceivedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoChunkedNoHeaderReceivedAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStack48
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a protoChunkedNoHeaderReceivedSize ∗
      A.pool ∗ stackAt s0.sp dropStack48

structure DropProtoChunkedHeaderReceivedGhost where
  a : BitVec 64
  st : V1State.Chunked.HeaderReceived

def dropProtoChunkedHeaderReceivedSpec (A : RustAlloc) :
    Spec DropProtoChunkedHeaderReceivedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoChunkedHeaderReceivedAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStack48
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a protoChunkedHeaderReceivedSize ∗
      A.pool ∗ stackAt s0.sp dropStack48

structure DropProtoChunkedEkSentCt1ReceivedGhost where
  a : BitVec 64
  st : V1State.Chunked.EkSentCt1Received

def dropProtoChunkedEkSentCt1ReceivedSpec (A : RustAlloc) :
    Spec DropProtoChunkedEkSentCt1ReceivedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoChunkedEkSentCt1ReceivedAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStack48
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a protoChunkedEkSentCt1ReceivedSize ∗
      A.pool ∗ stackAt s0.sp dropStack48

/-- Stack budget for `drop_glue::<proto::pq_ratchet::v1_state::chunked::HeaderSent>` (`0x4ca84`):
    48B own frame + 48B callee frame (`drop_glue::<ProtoPolynomialEncoder>` `0x4c500`). -/
abbrev dropStack96 : Nat := dropStack48 + 48

structure DropProtoChunkedHeaderSentGhost where
  a : BitVec 64
  st : V1State.Chunked.HeaderSent

def dropProtoChunkedHeaderSentSpec (A : RustAlloc) :
    Spec DropProtoChunkedHeaderSentGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoChunkedHeaderSentAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStack96
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a protoChunkedHeaderSentSize ∗
      A.pool ∗ stackAt s0.sp dropStack96

/-! ## `drop_glue::<proto::pq_ratchet::v1_state::chunked::Ct1Received>` (`0x4cb70`) -/

local macro "proto_chunked_ct1_received_steps" entry:term : tactic =>
  `(tactic| (
  wp_init x s0
  rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropProtoChunkedCt1ReceivedGhost.a, DropProtoChunkedCt1ReceivedGhost.st,
    protoChunkedCt1ReceivedAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  have hsub_4144 : (s0.sp - 32#64) - 4112#64 = s0.sp - 4144#64 := by bv_omega
  nth_rw 1 [stackAt_dropStack48_split32 s0.sp]
  nth_rw 1 [stackAt_allocHook16_split_bottom (s0.sp - 32#64)]
  rw [hsub_4144]
  cells_unfold
  wp_pull_exists
  rename_i fp_old lr_old x20_old x19_old
  refine seq_clean (mid := $entry + 116#64)
    (P_mid := (memRegion a 104 ∗
      optProtoPolynomialEncoderAt A (a + 104#64) (st.sendingEk.map pbToProtoPolyEncoder)) ∗
      A.pool ∗
      (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_none]
      wp_steps
      refine SepWP.focus_weaken
        (optProtoUnchunked2Vec_none_entails_memRegion_104 a)
        (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
    | some u =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_some]
      refine SepWP.weaken_pre
        (sepConj_mono_left (protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc A a u)) ?_
      wp_pull_exists; rename_i g
      wp_focus_pure; intro hcap1_lt
      have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
      refine seq_clean (mid := $entry + 76#64)
        (P_mid := ((protoUnchunked2VecHeadersAt a g ∗
          memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
          optProtoPolynomialEncoderAt A (a + 104#64) (st.sendingEk.map pbToProtoPolyEncoder)) ∗
          A.pool ∗
          (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
        ?_ ?_
      · cases hauth : u.auth with
        | none =>
          rw [optProtoAuthenticatorAt_48_none]
          dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt]
          wp_steps
          refine SepWP.focus_weaken
            (optProtoAuthenticatorAt_48_none_entails_memRegion_48 A a)
            (by sep_focus) ?_
          refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken
            (protoAuthenticatorAt_entails_dealloc A (a + 48#64) auth)
            (by sep_focus) ?_
          wp_pull_exists; rename_i ga
          rw [twoVecHeadersAt_48_eq]
          wp_focus_pure; intro hga_lt
          have hne_nonea := cap_add_one_beq_zero_false hga_lt
          refine seq_clean (mid := $entry + 56#64)
            (P_mid := ((protoUnchunked2VecHeadersAt a g ∗
              (auth48HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
              memRegion (a + 96#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
              optProtoPolynomialEncoderAt A (a + 104#64) (st.sendingEk.map pbToProtoPolyEncoder)) ∗
              A.pool ∗
              (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
            ?_ ?_
          · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt, vecCapPtrDealloc]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
              simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
            · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
          · intro sa1 hpca1 hruna1 ⟨⟨hx21_a1, hx22_a1, hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx19_a1, hx20_a1⟩
            dsimp only [auth48HeadersAt, vecCapPtrDealloc]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
              simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps
              refine SepWP.focus_weaken (auth48HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
            · wp_steps; wp_apply
              refine SepWP.focus_weaken (auth48HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre (by rw [hsp_a1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
        refine seq_clean (mid := $entry + 96#64)
          (P_mid := ((protoUnchunked2VecHeadersAt a g ∗
            memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
            vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
            optProtoPolynomialEncoderAt A (a + 104#64) (st.sendingEk.map pbToProtoPolyEncoder)) ∗
            A.pool ∗
            (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
          by_cases hc1 : (g.v1.cap == 0#64) = true <;>
            simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
        · intro s2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
          dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
          by_cases hc2 : (g.v2.cap == 0#64) = true <;>
            simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.focus_weaken
              (protoUnchunked2VecHeadersAt_entails_memRegion_104' a g)
              (by sep_focus) ?_
            wp_done
          · wp_steps; wp_apply
            refine SepWP.focus_weaken
              (protoUnchunked2VecHeadersAt_entails_memRegion_104' a g)
              (by sep_focus) ?_
            refine align_pre (by rw [hsp_2]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
  · intro s3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
    cases hek : st.sendingEk with
    | none =>
      simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
      have h112 : (a + 104#64) + 8#64 = a + 112#64 := BitVec.add_assoc a 104#64 8#64
      rw [h112]
      wp_steps
      have hjoin : memRegion a 104 ∗ ((a + 104#64) ↦₆₄ noneCap) ∗ memRegion (a + 112#64) 48 ⊢
          memRegion a 160 := by
        rw [← h112,
            ProofLib.memRegion_split' (b := a) (n := 104) (k := 56) (b' := a + 104#64) rfl rfl (by decide)]
        exact sepConj_mono_right (optProtoPolyEncoder_none_entails_memRegion_56 (a + 104#64))
      refine SepWP.focus_weaken hjoin (by sep_focus) ?_
      refine SepWP.focus_weaken
        (stack_restore_48_from_32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x20) (s0.readReg64 .x19))
        (by sep_focus) ?_
      wp_done
    | some enc =>
      simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
      refine SepWP.focus_weaken
        (protoPolynomialEncoderAt_expose_cap A (a + 104#64) (pbToProtoPolyEncoder enc))
        (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr
      wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      wp_steps
      refine SepWP.focus_weaken
        (protoPolynomialEncoderAt_unexpose_cap A (a + 104#64) cap ptr (pbToProtoPolyEncoder enc))
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (stack_restore_48_from_32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x20) (s0.readReg64 .x19))
        (by sep_focus) ?_
      wp_call hpoly_enc_raw ⟨a + 104#64, pbToProtoPolyEncoder enc⟩
      have hjoin : memRegion a 104 ∗ memRegion (a + 104#64) protoPolynomialEncoderSize ⊢
          memRegion a 160 := by
        rw [show (160 : Nat) = 104 + protoPolynomialEncoderSize from rfl,
            ProofLib.memRegion_split a 104 protoPolynomialEncoderSize (by decide)]
        exact Entails.refl _
      refine SepWP.focus_weaken hjoin (by sep_focus) ?_
      wp_done))

theorem drop_proto_chunked_ct1_received_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedCt1ReceivedName)
      (dropProtoChunkedCt1ReceivedSpec A) := by
  simp only [dropProtoChunkedCt1ReceivedSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedCt1ReceivedName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>") (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hpoly_enc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedCt1ReceivedName +
        bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>"))
      (dropProtoPolyEncoderSpec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropProtoChunkedCt1ReceivedName =
        (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName +
          bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>") :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>")) (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>")
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>") (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_proto_poly_encoder_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [rustDeallocSpec] at hdealloc_raw
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>"
  dsimp only [dropProgAtExt, dropProtoChunkedCt1ReceivedName,
    protoChunkedCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpoly_enc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>" = entry
  examples_hide_fetches; proto_chunked_ct1_received_steps entry

theorem drop_proto_chunked_ct1_received_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_282).rebase (blkPl_282).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpoly_enc_raw : subroutine_ok ((blkPC_282).rebase (blkPl_282).base H)
      (lsmpl.base 271) (dropProtoPolyEncoderSpec A)) :
    subroutine_ok ((blkPC_282).rebase (blkPl_282).base H) (blkPl_282).base
      (dropProtoChunkedCt1ReceivedSpec A) := by
  simp only [dropProtoChunkedCt1ReceivedSpec]
  have hdealloc_raw := hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [protoChunkedCt1ReceivedSize] at *
  proto_chunked_ct1_received_steps (blkPl_282).base

/-! ## `drop_glue::<proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>` (`0x4cce4`) -/

local macro "proto_chunked_no_header_received_body_steps" prog:term:max entry:term:max : tactic =>
  `(tactic| (
  intro cur cnt bs s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP $prog ($entry + 104#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep))

local macro "proto_chunked_no_header_received_loop_steps" entry:term : tactic =>
  `(tactic| (
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := $entry + 104#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean (mid := $entry + 116#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ sm.readReg64 .x22 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2 hx21_2 hx22_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _))

local macro "proto_chunked_no_header_received_main_steps" entry:term : tactic =>
  `(tactic| (
  wp_init x s0; rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropProtoChunkedNoHeaderReceivedGhost.a, DropProtoChunkedNoHeaderReceivedGhost.st,
    protoChunkedNoHeaderReceivedAt] at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack48_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean (mid := $entry + 76#64)
    (P_mid := (optProtoPolynomialDecoderAt A a (st.receivingHdr.map pbToProtoPolyDecoder) ∗
      memRegion (a + 40#64) 56) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · cases huc : st.uc with
    | none =>
      have h48 : (a + 40#64) + 8#64 = a + 48#64 := BitVec.add_assoc a 40#64 8#64
      rw [optProtoUnchunkedNoHeaderReceivedAt_none, h48]
      wp_steps
      have hjoin : ((a + 40#64) ↦₆₄ none2Cap) ∗ memRegion (a + 48#64) 48 ⊢ memRegion (a + 40#64) 56 := by
        rw [← h48]
        exact optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A (a + 40#64)
      refine SepWP.focus_weaken hjoin (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
    | some u =>
      rw [optProtoUnchunkedNoHeaderReceivedAt_some]
      unfold protoUnchunkedNoHeaderReceivedAt
      cases hauth : u.auth with
      | none =>
        have hnone40 : optProtoAuthenticatorAt A (a + 40#64) none =
            ((a + 40#64) ↦₆₄ noneCap) ∗ memRegion (a + 48#64) 40 := by
          rw [optProtoAuthenticatorAt_none, BitVec.add_assoc a 40#64 8#64]; rfl
        rw [hnone40]
        wp_steps
        refine SepWP.focus_weaken
          (optProtoAuthenticatorAt_40_none_entails_memRegion_56 A a u.epoch)
          (by sep_focus) ?_
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.focus_weaken
          (protoAuthenticatorAt_entails_dealloc A (a + 40#64) auth)
          (by sep_focus) ?_
        wp_pull_exists; rename_i ga
        rw [twoVecHeadersAt_40_eq]
        wp_focus_pure; intro hga_lt
        have hne_none2 := cap_add_two_beq_zero_false hga_lt
        have hne_none1 := cap_add_one_beq_zero_false hga_lt
        refine seq_clean (mid := $entry + 56#64)
          (P_mid := (optProtoPolynomialDecoderAt A a (st.receivingHdr.map pbToProtoPolyDecoder) ∗
            ((auth40HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
             (((a + 40#64) + 48#64) ↦₆₄ u.epoch))) ∗
            A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [auth40HeadersAt, vecCapPtrDealloc]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
            simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
          · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
        · intro sa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx19_a1⟩
          dsimp only [auth40HeadersAt, vecCapPtrDealloc]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
            simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.focus_weaken (auth40HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
            refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
          · wp_steps; wp_apply
            refine SepWP.focus_weaken (auth40HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
            refine align_pre (by rw [hsp_a1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    have hjoin96_from_40 : memRegion a 40 ∗ memRegion (a + 40#64) 56 ⊢ memRegion a 96 := by
      rw [ProofLib.memRegion_split' (b := a) (n := 40) (k := 56) (b' := a + 40#64) rfl rfl (by decide)]
      exact Entails.refl _
    cases hhdr : st.receivingHdr with
    | none =>
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
      wp_steps
      refine SepWP.focus_weaken (optProtoPolyDecoder_none_entails_memRegion_40 a) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin96_from_40 (by sep_focus) ?_
      refine SepWP.focus_weaken
        (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
        (by sep_focus) ?_
      wp_done
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
      let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A a pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g
      wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
      refine seq_clean (mid := $entry + 140#64)
        (P_mid := (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if g.cap = 0 then emp
           else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
          memRegion (a + 24#64) 16 ∗ memRegion (a + 40#64) 56 ∗
          A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap)
        ?_ ?_
      · generalize hxs : pb.pts = xs at hpts_le ⊢
        cases xs with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
            BitVec.add_zero, arrayAt, emp_sepConj]
          wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
        | cons bs tl =>
          have hlen_pos : 0 < (bs :: tl).length := by simp
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
            have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
            omega
          have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
          have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_clean (mid := $entry + 116#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              ((a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗
               ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
               A.live g.ptr (g.cap.toNat * 24) 8 ∗
               memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
                 ((g.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (a + 24#64) 16 ∗ memRegion (a + 40#64) 56 ∗
               (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
              sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
              sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64)
            ?_ ?_
          · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
          · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
            refine SepWP.strengthen_entails_const ?_
              (hloop s0 (s0.sp - 48#64) g.ptr g.cap hfsp_align (bs :: tl) g.ptr s_loop _
                (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
                hx19_loop hx20_loop hx21_loop hx22_loop)
            have hsplit : g.cap.toNat * 24 =
                (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
              rw [← Nat.add_mul]; congr 1; omega
            have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
              rw [← hsplit]; omega
            conv_rhs =>
              arg 2; arg 2; arg 2; arg 1; arg 2
              rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24)
                    ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
            exact Entails.of_eq (by ac_rfl)
      · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2⟩
        by_cases hc : g.cap = 0
        · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_2 ⊢; wp_steps
          refine SepWP.focus_weaken
            (protoPolyDecoderHeaders_entails_memRegion_40 a 0 g.ptr (BitVec.ofNat 64 pb.pts.length))
            (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin96_from_40 (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
            (by sep_focus) ?_
          wp_done
        · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_mul_24 hpts_cap_lt
          simp only [hc, ↓reduceIte]; wp_steps
          refine SepWP.focus_weaken
            (protoPolyDecoderHeaders_entails_memRegion_40 a g.cap g.ptr (BitVec.ofNat 64 pb.pts.length))
            (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin96_from_40 (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
            (by sep_focus) ?_
          rw [stackAt_dropStack48_split_bottom s0.sp]
          wp_call hdealloc_raw (g.ptr, g.cap.toNat * 24, 8)
          rw [← stackAt_dropStack48_split_bottom s0.sp]
          wp_done))

private theorem drop_proto_chunked_no_header_received_body {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedNoHeaderReceivedName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoChunkedNoHeaderReceivedName + 116#64 →
      s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext)
        ((dropProgAtExt b ext).fnAddr dropProtoChunkedNoHeaderReceivedName + 104#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [dropProgAtExt, dropProtoChunkedNoHeaderReceivedName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>" = entry
  examples_hide_fetches; proto_chunked_no_header_received_body_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry

private theorem drop_proto_chunked_no_header_received_loop {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedNoHeaderReceivedName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoChunkedNoHeaderReceivedName + 116#64 →
      s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext)
        ((dropProgAtExt b ext).fnAddr dropProtoChunkedNoHeaderReceivedName + 140#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_proto_chunked_no_header_received_body (b := b) (ext := ext) hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  dsimp only [dropProgAtExt, dropProtoChunkedNoHeaderReceivedName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>" = entry
  examples_hide_fetches; proto_chunked_no_header_received_loop_steps entry

theorem drop_proto_chunked_no_header_received_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedNoHeaderReceivedName)
      (dropProtoChunkedNoHeaderReceivedSpec A) := by
  simp only [dropProtoChunkedNoHeaderReceivedSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedNoHeaderReceivedName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>") (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hloop := drop_proto_chunked_no_header_received_loop (b := b) (ext := ext) hdealloc_raw
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>"
  dsimp only [dropProgAtExt, dropProtoChunkedNoHeaderReceivedName,
    protoChunkedNoHeaderReceivedSize, BitVec.ofNat_eq_ofNat] at hloop hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>" = entry
  examples_hide_fetches; proto_chunked_no_header_received_main_steps entry

section PlacedProtoChunkedNoHeaderReceived
variable [LibsignalPlacement]

private theorem drop_proto_chunked_no_header_received_body_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_284).rebase (blkPl_284).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_284).base + 116#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_284).rebase (blkPl_284).base H) ((blkPl_284).base + 104#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc
  proto_chunked_no_header_received_body_steps ((blkPC_284).rebase (blkPl_284).base H) (blkPl_284).base

private theorem drop_proto_chunked_no_header_received_loop_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_284).rebase (blkPl_284).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_284).base + 116#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_284).rebase (blkPl_284).base H) ((blkPl_284).base + 140#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_proto_chunked_no_header_received_body_placed hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  proto_chunked_no_header_received_loop_steps (blkPl_284).base

theorem drop_proto_chunked_no_header_received_placed_ok {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_284).rebase (blkPl_284).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_284).rebase (blkPl_284).base H) (blkPl_284).base
      (dropProtoChunkedNoHeaderReceivedSpec A) := by
  simp only [dropProtoChunkedNoHeaderReceivedSpec]
  have hdealloc_raw := hdealloc
  have hloop := drop_proto_chunked_no_header_received_loop_placed hdealloc_raw
  dsimp only [protoChunkedNoHeaderReceivedSize] at *
  proto_chunked_no_header_received_main_steps (blkPl_284).base

end PlacedProtoChunkedNoHeaderReceived

end CryptoVerification.SpqrV1.Drop
